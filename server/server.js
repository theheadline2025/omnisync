#!/usr/bin/env node
/**
 * OmniSync server
 * ===========================================================================
 * Zero-dependency Node.js server: HTTP + RFC 6455 WebSocket, room registry,
 * authoritative timeline (with RTT back-dating), leader delegation, WebRTC
 * signalling relay, heartbeats and drift telemetry intake.
 *
 * Why no `ws` dependency: this file must run with nothing but `node server.js`.
 * The WebSocket layer below is a deliberately small, hazarding-free subset of
 * RFC 6455 (text frames, fragmentation, ping/pong, close). It does not
 * implement permessage-deflate and never negotiates extensions.
 *
 * Endpoints
 *   ws://<host>:<port>/          protocol endpoint (also accepted on any path)
 *   GET /                        human-readable status page
 *   GET /health                  JSON health probe
 *   GET /demo                    self-hosted media test page
 *   GET /media/tone.wav          60 s generated WAV (no assets on disk)
 * ===========================================================================
 */

'use strict';

const http = require('node:http');
const crypto = require('node:crypto');
const { EventEmitter } = require('node:events');

/* ===========================================================================
 * 1. Configuration
 * ======================================================================== */

/**
 * Capabilities this build actually implements. Advertised on /health so a
 * client can refuse to talk to an outdated server instead of silently losing
 * frames it does not understand.
 */
const FEATURES = Object.freeze([
  'clock',
  'sync.command',
  'sync.pulse',
  'leader.migrate',
  'chat',
  'reactions',
  'typing',
  'chat.history',
]);

/** Coarse build marker: changes whenever the advertised surface changes. */
const BUILD_ID = '1.1.0+chat';

const CONFIG = {
  port: Number(process.env.PORT || 8787),
  host: process.env.HOST || '0.0.0.0',

  protocolVersion: 1,
  maxPayload: 16 * 1024,             // C→S frame cap (spec §10.1)
  maxBufferBytes: 256 * 1024,        // hard stop for a slow-drip attacker
  handshakeTimeoutMs: 10000,
  idleTimeoutMs: 90000,              // no pong/no frames → drop
  pingIntervalMs: 25000,

  maxRooms: 5000,
  maxMembersPerRoom: 32,
  roomTtlMs: 5 * 60 * 1000,          // empty room GC

  rateLimit: { frames: 120, windowMs: 10000 },
  commandLimit: { frames: 12, windowMs: 1000 },
  chatLimit: { frames: 8, windowMs: 10000 },
  chatHistory: 50,
  chatMaxLength: 500,

  scheduleSlack: { min: 80, max: 400, default: 120, marginMs: 40 },

  logLevel: process.env.LOG_LEVEL || 'info',
};

/* ===========================================================================
 * 2. Logging + time
 * ======================================================================== */

const LEVELS = { error: 0, warn: 1, info: 2, debug: 3 };
const CURRENT_LEVEL = LEVELS[CONFIG.logLevel] != null ? LEVELS[CONFIG.logLevel] : LEVELS.info;

function emit(level, ...args) {
  if (LEVELS[level] > CURRENT_LEVEL) return;
  const ts = new Date().toISOString();
  const fn = level === 'error' ? console.error : level === 'warn' ? console.warn : console.log;
  fn(`[${ts}] [${level}]`, ...args);
}
const log = {
  error: (...a) => emit('error', ...a),
  warn: (...a) => emit('warn', ...a),
  info: (...a) => emit('info', ...a),
  debug: (...a) => emit('debug', ...a),
};

// Monotonic server clock: immune to NTP steps for the life of the process.
const BOOT_WALL = Date.now();
const BOOT_MONO = performance.now();
const serverNow = () => Math.round(BOOT_WALL + (performance.now() - BOOT_MONO));

const clamp = (n, lo, hi) => (Number.isFinite(n) ? (n < lo ? lo : n > hi ? hi : n) : lo);
const median = (arr) => {
  if (!arr.length) return 0;
  const s = [...arr].sort((a, b) => a - b);
  const m = s.length >> 1;
  return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2;
};

const ID_ALPHABET = '0123456789abcdefghjkmnpqrstvwxyz';
function ulid() {
  const t = Date.now().toString(36).padStart(9, '0');
  const bytes = crypto.randomBytes(16);
  let out = '';
  for (let i = 0; i < 16; i++) out += ID_ALPHABET[bytes[i] % 32];
  return (t + out).slice(0, 26);
}

/** Human-typable room code: no 0/O/1/I/L ambiguity. */
const CODE_ALPHABET = 'ABCDEFGHJKMNPQRSTUVWXYZ23456789';
function roomCode(len = 6) {
  const bytes = crypto.randomBytes(len);
  let out = '';
  for (let i = 0; i < len; i++) out += CODE_ALPHABET[bytes[i] % CODE_ALPHABET.length];
  return out;
}

/* ===========================================================================
 * 3. Minimal RFC 6455 WebSocket implementation
 * ======================================================================== */

const WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
const OP = { CONT: 0x0, TEXT: 0x1, BINARY: 0x2, CLOSE: 0x8, PING: 0x9, PONG: 0xa };

class WsConnection extends EventEmitter {
  constructor(socket, head) {
    super();
    this.socket = socket;
    this.buffer = head && head.length ? Buffer.from(head) : Buffer.alloc(0);
    this.fragments = [];
    this.fragmentOpcode = 0;
    this.closed = false;
    this.lastFrameAt = Date.now();
    this.isAlive = true;

    socket.setNoDelay(true);
    socket.on('data', (chunk) => this._onData(chunk));
    socket.on('close', () => this._finalize());
    socket.on('error', (err) => {
      log.debug('socket error:', err && err.message);
      this._finalize();
    });
    socket.on('end', () => this._finalize());

    if (this.buffer.length) {
      const pending = this.buffer;
      this.buffer = Buffer.alloc(0);
      this._onData(pending);
    }
  }

  /* --- inbound ------------------------------------------------------ */
  _onData(chunk) {
    if (this.closed) return;
    this.buffer = this.buffer.length ? Buffer.concat([this.buffer, chunk]) : chunk;
    if (this.buffer.length > CONFIG.maxBufferBytes) {
      log.warn('buffer limit exceeded; closing');
      this.close(1009, 'buffer overflow');
      return;
    }
    // Parse as many complete frames as the buffer holds.
    for (;;) {
      const frame = this._tryParse();
      if (!frame) break;
      try {
        this._handleFrame(frame);
      } catch (err) {
        log.warn('frame handler threw:', err && err.message);
        this.close(1011, 'internal error');
        return;
      }
      if (this.closed) return;
    }
  }

  _tryParse() {
    const b = this.buffer;
    if (b.length < 2) return null;

    const b0 = b[0];
    const b1 = b[1];
    const fin = (b0 & 0x80) !== 0;
    const rsv = b0 & 0x70;
    const opcode = b0 & 0x0f;
    const masked = (b1 & 0x80) !== 0;
    let len = b1 & 0x7f;
    let offset = 2;

    // No extensions were negotiated, so RSV bits must be zero.
    if (rsv !== 0) {
      this.close(1002, 'reserved bits set');
      return null;
    }
    // Clients MUST mask (RFC 6455 §5.1).
    if (!masked) {
      this.close(1002, 'client frame not masked');
      return null;
    }

    if (len === 126) {
      if (b.length < 4) return null;
      len = b.readUInt16BE(2);
      offset = 4;
    } else if (len === 127) {
      if (b.length < 10) return null;
      const hi = b.readUInt32BE(2);
      const lo = b.readUInt32BE(6);
      if (hi > 0x1fffff) {
        this.close(1009, 'frame too large');
        return null;
      }
      len = hi * 0x100000000 + lo;
      offset = 10;
    }

    if (len > CONFIG.maxPayload) {
      this.close(1009, 'frame too large');
      return null;
    }
    if (b.length < offset + 4 + len) return null;

    const mask = b.subarray(offset, offset + 4);
    offset += 4;
    const payload = Buffer.allocUnsafe(len);
    for (let i = 0; i < len; i++) payload[i] = b[offset + i] ^ mask[i & 3];
    this.buffer = b.subarray(offset + len);

    return { fin, opcode, payload };
  }

  _handleFrame({ fin, opcode, payload }) {
    this.lastFrameAt = Date.now();
    this.isAlive = true;

    // Control frames may be interleaved and must not be fragmented.
    if (opcode >= 0x8) {
      if (!fin) {
        this.close(1002, 'fragmented control frame');
        return;
      }
      if (payload.length > 125) {
        this.close(1002, 'control frame too long');
        return;
      }
      switch (opcode) {
        case OP.PING:
          this._write(OP.PONG, payload);
          return;
        case OP.PONG:
          this.isAlive = true;
          return;
        case OP.CLOSE: {
          const code = payload.length >= 2 ? payload.readUInt16BE(0) : 1005;
          const reason = payload.length > 2 ? payload.subarray(2).toString('utf8') : '';
          log.debug('peer closed:', code, reason);
          this._write(OP.CLOSE, payload.length >= 2 ? payload.subarray(0, 2) : Buffer.alloc(0));
          this._finalize();
          return;
        }
        default:
          this.close(1002, 'unknown control opcode');
          return;
      }
    }

    // Data frames, possibly fragmented.
    if (opcode === OP.CONT) {
      if (!this.fragmentOpcode) {
        this.close(1002, 'continuation without start');
        return;
      }
      this.fragments.push(payload);
    } else {
      if (this.fragmentOpcode) {
        this.close(1002, 'interleaved data frames');
        return;
      }
      this.fragmentOpcode = opcode;
      this.fragments = [payload];
    }

    if (!fin) return;

    const total = Buffer.concat(this.fragments);
    const kind = this.fragmentOpcode;
    this.fragments = [];
    this.fragmentOpcode = 0;

    if (kind === OP.TEXT) {
      this.emit('message', total.toString('utf8'));
    } else if (kind === OP.BINARY) {
      this.emit('binary', total);
    }
  }

  /* --- outbound ----------------------------------------------------- */
  _write(opcode, payload) {
    if (this.closed || !this.socket.writable) return;
    const len = payload.length;
    let header;
    if (len < 126) {
      header = Buffer.allocUnsafe(2);
      header[1] = len;
    } else if (len < 65536) {
      header = Buffer.allocUnsafe(4);
      header[1] = 126;
      header.writeUInt16BE(len, 2);
    } else {
      header = Buffer.allocUnsafe(10);
      header[1] = 127;
      header.writeUInt32BE(Math.floor(len / 0x100000000), 2);
      header.writeUInt32BE(len >>> 0, 6);
    }
    header[0] = 0x80 | opcode; // FIN + opcode, server frames are never masked
    try {
      this.socket.write(Buffer.concat([header, payload]));
    } catch (err) {
      log.debug('write failed:', err && err.message);
      this._finalize();
    }
  }

  send(text) {
    this._write(OP.TEXT, Buffer.from(String(text), 'utf8'));
  }

  sendJson(obj) {
    let text;
    try {
      text = JSON.stringify(obj);
    } catch {
      return false;
    }
    this.send(text);
    return true;
  }

  ping() {
    this._write(OP.PING, Buffer.alloc(0));
  }

  close(code = 1000, reason = '') {
    if (this.closed) return;
    const body = Buffer.allocUnsafe(2 + Buffer.byteLength(reason));
    body.writeUInt16BE(code, 0);
    body.write(reason, 2);
    this._write(OP.CLOSE, body);
    this._finalize();
  }

  _finalize() {
    if (this.closed) return;
    this.closed = true;
    try {
      this.socket.end();
    } catch {
      /* ignore */
    }
    try {
      this.socket.destroy();
    } catch {
      /* ignore */
    }
    this.emit('close');
  }
}

/* ===========================================================================
 * 4. Domain: rooms, members, authoritative timeline
 * ======================================================================== */

/** Palette shared with the client so a name colour is always valid. */
const PROFILE_COLORS = Object.freeze([
  '#5b7cff', '#e5484d', '#f5a524', '#30a46c', '#8e4ec6',
  '#12a594', '#e93d82', '#3e63dd', '#d6409f', '#f76b15',
]);

/** Avatars are emoji, so no uploads and no storage are involved. */
const PROFILE_AVATARS = Object.freeze([
  { id: 'fox', cp: 0x1f98a }, { id: 'panda', cp: 0x1f43c }, { id: 'cat', cp: 0x1f431 },
  { id: 'dog', cp: 0x1f436 }, { id: 'frog', cp: 0x1f438 }, { id: 'unicorn', cp: 0x1f984 },
  { id: 'alien', cp: 0x1f47d }, { id: 'robot', cp: 0x1f916 }, { id: 'ghost', cp: 0x1f47b },
  { id: 'penguin', cp: 0x1f427 }, { id: 'lion', cp: 0x1f981 }, { id: 'owl', cp: 0x1f989 },
]);

function sanitizeColor(value) {
  if (typeof value !== 'string') return PROFILE_COLORS[0];
  const v = value.trim().toLowerCase();
  return PROFILE_COLORS.includes(v) ? v : PROFILE_COLORS[0];
}

function sanitizeAvatarId(value) {
  if (typeof value !== 'string') return PROFILE_AVATARS[0].id;
  const v = value.trim().toLowerCase();
  return PROFILE_AVATARS.some((a) => a.id === v) ? v : PROFILE_AVATARS[0].id;
}

class Member {
  constructor({ id, displayName, caps, media, conn, ip, color, avatar }) {
    this.id = id;
    this.displayName = displayName || 'Guest';
    this.color = sanitizeColor(color);
    this.avatar = sanitizeAvatarId(avatar);
    this.caps = caps || {};
    this.media = media || null;
    this.conn = conn;
    this.ip = ip;
    this.joinedAt = Date.now();
    this.rttSamples = [];
    this.p95Rtt = 0;
    this.lastDrift = null;
    this.rateLocked = false;
  }

  noteRtt(ms) {
    if (!Number.isFinite(ms) || ms < 0 || ms > 30000) return;
    this.rttSamples.push(ms);
    if (this.rttSamples.length > 15) this.rttSamples.shift();
    const sorted = [...this.rttSamples].sort((a, b) => a - b);
    const idx = Math.min(sorted.length - 1, Math.floor(sorted.length * 0.95));
    this.p95Rtt = Math.round(sorted[idx]);
  }

  toPublic() {
    return {
      id: this.id,
      displayName: this.displayName,
      color: this.color,
      avatar: this.avatar,
      caps: this.caps,
      rtt: this.p95Rtt,
      joinedAt: this.joinedAt,
    };
  }
}

class Room {
  constructor({ id, code, media, config }) {
    this.id = id;
    this.code = code;
    this.hostId = null;
    this.leaderEpoch = 1;
    this.members = new Map();     // id -> Member
    this.seq = 0;
    this.media = media || null;
    this.config = Object.assign(
      {
        pulseMs: 3000,
        rateTickMs: 250,
        deadbandMs: 40,
        laneMs: 300,
        seekMs: 500,
        maxRate: 0.05,
        maxRateAggressive: 0.08,
        meshMax: 8,
        controlLock: false,
        mode: 'scheduled',
      },
      config || {}
    );
    /** @type {{position:number, serverTs:number, state:string, playbackRate:number}|null} */
    this.anchor = null;
    this.createdAt = Date.now();
    this.emptySince = null;
    this.stats = { commands: 0, seeks: 0, pulses: 0, driftSamples: 0 };
    /** Bounded chat/system transcript so late joiners see recent context. */
    this.history = [];
  }

  addChat(entry) {
    this.history.push(entry);
    if (this.history.length > CONFIG.chatHistory) this.history.shift();
    return entry;
  }

  systemMessage(text) {
    return this.addChat({ id: ulid(), kind: 'system', text, ts: serverNow() });
  }

  /* --- membership --------------------------------------------------- */
  add(member) {
    if (this.members.size >= CONFIG.maxMembersPerRoom) {
      return { ok: false, code: 'E_ROOM_FULL', message: 'Room is full' };
    }
    this.members.set(member.id, member);
    this.emptySince = null;

    if (!this.hostId) {
      this.hostId = member.id;
      this.leaderEpoch = 1;
    }

    // Media compatibility gate (three-band rule, spec §12.4.1).
    if (this.media && member.media) {
      const delta = Math.abs((this.media.durationMs || 0) - (member.media.durationMs || 0));
      const bothNonLive = !this.media.isLive && !member.media.isLive;
      if (bothNonLive && this.media.durationMs > 0 && member.media.durationMs > 0 && delta > 30000) {
        this.members.delete(member.id);
        return {
          ok: false,
          code: 'E_MEDIA_MISMATCH',
          message: 'This room is watching different media (duration differs by ' + Math.round(delta / 1000) + 's).',
          fatal: false,
        };
      }
      if (bothNonLive && delta > 2000) {
        member.mediaMismatchWarning = true;
      }
    } else if (!this.media && member.media) {
      this.media = member.media;
    }

    return { ok: true };
  }

  remove(id) {
    const member = this.members.get(id);
    if (!member) return null;
    this.members.delete(id);
    if (this.members.size === 0) this.emptySince = Date.now();

    let migrated = null;
    if (this.hostId === id) {
      migrated = this._electHost();
    }
    return { member, migrated };
  }

  /** Lowest p95 RTT, then earliest join, then lowest id. Deterministic. */
  _electHost() {
    const candidates = [...this.members.values()].filter((m) => m.conn && !m.conn.closed);
    if (!candidates.length) {
      this.hostId = null;
      this.leaderEpoch += 1;
      return null;
    }
    candidates.sort((a, b) => {
      const ra = a.p95Rtt || 9999;
      const rb = b.p95Rtt || 9999;
      if (ra !== rb) return ra - rb;
      if (a.joinedAt !== b.joinedAt) return a.joinedAt - b.joinedAt;
      return a.id < b.id ? -1 : 1;
    });
    const next = candidates[0];
    this.hostId = next.id;
    this.leaderEpoch += 1;
    log.info(`room ${this.code}: host migrated to ${next.id.slice(0, 6)} (epoch ${this.leaderEpoch})`);
    return next;
  }

  /* --- timeline ----------------------------------------------------- */
  /**
   * Apply a play/pause/seek command and republish the anchor.
   * The anchor is back-dated by the sender's one-way latency while playing,
   * because the sender's media kept advancing during the message flight.
   */
  applyCommand(member, payload) {
    const kind = String(payload.kind || 'play');
    if (!['play', 'pause', 'seek', 'episode', 'rate-locked'].includes(kind)) {
      return { ok: false, code: 'E_PAYLOAD_INVALID', message: 'unknown command kind' };
    }

    const sentAt = serverNow();
    const durationSec = (this.media && this.media.durationMs ? this.media.durationMs : 0) / 1000;
    const rtt = clamp(Number(payload.senderRTT) || 0, 0, 5000);

    let state = payload.state === 'paused' ? 'paused' : 'playing';
    if (kind === 'pause') state = 'paused';
    if (kind === 'play') state = 'playing';

    let position = Number(payload.baseTimestamp);
    if (!Number.isFinite(position) || position < 0) position = 0;

    // One-way latency compensation (spec §5.5). Only while playing: a paused
    // timeline does not advance in flight.
    if (state === 'playing') position += rtt / 2000;

    if (durationSec > 0) position = clamp(position, 0, Math.max(0, durationSec - 0.05));

    // Collapse duplicate intents. A player that fires `play` and `playing`
    // (or our own engine re-asserting) would otherwise burn a seq and force
    // every peer through an apply cycle for no state change.
    const last = this._lastCommand;
    if (
      last &&
      member &&
      last.memberId === member.id &&
      last.kind === kind &&
      last.state === state &&
      Math.abs(last.position - position) < 0.05 &&
      sentAt - last.at < 150
    ) {
      return { ok: true, duplicate: true, anchor: this.anchor, seq: this.seq };
    }
    this._lastCommand = { memberId: member ? member.id : null, kind, state, position, at: sentAt };

    this.seq += 1;
    this.anchor = {
      seq: this.seq,
      position: Math.round(position * 1000) / 1000,
      serverTs: sentAt,
      state,
      playbackRate: 1,
    };
    this.stats.commands += 1;
    if (kind === 'seek') this.stats.seeks += 1;

    const applyAt = sentAt + this._scheduleSlack();
    return { ok: true, anchor: this.anchor, applyAt, kind, causedBy: member ? member.id : null, rtt };
  }

  /** Slack = p95(RTT)/2 + margin, clamped — gives slow peers time to arrive. */
  _scheduleSlack() {
    const rtts = [...this.members.values()].map((m) => m.p95Rtt).filter((r) => r > 0);
    if (!rtts.length) return CONFIG.scheduleSlack.default;
    const p95 = Math.max(...rtts);
    return Math.round(clamp(p95 / 2 + CONFIG.scheduleSlack.marginMs, CONFIG.scheduleSlack.min, CONFIG.scheduleSlack.max));
  }

  projectedPosition(nowMs) {
    if (!this.anchor) return 0;
    if (this.anchor.state !== 'playing') return this.anchor.position;
    return this.anchor.position + (nowMs - this.anchor.serverTs) / 1000;
  }

  /* --- messaging ---------------------------------------------------- */
  broadcast(frame, exceptId) {
    let sent = 0;
    for (const member of this.members.values()) {
      if (exceptId && member.id === exceptId) continue;
      if (!member.conn || member.conn.closed) continue;
      if (member.conn.sendJson(frame)) sent++;
    }
    return sent;
  }

  snapshot(forMemberId) {
    return {
      roomId: this.id,
      code: this.code,
      yourId: forMemberId,
      hostId: this.hostId,
      leaderEpoch: this.leaderEpoch,
      seq: this.seq,
      anchor: this.anchor,
      applyAt: this.anchor ? this.anchor.serverTs + this._scheduleSlack() : 0,
      media: this.media,
      members: [...this.members.values()].map((m) => m.toPublic()),
      config: this.config,
      chat: this.history,
      serverTs: serverNow(),
    };
  }
}

/* ===========================================================================
 * 5. Server state
 * ======================================================================== */

const rooms = new Map();          // roomId -> Room
const roomsByCode = new Map();    // CODE -> Room
const connState = new WeakMap();  // WsConnection -> { memberId, roomId, bucket, burst }

function makeTokenBucket(frames, windowMs) {
  return { frames, windowMs, tokens: frames, last: Date.now() };
}

function takeToken(bucket, cost = 1) {
  const nowMs = Date.now();
  const elapsed = nowMs - bucket.last;
  if (elapsed > 0) {
    bucket.tokens = Math.min(bucket.frames, bucket.tokens + (elapsed / bucket.windowMs) * bucket.frames);
    bucket.last = nowMs;
  }
  if (bucket.tokens < cost) return false;
  bucket.tokens -= cost;
  return true;
}

/* ===========================================================================
 * 6. Frame helpers
 * ======================================================================== */

function frame(type, payload, extra) {
  return Object.assign(
    {
      v: CONFIG.protocolVersion,
      id: ulid(),
      type,
      ts: serverNow(),
      payload: payload === undefined ? {} : payload,
    },
    extra || {}
  );
}

function sendError(conn, code, message, opts = {}) {
  const f = frame('error', {
    code,
    message,
    requestId: opts.requestId || null,
    retryable: !!opts.retryable,
    retryAfterMs: opts.retryAfterMs || 0,
    fatal: !!opts.fatal,
    detail: opts.detail || null,
  });
  if (conn && !conn.closed) conn.sendJson(f);
}

function send(conn, type, payload, extra) {
  if (!conn || conn.closed) return false;
  return conn.sendJson(frame(type, payload, extra));
}

/* ===========================================================================
 * 7. Protocol handling
 * ======================================================================== */

const HANDLERS = Object.create(null);

function stateOf(conn) {
  return connState.get(conn) || null;
}

function memberOf(conn) {
  const st = stateOf(conn);
  if (!st || !st.roomId || !st.memberId) return null;
  const room = rooms.get(st.roomId);
  if (!room) return null;
  return { room, member: room.members.get(st.memberId) || null, st };
}

/* --- ping / pong ---------------------------------------------------- */
HANDLERS.ping = (conn) => {
  send(conn, 'pong', { t: serverNow() });
};

/* --- clock ---------------------------------------------------------- */
HANDLERS['clock.sample'] = (conn, msg) => {
  const t0 = msg.payload && msg.payload.t0;
  if (!Number.isFinite(t0)) {
    sendError(conn, 'E_PAYLOAD_INVALID', 'clock.sample requires numeric t0');
    return;
  }
  // The client's t0 is echoed verbatim; `srv` is our monotonic clock. When the
  // caller is in a room we stamp the room id so the reply is routable even for
  // a client with several sessions.
  const st = stateOf(conn);
  const extra = st && st.roomId ? { roomId: st.roomId } : {};
  send(conn, 'clock.ack', { t0, srv: serverNow() }, extra);
};

/* --- room create ---------------------------------------------------- */
HANDLERS['room.create'] = (conn, msg) => {
  const st = stateOf(conn);
  if (st && st.roomId) {
    sendError(conn, 'E_STATE_CONFLICT', 'already in a room');
    return;
  }
  if (rooms.size >= CONFIG.maxRooms) {
    sendError(conn, 'E_INTERNAL', 'server at room capacity', { retryable: true, retryAfterMs: 5000 });
    return;
  }

  const p = msg.payload || {};
  const memberId = ulid();
  const roomId = ulid();

  let code;
  let guard = 0;
  do {
    code = roomCode(6);
    guard++;
  } while (roomsByCode.has(code) && guard < 50);
  if (roomsByCode.has(code)) {
    sendError(conn, 'E_INTERNAL', 'could not allocate room code', { retryable: true, retryAfterMs: 1000 });
    return;
  }

  const room = new Room({
    id: roomId,
    code,
    media: sanitizeMedia(p.media),
    config: p.config,
  });
  const member = new Member({
    id: memberId,
    displayName: sanitizeName(p.displayName),
    color: p.color,
    avatar: p.avatar,
    caps: p.caps,
    media: sanitizeMedia(p.media),
    conn,
    ip: safeIp(conn),
  });

  const added = room.add(member);
  if (!added.ok) {
    sendError(conn, added.code, added.message, { fatal: false });
    return;
  }

  rooms.set(roomId, room);
  roomsByCode.set(code, room);
  connState.set(conn, Object.assign(stateOf(conn) || {}, { roomId, memberId }));

  log.info(`room created ${code} (${roomId.slice(0, 6)}) by ${memberId.slice(0, 6)}`);

  room.systemMessage(`${member.displayName} started the party`);
  send(conn, 'room.state', room.snapshot(memberId), { roomId });
};

/* --- room join ------------------------------------------------------ */
HANDLERS['room.join'] = (conn, msg) => {
  const st = stateOf(conn);
  const p = msg.payload || {};
  const code = String(p.code || '').trim().toUpperCase();

  // Re-join (socket resume or "refresh"): same room, keep identity if possible.
  let room = null;
  if (st && st.roomId && rooms.has(st.roomId)) {
    room = rooms.get(st.roomId);
  } else if (code) {
    room = roomsByCode.get(code) || null;
  }

  if (!room) {
    sendError(conn, 'E_ROOM_NOT_FOUND', 'No room with that code.', { fatal: false });
    return;
  }

  // Resume path: the same connection already owns a member in this room.
  if (st && st.roomId === room.id && st.memberId && room.members.has(st.memberId)) {
    const member = room.members.get(st.memberId);
    member.media = sanitizeMedia(p.media) || member.media;
    send(conn, 'room.state', room.snapshot(member.id), { roomId: room.id, resumed: true });
    return;
  }

  const memberId = ulid();
  const member = new Member({
    id: memberId,
    displayName: sanitizeName(p.displayName),
    color: p.color,
    avatar: p.avatar,
    caps: p.caps,
    media: sanitizeMedia(p.media),
    conn,
    ip: safeIp(conn),
  });

  const added = room.add(member);
  if (!added.ok) {
    sendError(conn, added.code, added.message, { fatal: false });
    return;
  }

  connState.set(conn, Object.assign(stateOf(conn) || {}, { roomId: room.id, memberId }));

  // Tell the newcomer the full truth first…
  send(conn, 'room.state', room.snapshot(memberId), { roomId: room.id });

  // …then tell everyone else.
  room.broadcast(
    frame('member.joined', { member: member.toPublic(), members: room.members.size }, { roomId: room.id }),
    memberId
  );

  const sys = room.systemMessage(`${member.displayName} joined`);
  room.broadcast(frame('chat.message', sys, { roomId: room.id }), memberId);

  log.info(`room ${room.code}: ${memberId.slice(0, 6)} joined (${room.members.size} members)`);
};

/* --- room leave ----------------------------------------------------- */
HANDLERS['room.leave'] = (conn) => {
  const ctx = memberOf(conn);
  if (!ctx || !ctx.member) return;
  const { room, member } = ctx;

  const result = room.remove(member.id);
  connState.set(conn, Object.assign(stateOf(conn) || {}, { roomId: null, memberId: null }));

  room.broadcast(frame('member.left', { id: member.id, members: room.members.size }, { roomId: room.id }));

  const sysLeave = room.systemMessage(`${member.displayName} left`);
  room.broadcast(frame('chat.message', sysLeave, { roomId: room.id }));

  if (result && result.migrated) {
    room.broadcast(
      frame(
        'leader.changed',
        { hostId: room.hostId, leaderEpoch: room.leaderEpoch, members: [...room.members.values()].map((m) => m.toPublic()) },
        { roomId: room.id }
      )
    );
  }
  log.info(`room ${room.code}: ${member.id.slice(0, 6)} left (${room.members.size} remain)`);
};

/* --- sync command (the only state transition) ----------------------- */
HANDLERS['sync.command'] = (conn, msg) => {
  const ctx = memberOf(conn);
  if (!ctx || !ctx.member) {
    sendError(conn, 'E_STATE_CONFLICT', 'join a room first', { fatal: false });
    return;
  }
  const { room, member, st } = ctx;

  if (!takeToken(st.commandBucket, 1)) {
    sendError(conn, 'E_RATE_LIMIT', 'Too many sync commands', { retryable: true, retryAfterMs: 250 });
    return;
  }
  if (room.config.controlLock && member.id !== room.hostId) {
    sendError(conn, 'E_FORBIDDEN', 'Only the host can change playback', { fatal: false });
    return;
  }

  const result = room.applyCommand(member, msg.payload || {});
  if (!result.ok) {
    sendError(conn, result.code || 'E_PAYLOAD_INVALID', result.message || 'bad command', { fatal: false });
    return;
  }
  if (result.duplicate) {
    // Silent no-op: the sender already knows the state it asked for.
    return;
  }

  const anchorFrame = frame(
    'sync.anchor',
    {
      anchor: result.anchor,
      applyAt: result.applyAt,
      causedBy: result.causedBy,
      reason: 'user',
      senderRtt: result.rtt,
    },
    { roomId: room.id, seq: result.anchor.seq, origin: member.id, leaderEpoch: room.leaderEpoch }
  );

  // Authoritative fan-out to everyone (including the sender, for confirmation).
  room.broadcast(anchorFrame);

  // Narrate meaningful playback changes in chat. Throttle by rate and by exact
  // text, not by kind: keying on kind let a stale "last kind" swallow a real
  // change that happened after a suppressed one.
  const kind = result.kind;
  if (kind === 'play' || kind === 'pause' || kind === 'seek') {
    let text;
    if (kind === 'play') text = `${member.displayName} resumed the video`;
    else if (kind === 'pause') text = `${member.displayName} paused the video`;
    else text = `${member.displayName} skipped to ${fmtClock(result.anchor.position)}`;

    const now = Date.now();
    const sinceLast = now - (room.lastNarrateAt || 0);
    const sameText = room.lastNarrateText === text;
    const allowed = sinceLast >= 600 && !(sameText && sinceLast < 2500);
    if (allowed) {
      room.lastNarrateAt = now;
      room.lastNarrateText = text;
      room.lastNarrateKind = kind;
      const sys = room.systemMessage(text);
      room.broadcast(frame('chat.message', sys, { roomId: room.id }));
    }
  }

  log.debug(`room ${room.code}: ${result.kind} @ ${result.anchor.position}s by ${member.displayName}(${member.id.slice(0, 6)}) seq ${result.anchor.seq}`);
};

/* --- heartbeat pulse (leader → everyone) ---------------------------- */
HANDLERS['sync.pulse'] = (conn, msg) => {
  const ctx = memberOf(conn);
  if (!ctx || !ctx.member) return;
  const { room, member } = ctx;

  if (member.id !== room.hostId) return; // only the leader pulses
  const p = msg.payload || {};
  const posMs = Number(p.posMs);
  if (!Number.isFinite(posMs)) return;

  room.stats.pulses += 1;

  const out = frame(
    'sync.pulse',
    {
      posMs: Math.max(0, Math.round(posMs)),
      state: p.state === 'paused' ? 'paused' : 'playing',
      seq: room.seq,
      leaderEpoch: room.leaderEpoch,
      srv: serverNow(),           // relay timestamp — receivers anchor on this
      leaderRttMs: Number(p.leaderRttMs) || 0,
    },
    { roomId: room.id, origin: member.id }
  );
  room.broadcast(out, member.id);
};

/* --- drift telemetry ------------------------------------------------ */
HANDLERS['drift.report'] = (conn, msg) => {
  const ctx = memberOf(conn);
  if (!ctx || !ctx.member) return;
  const samples = (msg.payload && msg.payload.samples) || [];
  if (!Array.isArray(samples)) return;
  ctx.member.lastDrift = samples.slice(-3);
  ctx.room.stats.driftSamples += samples.length;
  // In-memory only; a real deployment ships these to a metrics sink.
};

/* --- WebRTC signalling relay ---------------------------------------- */
function relaySignal(conn, msg, kind) {
  const ctx = memberOf(conn);
  if (!ctx || !ctx.member) {
    sendError(conn, 'E_STATE_CONFLICT', 'not in a room', { fatal: false });
    return;
  }
  const { room, member } = ctx;
  const p = msg.payload || {};
  const targetId = p.to;
  if (!targetId || !room.members.has(targetId)) return;

  if (kind === 'sdp') {
    const sdp = p.sdp;
    if (!sdp || typeof sdp !== 'object' || typeof sdp.sdp !== 'string') return;
    if (sdp.sdp.length > 32768) {
      sendError(conn, 'E_PAYLOAD_INVALID', 'SDP too large');
      return;
    }
  } else {
    const cand = p.candidate;
    if (!cand || typeof cand.candidate !== 'string') return;
  }

  const target = room.members.get(targetId);
  // Rewrite `from` server-side so a peer cannot spoof another participant.
  target.conn.sendJson(
    frame(kind, Object.assign({}, p, { from: member.id, to: undefined }), { roomId: room.id })
  );
}

HANDLERS['rtc.sdp'] = (conn, msg) => relaySignal(conn, msg, 'rtc.sdp');
HANDLERS['rtc.ice'] = (conn, msg) => relaySignal(conn, msg, 'rtc.ice');

/* --- rate lock notification (client → host visibility) -------------- */
HANDLERS['rate.locked'] = (conn, msg) => {
  const ctx = memberOf(conn);
  if (!ctx || !ctx.member) return;
  ctx.member.rateLocked = true;
  ctx.room.broadcast(
    frame('rate.locked', { participantId: ctx.member.id, reason: (msg.payload && msg.payload.reason) || 'site-reset' }, { roomId: ctx.room.id })
  );
};

/* --- chat ----------------------------------------------------------- */
function sanitizeChat(raw) {
  const text = String(raw == null ? '' : raw)
    .replace(/[\u0000-\u0008\u000b-\u001f\u007f]/g, '')
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, CONFIG.chatMaxLength);
  return text;
}

HANDLERS['chat.send'] = (conn, msg) => {
  const ctx = memberOf(conn);
  if (!ctx || !ctx.member) {
    sendError(conn, 'E_STATE_CONFLICT', 'join a room first', { fatal: false });
    return;
  }
  const { room, member, st } = ctx;
  if (!takeToken(st.chatBucket, 1)) {
    sendError(conn, 'E_RATE_LIMIT', 'You are sending messages too quickly', { retryable: true, retryAfterMs: 600 });
    return;
  }
  const text = sanitizeChat(msg.payload && msg.payload.text);
  const wantsReaction = !!msg.payload && msg.payload.kind === 'reaction';

  if (wantsReaction) {
    const emoji = sanitizeChat(msg.payload && msg.payload.emoji).slice(0, 8);
    if (!emoji) return;
    // Reactions are ephemeral: broadcast once, never stored, never in history.
    // They belong on the video, not in the transcript.
    room.broadcast(
      frame(
        'chat.message',
        {
          id: ulid(),
          kind: 'reaction',
          from: member.id,
          displayName: member.displayName,
          color: member.color,
          emoji,
          text: emoji,
          ts: serverNow(),
        },
        { roomId: room.id }
      )
    );
    return;
  }

  if (!text) return;

  const entry = room.addChat({
    id: ulid(),
    kind: 'message',
    from: member.id,
    displayName: member.displayName,
    color: member.color,
    avatar: member.avatar,
    text,
    ts: serverNow(),
  });
  room.broadcast(frame('chat.message', entry, { roomId: room.id }));
};

/* Profile changes take effect immediately and are visible to the room. */
HANDLERS['profile.update'] = (conn, msg) => {
  const ctx = memberOf(conn);
  if (!ctx || !ctx.member) {
    sendError(conn, 'E_STATE_CONFLICT', 'join a room first', { fatal: false });
    return;
  }
  const { room, member } = ctx;
  const p = msg.payload || {};
  if (p.displayName !== undefined) member.displayName = sanitizeName(p.displayName);
  if (p.color !== undefined) member.color = sanitizeColor(p.color);
  if (p.avatar !== undefined) member.avatar = sanitizeAvatarId(p.avatar);
  room.broadcast(frame('member.updated', { member: member.toPublic() }, { roomId: room.id }));
};

/* Typing presence: clients throttle; the server only fans it out. */
HANDLERS['chat.typing'] = (conn, msg) => {
  const ctx = memberOf(conn);
  if (!ctx || !ctx.member) return;
  const p = (msg && msg.payload) || {};
  // `typing:false` is how a cleared composer tells everyone to stop showing
  // "X is typing…" immediately, instead of waiting for a timeout.
  const typing = p.typing !== false;
  ctx.room.broadcast(
    frame(
      'chat.typing',
      { id: ctx.member.id, displayName: ctx.member.displayName, typing },
      { roomId: ctx.room.id }
    ),
    ctx.member.id
  );
};

/* ===========================================================================
 * 8. Sanitisation helpers
 * ======================================================================== */

/** m:ss / h:mm:ss for chat narration. */
function fmtClock(seconds) {
  const total = Math.max(0, Math.floor(Number(seconds) || 0));
  const h = Math.floor(total / 3600);
  const m = Math.floor((total % 3600) / 60);
  const s = total % 60;
  const pad = (n) => String(n).padStart(2, '0');
  return h ? `${h}:${pad(m)}:${pad(s)}` : `${m}:${pad(s)}`;
}

function sanitizeName(name) {
  const s = String(name == null ? '' : name)
    .replace(/[\u0000-\u001f\u007f]/g, '')
    .trim()
    .slice(0, 24);
  return s || 'Guest';
}

function sanitizeMedia(media) {
  if (!media || typeof media !== 'object') return null;
  const durationMs = Number(media.durationMs);
  // `url` is what lets the join page send an invitee to the exact video.
  let url = '';
  if (typeof media.url === 'string' && /^https?:\/\//i.test(media.url)) {
    url = media.url.slice(0, 2000);
  }
  return {
    kind: media.kind === 'audio' ? 'audio' : 'video',
    durationMs: Number.isFinite(durationMs) ? clamp(Math.round(durationMs), 0, 24 * 3600 * 1000) : 0,
    isLive: !!media.isLive,
    fingerprint: typeof media.fingerprint === 'string' ? media.fingerprint.slice(0, 16) : '',
    origin: typeof media.origin === 'string' ? media.origin.slice(0, 200) : '',
    title: typeof media.title === 'string' ? media.title.slice(0, 120) : '',
    url,
    drm: 'none',
  };
}

function safeIp(conn) {
  try {
    return (conn.socket && conn.socket.remoteAddress) || '';
  } catch {
    return '';
  }
}

/* ===========================================================================
 * 9. Connection handling
 * ======================================================================== */

function attachConnection(conn) {
  connState.set(conn, {
    roomId: null,
    memberId: null,
    connectedAt: Date.now(),
    bucket: makeTokenBucket(CONFIG.rateLimit.frames, CONFIG.rateLimit.windowMs),
    commandBucket: makeTokenBucket(CONFIG.commandLimit.frames, CONFIG.commandLimit.windowMs),
    chatBucket: makeTokenBucket(CONFIG.chatLimit.frames, CONFIG.chatLimit.windowMs),
  });

  conn.on('message', (text) => {
    const st = stateOf(conn);
    if (!st) return;

    if (!takeToken(st.bucket, 1)) {
      sendError(conn, 'E_RATE_LIMIT', 'Too many frames', { retryable: true, retryAfterMs: 500 });
      conn.close(1008, 'rate limit');
      return;
    }

    let msg;
    try {
      msg = JSON.parse(text);
    } catch {
      sendError(conn, 'E_PAYLOAD_INVALID', 'frame is not JSON', { fatal: false });
      return;
    }
    if (!msg || typeof msg.type !== 'string') {
      sendError(conn, 'E_PAYLOAD_INVALID', 'missing type', { fatal: false });
      return;
    }
    if (msg.v != null && msg.v !== CONFIG.protocolVersion) {
      sendError(conn, 'E_VERSION', 'Unsupported protocol version ' + msg.v, { fatal: true });
      return;
    }

    const handler = HANDLERS[msg.type];
    if (!handler) {
      sendError(conn, 'E_UNKNOWN_TYPE', 'Unknown frame type: ' + msg.type, { fatal: false });
      return;
    }
    try {
      handler(conn, msg);
    } catch (err) {
      log.error('handler error for', msg.type, err && err.stack ? err.stack : err);
      sendError(conn, 'E_INTERNAL', 'Internal error', { retryable: true, retryAfterMs: 1000 });
    }
  });

  conn.on('close', () => {
    const ctx = memberOf(conn);
    if (ctx && ctx.member) {
      const { room, member } = ctx;
      const result = room.remove(member.id);
      room.broadcast(frame('member.left', { id: member.id, members: room.members.size }, { roomId: room.id }));
      const sys = room.systemMessage(`${member.displayName} left`);
      room.broadcast(frame('chat.message', sys, { roomId: room.id }));
      if (result && result.migrated) {
        room.broadcast(
          frame(
            'leader.changed',
            { hostId: room.hostId, leaderEpoch: room.leaderEpoch, members: [...room.members.values()].map((m) => m.toPublic()) },
            { roomId: room.id }
          )
        );
      }
      log.info(`disconnect: ${member.id.slice(0, 6)} removed from ${room.code} (${room.members.size} remain)`);
    }
    connState.delete(conn);
  });
}

/* ===========================================================================
 * 10. HTTP surface
 * ======================================================================== */

function json(res, status, body) {
  const payload = JSON.stringify(body);
  res.writeHead(status, {
    'content-type': 'application/json; charset=utf-8',
    'content-length': Buffer.byteLength(payload),
    'cache-control': 'no-store',
    'access-control-allow-origin': '*',
  });
  res.end(payload);
}

function text(res, status, body, type = 'text/plain; charset=utf-8') {
  res.writeHead(status, { 'content-type': type, 'content-length': Buffer.byteLength(body) });
  res.end(body);
}

/** 60 s, 8 kHz, mono, 16-bit PCM sine — generated once, held in memory. */
function buildToneWav({ seconds = 60, sampleRate = 8000 } = {}) {
  const total = seconds * sampleRate;
  const dataBytes = total * 2;
  const buf = Buffer.alloc(44 + dataBytes);
  buf.write('RIFF', 0, 'ascii');
  buf.writeUInt32LE(36 + dataBytes, 4);
  buf.write('WAVE', 8, 'ascii');
  buf.write('fmt ', 12, 'ascii');
  buf.writeUInt32LE(16, 16);
  buf.writeUInt16LE(1, 20);              // PCM
  buf.writeUInt16LE(1, 22);              // mono
  buf.writeUInt32LE(sampleRate, 24);
  buf.writeUInt32LE(sampleRate * 2, 28); // byte rate
  buf.writeUInt16LE(2, 32);              // block align
  buf.writeUInt16LE(16, 34);             // bits
  buf.write('data', 36, 'ascii');
  buf.writeUInt32LE(dataBytes, 40);
  for (let i = 0; i < total; i++) {
    // Soft 220 Hz tone with a slow amplitude envelope so drift is audible.
    const t = i / sampleRate;
    const env = 0.15 * (0.6 + 0.4 * Math.sin(2 * Math.PI * 0.1 * t));
    const v = Math.round(Math.sin(2 * Math.PI * 220 * t) * env * 32767);
    buf.writeInt16LE(v, 44 + i * 2);
  }
  return buf;
}

const TONE_WAV = buildToneWav();

const DEMO_HTML = `<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<title>OmniSync demo — self-hosted media</title>
<style>
  body{background:#0b0f17;color:#e8edf7;font-family:system-ui,-apple-system,Segoe UI,sans-serif;
       margin:0;min-height:100vh;display:grid;place-items:center;padding:24px}
  .card{width:min(680px,100%);background:#111827;border:1px solid #1f2a3d;border-radius:16px;padding:26px}
  h1{margin:0 0 6px;font-size:22px}
  p{color:#94a3b8;font-size:14px;line-height:1.6}
  audio{width:100%;margin:16px 0}
  .k{font-family:ui-monospace,monospace;color:#7dd3fc}
  code{background:#0b1220;padding:2px 6px;border-radius:5px;font-size:12px}
  ol{color:#94a3b8;font-size:13px;line-height:1.8}
</style></head>
<body><div class="card">
  <h1>OmniSync demo</h1>
  <p>This page is served by the OmniSync server itself. The audio element below is a
     plain, self-hosted <code>&lt;audio&gt;</code> — no adapter, no site integration.</p>
  <audio id="demo" controls preload="metadata" src="/media/tone.wav"></audio>
  <p>Current time: <span class="k" id="t">0.000</span>s &nbsp;·&nbsp;
     duration: <span class="k" id="d">–</span>s &nbsp;·&nbsp;
     rate: <span class="k" id="r">1.00</span></p>
  <ol>
    <li>Click the OmniSync toolbar icon to open the panel.</li>
    <li>Press <b>Create</b> in one browser, <b>Join</b> with the code in another.</li>
    <li>Press play on one side — the other follows within ~120 ms.</li>
  </ol>
</div>
<script>
  const a = document.getElementById('demo');
  const t = document.getElementById('t'), d = document.getElementById('d'), r = document.getElementById('r');
  const tick = () => { t.textContent = a.currentTime.toFixed(3); r.textContent = a.playbackRate.toFixed(2); };
  a.addEventListener('loadedmetadata', () => { d.textContent = a.duration.toFixed(2); });
  a.addEventListener('timeupdate', tick);
  a.addEventListener('ratechange', tick);
  setInterval(tick, 120);
</script>
</body></html>`;

const STATUS_HTML = `<!doctype html><html><head><meta charset="utf-8">
<title>OmniSync server</title><style>
body{background:#0b0f17;color:#e8edf7;font-family:system-ui,sans-serif;margin:0;padding:40px}
h1{font-size:20px;margin:0 0 16px}table{border-collapse:collapse;font-size:13px}
td{border-bottom:1px solid #1f2a3d;padding:7px 18px 7px 0}td:first-child{color:#94a3b8}
code{color:#7dd3fc;font-family:ui-monospace,monospace}
</style></head><body>
<h1>OmniSync server</h1>
<table>
<tr><td>WebSocket</td><td><code>ws://localhost:PORT/</code></td></tr>
<tr><td>Health</td><td><code>/health</code></td></tr>
<tr><td>Demo page</td><td><a href="/demo" style="color:#7dd3fc">/demo</a></td></tr>
<tr><td>Protocol</td><td>v1</td></tr>
</table></body></html>`;

/* ===========================================================================
 * 10b. Join landing page *
 * The equivalent of https://www.teleparty.com/join/<id>: our own page, so an
 * invite link never has to be bolted onto the streaming site's URL. It shows
 * who is in the party, then sends the invitee to the exact video the host is
 * watching, with the party code attached for the extension to pick up.
 * ======================================================================== */

/** Public base URL as the client reached us (works for localhost or LAN IP). */
function hostBase(req) {
  const raw = String((req && req.headers && req.headers.host) || '127.0.0.1:' + CONFIG.port);
  const host = raw.replace(/[^A-Za-z0-9.\-:[\]]/g, '').slice(0, 120) || '127.0.0.1:' + CONFIG.port;
  const proto = String((req && req.headers && req.headers['x-forwarded-proto']) || '').toLowerCase();
  return (proto === 'https' ? 'https://' : 'http://') + host;
}

const ENDED_HTML = `<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Party ended - OmniSync</title><style>
body{background:#0b0f17;color:#e8edf7;font-family:system-ui,sans-serif;margin:0;min-height:100vh;
     display:flex;align-items:center;justify-content:center;padding:24px}
.card{max-width:420px;background:#141b2a;border:1px solid #24304a;border-radius:14px;padding:26px;text-align:center}
h1{font-size:18px;margin:0 0 10px}p{color:#94a3b8;font-size:13px;line-height:1.6;margin:0}
</style></head><body><div class="card">
<h1>This party has ended</h1>
<p>The room no longer exists on this server. Ask your friend for a fresh invite link.</p>
</div></body></html>`;

function joinPageHtml(room, baseUrl) {
  const esc = (s) =>
    String(s == null ? '' : s).replace(/[&<>"']/g, (c) => ({
      '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
    }[c]));
  const members = [...room.members.values()];
  const n = members.length;
  const title = (room.media && room.media.title) || 'a video';
  const target = room.media && room.media.url ? room.media.url : '';
  let href = '';
  if (target) {
    try {
      const u = new URL(target);
      u.searchParams.set('omnisync', room.code);
      href = u.toString();
    } catch {
      href = target;
    }
  }

  const list = members
    .map((m) => `<li><span class="dot" style="background:${esc(m.color)}"></span>${esc(m.displayName)}${
      m.id === room.hostId ? ' <b>host</b>' : ''
    }</li>`)
    .join('');

  return `<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Join the OmniSync party</title><style>
*{box-sizing:border-box}
body{background:#0b0f17;color:#e8edf7;font-family:system-ui,-apple-system,"Segoe UI",sans-serif;
     margin:0;min-height:100vh;display:flex;align-items:center;justify-content:center;padding:24px}
.card{width:100%;max-width:460px;background:#141b2a;border:1px solid #24304a;border-radius:14px;
      padding:26px;box-shadow:0 24px 60px rgba(0,0,0,.5)}
.brand{display:flex;align-items:center;gap:9px;margin-bottom:18px}
.mark{width:26px;height:26px;border-radius:8px;background:linear-gradient(135deg,#5b7cff,#8a5bff);
      display:flex;align-items:center;justify-content:center;font-weight:800;font-size:13px}
.brand b{font-size:15px}
h1{margin:0 0 6px;font-size:19px}
p{color:#94a3b8;font-size:13px;line-height:1.6;margin:0 0 14px}
.media{background:#0f1626;border:1px solid #24304a;border-radius:9px;padding:10px 12px;
       font-size:13px;color:#cbd5e1;margin-bottom:14px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.code{font-family:ui-monospace,monospace;letter-spacing:3px;color:#9db4ff;font-size:15px}
ul{list-style:none;padding:0;margin:0 0 16px;display:flex;flex-direction:column;gap:7px}
li{font-size:13px;color:#cbd5e1;display:flex;align-items:center;gap:8px}
li b{font-size:10px;background:#5b7cff33;color:#9db4ff;padding:1px 6px;border-radius:999px}
.dot{width:8px;height:8px;border-radius:50%;flex:0 0 auto}
a.go{display:block;text-align:center;text-decoration:none;background:#5b7cff;color:#fff;
     padding:13px;border-radius:9px;font-weight:700;font-size:14px}
a.go:hover{background:#4a6ae8}
.hint{font-size:11px;color:#64748b;margin-top:12px;line-height:1.6}
</style></head><body><div class="card">
  <div class="brand"><span class="mark">O</span><b>OmniSync</b></div>
  <h1>You're invited to a watch party</h1>
  <p><span class="code">${esc(room.code)}</span> &middot; ${n} watching</p>
  <div class="media">${esc(title)}</div>
  <ul>${list}</ul>
  ${href
    ? `<a class="go" href="${esc(href)}">Open the video and join</a>`
    : `<p>This party has no video attached yet. Ask the host to press play.</p>`}
  <div class="hint">The button opens the same video with the party code attached. If the
  OmniSync extension is installed it joins automatically; otherwise install it first, then
  reopen this link.</div>
</div></body></html>`;
}

/* ===========================================================================
 * 11. HTTP server + WS upgrade
 * ======================================================================== */
const server = http.createServer((req, res) => {
  let url;
  try {
    url = new URL(req.url, `http://${req.headers.host || 'localhost'}`);
  } catch {
    text(res, 400, 'bad request');
    return;
  }

  if (req.method === 'OPTIONS') {
    res.writeHead(204, { 'access-control-allow-origin': '*', 'access-control-allow-methods': 'GET,OPTIONS' });
    res.end();
    return;
  }

  switch (url.pathname) {
    case '/health':
      json(res, 200, {
        ok: true,
        protocol: CONFIG.protocolVersion,
        // Advertised capability set. A client (or a test) can detect a server
        // that is older than the extension instead of failing mysteriously.
        features: FEATURES,
        build: BUILD_ID,
        uptimeSec: Math.round(process.uptime()),
        rooms: rooms.size,
        members: [...rooms.values()].reduce((n, r) => n + r.members.size, 0),
        serverTs: serverNow(),
      });
      return;

    case '/':
      text(res, 200, STATUS_HTML.replace('PORT', String(CONFIG.port)), 'text/html; charset=utf-8');
      return;

    case '/demo':
      text(res, 200, DEMO_HTML, 'text/html; charset=utf-8');
      return;

    case '/media/tone.wav':
      res.writeHead(200, {
        'content-type': 'audio/wav',
        'content-length': TONE_WAV.length,
        'accept-ranges': 'bytes',
        'cache-control': 'public, max-age=3600',
      });
      res.end(TONE_WAV);
      return;

    default:
      break;
  }

  /* --- join landing page + room API (dynamic paths) -------------------- */
  const joinMatch = /^\/join\/([A-Za-z0-9]{4,12})\/?$/.exec(url.pathname);
  if (joinMatch) {
    const room = roomsByCode.get(joinMatch[1].toUpperCase());
    if (!room) {
      text(res, 404, ENDED_HTML, 'text/html; charset=utf-8');
      return;
    }
    text(res, 200, joinPageHtml(room, hostBase(req)), 'text/html; charset=utf-8');
    return;
  }

  const apiMatch = /^\/api\/room\/([A-Za-z0-9]{4,12})\/?$/.exec(url.pathname);
  if (apiMatch) {
    const room = roomsByCode.get(apiMatch[1].toUpperCase());
    if (!room) {
      json(res, 404, { ok: false, code: 'E_ROOM_NOT_FOUND' });
      return;
    }
    json(res, 200, {
      ok: true,
      code: room.code,
      roomId: room.id,
      hostId: room.hostId,
      leaderEpoch: room.leaderEpoch,
      members: [...room.members.values()].map((m) => m.toPublic()),
      media: room.media,
      anchor: room.anchor
        ? { position: room.anchor.position, state: room.anchor.state, seq: room.anchor.seq }
        : null,
      joinUrl: hostBase(req) + '/join/' + room.code,
      serverTs: serverNow(),
    });
    return;
  }

  text(res, 404, 'not found');
});

server.on('upgrade', (req, socket, head) => {
  const key = req.headers['sec-websocket-key'];
  const upgrade = String(req.headers.upgrade || '').toLowerCase();
  const version = req.headers['sec-websocket-version'];

  if (upgrade !== 'websocket' || !key || version !== '13') {
    socket.write('HTTP/1.1 400 Bad Request\r\nConnection: close\r\n\r\n');
    socket.destroy();
    return;
  }
  // Must be a well-formed, 16-byte base64 key.
  let keyBytes;
  try {
    keyBytes = Buffer.from(String(key), 'base64');
  } catch {
    keyBytes = null;
  }
  if (!keyBytes || keyBytes.length !== 16) {
    socket.write('HTTP/1.1 400 Bad Request\r\nConnection: close\r\n\r\n');
    socket.destroy();
    return;
  }

  const accept = crypto
    .createHash('sha1')
    .update(String(key) + WS_GUID)
    .digest('base64');

  socket.write(
    'HTTP/1.1 101 Switching Protocols\r\n' +
      'Upgrade: websocket\r\n' +
      'Connection: Upgrade\r\n' +
      `Sec-WebSocket-Accept: ${accept}\r\n` +
      '\r\n'
  );

  const conn = new WsConnection(socket, head);
  attachConnection(conn);
  log.debug('ws connection established');
});

/* ===========================================================================
 * 12. Housekeeping
 * ======================================================================== */

// Dead-peer detection + empty-room GC.
const sweeper = setInterval(() => {
  const nowMs = Date.now();

  for (const room of [...rooms.values()]) {
    if (room.emptySince && nowMs - room.emptySince > CONFIG.roomTtlMs) {
      rooms.delete(room.id);
      roomsByCode.delete(room.code);
      log.info(`room ${room.code} expired`);
    }
  }

  // Nothing to iterate for sockets: each connection self-reports via ping/pong.
}, 30000);

const pinger = setInterval(() => {
  // We ping every live room member; a member that stops responding is closed
  // by the WsConnection idle watchdog below.
  for (const room of rooms.values()) {
    for (const member of room.members.values()) {
      const conn = member.conn;
      if (!conn || conn.closed) continue;
      if (Date.now() - conn.lastFrameAt > CONFIG.idleTimeoutMs) {
        log.info(`idle timeout for ${member.id.slice(0, 6)}`);
        conn.close(1001, 'idle');
        continue;
      }
      try {
        conn.ping();
      } catch {
        /* ignore */
      }
    }
  }
}, CONFIG.pingIntervalMs);

/* ===========================================================================
 * 13. Boot + shutdown
 * ======================================================================== */

function start() {
  server.listen(CONFIG.port, CONFIG.host, () => {
    log.info(`OmniSync server listening on ws://${CONFIG.host}:${CONFIG.port}`);
    log.info(`demo page: http://localhost:${CONFIG.port}/demo`);
  });
}

server.on('error', (err) => {
  if (err && err.code === 'EADDRINUSE') {
    log.error(`port ${CONFIG.port} is already in use; set PORT to choose another`);
  } else {
    log.error('server error:', err && err.stack ? err.stack : err);
  }
  process.exitCode = 1;
});

function shutdown(signal) {
  log.info(`${signal} received; shutting down`);
  clearInterval(sweeper);
  clearInterval(pinger);
  for (const room of rooms.values()) {
    for (const member of room.members.values()) {
      try {
        member.conn && member.conn.close(1001, 'server shutting down');
      } catch {
        /* ignore */
      }
    }
  }
  server.close(() => {
    log.info('closed');
    process.exit(0);
  });
  // Hard stop if the event loop refuses to drain.
  setTimeout(() => process.exit(0), 3000).unref();
}

if (require.main === module) {
  process.on('SIGINT', () => shutdown('SIGINT'));
  process.on('SIGTERM', () => shutdown('SIGTERM'));
  process.on('uncaughtException', (err) => {
    log.error('uncaught exception:', err && err.stack ? err.stack : err);
  });
  process.on('unhandledRejection', (err) => {
    log.error('unhandled rejection:', err && err.stack ? err.stack : err);
  });
  start();
}

module.exports = {
  CONFIG,
  serverNow,
  rooms,
  roomsByCode,
  Room,
  Member,
  WsConnection,
  buildToneWav,
  start,
  server,
};
