#!/usr/bin/env node
// DEAD ZONE server: zero dependencies, Node 18+.
//
//   node server.js
//
// Put this file next to index.html. It serves the game and implements the
// /api + /events endpoints the game already talks to:
//   - accounts      -> users.json   (passwords stored as salted scrypt hashes)
//   - cloud saves   -> saves.json   (one save per account)
//   - lobby list    -> memory       (hosts send a heartbeat every 5s)
//   - live co-op    -> memory       (presence + messages relayed over SSE)
//
// Both JSON files are created automatically. A .bak.json snapshot (refreshed
// at most every 10 minutes) is kept beside each one.
'use strict';

const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = +process.env.PORT || 3000;
// Keep 127.0.0.1 when fronting with `tailscale serve`; use HOST=0.0.0.0 only if you must.
const HOST = process.env.HOST || '127.0.0.1';
const DIR = __dirname;
const GAME = path.join(DIR, 'index.html');
const USERS_FILE = path.join(DIR, 'users.json');
const SAVES_FILE = path.join(DIR, 'saves.json');

const MAX_PLAYERS = 8;     // players per lobby
const PEER_TTL = 20000;    // drop a connected peer that has sent nothing for this long (ms)
const LOBBY_TTL = 15000;   // drop a lobby if its host stops sending heartbeats (ms)
const FAIL_LIMIT = 8;      // wrong passwords before a 60s lockout on that account
const SAVE_MAX = 200000;   // max bytes of save data per account
const FLUSH_MS = 50;       // presence broadcasts are coalesced to ~20/s per room

// ---------- persistence ----------
function load(file) {
  if (!fs.existsSync(file)) return Object.create(null);
  try {
    return Object.assign(Object.create(null), JSON.parse(fs.readFileSync(file, 'utf8')));
  } catch (e) {
    console.error(`Cannot read ${file}: ${e.message}`);
    console.error('Fix it, or restore from the .bak.json copy. Refusing to start so nothing gets overwritten.');
    process.exit(1);
  }
}

function store(file, data, pretty) {
  const bak = file.replace(/\.json$/, '.bak.json');
  let timer = null;
  const now = () => {
    clearTimeout(timer);
    timer = null;
    try {
      let stale = true;
      try { stale = Date.now() - fs.statSync(bak).mtimeMs > 600000; } catch {}
      if (stale && fs.existsSync(file)) fs.copyFileSync(file, bak);
      const tmp = file + '.tmp';
      fs.writeFileSync(tmp, JSON.stringify(data, null, pretty ? 2 : 0));
      fs.renameSync(tmp, file);
    } catch (e) {
      console.error('Write failed for ' + file + ': ' + e.message);
    }
  };
  return { now, later: () => { if (!timer) timer = setTimeout(now, 400); } };
}

const users = load(USERS_FILE); // { username: { salt, hash, created } }
const saves = load(SAVES_FILE); // { username: { s, l, b, p, g } }
const usersFile = store(USERS_FILE, users, true);
const savesFile = store(SAVES_FILE, saves, false);

// ---------- accounts ----------
const U_RE = /^[a-z0-9_]{3,16}$/;
const H_RE = /^[0-9a-f]{64}$/;      // the client sends SHA-256 hex of "dz1|user|password"
const ID_RE = /^[a-z0-9]{1,16}$/;
const PEER_RE = /^[a-z0-9]{4,16}$/;
const ROOM_RE = /^dz-[a-z0-9]{1,16}$/;

const scrypt = (h, salt) => new Promise((ok, no) =>
  crypto.scrypt(h, salt, 32, (e, k) => (e ? no(e) : ok(k.toString('hex')))));

// Tokens are signed (HMAC) instead of kept in memory, so a server restart does not log everyone out
// or silently break their lobby/cloud-save connection. The secret lives in secret.key.
const SECRET_FILE = path.join(DIR, 'secret.key');
const SECRET = (() => {
  try {
    const k = fs.readFileSync(SECRET_FILE, 'utf8').trim();
    if (/^[0-9a-f]{64}$/.test(k)) return Buffer.from(k, 'hex');
  } catch {}
  const k = crypto.randomBytes(32);
  try { fs.writeFileSync(SECRET_FILE, k.toString('hex'), { mode: 0o600 }); }
  catch (e) { console.error('Could not write secret.key (' + e.message + '); logins will not survive a restart'); }
  return k;
})();
const TOKEN_DAYS = 60;
const sign = body => crypto.createHmac('sha256', SECRET).update(body).digest('hex').slice(0, 32);
const mint = user => {
  const body = user + '.' + (Date.now() + TOKEN_DAYS * 86400000).toString(36);
  return body + '.' + sign(body);
};
const who = tok => {
  if (typeof tok !== 'string' || tok.length > 80) return null;
  const parts = tok.split('.');
  if (parts.length !== 3) return null;
  const [u, exp, sig] = parts, want = sign(u + '.' + exp);
  if (sig.length !== want.length || !crypto.timingSafeEqual(Buffer.from(sig), Buffer.from(want))) return null;
  if (!U_RE.test(u) || !users[u] || parseInt(exp, 36) < Date.now()) return null;
  return u;
};

const fails = new Map(); // username -> { n, until }
const isLocked = u => {
  const f = fails.get(u);
  if (!f) return false;
  if (Date.now() > f.until) { fails.delete(u); return false; }
  return f.n >= FAIL_LIMIT;
};
const addFail = u => {
  if (fails.size > 5000) fails.clear();
  const f = fails.get(u) || { n: 0 };
  f.n++;
  f.until = Date.now() + 60000;
  fails.set(u, f);
};

// ---------- lobbies + rooms ----------
const lobbies = new Map(); // id -> { id, host, name, seed, ph, n, t, kicked:Set }
const rooms = new Map();   // "dz-<id>" -> { name, peers: Map(peerId -> peer), dirty }
// peer = { user, res, pres, host, en, ew, seq, t }

const sse = (res, ev, data) => {
  try { res.write('event: ' + ev + '\ndata: ' + JSON.stringify(data) + '\n\n'); } catch {}
};

// Presence is "latest state wins", so a client that cannot keep up simply skips frames
// instead of letting its socket buffer (and therefore its lag) grow without limit.
const BACKLOG = 256 * 1024;
function flush(r) {
  r.dirty = false;
  const o = {};
  for (const [id, p] of r.peers) o[id] = p.pres;
  const msg = 'event: peers\ndata: ' + JSON.stringify(o) + '\n\n';
  for (const p of r.peers.values()) {
    if (!p.res) continue;               // stream currently down: presence is kept, nothing is sent
    if (p.res.writableLength > BACKLOG) { r.dirty = true; continue; } // retry next tick with fresher state
    try { p.res.write(msg); } catch {}
  }
}

function events(req, res, url) {
  const q = url.searchParams;
  const room = q.get('room') || '', peer = q.get('peer') || '', user = who(q.get('tok'));
  const bail = c => { res.writeHead(c); res.end(); };
  if (!user) return bail(401);
  if (!ROOM_RE.test(room) || !PEER_RE.test(peer)) return bail(400);
  const lob = lobbies.get(room.slice(3));
  if (lob && lob.host !== user && lob.kicked.has(user)) return bail(403);

  let r = rooms.get(room);
  if (!r) { r = { name: room, peers: new Map(), dirty: false }; rooms.set(room, r); }
  const old = r.peers.get(peer);
  if (old && old.user !== user) return bail(409);
  if (!old && r.peers.size >= MAX_PLAYERS) return bail(403);
  if (old) { try { old.res.end(); } catch {} } // EventSource auto-reconnects with the same peer id

  const p = { user, res, pres: old ? old.pres : { nm: user }, host: old ? old.host : false, en: 0, ew: 0, seq: old ? old.seq : 0, t: Date.now() };
  r.peers.set(peer, p);
  req.socket.setNoDelay(true);
  req.socket.setTimeout(0);
  res.writeHead(200, {
    'Content-Type': 'text/event-stream',
    'Cache-Control': 'no-cache, no-transform',
    'Connection': 'keep-alive',
    'X-Accel-Buffering': 'no',
  });
  res.write('retry: 2000\n\n');
  flush(r);
  req.on('close', () => {
    // Keep the player for PEER_TTL after the stream drops (presence POSTs can still arrive, and the
    // EventSource reconnects with the same peer id). A wifi blip no longer makes everyone see them vanish.
    if (r.peers.get(peer) !== p) return;
    p.res = null;
    r.dirty = true;
  });
}

const peerOf = (user, b) => {
  const r = rooms.get(b.room), p = r && r.peers.get(b.peer);
  return p && p.user === user ? { r, p } : null;
};

// ---------- API ----------
const OK = { ok: 1 };

async function api(b) {
  if (!b || typeof b !== 'object') return { err: 'bad' };

  if (b.op === 'signup' || b.op === 'login') {
    const u = String(b.u || ''), h = String(b.h || '');
    if (!U_RE.test(u) || !H_RE.test(h)) return { err: 'bad' };
    if (isLocked(u)) return { err: 'bad' };
    if (b.op === 'signup') {
      if (users[u]) return { err: 'taken' };
      const salt = crypto.randomBytes(16).toString('hex');
      const hash = await scrypt(h, salt);
      if (users[u]) return { err: 'taken' }; // someone else signed up while we were hashing
      users[u] = { salt, hash, created: new Date().toISOString() };
      usersFile.later();
      return { tok: mint(u) };
    }
    const rec = users[u];
    const got = await scrypt(h, rec ? rec.salt : '00'.repeat(16)); // same work either way
    const good = rec && crypto.timingSafeEqual(Buffer.from(got, 'hex'), Buffer.from(rec.hash, 'hex'));
    if (!good) { addFail(u); return { err: 'bad' }; }
    fails.delete(u);
    return { tok: mint(u) };
  }

  const user = who(b.tok);
  if (!user) return { err: 'auth' };

  switch (b.op) {
    case 'sget':
      return { data: saves[user] || null };

    case 'sset': {
      const d = b.data;
      if (!d || typeof d !== 'object' || Array.isArray(d)) return { err: 'bad' };
      if (JSON.stringify(d).length > SAVE_MAX) return { err: 'big' };
      saves[user] = d;
      savesFile.later();
      return OK;
    }

    case 'swipe': // the in-game "delete progress" button
      delete saves[user];
      savesFile.later();
      return OK;

    case 'list':
      return {
        list: [...lobbies.values()].map(l => {
          const r = rooms.get('dz-' + l.id);
          return {
            id: l.id, name: l.name, host: l.host, ph: l.ph, n: l.n, seed: l.seed,
            t: Date.now(), // stale lobbies are pruned server-side
            p: r ? [...r.peers.values()].map(p => p.pres.nm).filter(Boolean) : [],
          };
        }),
      };

    case 'beat': {
      const id = String(b.id || '');
      if (!ID_RE.test(id)) return { err: 'bad' };
      let l = lobbies.get(id);
      if (l && l.host !== user) return { err: 'taken' };
      for (const [k, o] of lobbies) if (o.host === user && k !== id) lobbies.delete(k); // one lobby per host
      if (!l) { l = { id, host: user, kicked: new Set() }; lobbies.set(id, l); }
      l.name = String(b.name || user).slice(0, 28);
      l.seed = (+b.seed || 0) >>> 0;
      l.ph = b.ph === 'raid' ? 'raid' : 'lobby';
      l.n = Math.max(1, Math.min(MAX_PLAYERS, (+b.n | 0) || 1));
      l.t = Date.now();
      return OK;
    }

    case 'del': {
      const l = lobbies.get(String(b.id || ''));
      if (l && l.host === user) lobbies.delete(l.id);
      return OK;
    }

    case 'kick': {
      const l = lobbies.get(String(b.id || ''));
      const target = String(b.user || '');
      if (!l || l.host !== user) return { err: 'bad' };
      if (target === user) return OK;
      l.kicked.add(target);
      const r = rooms.get('dz-' + l.id);
      if (r) {
        for (const [id, p] of [...r.peers]) {
          if (p.user !== target) continue;
          sse(p.res, 'kicked', {});
          try { p.res.end(); } catch {}
          r.peers.delete(id);
        }
        flush(r);
      }
      return OK;
    }

    case 'pres': { // merge a patch into this peer's presence
      const hit = peerOf(user, b);
      const patch = b.patch;
      if (!hit || !patch || typeof patch !== 'object' || Array.isArray(patch)) return { err: 'bad' };
      if (JSON.stringify(patch).length > 60000) return { err: 'big' };
      const { r, p } = hit;
      p.t = Date.now();
      const sq = +b.seq;
      if (sq > 0) {                  // parallel POSTs can arrive out of order; never apply an older one
        if (sq <= p.seq) return OK;
        p.seq = sq;
      }
      for (const k of Object.keys(patch)) if (k !== '__proto__') p.pres[k] = patch[k];
      const l = lobbies.get(r.name.slice(3));
      if (l && l.host === user) { p.host = true; l.t = Date.now(); } // host activity keeps the lobby alive
      p.pres.nm = user;              // names come from the account, not the client
      if (!p.host) delete p.pres.h;  // only the lobby owner can claim host
      r.dirty = true;
      return OK;
    }

    case 'emit': { // broadcast a message to everyone in the room (sender included)
      const hit = peerOf(user, b);
      if (!hit || typeof b.topic !== 'string' || b.topic.length > 32) return { err: 'bad' };
      const { r, p } = hit, now = Date.now();
      p.t = now;
      if (now - p.ew > 1000) { p.ew = now; p.en = 0; }
      if (++p.en > 60) return { err: 'rate' };
      const msg = 'event: msg\ndata: ' + JSON.stringify({ topic: b.topic, peer: b.peer, data: b.data }) + '\n\n';
      for (const o of r.peers.values()) { try { o.res.write(msg); } catch {} }
      return OK;
    }
  }
  return { err: 'bad' };
}

// ---------- HTTP ----------
function body(req, max = 400000) {
  return new Promise((ok, no) => {
    let n = 0;
    const chunks = [];
    req.on('data', d => {
      n += d.length;
      if (n > max) { no(new Error('too big')); req.destroy(); return; }
      chunks.push(d);
    });
    req.on('end', () => {
      try { ok(JSON.parse(Buffer.concat(chunks).toString() || '{}')); } catch (e) { no(e); }
    });
    req.on('error', no);
  });
}

function json(res, obj) {
  res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store' });
  res.end(JSON.stringify(obj));
}

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, 'http://x');
  try {
    if (req.method === 'GET' && url.pathname === '/events') return events(req, res, url);
    if (req.method === 'POST' && url.pathname === '/api') return json(res, await api(await body(req)));
    if ((req.method === 'GET' || req.method === 'HEAD') && (url.pathname === '/' || url.pathname === '/index.html')) {
      return fs.readFile(GAME, (e, data) => { // read per request, so edits to index.html show up on refresh
        if (e) { res.writeHead(500); return res.end('index.html not found next to server.js'); }
        res.writeHead(200, {
          'Content-Type': 'text/html; charset=utf-8',
          'Cache-Control': 'no-cache',
          'X-Content-Type-Options': 'nosniff',
          'Referrer-Policy': 'no-referrer',
        });
        res.end(req.method === 'HEAD' ? undefined : data);
      });
    }
    if (url.pathname === '/favicon.ico') { res.writeHead(204); return res.end(); }
    res.writeHead(404);
    res.end('not found'); // users.json / saves.json are never served
  } catch (e) {
    if (!res.headersSent) { res.writeHead(400); res.end('{"err":"bad"}'); }
  }
});

// ---------- background jobs ----------
setInterval(() => { for (const r of rooms.values()) if (r.dirty) flush(r); }, FLUSH_MS);
setInterval(() => { for (const r of rooms.values()) for (const p of r.peers.values()) { try { p.res.write(':\n\n'); } catch {} } }, 20000);
setInterval(() => {
  const now = Date.now();
  for (const [id, l] of lobbies) {
    if (now - l.t <= LOBBY_TTL) continue;
    const r = rooms.get('dz-' + id);
    if (r && [...r.peers.values()].some(p => p.user === l.host && now - p.t < PEER_TTL)) continue; // host still there; keep the kick list
    lobbies.delete(id);
  }
  // half-open connections (phone switched networks, laptop slept) never fire 'close' on their own
  for (const [name, r] of rooms) {
    for (const [id, p] of r.peers) {
      if (now - p.t <= PEER_TTL) continue;
      try { p.res.end(); } catch {}
      r.peers.delete(id);
      r.dirty = true;
    }
    if (!r.peers.size) rooms.delete(name);
  }
}, 5000);

function bye() { usersFile.now(); savesFile.now(); process.exit(0); }
process.on('SIGINT', bye);
process.on('SIGTERM', bye);

server.on('error', e => { console.error(e.code === 'EADDRINUSE' ? `Port ${PORT} is already in use (try PORT=3001)` : e.message); process.exit(1); });
server.listen(PORT, HOST, () => {
  console.log(`DEAD ZONE server listening on http://${HOST}:${PORT}`);
  console.log(`${Object.keys(users).length} accounts loaded from users.json`);
  if (!fs.existsSync(GAME)) console.warn('WARNING: index.html not found next to server.js');
});
