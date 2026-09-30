/* Audio engine (PLAN.md Appendix C). Web Audio only: no <audio> elements and no Media Session
   metadata, so the speaker's play/pause button has nothing to grab.
   - One AudioContext, created WITHOUT a sampleRate option (that has caused Bluetooth bugs).
   - Each clip is AudioBufferSourceNode -> GainNode -> destination. FADE ramps to 0 over 2 s,
     STOP over 50 ms. Only one clip at a time.
   - Pack bytes stay in memory; decoded AudioBuffers live in a 4-entry LRU filled ahead of time
     (on arm and when the queue changes), so PLAY normally starts with no decoding at all.
   - iOS can leave a context "running" but silent, stuck "interrupted", or hang resume(); every
     suspicious sign is reported as 'trouble' so the app can show TAP TO RE-ARM.
   - Keep speaker awake (optional): a looping noise bed at -60 dBFS on its own GainNode, so a Bluetooth
     speaker never idles into standby and clips the start of the next clip. It is never "the clip". */
const AudioEngine = (() => {
  'use strict';
  const LRU_SIZE = 4, RESUME_TIMEOUT_MS = 3000, VERIFY_MS = 1500, FADE_S = 2, STOP_S = 0.05, BED_GAIN = 0.001;
  // Bluetooth can take a second or more to start rendering, and each new context starts it again, so the
  // checks wait and double-check (a too-eager check made every Re-arm fail the same way: a loop).
  const STARTUP = new Set(['audio did not start', 'audio did not resume', 'audio clock is stuck']);
  const AC = window.AudioContext || window.webkitAudioContext;

  let ctx = null, gen = 0;          // gen changes with every new context (stale decodes are dropped)
  let wasRunning = false;           // a context only "breaks" after it has run once
  let trouble = '';                 // why audio may be dead; cleared by arm()
  let ready = Promise.resolve(false);
  let bytes = new Map();            // path -> ArrayBuffer (never handed to decodeAudioData itself)
  const lru = new Map();            // path -> AudioBuffer, least recently used first
  const inflight = new Map();       // path -> Promise<AudioBuffer>
  let clip = null;                  // the one playing clip
  let bed = null, keepAwake = false; // {ctx, src, gain}: the noise bed, and whether the app wants one
  const listeners = { trouble: [], change: [], healed: [] };

  const emit = (type, arg) => listeners[type].forEach(fn => { try { fn(arg); } catch (e) { console.error(e); } });
  const on = (type, fn) => listeners[type].push(fn);

  // Silent switch: without this, iOS plays Web Audio through the ringer channel (muted).
  function session() {
    try { if (navigator.audioSession) navigator.audioSession.type = 'playback'; } catch (e) { /* older iOS */ }
  }
  session();

  const log = [];                    // recent trouble, shown in Diagnostics
  function flag(reason) {
    trouble = reason;
    log.push({ at: new Date().toLocaleTimeString(), reason, state: ctx ? ctx.state : 'none',
               session: navigator.audioSession ? navigator.audioSession.state : 'n/a' });
    if (log.length > 20) log.shift();
    emit('trouble', reason);
    emit('change');
  }
  function heal() {                  // a late start is not a dead context: clear startup trouble
    if (trouble && STARTUP.has(trouble) && ctx && ctx.state === 'running') {
      trouble = '';
      emit('healed');
      emit('change');
    }
  }
  // "Clock stuck" only if it has not moved at the first look AND still has not moved a bit later.
  function verifyClock(ac, stillRelevant) {
    const t0 = ac.currentTime;
    setTimeout(() => {
      if (!stillRelevant() || ac !== ctx || ac.currentTime > t0 + 0.05) return;
      const t1 = ac.currentTime;
      setTimeout(() => {
        if (stillRelevant() && ac === ctx && ac.currentTime <= t1 + 0.05) flag('audio clock is stuck');
      }, VERIFY_MS);
    }, VERIFY_MS);
  }

  // Kick off resume() synchronously; the promise says whether it is running within 1 s.
  function resume() {
    session();
    const c = ctx;
    if (!c) return Promise.resolve(false);
    let p;
    try { p = c.resume(); } catch (e) { p = Promise.reject(e); }
    let t;
    return Promise.race([
      Promise.resolve(p).then(() => c.state === 'running', () => false),
      new Promise(r => { t = setTimeout(() => r(c.state === 'running'), RESUME_TIMEOUT_MS); }),   // resume() can hang on iOS
    ]).finally(() => clearTimeout(t));
  }

  /* Arm: call SYNCHRONOUSLY inside a tap handler, before any await.
     fresh=true always builds a new context (Re-arm); otherwise an existing healthy one is reused.
     midway() runs after the new context is resuming and before the old one is closed (wake lock).
     Returns a promise: true if the context is running within 1 s. */
  function arm(fresh, midway) {
    session();
    const old = ctx;
    if (fresh || !ctx || ctx.state === 'closed' || trouble) {
      const c = new AC();
      ctx = c; gen++; wasRunning = false;
      c.onstatechange = () => onState(c);
      lru.clear(); inflight.clear();          // buffers belong to the old context; bytes stay
      bed = null;                             // it dies with the old context
    }
    if (keepAwake) startBed();                // still inside the tap
    trouble = '';
    const g = gen;
    ready = resume();
    ready.then(ok => { if (!ok && g === gen && ctx && ctx.state !== 'running') flag('audio did not start'); });
    if (midway) midway();
    if (old && old !== ctx) {
      stopNow('rearm');                       // its clip dies with the old context
      old.onstatechange = null;
      try { old.close().catch(() => {}); } catch (e) { /* already closed */ }   // never awaited
    }
    emit('change');
    return ready;
  }

  function onState(c) {
    if (c !== ctx) return;
    if (c.state === 'running') { wasRunning = true; heal(); }
    else if (wasRunning) flag('audio ' + c.state);          // suspended / interrupted / closed
    emit('change');
  }

  // Anything that can silently kill iOS audio counts as trouble once we have a context.
  document.addEventListener('visibilitychange', () => {
    if (document.visibilityState === 'visible' && ctx) flag('app went to the background');
  });
  window.addEventListener('pageshow', e => { if (e.persisted && ctx) flag('page was restored'); });
  if (navigator.audioSession && navigator.audioSession.addEventListener) {
    navigator.audioSession.addEventListener('statechange', () => {
      if (navigator.audioSession.state === 'interrupted' && ctx) flag('audio session interrupted');
      emit('change');
    });
  }

  // ---- bytes and decoded buffers
  function setBytes(files) {                 // {path: {bytes, type}} or null to forget the pack
    stopNow('replaced');
    bytes = new Map(files ? Object.entries(files).map(([k, v]) => [k, v.bytes]) : []);
    lru.clear(); inflight.clear();
  }

  function decode(c, ab) {                   // promise and callback forms (older WebKit)
    return new Promise((resolve, reject) => {
      try {
        const p = c.decodeAudioData(ab, resolve, reject);
        if (p && p.then) p.then(resolve, reject);
      } catch (e) { reject(e); }
    });
  }

  let offline = null;
  function testDecode(ab) {                  // import check: no gesture needed, no sound made
    const OAC = window.OfflineAudioContext || window.webkitOfflineAudioContext;
    if (!offline) offline = new OAC(2, 44100, 44100);
    return decode(offline, ab);
  }

  function touch(path) {
    const b = lru.get(path);
    if (b) { lru.delete(path); lru.set(path, b); }
    return b;
  }

  function buffer(path) {
    const hit = touch(path);
    if (hit) return Promise.resolve(hit);
    if (inflight.has(path)) return inflight.get(path);
    const ab = bytes.get(path);
    if (!ctx) return Promise.reject(new Error('Audio is not armed.'));
    if (!ab) return Promise.reject(new Error('This clip is missing from the pack.'));
    const g = gen;
    const p = decode(ctx, ab.slice(0)).then(buf => {       // slice: decodeAudioData detaches its input
      if (g === gen) {
        lru.set(path, buf);
        while (lru.size > LRU_SIZE) lru.delete(lru.keys().next().value);
      }
      return buf;
    }).finally(() => { if (inflight.get(path) === p) inflight.delete(path); });
    inflight.set(path, p);
    return p;
  }

  // Decode the next clips in order; afterwards paths[0] is the most recently used.
  async function prefetch(paths) {
    const list = [...new Set(paths.filter(Boolean))].slice(0, LRU_SIZE);
    for (const p of list) { try { await buffer(p); } catch (e) { /* reported when it is played */ } }
    for (let i = list.length - 1; i >= 0; i--) touch(list[i]);
  }

  // ---- playback
  function stopNow(reason) {                 // immediate, no ramp (context is going away)
    const c = clip;
    if (!c) return;
    try { if (c.src) c.src.stop(); } catch (e) { /* not started */ }
    finish(c, reason);
  }

  function finish(c, reason, err) {
    if (c.done) return;
    c.done = true;
    clearTimeout(c.safety);
    if (clip === c) clip = null;
    try { if (c.gain) c.gain.disconnect(); } catch (e) { /* ignore */ }
    if (c.onDone) c.onDone(reason, err);
    emit('change');
  }

  // Call SYNCHRONOUSLY inside the PLAY tap. onDone(reason) gets ended | faded | stopped | rearm | error.
  function play(path, onDone) {
    session();
    if (!ctx) arm(true);
    const running = resume();                  // every PLAY resumes (kicked off before any await)
    stopNow('replaced');                       // one sound at a time
    const c = { path, onDone, src: null, gain: null, done: false, reason: '', safety: 0 };
    clip = c;
    running.then(ok => { if (!ok && clip === c && ctx && ctx.state !== 'running') flag('audio did not resume'); });
    const start = buf => {
      if (clip !== c || c.done) return;        // stopped or re-armed while decoding
      const ac = ctx, src = ac.createBufferSource(), gain = ac.createGain();
      src.buffer = buf;
      src.connect(gain);
      gain.connect(ac.destination);
      src.onended = () => finish(c, c.reason || 'ended');
      src.start();
      c.src = src; c.gain = gain;
      // A context that says "running" but whose clock does not move is not making sound.
      verifyClock(ac, () => clip === c);
      c.safety = setTimeout(() => finish(c, c.reason || 'ended'), (buf.duration + 1.5) * 1000);   // if onended never fires
      emit('change');
    };
    const hit = touch(path);
    if (hit) start(hit);
    else buffer(path).then(start, err => { if (clip === c) finish(c, 'error', err); });
    return c;
  }

  function rampOut(sec, reason) {
    const c = clip;
    if (!c) return false;
    session();
    if (!c.src) { finish(c, reason); return true; }          // still decoding: just cancel it
    resume();
    const ac = ctx, g = c.gain.gain, now = ac.currentTime;
    c.reason = reason;
    g.cancelScheduledValues(now);
    g.setValueAtTime(g.value, now);
    g.linearRampToValueAtTime(0, now + sec);
    try { c.src.stop(now + sec + 0.02); } catch (e) { /* older WebKit: the first stop() time stands, gain is 0 anyway */ }
    clearTimeout(c.safety);
    c.safety = setTimeout(() => finish(c, reason), (sec + 1) * 1000);
    return true;
  }
  const fade = () => rampOut(FADE_S, 'faded');
  const stop = () => rampOut(STOP_S, 'stopped');

  // Sound Check: a ~0.6 s two-note chime at a moderate level.
  function chime() {
    if (!ctx) return;
    session();
    resume();
    const ac = ctx, t = ac.currentTime + 0.05, out = ac.createGain();
    out.gain.value = 0.3;
    out.connect(ac.destination);
    [[880, 0], [1318.5, 0.16]].forEach(([freq, dt]) => {
      const o = ac.createOscillator(), g = ac.createGain();
      o.type = 'sine';
      o.frequency.value = freq;
      g.gain.setValueAtTime(0.0001, t + dt);
      g.gain.exponentialRampToValueAtTime(1, t + dt + 0.02);
      g.gain.exponentialRampToValueAtTime(0.0001, t + dt + 0.42);
      o.connect(g);
      g.connect(out);
      o.start(t + dt);
      o.stop(t + dt + 0.45);
    });
    // No clock check here: the Sound Check asks the parent whether it was heard.
  }

  // ---- keep speaker awake: 2 s of white noise, looped, far below anything audible over a field
  function startBed() {
    if (!ctx || ctx.state === 'closed' || (bed && bed.ctx === ctx)) return;
    stopBed();
    try {
      const ac = ctx, n = Math.round(ac.sampleRate * 2), buf = ac.createBuffer(1, n, ac.sampleRate), d = buf.getChannelData(0);
      for (let i = 0; i < n; i++) d[i] = Math.random() * 2 - 1;
      const src = ac.createBufferSource(), gain = ac.createGain();
      src.buffer = buf;
      src.loop = true;
      gain.gain.value = BED_GAIN;
      src.connect(gain);
      gain.connect(ac.destination);
      src.start();
      bed = { ctx: ac, src, gain };
    } catch (e) { bed = null; }
  }
  function stopBed() {
    const b = bed;
    bed = null;
    if (!b) return;
    try { b.src.stop(); } catch (e) { /* not started */ }
    try { b.gain.disconnect(); } catch (e) { /* ignore */ }
  }
  function setKeepAwake(on) {                // call inside a tap when turning it on
    keepAwake = !!on;
    if (keepAwake) startBed(); else stopBed();
  }

  function info() {
    const s = navigator.audioSession;
    return {
      state: ctx ? ctx.state : 'not armed',
      sampleRate: ctx ? ctx.sampleRate : null,
      latency: ctx && ctx.baseLatency != null ? Math.round(ctx.baseLatency * 1000) + ' ms' : 'n/a',
      clock: ctx ? ctx.currentTime.toFixed(1) + ' s' : 'n/a',
      session: s ? `${s.type} / ${s.state}` : 'not available',
      decoded: [...lru.keys()].length,
      clips: bytes.size,
      trouble,
      bed: !!(bed && bed.ctx === ctx),
      log: log.slice().reverse(),
    };
  }

  return {
    on, arm, resume, play, fade, stop, chime, prefetch, setBytes, testDecode, info, setKeepAwake,
    touch: () => { session(); if (ctx) resume(); },   // for taps that should keep audio awake
    state: () => (ctx ? ctx.state : 'not armed'),
    trouble: () => trouble,
    ready: () => ready,
    hasBytes: () => bytes.size > 0,
    playing: () => !!clip,
    // Test hook for this PC only (the live site ignores it): simulate an iOS audio failure.
    debugFlag: reason => { if (/^(localhost|127\.0\.0\.1)$/.test(location.hostname)) flag(reason); },
  };
})();
