/* Walk-Up Soundboard: screens, team-pack import, batting order and the game (PLAN.md sections 7-9,
   Appendix C). Audio lives in audio.js (AudioEngine), storage in store.js (Store), zips in zip.js.
   Game flow: IDLE -> PLAYING -> (FADE 2 s | clip ends | STOP) -> COOLDOWN 2 s -> next batter.
   A silent batter's PLAY goes straight to COOLDOWN; STOP in the first 3 s aborts (she stays up).
   Warm-up music (Batting order screen, only when no game is active) shuffles the pack's warm-up songs forever.
   The shell is generic: every name, number and clip comes from the team pack on this phone. */
(() => {
  'use strict';

  const APP_VERSION = '2026.10.07-1';        // keep equal to VERSION in sw.js
  const DEBOUNCE_MS = 400, FADE_LOCK_MS = 3000, COOLDOWN_MS = 2000, LOCK_HOLD_MS = 1500,
        LONG_PRESS_MS = 550, RESUME_WINDOW_MS = 6 * 3600 * 1000, STATE_KEY = 'walkup.game.v1',
        CHECK_TTL_MS = 6 * 3600 * 1000, TEST_FADE_AT_MS = 5000;
  const MODES = ['full', 'intro_only', 'silent'];
  const CHECKS = [                           // pre-game checklist: [id, text]
    ['speaker', 'Speaker connected and tested'],
    ['airplane', 'Airplane Mode on, then Bluetooth back on'],
    ['focus', 'Focus or Do Not Disturb on (no calls or alerts)'],
    ['battery', 'Phone plugged into the battery pack'],
    ['volume', 'Phone volume all the way up'],
    ['vlc', 'VLC backup ready'],
  ];
  const NOT_OFFLINE = 'NOT saved for offline use: it may not open in Airplane Mode. On Wi-Fi, open Settings and tap Check for update.';
  const LOCAL = ['localhost', '127.0.0.1', '[::1]'].includes(location.hostname);
  const audio = AudioEngine;
  const $ = id => document.getElementById(id);

  // ---- tiny DOM builder (pack text always goes in as text, never as HTML)
  function h(tag, props, ...kids) {
    const el = document.createElement(tag);
    for (const [k, v] of Object.entries(props || {})) {
      if (v == null || v === false) continue;
      if (k.startsWith('on')) el.addEventListener(k.slice(2), v);
      else if (k === 'class') el.className = v;
      else if (k === 'dataset') Object.assign(el.dataset, v);
      else el.setAttribute(k, v === true ? '' : v);
    }
    for (const kid of kids.flat()) if (kid != null && kid !== false) el.append(kid instanceof Node ? kid : String(kid));
    return el;
  }

  // ---- saved state: localStorage can throw (private mode, blocked storage), so every access is wrapped
  const blank = () => ({ order: null, absent: [], lastOrder: [], cur: null, queued: null, slot: null,
                         soundCheckAt: 0, gameAt: 0, savedAt: 0, active: false, checks: {}, keepAwake: false });
  let S = blank();
  try {
    const saved = JSON.parse(localStorage.getItem(STATE_KEY) || 'null');
    if (saved && typeof saved === 'object') S = Object.assign(blank(), saved);
  } catch (e) { /* start fresh */ }
  if (S.order != null && !Array.isArray(S.order)) S.order = null;
  if (!Array.isArray(S.absent)) S.absent = [];
  if (!Array.isArray(S.lastOrder)) S.lastOrder = [];
  if (!S.slot || typeof S.slot !== 'object' || !Number.isInteger(S.slot.at)) S.slot = null;
  S.checks = S.checks && typeof S.checks === 'object' && !Array.isArray(S.checks)
    ? Object.fromEntries(Object.entries(S.checks).filter(([, t]) => Number.isFinite(t))) : {};
  if (typeof S.keepAwake !== 'boolean') S.keepAwake = false;

  function save() {
    S.savedAt = Date.now();
    try { localStorage.setItem(STATE_KEY, JSON.stringify(S)); } catch (e) { /* the game still runs */ }
  }

  // ---- runtime state
  let pack = null;                 // {id, meta, importedAt} (no audio)
  let P = new Map();               // player id -> player
  let loadedPackId = null;         // whose audio bytes are in memory
  let screen = '';
  let phase = 'idle';              // idle | playing | cooldown
  let fading = false, stopEarly = false, playAt = 0, lastTap = 0, lastStop = 0, coolUntil = 0, coolTimer = 0, tickTimer = 0, playSeq = 0;
  let locked = false, tapIn = false, importing = false;
  let armedAt = 0, soundOkAt = 0, armSeq = 0;
  const rearms = [];                         // recent Re-arm taps, to spot a Re-arm that isn't helping
  let swStatus = null, swError = '';
  let sheetKind = '', sheetModal = false, sheetAt = 0, shownCur = null, toastTimer = 0;
  let checkOpen = true;                      // checklist expanded (in memory only)
  let spk = { playing: false, asked: false, help: false, error: '' }, testSeq = 0, testTimer = 0;   // Test speaker
  // Warm-up music: order = this round's shuffled entry indexes, k = the current one (-1 before the first),
  // next = the following round once something has peeked past this one. pos = paused position (s).
  const W = { order: [], k: -1, next: null, state: 'stopped', pos: 0, seq: 0, lastTap: 0, timer: 0 };

  // ---- players and lineup
  const player = id => P.get(id) || null;
  const clipOf = p => (!p ? null : p.mode === 'full' ? p.full : p.mode === 'intro_only' ? p.intro || p.full : null);
  const numText = p => (p && p.number ? '#' + p.number : '');
  const label = p => (p ? [p.name, numText(p)].filter(Boolean).join(' ') : '—');
  const modeText = p => (p.mode === 'silent' ? 'No music' : p.mode === 'intro_only' ? 'Announcer only' : p.song_title || 'Song');
  const packIds = () => (pack ? pack.meta.players.map(p => p.id) : []);
  const order = () => S.order || [];
  const byName = (a, b) => ((player(a) || {}).name || a).localeCompare((player(b) || {}).name || b);

  function indexPlayers() { P = new Map(pack.meta.players.map(p => [p.id, p])); }

  // S.slot = {id, at}: the at-bat girl left her place mid-clip (Absent / Move to end), and whoever is now
  // at index `at` bats after her. dropFromOrder() shifts it when someone ahead of it leaves.
  const slotOf = id => (S.slot && S.slot.id === id ? S.slot.at : null);

  function nextOf(id) {                      // wraps; an id not in the order leads to the first batter
    const o = order(), n = o.length, s = slotOf(id);
    if (!n) return null;
    if (s == null) return o[(o.indexOf(id) + 1) % n];
    return o[s % n] !== id || n === 1 ? o[s % n] : o[(s + 1) % n];     // she may have moved into it
  }
  function prevOf(id) {
    const o = order(), n = o.length, s = slotOf(id), i = s != null ? s : o.indexOf(id);
    if (!n) return null;
    if (i < 0) return o[0];
    const p = o[(i - 1 + n) % n];
    return p !== id || n === 1 ? p : o[(i - 2 + n) % n];
  }
  function upcoming(k) {                     // who follows the at-bat batter (a queued pick comes first)
    const o = order(), out = [];
    let id = S.queued && S.queued !== S.cur && o.includes(S.queued) ? S.queued : nextOf(S.cur);
    for (let i = 0; i < o.length && out.length < k; i++, id = o[(o.indexOf(id) + 1) % o.length]) {
      if (id !== S.cur && !out.includes(id)) out.push(id);
    }
    return out;
  }
  function setCur(id) { S.cur = id; S.queued = null; S.slot = null; }
  function dropFromOrder(id) {               // take id out of the order; S.slot stays on the same batter
    const o = order(), i = o.indexOf(id);
    if (i < 0) return;
    if (S.slot && i < S.slot.at) S.slot.at--;
    S.order = o.filter(x => x !== id);
  }

  // Re-import never reshuffles: removed players drop out, new ones go to the end marked absent.
  function mergeLineup() {
    const ids = packIds(), inPack = new Set(ids);
    if (!Array.isArray(S.order)) {                        // first pack ever: everyone, pack order
      S.order = ids.slice();
      S.absent = [];
    } else {
      const known = new Set([...S.order, ...S.absent]);
      S.order = [...new Set(S.order)].filter(id => inPack.has(id));
      S.absent = [...new Set(S.absent)].filter(id => inPack.has(id) && !S.order.includes(id))
        .concat(ids.filter(id => !known.has(id)));
    }
    S.lastOrder = S.lastOrder.filter(id => inPack.has(id));
    if (!S.order.includes(S.queued)) S.queued = null;
    if (!S.order.includes(S.cur)) setCur(nextOf(S.cur));   // e.g. relaunched after she left mid-clip
  }

  // Before `id` leaves her place: if she is up, the at-bat moves on. Mid-clip her place is kept in
  // S.slot, so whoever holds it when the clip ends bats next, however the order changes meanwhile.
  function leaving(id) {
    if (S.queued === id) S.queued = null;
    if (id !== S.cur) return;
    if (phase === 'idle') setCur(upcoming(1)[0] || null);
    else if (slotOf(id) == null) S.slot = { id, at: order().indexOf(id) };
  }
  function markAbsent(id) {
    leaving(id);
    dropFromOrder(id);
    if (!S.absent.includes(id)) S.absent.push(id);
    changed();
  }
  function moveToEnd(id) {
    if (order().includes(id)) leaving(id);
    S.absent = S.absent.filter(x => x !== id);
    dropFromOrder(id);
    S.order = order().concat(id);
    if (!S.cur) S.cur = id;
    changed();
  }
  function batNext(id) {                     // right after the at-bat batter (or into the place she left)
    if (id === S.cur) return;
    S.absent = S.absent.filter(x => x !== id);
    dropFromOrder(id);
    const o = order(), s = slotOf(S.cur);
    o.splice(s != null ? s : o.indexOf(S.cur) + 1, 0, id);
    S.order = o;
    S.queued = null;
    if (!S.cur) S.cur = id;
    changed();
  }
  function queueBatter(id) {                 // tap a lineup row: she is the one PLAY plays next
    if (phase === 'idle') setCur(id); else S.queued = id === S.cur ? null : id;
    changed();
  }
  function advance() {
    setCur(S.queued && order().includes(S.queued) ? S.queued : nextOf(S.cur));
    changed();
  }

  function changed() { save(); render(); prefetchQueue(); }
  function prefetchQueue() {                 // decode ahead so PLAY never waits
    if (!S.active || !pack || loadedPackId !== pack.id || audio.state() === 'not armed') return;
    audio.prefetch([S.cur, ...upcoming(2)].map(id => clipOf(player(id))));
  }

  // ---- screens
  function show(name) {
    if (name === 'roll') checkOpen = !allTicked();      // each visit: open unless all six are ticked
    screen = name;
    for (const s of ['pack', 'roll', 'game']) $('scr-' + s).hidden = s !== name;
    render();
  }
  function render() {
    if (screen === 'pack') renderPack();
    else if (screen === 'roll') renderRoll();
    else if (screen === 'game') renderGame();
    renderWarm();                            // hidden whenever a game is active
    updatePill();
  }

  function renderPack() {
    const m = pack && pack.meta;
    $('pack-status').textContent = m ? `Pack from ${m.created || 'an unknown date'} · ${m.players.length} players` : 'No team pack on this phone yet.';
    $('import-label').textContent = m ? 'Import a new team pack' : 'Import team pack';
    $('btn-local').hidden = !LOCAL;
    $('pack-players').hidden = !m;
    $('pack-list').replaceChildren(...(m ? m.players.map((p, i) => h('li', null,
      h('span', { class: 'n' }, i + 1), h('span', { class: 'who' }, label(p)), h('span', { class: 'what' }, modeText(p)))) : []));
    $('btn-to-roll').hidden = !m;
    for (const el of [$('file-a'), $('file-b'), $('btn-local')]) el.disabled = importing;
    $('offline-line').textContent = !('serviceWorker' in navigator)
      ? 'Offline mode needs the https address of this app.'
      : swStatus ? (swStatus.offline ? `Ready offline · app ${swStatus.pinned}` : NOT_OFFLINE) : swError || 'Saving the app for offline use…';
  }

  function renderRoll() {
    const o = order(), absent = [...S.absent].sort(byName);
    const row = (id, n) => { const p = player(id); return h('li', { dataset: { id } },
      n ? h('span', { class: 'n' }, n) : null, h('span', null, p ? p.name : id), h('span', { class: 'num' }, numText(p))); };
    $('roll-summary').textContent = pack ? `${o.length} batting · ${absent.length} absent · pack from ${pack.meta.created}` : '';
    $('tapin-banner').hidden = !tapIn;
    $('absent-title').textContent = tapIn ? 'Not tapped yet' : 'Absent';
    $('absent-hint').textContent = tapIn ? 'tap in batting order' : 'tap a name to add her to the end';
    $('roll-order').replaceChildren(...(o.length ? o.map((id, i) => row(id, i + 1))
      : [h('li', { class: 'empty' }, tapIn ? 'Tap the first batter below.' : 'Nobody is batting yet. Tap names below.')]));
    $('roll-absent').replaceChildren(...(absent.length ? absent.map(id => row(id)) : [h('li', { class: 'empty' }, 'Nobody absent.')]));
    $('btn-start').disabled = !o.length;
    $('btn-last').disabled = !S.lastOrder.length;
    renderChecklist();
  }

  // ---- pre-game checklist: reminders only, it never blocks Start game. A tick lasts 6 hours (one game day).
  const ticked = id => Number.isFinite(S.checks[id]) && Date.now() - S.checks[id] < CHECK_TTL_MS;
  const allTicked = () => CHECKS.every(([id]) => ticked(id));
  function renderChecklist() {
    const done = CHECKS.filter(([id]) => ticked(id)).length, all = done === CHECKS.length, st = swStatus;
    const head = h('button', { class: 'check-head', 'aria-expanded': String(checkOpen), onclick: () => { checkOpen = !checkOpen; renderChecklist(); } },
      h('b', null, 'Before the game'),
      h('span', { class: 'check-count' + (all ? ' done' : '') }, all ? '✓ All set' : `${done} of ${CHECKS.length}`));
    if (!checkOpen) { $('checklist').replaceChildren(head); return; }
    const offline = !('serviceWorker' in navigator) ? 'offline mode needs the https address of this app'
      : st ? (st.offline ? 'saved for offline use' : 'not saved for offline use (see Settings)') : swError || 'checking offline copy…';
    $('checklist').replaceChildren(head, h('div', { class: 'check-body' },
      h('p', { class: 'check-auto' }, h('span', { class: 'mark ' + (st && st.offline ? 'ok' : 'warn'), 'aria-hidden': 'true' }, st && st.offline ? '✓' : '!'),
        h('span', null, `Pack from ${pack ? pack.meta.created || 'an unknown date' : '—'} · ${offline}`)),
      CHECKS.map(([id, text]) => h('button', { class: 'tick', role: 'checkbox', 'aria-checked': String(ticked(id)), onclick: () => toggleCheck(id) },
        h('span', { class: 'box', 'aria-hidden': 'true' }, ticked(id) ? '✓' : ''), h('span', null, text))),
      h('button', { class: 'btn', onclick: openSpeaker }, 'Connect speaker')));
  }
  function toggleCheck(id) {
    if (ticked(id)) delete S.checks[id]; else S.checks[id] = Date.now();
    save();
    render();
  }
  function rollTap(id) {                     // roll call: batting -> absent, absent -> end of the order
    if (order().includes(id)) {
      S.order = order().filter(x => x !== id);
      S.absent.push(id);
    } else {
      S.absent = S.absent.filter(x => x !== id);
      S.order = order().concat(id);
    }
    changed();
  }
  function everyoneAbsent() { S.order = []; S.absent = packIds(); setCur(null); }

  function renderGame() {
    const p = player(S.cur), up = upcoming(2);
    const name = p ? p.name.toUpperCase() : 'NO BATTERS';
    $('ab-name').textContent = name;
    $('ab-name').parentNode.classList.toggle('long', name.length > 9);
    $('ab-num').textContent = numText(p);
    $('ab-song').textContent = p ? modeText(p) : 'Long-press a name below to add her back.';
    $('on-deck').textContent = up[0] ? label(player(up[0])) : '—';
    $('in-hole').textContent = up[1] ? label(player(up[1])) : '—';
    renderLineup(up[0]);
    renderControls();
    $('btn-back').disabled = $('btn-skip').disabled = locked || phase !== 'idle';
    for (const b of document.querySelectorAll('[data-act=settings]')) b.disabled = locked;
    $('btn-lock').textContent = locked ? 'LOCKED' : 'LOCK';
    document.body.classList.toggle('locked', locked);
  }

  function renderLineup(onDeck) {
    const list = $('lineup');
    const rows = order().map((id, i) => {
      const p = player(id);
      const tag = id === S.cur ? (phase === 'playing' ? 'PLAYING' : 'AT BAT') : id === S.queued ? 'NEXT' : id === onDeck ? 'ON DECK' : null;
      return h('li', { class: id === S.cur ? 'cur' : '', dataset: { id } },
        h('span', { class: 'n' }, i + 1), h('span', null, p ? p.name : id), h('span', { class: 'num' }, numText(p)),
        tag && h('span', { class: 'tag' }, tag));
    });
    if (S.absent.length) {
      rows.push(h('li', { class: 'divider' }, 'ABSENT · tap to add back'));
      for (const id of [...S.absent].sort(byName)) {
        const p = player(id);
        rows.push(h('li', { class: 'out', dataset: { id, absent: '1' } }, h('span', { class: 'n' }), h('span', null, p ? p.name : id), h('span', { class: 'num' }, numText(p))));
      }
    }
    list.replaceChildren(...rows);
    if (S.cur !== shownCur) {                // keep the at-bat row in view as the game moves on
      shownCur = S.cur;
      const r = list.querySelector('li.cur');
      if (r && (r.offsetTop < list.scrollTop || r.offsetTop + r.offsetHeight > list.scrollTop + list.clientHeight)) {
        list.scrollTop = Math.max(0, r.offsetTop - 8);
      }
    }
  }

  function renderControls() {
    const btn = $('btn-play'), p = player(S.cur), now = performance.now();
    let cls = 'play', kids;
    if (phase === 'playing') {
      const left = Math.ceil((FADE_LOCK_MS - (now - playAt)) / 1000);
      if (fading) { cls += ' fade wait'; kids = [h('span', { class: 'verb' }, 'FADING…')]; }
      else if (left > 0) { cls += ' fade wait'; kids = [h('span', { class: 'verb' }, 'FADE'), h('span', { class: 'small' }, `ready in ${left}`)]; }
      else { cls += ' fade'; kids = [h('span', { class: 'verb' }, 'FADE')]; }
    } else if (phase === 'cooldown') {
      cls += ' cool';
      kids = [h('span', { class: 'small' }, 'NEXT BATTER IN'), h('span', { class: 'who' }, Math.max(1, Math.ceil((coolUntil - now) / 1000)))];
    } else if (!p) {
      cls += ' none';
      kids = [h('span', { class: 'small' }, 'No batters in the lineup')];
    } else if (!clipOf(p)) {
      cls += ' silent';
      kids = [h('span', { class: 'who' }, `NEXT: ${p.name.toUpperCase()} (no music)`), h('span', { class: 'small' }, '— tap to advance')];
    } else {
      const who = [p.name.toUpperCase(), numText(p)].filter(Boolean).join(' ');
      if (who.length > 11) cls += ' long';
      kids = [h('span', { class: 'verb' }, 'PLAY'), ' ', h('span', { class: 'who' }, who)];
      if (p.mode === 'intro_only') kids.push(h('span', { class: 'small' }, 'announcer only'));
    }
    btn.className = cls;
    btn.replaceChildren(...kids);
    $('btn-stop').classList.toggle('idle', phase !== 'playing');
  }
  function startTick() {                     // countdowns on the big button while not idle
    if (tickTimer) return;
    tickTimer = setInterval(() => {
      if (phase === 'idle') { clearInterval(tickTimer); tickTimer = 0; }
      if (screen === 'game') renderControls();
    }, 200);
  }

  // ---- status pill
  const wake = {
    supported: 'wakeLock' in navigator, sentinel: null, error: '',
    held() { return !!(this.sentinel && !this.sentinel.released); },
    request() {                              // call inside a tap (Start / Re-arm)
      if (!this.supported) return;
      const old = this.sentinel;
      try {
        navigator.wakeLock.request('screen').then(s => {
          this.sentinel = s;
          this.error = '';
          s.addEventListener('release', updatePill);
          if (old && !old.released) old.release().catch(() => {});
          updatePill();
        }, e => { this.error = (e && e.message) || String(e); updatePill(); });
      } catch (e) { this.error = e.message; }
    },
  };

  function issues() {
    const out = [];
    if (!pack) out.push('No team pack on this phone.');
    else if (loadedPackId !== pack.id) out.push('Pack audio is not loaded yet (Start game loads it).');
    const st = audio.state();
    if (st !== 'running') out.push(`Audio is ${st}.`);
    if (audio.trouble()) out.push(`Audio was interrupted: ${audio.trouble()}.`);
    if (wake.supported && !wake.held()) out.push('Screen wake lock is not held.');
    if (!armedAt || soundOkAt < armedAt) out.push('Sound Check not confirmed since audio was armed.');
    if (swStatus && !swStatus.offline) out.push('The app is not saved for offline use (see Settings).');
    return out;
  }
  function updatePill() {
    const pill = $('pill'), ok = !issues().length;
    pill.className = 'pill ' + (ok ? 'ok' : 'check');
    pill.textContent = ok ? 'READY' : 'CHECK';
    pill.disabled = locked;
  }

  // ---- arming: everything up to the first await runs inside the tap (iOS needs the gesture)
  function armNow(fresh) {
    audio.arm(fresh, () => wake.request());
    armedAt = Date.now();
    soundOkAt = 0;
    $('rearm').hidden = $('trouble-banner').hidden = true;
    updatePill();
  }

  // Audio trouble: TAP TO RE-ARM covers the screen, but never over a playing clip (FADE and STOP must stay
  // live, and she may still be hearing it). Then a banner shows, and the overlay comes when the clip ends.
  function showTrouble(why) {
    const on = !!why && S.active && screen === 'game', playing = phase === 'playing';
    $('trouble-banner').textContent = `Sound may be off (${why}). Silent? Tap STOP, then RE-ARM.`;
    $('trouble-banner').hidden = !(on && playing);
    if (on && !playing) {
      const now = Date.now(), recent = rearms.filter(t => now - t < 60000).length;
      $('rearm-why').textContent = recent >= 2
        ? `Re-arm isn't fixing it (${why}). Swipe the app closed and reopen it, or use VLC for now.`
        : `Sound may be off (${why}). One tap fixes it.`;
      $('rearm').hidden = false;
    }
  }

  async function afterArm() {
    const my = ++armSeq;
    sheetOpen('check', [h('h2', null, 'Sound Check'), h('p', { class: 'lead' }, 'Getting the team pack ready…'),
      h('button', { class: 'btn', onclick: () => { armSeq++; sheetClose(); } }, 'Cancel')], true);
    try {
      await ensureBytes();
    } catch (e) {
      if (my === armSeq) storageFailed(e);
      return;
    }
    // A decode that never settles (WebKit) must not hold this sheet up: 3 s, then prefetchQueue carries on.
    await Promise.race([audio.prefetch([S.cur, ...upcoming(2)].map(id => clipOf(player(id)))),
      new Promise(r => setTimeout(r, 3000))]);
    await audio.musicQuiet();                // Start game's warm-up fade finishes before the chime
    const ok = await audio.ready();
    if (my !== armSeq) return;
    audio.chime();
    sheetOpen('check', [
      h('h2', null, 'Did you hear the chime?'),
      h('p', null, ok ? 'It just played through the speaker.' : 'Audio did not start. Tap No to try again.'),
      h('p', { class: 'note' }, 'Speaker connected and phone volume up? Only tap Yes if you heard it.'),
      h('div', { class: 'row2' },
        h('button', { class: 'btn huge primary', onclick: soundYes }, 'Yes'),
        h('button', { class: 'btn huge', onclick: soundNo }, 'No — try again')),
    ], true);
    updatePill();
  }
  function soundYes() {
    soundOkAt = S.soundCheckAt = S.checks.speaker = Date.now();
    save();
    sheetClose();
    render();
  }
  function soundNo() { armNow(true); afterArm(); }        // re-arm inside this tap, then chime again

  async function ensureBytes() {                          // IndexedDB -> memory, once per pack
    if (loadedPackId === pack.id && audio.hasBytes()) return;
    const files = await Store.loadFiles(pack.id);
    audio.setBytes(files);
    loadedPackId = pack.id;
  }

  function storageFailed(e) {
    sheetOpen('storage', [
      h('h2', null, 'Storage problem'),
      h('p', null, `The team pack on this phone could not be read: ${(e && e.message) || e}`),
      h('p', { class: 'note' }, 'Reload usually fixes it. If it does not, use VLC for this game.'),
      h('button', { class: 'btn huge primary', onclick: () => location.reload() }, 'Reload'),
    ], true);
  }

  // ---- game start / resume / end
  function startGame() {                     // click handler: synchronous until afterArm()
    if (!pack || !order().length) return;
    warmStop(1.5, true);                     // inside the tap, before the Sound Check
    stopTest();                              // never under the Sound Check chime
    armNow(false);
    tapIn = false;
    Object.assign(S, { lastOrder: order().slice(), cur: order()[0], queued: null, slot: null, gameAt: Date.now(), active: true });
    applyKeepAwake();                        // after active is set, still inside the tap
    phase = 'idle';
    save();
    show('game');
    afterArm();
  }
  function resumeGame() {
    warmStop(1.5, true);
    stopTest();
    armNow(false);
    if (!order().includes(S.queued)) S.queued = null;
    if (!order().includes(S.cur)) setCur(nextOf(S.cur));
    S.active = true;
    applyKeepAwake();
    phase = 'idle';
    save();
    show('game');
    afterArm();
  }
  function offerResume() {
    sheetOpen('resume', [
      h('h2', null, 'Resume game?'),
      h('p', { class: 'lead' }, 'Next up: ', h('b', null, label(player(S.cur) || player(order()[0])))),
      h('button', { class: 'btn huge primary', onclick: () => { sheetClose(); resumeGame(); } }, 'Resume'),
      h('button', { class: 'btn big', onclick: () => { sheetClose(); S.active = false; save(); show('roll'); } }, 'New game'),
    ], true);
  }
  function endGame() {
    sheetClose();
    playSeq++;                               // ignore the stopped clip's callback
    if (phase === 'playing') audio.stop();
    clearTimeout(coolTimer);
    phase = 'idle';
    fading = false;
    locked = false;
    S.active = false;
    S.queued = S.slot = null;
    applyKeepAwake();
    save();
    show('roll');
  }
  function confirmEndGame() {                // one stray tap next to Re-arm must not lose the batting position
    sheetOpen('end', [
      h('h2', null, 'End this game?'),
      h('p', { class: 'lead' }, 'Next up: ', h('b', null, label(player(S.cur)))),
      h('p', { class: 'note' }, 'Sound trouble? Keep playing and use Re-arm instead.'),
      h('button', { class: 'btn huge primary', onclick: sheetClose }, 'Keep playing'),
      h('button', { class: 'btn big', onclick: endGame }, 'End game'),
    ]);
  }

  // ---- game controls
  function onPlay() {
    audio.touch();                           // every PLAY tap: audio session + resume(), synchronously
    const now = performance.now();
    if (now - lastTap < DEBOUNCE_MS) return;
    if (phase === 'playing') {               // the button is FADE now
      if (fading || now - playAt < FADE_LOCK_MS) return;   // ignored for the first 3 s
      lastTap = now;
      fading = true;
      audio.fade();
      renderControls();
      return;
    }
    if (phase !== 'idle') return;            // cooldown
    const p = player(S.cur);
    if (!p) return;
    lastTap = now;
    const path = clipOf(p);
    if (!path) { cooldown(); return; }       // silent: PLAY moves on, after the same cooldown as a clip
    if (!pack || loadedPackId !== pack.id) { toast('Still loading the team pack…'); return; }
    phase = 'playing';
    fading = stopEarly = false;
    playAt = now;
    const my = ++playSeq;
    audio.play(path, (reason, err) => { if (my === playSeq) clipDone(reason, err); });
    render();
    startTick();
  }

  function clipDone(reason, err) {
    const early = reason === 'stopped' && stopEarly;
    fading = stopEarly = false;
    if (early || reason === 'rearm' || reason === 'replaced' || reason === 'error') {
      phase = 'idle';                        // cut off, not finished: the same batter stays up...
      const here = order().includes(S.cur);
      if (reason === 'error') toast(`Could not play this clip: ${(err && err.message) || 'unknown error'}`);
      else if (early && here) toast(`Stopped. ${label(player(S.cur))} is still up.`);
      if (here) render(); else advance();    // ...unless she has left the lineup
    } else {
      cooldown();                            // ended / faded / stopped
    }
    showTrouble(audio.trouble());            // held back while the clip played
  }
  function cooldown() {                      // PLAY is ignored for 2 s, then the next batter is up
    phase = 'cooldown';
    coolUntil = performance.now() + COOLDOWN_MS;
    clearTimeout(coolTimer);
    coolTimer = setTimeout(() => { phase = 'idle'; advance(); }, COOLDOWN_MS);
    render();
    startTick();
  }

  function onStop() {                        // always works, locked or not
    audio.touch();
    const now = performance.now();
    if (now - lastStop < DEBOUNCE_MS) return;
    lastStop = now;
    if (phase !== 'playing') return;
    // Before FADE is live (3 s, before her name is even said) STOP aborts: she stays up for her real walk-up.
    stopEarly = now - playAt < FADE_LOCK_MS;
    lastTap = now;                           // and PLAY waits out the debounce
    audio.stop();
  }

  function idleTap() {
    const now = performance.now();
    if (locked || phase !== 'idle' || now - lastTap < DEBOUNCE_MS) return false;
    lastTap = now;
    return true;
  }
  function onBack() { if (idleTap()) { setCur(prevOf(S.cur)); changed(); } }
  function onSkip() { if (idleTap()) { setCur(upcoming(1)[0] || S.cur); changed(); } }

  function toggleLock() {
    locked = !locked;
    if (locked) sheetClose();
    render();
    toast(locked ? 'Locked: only PLAY, FADE and STOP work.' : 'Unlocked.');
  }

  function openMenu(id) {
    if (locked) return;
    const p = player(id), batting = order().includes(id);
    sheetOpen('menu', [
      h('p', { class: 'big-name' }, label(p)),
      batting && h('button', { class: 'btn big', onclick: () => { sheetClose(); markAbsent(id); } }, 'Absent'),
      id !== S.cur && h('button', { class: 'btn big', onclick: () => { sheetClose(); batNext(id); } }, 'Bat next'),
      h('button', { class: 'btn big', onclick: () => { sheetClose(); moveToEnd(id); } }, 'Move to end'),
      h('button', { class: 'btn big dark', onclick: sheetClose }, 'Cancel'),
    ]);
  }

  // Tap vs long-press on list rows (pointer events; a scroll cancels both).
  function pressable(list, onTap, onLong) {
    let timer = 0, row = null, x = 0, y = 0;
    const clear = () => { clearTimeout(timer); timer = 0; if (row) row.classList.remove('pressing'); };
    list.addEventListener('pointerdown', e => {
      clear();
      row = locked ? null : e.target.closest('li[data-id]');
      if (!row) return;
      x = e.clientX; y = e.clientY;
      row.classList.add('pressing');
      timer = setTimeout(() => { const id = row.dataset.id; clear(); row = null; onLong(id); }, LONG_PRESS_MS);
    });
    list.addEventListener('pointermove', e => {
      if (timer && Math.hypot(e.clientX - x, e.clientY - y) > 10) { clear(); row = null; }
    });
    list.addEventListener('pointerup', () => {
      if (!timer || !row) return;
      const r = row;
      clear();
      row = null;
      onTap(r.dataset.id, r);
    });
    list.addEventListener('pointercancel', () => { clear(); row = null; });
    list.addEventListener('contextmenu', e => e.preventDefault());
  }

  // Hold-to-toggle (LOCK): a progress bar fills for 1.5 s; letting go early cancels.
  function holdable(el, ms, fn) {
    let timer = 0, done = false;
    const cancel = () => { clearTimeout(timer); timer = 0; el.classList.remove('holding'); };
    el.addEventListener('pointerdown', e => {
      e.preventDefault();
      cancel();
      done = false;
      void el.offsetWidth;                   // restart the fill animation
      el.classList.add('holding');
      timer = setTimeout(() => { cancel(); done = true; fn(); }, ms);
    });
    for (const ev of ['pointerup', 'pointerleave', 'pointercancel']) el.addEventListener(ev, cancel);
    el.addEventListener('contextmenu', e => e.preventDefault());
    el.addEventListener('click', () => { if (!done) toast(`Hold ${locked ? 'LOCKED' : 'LOCK'} for 1.5 seconds.`); done = false; });
  }

  // ---- import
  async function parsePack(buf, progress) {
    const entries = WalkupZip.readZip(buf);
    if (!entries['pack.json']) throw new Error('This file has no pack.json, so it is not a team pack.');
    let raw;
    try { raw = JSON.parse(new TextDecoder().decode(entries['pack.json'])); } catch (e) { throw new Error('pack.json is not readable (bad JSON).'); }
    if (!raw || raw.schema !== 1) {
      throw new Error(`This pack is format ${raw && raw.schema}, but this app reads format 1. Rebuild the pack or update the app.`);
    }
    const players = checkPlayers(raw, entries);
    const warmup = checkWarmup(raw, entries, players);
    const names = Object.keys(entries).filter(n => n.startsWith('audio/'));
    const files = {};
    for (let i = 0; i < names.length; i++) {  // test-decode EVERY clip now, not at the game
      const name = names[i];
      progress(i + 1, names.length);
      const bytes = entries[name].slice().buffer;          // own copy, not a view of the whole zip
      let decoded;
      try {
        decoded = await audio.testDecode(bytes.slice(0));  // decodeAudioData detaches what it is given
      } catch (e) {
        throw new Error(`${name} will not play on this device (${(e && e.message) || 'could not decode'}). Rebuild the pack.`);
      }
      if (!decoded || !(decoded.duration > 0.1)) throw new Error(`${name} is empty.`);
      files[name] = { bytes, type: 'audio/mp4' };
    }
    return { meta: { schema: 1, created: String(raw.created || ''), players, warmup }, files };
  }

  // Optional "warmup" list (packs before it have none): every file must be in the pack, like player audio.
  function checkWarmup(raw, entries, players) {
    if (raw.warmup == null) return [];
    if (!Array.isArray(raw.warmup)) throw new Error('pack.json "warmup" is not a list.');
    const ids = new Set(players.map(p => p.id));
    return raw.warmup.map((w, i) => {
      const where = `pack.json warm-up song ${i + 1}`;
      if (!w || typeof w !== 'object') throw new Error(`${where} is not readable.`);
      if (typeof w.file !== 'string' || !w.file.startsWith('audio/') || !(w.file in entries)) {
        throw new Error(`${where}: "${w.file}" is missing from the pack.`);
      }
      return {
        file: w.file, title: typeof w.title === 'string' && w.title.trim() ? w.title.trim() : `Song ${i + 1}`,
        players: Array.isArray(w.players) ? [...new Set(w.players.filter(id => ids.has(id)))] : [],
        seconds: Number.isFinite(+w.seconds) ? +w.seconds : 0,
        lufs: w.lufs == null || !Number.isFinite(+w.lufs) ? null : +w.lufs,
      };
    });
  }

  function checkPlayers(raw, entries) {
    if (!Array.isArray(raw.players) || !raw.players.length) throw new Error('pack.json lists no players.');
    const seen = new Set();
    return raw.players.map((p, i) => {
      const where = `pack.json player ${i + 1}`;
      if (!p || typeof p.id !== 'string' || !p.id) throw new Error(`${where} has no id.`);
      if (seen.has(p.id)) throw new Error(`${where}: id "${p.id}" appears twice.`);
      seen.add(p.id);
      if (!MODES.includes(p.mode)) throw new Error(`${where} has an unknown mode "${p.mode}".`);
      const file = key => {
        const v = p[key];
        if (v == null || v === '') return null;
        if (typeof v !== 'string' || !(v in entries)) throw new Error(`${where}: "${v}" is missing from the pack.`);
        return v;
      };
      const q = {
        id: p.id, name: String(p.name || p.id).trim(), number: p.number == null ? '' : String(p.number).trim(),
        song_title: String(p.song_title || ''), mode: p.mode,
        order: Number.isFinite(+p.order) ? +p.order : i + 1,
        full: file('full'), intro: file('intro'),
        seconds: +p.seconds || 0, lufs: p.lufs == null ? null : +p.lufs,
      };
      if (q.mode === 'full' && !q.full) throw new Error(`${where} is "full" but has no track.`);
      if (q.mode === 'intro_only' && !q.intro && !q.full) throw new Error(`${where} is "intro_only" but has no audio.`);
      if (q.mode === 'silent') q.full = null;
      return q;
    }).sort((a, b) => a.order - b.order);
  }

  async function importFrom(getBytes, from) {
    if (importing || locked) return;
    importing = true;
    warmStop(0.4, true);
    const prog = $('import-progress'), err = $('import-error'), ok = $('import-ok');
    err.hidden = ok.hidden = true;
    prog.hidden = false;
    prog.textContent = `Reading ${from}…`;
    renderPack();
    try {
      const buf = await getBytes();
      const { meta, files } = await parsePack(buf, (i, n) => { prog.textContent = `Checking audio ${i} of ${n}…`; });
      prog.textContent = 'Saving to this phone…';
      const rec = await Store.replacePack(meta, files);     // new record -> flip current -> delete old
      try { if (navigator.storage && navigator.storage.persist) navigator.storage.persist().catch(() => {}); } catch (e) { /* optional */ }
      audio.setBytes(null);                  // Start game loads the new pack from storage
      loadedPackId = null;
      pack = rec;
      Object.assign(W, { order: [], k: -1, next: null, state: 'stopped', pos: 0 });
      indexPlayers();
      S.active = false;
      applyKeepAwake();
      mergeLineup();
      save();
      ok.textContent = `Imported the pack from ${meta.created || 'an unknown date'}: ${meta.players.length} players, every clip checked.`;
      ok.hidden = false;
    } catch (e) {
      err.textContent = (e && e.message) || String(e);
      err.hidden = false;
    } finally {
      importing = false;
      prog.hidden = true;
      render();
    }
  }
  function fromFile(input) {
    const f = input.files && input.files[0];
    input.value = '';                        // picking the same file again still fires change
    if (f) importFrom(() => (f.arrayBuffer ? f.arrayBuffer() : new Response(f).arrayBuffer()), f.name);
  }
  function fromThisPC() {                    // review server on the same machine (localhost only)
    importFrom(async () => {
      const r = await fetch('/download/team-pack', { cache: 'no-store' });
      if (!r.ok) {
        let msg = `The PC answered ${r.status}.`;
        try { msg = (await r.json()).error || msg; } catch (e) { /* not JSON */ }
        throw new Error(msg);
      }
      return r.arrayBuffer();
    }, 'the pack from this PC');
  }

  // ---- sheets and toast
  function sheetOpen(kind, kids, modal = false) {
    sheetKind = kind;
    sheetModal = modal;
    sheetAt = performance.now();
    $('sheet-body').replaceChildren(...kids.filter(Boolean));
    $('sheet').hidden = false;
  }
  // Redraw the open sheet in place: same scroll position, and taps are not held off as for a new sheet.
  function sheetRedraw(draw) {
    const b = $('sheet-body'), y = b.scrollTop, at = sheetAt;
    draw();
    sheetAt = at;
    b.scrollTop = y;
  }
  function sheetClose() {
    sheetKind = '';
    $('sheet').hidden = true;
    $('sheet-body').replaceChildren();
  }
  function toast(msg, ms = 2600) {
    const t = $('toast');
    t.textContent = msg;
    t.hidden = false;
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => { t.hidden = true; }, ms);
  }

  // ---- connect speaker, test speaker, keep speaker awake. iOS can't see or pick Bluetooth devices or read
  // the volume, so this is instructions plus a real clip at game volume for the parent to judge by ear.
  function testPick() {                      // first batter with music, else the first such player in the pack
    for (const id of [...order(), ...packIds()]) { const p = player(id), path = clipOf(p); if (path) return { p, path }; }
    return null;
  }
  function openSpeaker() {
    spk = { playing: spk.playing, asked: spk.playing, help: false, error: '' };
    drawSpeaker();
  }
  function redrawSpeaker() { if (sheetKind === 'speaker') sheetRedraw(drawSpeaker); }
  function drawSpeaker() {
    const kids = [h('h2', null, 'Connect speaker'), h('ol', { class: 'steps' },
      h('li', null, 'Turn the speaker on.'),
      h('li', null, 'Swipe down from the top-right corner to open Control Center. Tap the AirPlay icon on the music tile and pick your speaker. (Or Settings > Bluetooth and tap it there.)'),
      h('li', null, "Turn the phone volume all the way up, then set the loudness with the speaker's own buttons."))];
    if (S.active) {                          // a batter's intro mid-game would confuse the field: chime only
      kids.push(h('button', { class: 'btn primary', disabled: !pack, onclick: () => { sheetClose(); armNow(true); afterArm(); } }, 'Re-arm audio and Sound Check'),
        h('p', { class: 'note' }, 'Uses the quiet chime, safe between batters.'));
    } else {
      const pick = testPick();
      kids.push(h('button', { class: 'btn big primary', disabled: !pick || spk.playing, onclick: testSpeaker }, spk.playing ? 'Playing…' : 'Test speaker'),
        h('p', { class: 'note' }, pick ? `Plays ${pick.p.name}'s intro at game volume, then fades.` : pack ? 'Nobody in the team pack has music to test with.' : 'Import the team pack first.'));
      if (spk.error) kids.push(h('p', { class: 'error', role: 'alert' }, spk.error));
      if (spk.asked) {
        kids.push(h('p', { class: 'lead' }, 'Did you hear it?'), h('div', { class: 'row2' },
          h('button', { class: 'btn huge primary', onclick: testYes }, 'Yes'),
          h('button', { class: 'btn huge', onclick: testNo }, 'No — try again')));
      }
      if (spk.help) kids.push(h('p', { class: 'error' }, "Check the speaker is on and picked in Control Center, the phone volume is up, and the sound isn't coming out of the phone itself. Then tap Test speaker again."));
    }
    kids.push(...keepAwakeSwitch(drawSpeaker), h('button', { class: 'btn dark', onclick: sheetClose }, 'Close'));
    sheetOpen('speaker', kids);
  }

  function testSpeaker() {                   // click handler: synchronous until the first await (iOS gesture)
    const pick = testPick();
    if (spk.playing || S.active || !pick) return;
    warmStop(0.3);                           // the test clip plays on its own
    const st = audio.state();
    if (st === 'not armed' || st === 'closed' || audio.trouble()) audio.arm(false);   // not armNow(): no game yet
    const my = ++testSeq;
    spk = { playing: true, asked: false, help: false, error: '' };
    redrawSpeaker();
    (async () => {
      const fail = msg => { if (my !== testSeq) return; spk.playing = false; spk.error = msg; redrawSpeaker(); };
      try { await ensureBytes(); } catch (e) { fail((e && e.message) || String(e)); return; }
      const ok = (await audio.ready()) || audio.state() === 'running';
      if (my !== testSeq) return;
      if (!ok) { fail("Audio didn't start. Tap Test speaker again."); return; }
      let t = 0;
      audio.play(pick.path, (reason, err) => {
        clearTimeout(t);                     // never fade whatever clip plays next
        if (testTimer === t) testTimer = 0;
        if (my !== testSeq) return;
        spk.playing = false;
        if (reason === 'error') { spk.asked = false; spk.error = `Could not play the clip: ${(err && err.message) || 'unknown error'}`; }
        redrawSpeaker();
      });
      t = testTimer = setTimeout(() => { if (testTimer === t) testTimer = 0; if (my === testSeq && spk.playing && audio.playing()) audio.fade(); }, TEST_FADE_AT_MS);
      spk.asked = true;
      redrawSpeaker();
    })();
  }
  function stopTest() {                      // a test clip still playing (or loading) stops now
    if (!spk.playing) return;
    testSeq++;
    clearTimeout(testTimer);
    testTimer = 0;
    spk.playing = false;
    audio.stop();
  }
  function testYes() {
    S.checks.speaker = Date.now();
    save();
    toast('Speaker checked.');
    sheetClose();
    render();
  }
  function testNo() {
    stopTest();
    spk = { playing: false, asked: false, help: true, error: '' };
    redrawSpeaker();
  }

  function applyKeepAwake() { audio.setKeepAwake(!!(S.keepAwake && S.active)); }   // on only during a game
  function keepAwakeSwitch(redraw) {
    const on = S.keepAwake;
    return [h('button', { class: 'switch', role: 'switch', 'aria-checked': String(on), onclick: () => {
      S.keepAwake = !S.keepAwake;
      save();
      applyKeepAwake();                      // inside the tap: may start the bed
      sheetRedraw(redraw);
      toast(!S.keepAwake ? 'Keep speaker awake is off.' : S.active ? 'Keep speaker awake is on.' : 'Keep speaker awake is on. It starts with the game.');
    } }, h('span', { class: 'switch-label' }, 'Keep speaker awake'), h('span', { class: 'switch-state' }, on ? 'ON' : 'OFF'), h('span', { class: 'knob', 'aria-hidden': 'true' })),
    h('p', { class: 'note' }, 'Plays a very faint hiss during a game so the speaker never dozes off and clips "Now batting". Off unless you turn it on.')];
  }

  // ---- warm-up music: only while no game is active. Every girl's song, shuffled, round after round; the engine
  // crossfades from one to the next and asks this queue what comes after the current song.
  const warmList = () => (pack && Array.isArray(pack.meta.warmup) ? pack.meta.warmup : []);
  const warmOn = () => warmList().length > 0 && !S.active;
  const warmCur = () => (W.k >= 0 ? warmList()[W.order[W.k]] || null : null);
  const mmss = t => `${Math.floor(t / 60)}:${String(Math.floor(t % 60)).padStart(2, '0')}`;
  function shuffled(n, avoid) {              // a new round never opens with the song that just played
    const a = [...Array(n).keys()];
    for (let i = n - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; }
    if (n > 1 && a[0] === avoid) { const j = 1 + Math.floor(Math.random() * (n - 1)); [a[0], a[j]] = [a[j], a[0]]; }
    return a;
  }
  function warmPeek() {                      // entry index that plays after the current one
    const n = warmList().length;
    if (!n) return null;
    if (!W.order.length) W.order = shuffled(n);
    if (W.k + 1 < W.order.length) return W.order[W.k + 1];
    if (!W.next) W.next = shuffled(n, W.order[W.k]);
    return W.next[0];
  }
  function warmTake() {
    const i = warmPeek();
    if (i == null) return null;
    if (W.k + 1 < W.order.length) W.k++;
    else { W.order = W.next; W.next = null; W.k = 0; }
    return i;
  }
  const fileOf = i => (i == null ? null : (warmList()[i] || {}).file || null);
  function whose(e) {                        // "Test One's song", "Test One and Test Two's song"
    const names = e.players.map(id => player(id)).filter(Boolean).map(p => p.name);
    if (!names.length) return '';
    return (names.length > 1 ? `${names.slice(0, -1).join(', ')} and ${names[names.length - 1]}` : names[0]) + "'s song";
  }
  function warmPos() {                       // [position, length] of the current song in seconds
    const e = warmCur(), i = audio.musicInfo();
    if (!e) return [0, 0];
    if (W.state === 'playing' && i.playing && i.path === e.file) return [i.position, i.duration || e.seconds];
    return [W.state === 'stopped' ? 0 : W.pos, e.seconds];
  }

  function warmToggle() {                    // click handler (mini player and sheet)
    const now = performance.now();
    if (now - W.lastTap < DEBOUNCE_MS) return;
    W.lastTap = now;
    if (W.state === 'playing') warmPause(); else warmPlay();
  }
  function warmPlay() {                      // synchronous until the first await (iOS gesture)
    if (!warmOn() || W.state === 'playing') return;
    const st = audio.state();
    if (st === 'not armed' || st === 'closed' || audio.trouble()) audio.arm(false);   // like Test speaker: not armNow()
    else audio.touch();
    wake.request();
    if (W.state === 'stopped' || W.k < 0) { warmTake(); W.pos = 0; }
    warmStart(W.pos, W.pos ? 0.5 : 1);
  }
  function warmStart(offset, fadeIn) {
    const e = warmCur(), my = ++W.seq;
    if (!e) return;
    W.state = 'playing';
    W.pos = offset;                          // what Pause keeps if it comes before the song starts
    warmChanged();
    (async () => {
      const fail = msg => { if (my !== W.seq) return; W.seq++; W.state = 'stopped'; warmChanged(); toast(msg, 4000); };
      try { await ensureBytes(); } catch (err) { fail((err && err.message) || String(err)); return; }
      const ok = (await audio.ready()) || audio.state() === 'running';
      if (my !== W.seq) return;
      if (!ok) { fail("Audio didn't start. Tap Play again."); return; }
      audio.musicPlay(e.file, { offset, fadeIn });
    })();
  }
  function warmPause() {                     // short fade; Play carries on from here
    if (W.state !== 'playing') return;
    W.pos = warmPos()[0];
    W.seq++;
    W.state = 'paused';
    audio.musicStop(0.4);
    warmChanged();
  }
  function warmSkip() {                      // click handler: ~1 s crossfade into the next song
    const now = performance.now();
    if (!warmOn() || W.state === 'stopped' || now - W.lastTap < DEBOUNCE_MS) return;
    W.lastTap = now;
    warmTake();
    W.pos = 0;
    if (W.state === 'paused') { warmChanged(); return; }
    audio.touch();
    warmStart(0, 1);
  }
  function warmStop(fadeS, release) {        // Start game, Test speaker, import: the music fades and forgets its place
    W.seq++;
    W.state = 'stopped';
    W.pos = 0;
    audio.musicStop(fadeS, release);
    warmChanged();
  }
  function warmEvent(e) {                    // from the engine: a song started, or the music died
    if (e.kind === 'song') W.pos = 0;
    if (e.kind === 'stopped' && e.reason !== 'stopped' && W.state === 'playing') {
      W.seq++;
      W.state = 'stopped';
      if (e.reason === 'error') toast(`Could not play this song: ${(e.error && e.error.message) || 'unknown error'}`, 4000);
    }
    warmChanged();
  }

  function renderWarm() {                    // the mini player in the Batting order dock
    const on = warmOn(), e = warmCur(), n = warmList().length, playing = W.state === 'playing';
    $('warm').hidden = !on;
    $('warm-note').hidden = !on || W.state === 'stopped';
    if (!on) return;
    $('warm-sub').textContent = W.state === 'stopped' || !e ? `${n} songs, shuffled` : `${e.title} · song ${W.k + 1} of ${n}`;
    $('warm-play').classList.toggle('on', playing);
    $('warm-play').setAttribute('aria-label', playing ? 'Pause warm-up music' : 'Play warm-up music');
    $('warm-skip').disabled = W.state === 'stopped';
  }
  function warmChanged() {
    renderWarm();
    if (sheetKind === 'warmup') sheetRedraw(drawWarm);
    warmTick();
  }
  function warmTick() {                      // ~1 s refresh, only while the sheet is open or music is playing
    const want = () => W.state === 'playing' || sheetKind === 'warmup';
    if (!want() || W.timer) return;
    W.timer = setInterval(() => {
      if (!want()) { clearInterval(W.timer); W.timer = 0; return; }
      renderWarm();
      warmProgress();
    }, 1000);
  }
  function warmProgress() {                  // in place, so a tap on the sheet's buttons is never lost to a redraw
    const fill = $('warm-fill'), time = $('warm-time');
    if (!fill || !time) return;
    const [pos, len] = warmPos(), pct = len ? Math.min(100, Math.round(pos / len * 100)) : 0;
    fill.style.width = pct + '%';
    fill.parentNode.setAttribute('aria-valuenow', pct);
    time.textContent = len ? `${mmss(pos)} / ${mmss(len)}` : '';
  }
  function openWarm() { drawWarm(); warmTick(); }
  function drawWarm() {
    const list = warmList(), e = W.state === 'stopped' ? null : warmCur(), n = list.length;
    if (!W.order.length && n) W.order = shuffled(n);
    const rest = W.order.slice(W.k + 1), up = rest.slice(0, 3);
    sheetOpen('warmup', [
      h('h2', null, 'Warm-up music'),
      h('p', { class: 'note' }, "Every girl's song, shuffled, on repeat"),
      h('div', { class: 'warm-now' },
        h('b', null, e ? e.title : 'Not playing'),
        h('span', null, e ? whose(e) : `${n} songs, shuffled`)),
      h('div', { class: 'warm-prog', role: 'progressbar', 'aria-label': 'Song progress', 'aria-valuemin': 0, 'aria-valuemax': 100, 'aria-valuenow': 0 },
        h('div', { class: 'warm-fill', id: 'warm-fill' })),
      h('p', { class: 'warm-time', id: 'warm-time' }),
      h('div', { class: 'row2' },
        h('button', { class: 'btn big primary', onclick: warmToggle }, W.state === 'playing' ? 'Pause' : 'Play'),
        h('button', { class: 'btn big', disabled: W.state === 'stopped', onclick: warmSkip }, 'Skip')),
      h('h3', null, 'Up next'),
      h('ol', { class: 'warm-next' }, up.map(i => h('li', null, list[i].title)),
        rest.length > up.length && h('li', { class: 'more' }, `and ${rest.length - up.length} more`)),
      h('p', { class: 'note' }, 'then reshuffles and keeps going'),
      h('button', { class: 'btn dark', onclick: sheetClose }, 'Close'),
    ]);
    warmProgress();
  }

  // ---- settings, updates, diagnostics
  function openSettings() {
    if (locked) return;
    const st = swStatus, kids = [h('h2', null, 'Settings')];

    // Safe any time, including mid-game: this is the in-game fix when sound drops out.
    kids.push(h('h3', null, 'Audio'), h('p', { class: 'good' }, 'Safe during a game.'),
      h('button', { class: 'btn', disabled: !pack, onclick: () => { sheetClose(); armNow(true); afterArm(); } }, 'Re-arm audio and Sound Check'),
      h('button', { class: 'btn', onclick: openSpeaker }, 'Connect speaker'),
      ...keepAwakeSwitch(() => openSettings()),
      h('button', { class: 'btn', onclick: openDiagnostics }, 'Diagnostics'));

    kids.push(h('h3', null, S.active ? 'Game' : 'Team pack'));
    if (S.active) kids.push(h('button', { class: 'btn', onclick: confirmEndGame }, 'End game…'));
    else kids.push(h('p', { class: 'note' }, 'Importing a new pack ends the current game.'),
      h('button', { class: 'btn', onclick: () => { sheetClose(); show('pack'); } }, 'Team pack and import'));

    // Version changes reload the app: only at home, never right before a game.
    kids.push(h('h3', null, 'App updates'), h('p', { class: 'note' }, 'At home on Wi-Fi only, never right before a game.'),
      h('p', null, `Running ${st ? st.pinned : APP_VERSION}`));
    if (!('serviceWorker' in navigator)) {
      kids.push(h('p', { class: 'note' }, 'Offline mode and updates need the https address of this app.'));
    } else if (!st) {
      kids.push(h('p', { class: 'note' }, swError || 'The offline copy is still starting.'));
    } else {
      if (!st.offline) kids.push(h('p', { class: 'error' }, NOT_OFFLINE));
      if (st.pinned !== st.latest) {
        kids.push(h('p', null, h('b', null, 'Update available: '), st.latest),
          h('button', { class: 'btn primary', onclick: () => swCommand('pin-latest') }, 'Update'));
      } else if (st.offline) {
        kids.push(h('p', { class: 'good' }, 'Ready offline. No update waiting.'));
      }
      const i = st.versions.indexOf(st.pinned);
      if (i > 0) kids.push(h('button', { class: 'btn', onclick: () => swCommand('rollback') }, `Roll back to ${st.versions[i - 1]}`));
      kids.push(h('button', { class: 'btn', onclick: checkForUpdate }, 'Check for update (needs Wi-Fi)'));
    }
    kids.push(h('button', { class: 'btn dark', onclick: sheetClose }, 'Close'));
    sheetOpen('settings', kids);
  }


  async function swSend(msg) {
    const reg = await Promise.race([navigator.serviceWorker.ready, new Promise(r => setTimeout(r, 4000))]);
    const target = navigator.serviceWorker.controller || (reg && reg.active);
    if (!target) throw new Error('The offline copy is not running yet.');
    return new Promise((resolve, reject) => {
      const ch = new MessageChannel(), t = setTimeout(() => reject(new Error('The offline copy did not answer.')), 4000);
      ch.port1.onmessage = e => { clearTimeout(t); resolve(e.data); };
      target.postMessage(msg, [ch.port2]);
    });
  }
  async function refreshSw() {
    try {
      const r = await swSend({ type: 'status' });
      if (!r.ok) throw new Error(r.error);
      swStatus = r;
      swError = '';
    } catch (e) { swError = e.message; }
    if (sheetKind === 'settings') openSettings();
    if (screen === 'pack') renderPack();
    if (screen === 'roll') renderRoll();
  }
  async function swCommand(type) {           // Update / Roll back: re-pin, then reload into that version
    try {
      const r = await swSend({ type });
      if (!r.ok) throw new Error(r.error);
      location.reload();
    } catch (e) { toast(e.message, 4000); }
  }
  async function checkForUpdate() {
    try {
      const reg = await navigator.serviceWorker.getRegistration();
      if (reg) await reg.update();
      toast('Checked. If there is a new version, Update shows up here.');
    } catch (e) { toast('Could not check for an update (offline?).'); }
    setTimeout(refreshSw, 1500);
  }
  async function initSw() {
    if (!('serviceWorker' in navigator)) return;
    // On this PC (review server) a pinned offline copy would hide every edit to app/: off unless ?sw=1.
    if (LOCAL && !/[?&]sw=1(&|$)/.test(location.search)) {
      swError = 'Offline copy is off on this PC (add ?sw=1 to the address to test it).';
      try {
        const scope = new URL('./', location.href).href;
        for (const r of await navigator.serviceWorker.getRegistrations()) if (r.scope.startsWith(scope)) await r.unregister();
        for (const k of await caches.keys()) if (k.startsWith('app-') || k === 'walkup-meta') await caches.delete(k);
      } catch (e) { /* nothing to clean up */ }
      if (screen === 'pack') renderPack();
      return;
    }
    navigator.serviceWorker.addEventListener('controllerchange', refreshSw);   // never reloads by itself
    try {
      await navigator.serviceWorker.register('sw.js', { scope: './', updateViaCache: 'none' });
      await refreshSw();
    } catch (e) {
      swError = 'Offline copy failed: ' + e.message;
      if (screen === 'pack') renderPack();
      if (screen === 'roll') renderRoll();
    }
  }

  async function openDiagnostics() {
    let persisted = 'unknown', used = 'n/a';
    try { if (navigator.storage && navigator.storage.persisted) persisted = (await navigator.storage.persisted()) ? 'yes' : 'no (iOS may clear it when space runs low)'; } catch (e) { /* n/a */ }
    try {
      if (navigator.storage && navigator.storage.estimate) {
        const est = await navigator.storage.estimate();
        used = `${(est.usage / 1e6).toFixed(1)} MB of ${(est.quota / 1e6).toFixed(0)} MB`;
      }
    } catch (e) { /* n/a */ }
    const a = audio.info(), bad = issues();
    const time = t => new Date(t).toLocaleTimeString([], { hour: 'numeric', minute: '2-digit' });
    const standalone = (window.matchMedia && matchMedia('(display-mode: standalone)').matches) || navigator.standalone === true;
    const rows = [
      ['App version', APP_VERSION + (swStatus ? ` (offline copy ${swStatus.pinned}${swStatus.pinned !== swStatus.latest ? `; ${swStatus.latest} waiting` : ''})` : '')],
      ['Team pack', pack ? pack.meta.created || 'unknown date' : 'none'],
      ['Players', pack ? `${pack.meta.players.length} in pack · ${order().length} batting · ${S.absent.length} absent` : '—'],
      ['Pack audio', pack && loadedPackId === pack.id ? `in memory (${a.clips} clips, ${a.decoded} decoded)` : 'not loaded'],
      ['Storage persisted', persisted],
      ['Storage used', used],
      ['Audio', `${a.state}${a.sampleRate ? ` · ${a.sampleRate} Hz` : ''} · latency ${a.latency} · clock ${a.clock}`],
      ['Audio session', a.session],
      ['Interruption', a.trouble || 'none'],
      ['Recent audio trouble', a.log.length ? a.log.slice(0, 6).map(e => `${e.at} ${e.reason} (${e.state}, session ${e.session})`).join(' · ') : 'none'],
      ['Wake lock', !wake.supported ? 'not supported here (set Auto-Lock to Never)' : wake.held() ? 'held' : `not held${wake.error ? ` (${wake.error})` : ''}`],
      ['Warm-up music', !warmList().length ? 'not in this pack'
        : `${warmList().length} songs · ${W.state === 'playing' && warmCur() ? 'playing ' + warmCur().title : W.state}`],
      ['Keep speaker awake', !S.keepAwake ? 'off' : !S.active ? 'on (starts with the game)' : a.bed ? 'on (playing)' : 'on (not playing: tap Re-arm)'],
      ['Speaker test', ticked('speaker') ? time(S.checks.speaker) : 'not today'],
      ['Sound Check', armedAt && soundOkAt >= armedAt ? `confirmed ${time(soundOkAt)}` : S.soundCheckAt ? `not since arming (last ${time(S.soundCheckAt)})` : 'not yet'],
      ['Home Screen app', standalone ? 'yes' : 'no (browser tab)'],
      ['User agent', navigator.userAgent],
    ];
    sheetOpen('diag', [
      h('h2', null, bad.length ? 'CHECK' : 'READY'),
      bad.length ? h('ul', { class: 'issues' }, bad.map(t => h('li', null, t))) : h('p', { class: 'good' }, 'Pack loaded, audio running, screen held awake, Sound Check confirmed.'),
      h('h3', null, 'Details'),
      h('table', { class: 'kv' }, rows.map(([k, v]) => h('tr', null, h('th', null, k), h('td', null, v)))),
      h('button', { class: 'btn dark', onclick: sheetClose }, 'Close'),
    ]);
  }

  // ---- wiring and startup
  function wire() {
    for (const b of document.querySelectorAll('[data-act=settings]')) b.addEventListener('click', openSettings);
    $('btn-to-roll').addEventListener('click', () => show('roll'));
    $('btn-to-pack').addEventListener('click', () => show('pack'));
    $('file-a').addEventListener('change', e => fromFile(e.target));
    $('file-b').addEventListener('change', e => fromFile(e.target));
    $('btn-local').addEventListener('click', fromThisPC);

    for (const id of ['roll-order', 'roll-absent']) {
      $(id).addEventListener('click', e => { const li = e.target.closest('li[data-id]'); if (li) rollTap(li.dataset.id); });
    }
    $('btn-tapin').addEventListener('click', () => { everyoneAbsent(); tapIn = true; changed(); });
    $('btn-last').addEventListener('click', () => {
      const ids = new Set(packIds()), last = S.lastOrder.filter(id => ids.has(id));
      S.order = last;
      S.absent = packIds().filter(id => !last.includes(id));
      tapIn = false;
      changed();
    });
    $('btn-clear').addEventListener('click', () => { everyoneAbsent(); tapIn = false; changed(); });
    $('btn-tapdone').addEventListener('click', () => { tapIn = false; render(); });
    $('btn-start').addEventListener('click', startGame);
    $('warm-open').addEventListener('click', openWarm);
    $('warm-play').addEventListener('click', warmToggle);
    $('warm-skip').addEventListener('click', warmSkip);
    audio.musicQueue({ peek: () => fileOf(warmPeek()), take: () => fileOf(warmTake()) });
    audio.on('music', warmEvent);

    $('btn-play').addEventListener('click', onPlay);
    $('btn-stop').addEventListener('click', onStop);
    $('btn-back').addEventListener('click', onBack);
    $('btn-skip').addEventListener('click', onSkip);
    holdable($('btn-lock'), LOCK_HOLD_MS, toggleLock);
    $('pill').addEventListener('click', () => { if (!locked) openDiagnostics(); });
    pressable($('lineup'), (id, row) => {
      if (locked) return;
      if (row.dataset.absent) openMenu(id); else queueBatter(id);
    }, openMenu);

    $('btn-rearm').addEventListener('click', () => { rearms.push(Date.now()); if (rearms.length > 5) rearms.shift(); armNow(true); afterArm(); });
    $('btn-rearm-details').addEventListener('click', () => { $('rearm').hidden = true; openDiagnostics(); });
    $('btn-rearm-hide').addEventListener('click', () => { $('rearm').hidden = true; updatePill(); });
    audio.on('healed', () => { $('rearm').hidden = $('trouble-banner').hidden = true; updatePill(); });
    $('sheet').addEventListener('click', e => {
      // A long-press can end with a stray click on the sheet that just opened under the finger.
      if (performance.now() - sheetAt < 450) { e.stopPropagation(); e.preventDefault(); return; }
      if (e.target === $('sheet') && !sheetModal) sheetClose();
    }, true);

    audio.on('trouble', why => { showTrouble(why); updatePill(); });
    audio.on('change', updatePill);
    document.addEventListener('visibilitychange', () => {
      if (document.visibilityState === 'visible' && S.active && !wake.held()) wake.request();
    });
    window.addEventListener('pagehide', save);
    setInterval(updatePill, 1000);
  }

  async function init() {
    const resumable = S.active && Date.now() - (S.savedAt || 0) < RESUME_WINDOW_MS;   // before any save()
    wire();
    initSw();
    try {
      pack = await Store.current();
    } catch (e) {
      show('pack');
      storageFailed(e);
      return;
    }
    if (!pack) {
      S.active = false;
      show('pack');
      return;
    }
    indexPlayers();
    mergeLineup();
    Store.prune(pack.id).catch(() => {});    // leftovers from an import that died mid-way
    if (!(resumable && order().length)) S.active = false;
    save();
    show('roll');
    if (S.active) offerResume();
  }

  init();
})();
