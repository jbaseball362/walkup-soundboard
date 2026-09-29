/* Service worker: caches ONLY the app shell (never audio), with pinned versions (PLAN.md Appendix C).
   Each version precaches into its own 'app-<VERSION>' cache. The page is always served from the
   PINNED version, so a deploy never changes the phone by itself (not even on a cold launch):
   only Update in settings re-pins, and Roll back re-pins the previous version, offline.
   Bump VERSION (and APP_VERSION in app.js) for every deploy; keep this file small and stable. */
const VERSION = '2026.09.29-4';
const SHELL = ['./', 'styles.css', 'app.js', 'audio.js', 'store.js', 'zip.js', 'manifest.webmanifest',
  'icons/icon-180.png', 'icons/icon-192.png', 'icons/icon-512.png'];
const META = 'walkup-meta', PIN_KEY = './__pinned', LIST_KEY = './__versions';
const cacheName = v => 'app-' + v;
let pinnedMemo = null;

async function readMeta(key) {
  const res = await (await caches.open(META)).match(key);
  return res ? res.json() : null;
}
async function writeMeta(key, value) {
  await (await caches.open(META)).put(key, new Response(JSON.stringify(value), { headers: { 'Content-Type': 'application/json' } }));
}
async function pinned() {
  if (!pinnedMemo) pinnedMemo = await readMeta(PIN_KEY);
  return pinnedMemo;
}
async function pin(v) {
  await writeMeta(PIN_KEY, v);
  pinnedMemo = v;
}
async function complete(v) {                 // every shell file of version v is saved (never creates a cache)
  if (!v || !(await caches.has(cacheName(v)))) return false;
  const cache = await caches.open(cacheName(v));
  for (const path of SHELL) if (!(await cache.match(path))) return false;
  return true;
}
async function versions() {                  // install order, oldest first, only ones fully saved
  const out = [];
  for (const v of (await readMeta(LIST_KEY)) || []) if (await complete(v)) out.push(v);
  return out;
}

// Safari rejects redirected responses for navigations (Cloudflare/GitHub may redirect index.html).
async function clean(res) {
  if (!res.redirected) return res;
  return new Response(await res.blob(), { status: res.status, statusText: res.statusText, headers: res.headers });
}

self.addEventListener('install', event => event.waitUntil((async () => {
  const name = cacheName(VERSION);
  // Versions are immutable: a complete copy (sw.js re-installed without a VERSION bump) is kept as is.
  if (!(await complete(VERSION))) {
    const live = (await caches.has(name)) && ((await readMeta(LIST_KEY)) || []).includes(VERSION);
    const cache = await caches.open(name);
    try {
      for (const path of SHELL) {
        const res = await fetch(new Request(path, { cache: 'reload' }));
        if (!res.ok) throw new Error(`${path}: HTTP ${res.status}`);
        await cache.put(path, await clean(res));
      }
    } catch (err) {
      if (!live) await caches.delete(name);   // never leave a half-filled version behind (nor delete a live one)
      throw err;
    }
  }
  const list = ((await readMeta(LIST_KEY)) || []).filter(v => v !== VERSION);
  await writeMeta(LIST_KEY, [...list, VERSION]);
  if (!(await complete(await pinned()))) await pin(VERSION);  // first install, or the pinned copy is gone
  await self.skipWaiting();
})()));

// Keep the pinned version, the latest, and (when those are the same) the one before it for Roll back.
// Only versions in LIST_KEY (fully installed) are ever deleted: a newer version still installing is not
// listed yet, and an older worker never deletes a newer one (it may still be waiting to activate).
async function prune() {
  const pin = await pinned(), list = (await readMeta(LIST_KEY)) || [], mine = list.indexOf(VERSION);
  if (mine < 0) return;                       // a newer worker already pruned us: not ours to do
  const keep = new Set([pin, VERSION, ...list.slice(mine + 1)]);
  if (pin === VERSION || !pin) {
    const i = list.indexOf(pin || VERSION);
    if (i > 0) keep.add(list[i - 1]);
  }
  for (const v of list) if (!keep.has(v)) await caches.delete(cacheName(v));
  await writeMeta(LIST_KEY, list.filter(v => keep.has(v)));
}

self.addEventListener('activate', event => event.waitUntil((async () => {
  await prune();
  await self.clients.claim();
})()));

self.addEventListener('fetch', event => {
  const req = event.request;
  if (req.method !== 'GET') return;
  const url = new URL(req.url), scope = new URL(self.registration.scope);
  // Outside the app folder (e.g. /download/team-pack on the review server): not ours.
  if (url.origin !== scope.origin || !url.pathname.startsWith(scope.pathname)) return;
  event.respondWith((async () => {
    const version = (await pinned()) || VERSION;
    const key = req.mode === 'navigate' ? scope.href : url.origin + url.pathname;   // navigations -> './'
    const hit = await caches.match(key, { cacheName: cacheName(version) });
    if (hit) return hit;
    try {
      return await clean(await fetch(req));   // only if the pinned cache lacks it
    } catch (err) {                           // offline and the pinned cache was evicted: better than a blank page
      const any = await caches.match(key, { cacheName: cacheName(VERSION) });
      if (any) return any;
      throw err;
    }
  })());
});

self.addEventListener('message', event => {
  const type = event.data && event.data.type;
  const reply = msg => (event.ports[0] ? event.ports[0].postMessage(msg) : event.source && event.source.postMessage(msg));
  event.waitUntil((async () => {
    try {
      if (type === 'pin-latest') {
        if (!(await complete(VERSION))) throw new Error('That version is not fully saved on this phone. Check for update again (on Wi-Fi).');
        await pin(VERSION);
        await prune();
      } else if (type === 'rollback') {
        const list = await versions(), i = list.indexOf(await pinned());
        if (i < 1) throw new Error('No earlier version is saved on this phone.');   // versions() = complete only
        await pin(list[i - 1]);
      } else if (type !== 'status') {
        return;
      }
      // offline: the version this phone runs is fully saved, so a cold launch works in Airplane Mode.
      const cur = await pinned();
      reply({ ok: true, pinned: cur, latest: VERSION, versions: await versions(), offline: await complete(cur) });
    } catch (err) {
      reply({ ok: false, error: String((err && err.message) || err) });
    }
  })());
});
