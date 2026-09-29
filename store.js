/* IndexedDB storage for the team pack. Only this phone ever sees it; nothing is uploaded.
   packs: {id, meta, importedAt, files: {path: {bytes: ArrayBuffer, type}}}   (one record per import)
   kv:    'current' -> {id, meta, importedAt}   (small, so launching never reads the audio)
   An import writes a NEW pack record, then flips 'current', then deletes the old record, so a
   half-written pack is never current. */
const Store = (() => {
  'use strict';
  const NAME = 'walkup', VERSION = 1, TIMEOUT_MS = 10000;
  let dbp = null;

  function withTimeout(p, ms, what) {
    let t;
    return Promise.race([p, new Promise((_, rej) => {
      t = setTimeout(() => rej(new Error(`Phone storage did not answer (${what}). Reload the app.`)), ms);
    })]).finally(() => clearTimeout(t));
  }

  function open() {
    if (!dbp) {
      dbp = withTimeout(new Promise((resolve, reject) => {
        const req = indexedDB.open(NAME, VERSION);
        req.onupgradeneeded = () => {
          const db = req.result;
          if (!db.objectStoreNames.contains('packs')) db.createObjectStore('packs', { keyPath: 'id' });
          if (!db.objectStoreNames.contains('kv')) db.createObjectStore('kv');
        };
        req.onsuccess = () => {
          const db = req.result;
          db.onversionchange = () => { db.close(); dbp = null; };
          db.onclose = () => { dbp = null; };          // e.g. after long backgrounding: reopen next time
          resolve(db);
        };
        req.onerror = () => reject(req.error || new Error('Could not open phone storage.'));
        req.onblocked = () => reject(new Error('Storage is busy. Close other copies of this app and reload.'));
      }), TIMEOUT_MS, 'open');
      dbp.catch(() => { dbp = null; });
    }
    return dbp;
  }

  // Run fn(stores) in one transaction; resolves with the last request's result once it COMMITS.
  function run(names, mode, fn, retry = true) {
    return open().then(db => withTimeout(new Promise((resolve, reject) => {
      const tx = db.transaction(names, mode), stores = {};
      for (const n of names) stores[n] = tx.objectStore(n);
      let result;
      const req = fn(stores);
      if (req) req.onsuccess = () => { result = req.result; };
      tx.oncomplete = () => resolve(result);
      tx.onerror = tx.onabort = () => reject(nice(tx.error));
    }), TIMEOUT_MS, names.join('+'))).catch(err => {
      // A stale connection (Safari after long backgrounding) throws InvalidStateError: reopen once.
      if (retry && err && (err.name === 'InvalidStateError' || err.name === 'UnknownError')) {
        dbp = null;
        return run(names, mode, fn, false);
      }
      throw err;
    });
  }

  function nice(err) {
    if (err && err.name === 'QuotaExceededError') return new Error('Not enough free storage on this phone for the team pack.');
    return err || new Error('Storage write failed.');
  }

  const current = () => run(['kv'], 'readonly', s => s.kv.get('current')).then(r => r || null);

  async function loadFiles(id) {
    const rec = await run(['packs'], 'readonly', s => s.packs.get(id));
    if (!rec || !rec.files) throw new Error('The team pack is missing from storage. Import it again.');
    return rec.files;
  }

  // Delete every pack record except keepId (old packs, or one left by an import that died mid-way).
  async function prune(keepId) {
    const ids = await run(['packs'], 'readonly', s => s.packs.getAllKeys());
    for (const id of ids || []) if (id !== keepId) await run(['packs'], 'readwrite', s => s.packs.delete(id));
  }

  async function replacePack(meta, files) {
    const importedAt = Date.now();
    const id = 'pack-' + importedAt.toString(36) + '-' + Math.random().toString(36).slice(2, 7);
    await run(['packs'], 'readwrite', s => s.packs.put({ id, meta, files, importedAt }));   // 1. new record
    const cur = { id, meta, importedAt };
    await run(['kv'], 'readwrite', s => s.kv.put(cur, 'current'));                        // 2. flip pointer
    await prune(id).catch(() => {});                                                      // 3. drop old
    return cur;
  }

  return { current, loadFiles, replacePack, prune };
})();
