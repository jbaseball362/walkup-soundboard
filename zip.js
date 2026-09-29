/* Reader for STORED (uncompressed) zip files such as the team pack written by walkup.py.
   readZip(bytes) -> {name: Uint8Array}. The arrays are views into `bytes` (no copy); use
   .slice() when one needs its own ArrayBuffer. Every entry's CRC-32 is checked, so a truncated
   or damaged download fails here with a clear message instead of later at the game.
   Loads as a plain <script> (window.WalkupZip) or with require() in Node for tests. */
(function (root) {
  'use strict';

  const EOCD = 0x06054b50, Z64_LOCATOR = 0x07064b50, Z64_EOCD = 0x06064b50,
        CENTRAL = 0x02014b50, LOCAL = 0x04034b50, MAX32 = 0xffffffff;

  let table = null;
  function crc32(u8) {
    if (!table) {
      table = new Uint32Array(256);
      for (let n = 0; n < 256; n++) {
        let c = n;
        for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
        table[n] = c >>> 0;
      }
    }
    let c = MAX32;
    for (let i = 0; i < u8.length; i++) c = table[(c ^ u8[i]) & 0xff] ^ (c >>> 8);
    return (c ^ MAX32) >>> 0;
  }

  function fail(msg) { throw new Error(msg); }

  function readZip(input) {
    const u8 = input instanceof Uint8Array ? input : new Uint8Array(input);
    const dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
    const u16 = o => dv.getUint16(o, true), u32 = o => dv.getUint32(o, true);
    const u64 = o => u32(o) + u32(o + 4) * 0x100000000;   // exact below 2^53, plenty here
    const damaged = 'The file is damaged or incomplete. Download the team pack again.';

    // End-of-central-directory record: the last 22 bytes, plus a comment of up to 64 KiB.
    let eocd = -1;
    for (let i = u8.length - 22; i >= 0 && i >= u8.length - 22 - 0xffff; i--) {
      if (u32(i) === EOCD) { eocd = i; break; }
    }
    if (eocd < 0) fail('This is not a zip file (or it was cut short). Download the team pack again.');
    let count = u16(eocd + 10), cdSize = u32(eocd + 12), cdOff = u32(eocd + 16);
    if (count === 0xffff || cdSize === MAX32 || cdOff === MAX32) {   // ZIP64 directory
      const loc = eocd - 20;
      if (loc < 0 || u32(loc) !== Z64_LOCATOR) fail(damaged);
      const z = u64(loc + 8);
      if (z + 56 > u8.length || u32(z) !== Z64_EOCD) fail(damaged);
      count = u64(z + 32); cdSize = u64(z + 40); cdOff = u64(z + 48);
    }
    if (cdOff + cdSize > u8.length) fail(damaged);

    const names = new TextDecoder('utf-8');
    const out = Object.create(null);    // no prototype: an entry named "__proto__" stays an entry
    let p = cdOff;
    for (let n = 0; n < count; n++) {
      if (p + 46 > u8.length || u32(p) !== CENTRAL) fail(damaged);
      const flags = u16(p + 8), method = u16(p + 10), crc = u32(p + 16);
      let size = u32(p + 20), usize = u32(p + 24), off = u32(p + 42);
      const nlen = u16(p + 28), xlen = u16(p + 30), clen = u16(p + 32);
      const name = names.decode(u8.subarray(p + 46, p + 46 + nlen));
      // A ZIP64 extra field (id 1) holds, in this order, the values that are 0xffffffff above.
      for (let x = p + 46 + nlen, end = x + xlen; x + 4 <= end; x += 4 + u16(x + 2)) {
        if (u16(x) !== 1) continue;
        let q = x + 4;
        if (usize === MAX32) { usize = u64(q); q += 8; }
        if (size === MAX32) { size = u64(q); q += 8; }
        if (off === MAX32) off = u64(q);
      }
      p += 46 + nlen + xlen + clen;
      if (name.endsWith('/')) continue;                     // folder entry, no data
      if (flags & 1) fail(`"${name}" is encrypted. Team packs are never encrypted; rebuild it with walkup.py.`);
      if (method !== 0) {
        fail(`"${name}" is compressed (method ${method}). Team packs must be stored without compression: ` +
             'use the .walkup file made by walkup.py, not a re-zipped copy.');
      }
      if (size !== usize) fail(damaged);
      // Sizes come from the central directory; the local header only tells us where the data starts.
      if (off + 30 > u8.length || u32(off) !== LOCAL) fail(damaged);
      const start = off + 30 + u16(off + 26) + u16(off + 28);
      if (start + size > u8.length) fail(damaged);
      const data = u8.subarray(start, start + size);
      if (crc32(data) !== crc) fail(`"${name}" is corrupt (checksum mismatch). Download the team pack again.`);
      if (name in out) fail(`The pack lists "${name}" twice.`);
      out[name] = data;
    }
    return out;
  }

  const api = { readZip, crc32 };
  if (typeof module === 'object' && module.exports) module.exports = api;
  else root.WalkupZip = api;
})(typeof self !== 'undefined' ? self : this);
