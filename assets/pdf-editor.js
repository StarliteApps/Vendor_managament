
/* ===================== STARLITE v14 · Split & Edit PDF =====================
   Satu editor di dalam aplikasi (tanpa pindah web, tanpa database baru):
   - Split: rentang / tiap N / per halaman / pilih visual, nama custom per file + pola nama, pasangan PO/BAP/SPK
   - Edit: susun, putar, hapus, gabung (PDF/JPG/PNG), hapus area permanen, teks lengkap, menggambar, undo/redo
   - Hasil: unduh / ZIP, Submit PDF massal, kembali ke form (Rapikan PDF), Signing Selesai → simpan hasil pecah ke Drive
   Diproses di browser (pdf.js + pdf-lib). Simpan ke Drive dibantu Supabase Storage (sementara). */
(function () {
  "use strict";
  if (typeof loadPdfLib !== "function" || typeof loadPdfJs !== "function") return;
  var $ = function (x) { return document.getElementById(x); };
  var E = function (t) { return String(t == null ? "" : t).replace(/[&<>"']/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]; }); };
  var toast = function (m, t, ms) { try { showToast(m, t || "info", ms); } catch (e) { console.log(m); } };
  var emp = function (v) { return typeof isEmpty === "function" ? isEmpty(v) : !String(v || "").trim(); };
  var N = function (v) { return String(v == null ? "" : v).toUpperCase().replace(/\s+/g, ""); };
  var loadJs = function (u) { return typeof loadScriptOnce === "function" ? loadScriptOnce(u) : new Promise(function (ok, no) { var s = document.createElement("script"); s.src = u; s.onload = ok; s.onerror = function () { no(new Error("Gagal memuat pustaka")); }; document.head.appendChild(s); }); };
  var MAX_MB = 50, MAX_PAGES = 300, DPI = 200;
  var COLORS = ["#4f46e5", "#e11d48", "#059669", "#d97706", "#0891b2", "#7c3aed", "#db2777", "#65a30d"];
  var PAL = ["#111827", "#dc2626", "#2563eb", "#16a34a", "#f59e0b", "#ffffff"];
  var FS = "https://cdn.jsdelivr.net/npm/@fontsource/", FSV = "5.1.1";
  var FONTS = [
    { k: "Helvetica", label: "Helvetica / Arial", css: "Helvetica, Arial, sans-serif", std: ["Helvetica", "HelveticaBold", "HelveticaOblique", "HelveticaBoldOblique"] },
    { k: "Times", label: "Times New Roman", css: '"Times New Roman", Times, serif', std: ["TimesRoman", "TimesRomanBold", "TimesRomanItalic", "TimesRomanBoldItalic"] },
    { k: "Courier", label: "Courier", css: '"Courier New", Courier, monospace', std: ["Courier", "CourierBold", "CourierOblique", "CourierBoldOblique"] },
    { k: "Roboto", label: "Roboto", fs: "roboto" },
    { k: "Open Sans", label: "Open Sans", fs: "open-sans" },
    { k: "Poppins", label: "Poppins", fs: "poppins" },
    { k: "Arimo", label: "Arimo (mirip Arial)", fs: "arimo" },
    { k: "Carlito", label: "Carlito (mirip Calibri)", fs: "carlito" },
    { k: "Dancing Script", label: "Dancing Script (tulisan tangan)", fs: "dancing-script", w4: 1 },
    { k: "Great Vibes", label: "Great Vibes (tanda tangan)", fs: "great-vibes", w4: 1 },
    { k: "Allura", label: "Allura (tanda tangan)", fs: "allura", w4: 1 }
  ];
  var fontOf = function (k) { return FONTS.filter(function (f) { return f.k === k; })[0] || FONTS[0]; };
  var fontCss = function (f) { return f.fs ? '"PE ' + f.k + '"' : f.css; };
  var fontUrl = function (f, b, i) { if (f.w4) b = i = false; return FS + f.fs + "@" + FSV + "/files/" + f.fs + "-latin-" + (b ? 700 : 400) + "-" + (i ? "italic" : "normal") + ".woff"; };
  var WF = {};
  function webFont(f, b, i) {
    if (!f.fs || typeof FontFace === "undefined") return Promise.resolve();
    var key = f.k + b + i;
    if (!WF[key]) WF[key] = new FontFace("PE " + f.k, "url(" + fontUrl(f, b, i) + ")", { weight: b ? "700" : "400", style: i ? "italic" : "normal" }).load().then(function (ff) { document.fonts.add(ff); }).catch(function () { });
    return WF[key];
  }
  var FB = {};
  function fontBytes(f, b, i) { var u = fontUrl(f, b, i); if (!FB[u]) FB[u] = fetch(u).then(function (r) { if (!r.ok) throw new Error("Font gagal dimuat"); return r.arrayBuffer(); }).catch(function (e) { delete FB[u]; throw e; }); return FB[u]; }

  // ---------- hak akses ----------
  try {
    if (typeof PERMS !== "undefined" && !PERMS.some(function (p) { return p.key === "pdf"; })) PERMS.push({ key: "pdf", group: "Aksi", label: "Split & Edit PDF (tidak berlaku untuk Viewer)", icon: "fa-scissors" });
    if (typeof DEFAULT_ROLE_PERMS !== "undefined") { DEFAULT_ROLE_PERMS.operator.pdf = true; DEFAULT_ROLE_PERMS.viewer.pdf = false; }
  } catch (e) { }
  if (typeof can === "function") {
    var origCan = can;
    window.can = can = function (k) { if (k === "pdf" && currentUser && currentUser.role === "viewer") return false; return origCan.apply(this, arguments); };
  }
  var canPdf = function () { try { return !!currentUser && currentUser.role !== "viewer" && can("pdf"); } catch (e) { return false; } };
  window.peCan = canPdf;

  // ---------- state ----------
  var PE = { docs: [], pages: [], cuts: new Set(), names: {}, pairs: {}, sel: new Set(), undo: [], redo: [], origin: { kind: "tab" }, mode: "split", mfiles: [], mopt: { marks: true, flatten: true, a4: false, blank: false, inter: false, interRev: true, outName: "" }, lock: false, base: "Dokumen", pattern: "", uid: 0, mf: false, open: false, last: -1 };
  var THUMB = {}, JS = {}, LIB = {}, IMGS = {}, IMGN = 0;
  // ---------- gambar sisipan (stempel / TTD / foto) ----------
  function loadImgEl(url) { return new Promise(function (ok, no) { var im = new Image(); im.onload = function () { ok(im); }; im.onerror = function () { no(new Error("Gambar tidak bisa dibaca")); }; im.src = url; }); }
  async function regImage(bytes, mime, fixedId) {
    var url = URL.createObjectURL(new Blob([bytes], { type: mime })), el = await loadImgEl(url), id = fixedId || "i" + (++IMGN);
    IMGS[id] = { bytes: bytes, mime: mime, url: url, el: el, w: el.naturalWidth, h: el.naturalHeight };
    return id;
  }
  async function fileToImage(file) {
    var bytes = await readBuf(file), type = /png/i.test(file.type) || /\.png$/i.test(file.name) ? "image/png" : /jpe?g/i.test(file.type) || /\.jpe?g$/i.test(file.name) ? "image/jpeg" : "";
    if (type) { try { return await regImage(bytes, type); } catch (e) { } }
    var url = URL.createObjectURL(file), el = await loadImgEl(url);   // webp / gif / bmp → PNG
    var c = document.createElement("canvas"), sc = Math.min(1, 2400 / Math.max(el.naturalWidth, el.naturalHeight)); c.width = Math.round(el.naturalWidth * sc); c.height = Math.round(el.naturalHeight * sc);
    c.getContext("2d").drawImage(el, 0, 0, c.width, c.height); URL.revokeObjectURL(url);
    return regImage(await canvasPng(c), "image/png");
  }
  function canvasPng(c) { return new Promise(function (ok, no) { c.toBlob(function (b) { if (!b) return no(new Error("Gagal membuat gambar")); b.arrayBuffer().then(function (a) { ok(new Uint8Array(a)); }); }, "image/png"); }); }
  // hapus latar putih (hasil scan stempel / tanda tangan) → PNG transparan
  async function knockWhite(id) {
    var src = IMGS[id]; if (!src) return id; if (src.clean) return src.clean;
    var c = document.createElement("canvas"), sc = Math.min(1, 2400 / Math.max(src.w, src.h)); c.width = Math.round(src.w * sc); c.height = Math.round(src.h * sc);
    var g = c.getContext("2d"); g.drawImage(src.el, 0, 0, c.width, c.height);
    var d = g.getImageData(0, 0, c.width, c.height), a = d.data;
    for (var i = 0; i < a.length; i += 4) { var m = Math.min(a[i], a[i + 1], a[i + 2]), l = (a[i] + a[i + 1] + a[i + 2]) / 3; if (m > 232 && l > 238) a[i + 3] = 0; else if (l > 200 && m > 190) a[i + 3] = Math.round(a[i + 3] * (238 - l) / 38); }
    g.putImageData(d, 0, 0);
    var nid = await regImage(await canvasPng(c), "image/png"); src.clean = nid; IMGS[nid].orig = id; return nid;
  }
  var dims = function (p) { var t = (p.r0 + p.rot) % 360; return t % 180 ? { w: p.h, h: p.w, t: t } : { w: p.w, h: p.h, t: t }; };
  var clone = function (o) { return JSON.parse(JSON.stringify(o)); };
  var safeName = function (s) { return String(s || "").replace(/\.pdf$/i, "").replace(/[\\/:*?"<>|\u0000-\u001f]+/g, "-").replace(/\s+/g, " ").trim().slice(0, 150); };

  function snap() { return JSON.stringify({ p: PE.pages, c: Array.from(PE.cuts), n: PE.names, a: PE.pairs, m: PE.mfiles, o: PE.mopt, f: PE.form || {} }); }
  function restore(s) { var o = JSON.parse(s); PE.pages = o.p; PE.cuts = new Set(o.c); PE.names = o.n; PE.pairs = o.a; if (o.m) PE.mfiles = o.m; if (o.o) PE.mopt = o.o; PE.form = o.f || {}; PE.sel = new Set(Array.from(PE.sel).filter(function (id) { return PE.pages.some(function (p) { return p.id === id; }); })); }
  function pushUndo() { PE.undo.push(snap()); if (PE.undo.length > 60) PE.undo.shift(); PE.redo = []; syncUndo(); autosave(); }
  // ---------- simpan otomatis di perangkat (IndexedDB) — pekerjaan tidak hilang bila tab tertutup ----------
  var DBP = null, SAVED = { docs: -1, imgs: -1 }, SAVE_T = null, DRAFT_DAYS = 7;
  function idb() { if (!DBP) DBP = new Promise(function (ok, no) { var r = indexedDB.open("starlite-pe", 1); r.onupgradeneeded = function () { r.result.createObjectStore("kv"); }; r.onsuccess = function () { ok(r.result); }; r.onerror = function () { DBP = null; no(r.error); }; }); return DBP; }
  function kv(mode, k, v) { return idb().then(function (db) { return new Promise(function (ok, no) { var t = db.transaction("kv", mode === "get" ? "readonly" : "readwrite"), st = t.objectStore("kv"), rq = mode === "get" ? st.get(k) : mode === "del" ? st.delete(k) : st.put(v, k); t.oncomplete = function () { ok(rq.result); }; t.onerror = function () { no(t.error); }; t.onabort = function () { no(t.error); }; }); }); }
  function autosave() { if (!PE.open || !window.indexedDB) return; clearTimeout(SAVE_T); SAVE_T = setTimeout(saveDraft, 1500); }
  async function saveDraft() {
    if (!PE.open || !PE.pages.length) return;
    try {
      if (SAVED.docs !== PE.docs.length) { await kv("put", "docs", PE.docs.map(function (d) { return { name: d.name, bytes: d.bytes }; })); SAVED.docs = PE.docs.length; }
      var ik = Object.keys(IMGS);
      if (SAVED.imgs !== ik.length) { var o = {}; ik.forEach(function (k) { var m = IMGS[k]; o[k] = { bytes: m.bytes, mime: m.mime, orig: m.orig || "", clean: m.clean || "" }; }); await kv("put", "imgs", o); SAVED.imgs = ik.length; }
      if (SAVED.ocr !== Object.keys(OCR).length) { await kv("put", "ocr", OCR); SAVED.ocr = Object.keys(OCR).length; }
      await kv("put", "draft", { at: Date.now(), mode: PE.mode, base: PE.base, origin: PE.origin, lock: PE.lock, pattern: PE.pattern, state: snap(), uid: PE.uid, imgn: IMGN, title: ($("pe-ttl") || {}).textContent || "", n: PE.pages.length, files: segs().length });
      var b = $("pe-saved"); if (b) { b.classList.remove("hidden"); b.classList.remove("flash"); void b.offsetWidth; b.classList.add("flash"); }
    } catch (e) { console.warn("Simpan otomatis gagal:", e && e.message); }
  }
  async function clearDraft() { clearTimeout(SAVE_T); SAVED = { docs: -1, imgs: -1 }; try { await kv("del", "draft"); await kv("del", "docs"); await kv("del", "imgs"); await kv("del", "ocr"); } catch (e) { } }
  async function getDraft() { try { var d = await kv("get", "draft"); if (d && Date.now() - d.at < DRAFT_DAYS * 864e5) return d; if (d) clearDraft(); } catch (e) { } return null; }
  async function restoreDraft(d) {
    busy("Memulihkan pekerjaan terakhir…", 15, "read");
    try {
      var docs = await kv("get", "docs") || [], imgs = await kv("get", "imgs") || {}, ocr = await kv("get", "ocr") || {};
      reset(); OCR = ocr;
      PE.docs = docs.map(function (x) { return { bytes: x.bytes, name: x.name }; });
      var ids = Object.keys(imgs);
      for (var i = 0; i < ids.length; i++) { var m = imgs[ids[i]]; try { await regImage(m.bytes, m.mime, ids[i]); IMGS[ids[i]].orig = m.orig || undefined; IMGS[ids[i]].clean = m.clean || undefined; } catch (e) { } busy("Memulihkan gambar…", 20 + 30 * (i + 1) / ids.length, "read"); }
      restore(d.state); PE.mode = /^(edit|merge|conv)$/.test(d.mode) ? d.mode : "split"; PE.base = d.base; PE.origin = d.origin || { kind: "tab" }; PE.lock = !!d.lock; PE.pattern = d.pattern || ""; PE.uid = d.uid || PE.uid; IMGN = Math.max(IMGN, d.imgn || 0);
      $("pe-ttl").textContent = d.title || "Split & Edit PDF";
      SAVED = { docs: PE.docs.length, imgs: ids.length }; SEEN = new Set();
      busy(null); render(); toast("Pekerjaan terakhir dipulihkan (" + d.n + " halaman)", "success");
    } catch (e) { busy(null); toast("Gagal memulihkan: " + e.message, "error"); }
  }
  function undo() { if (!PE.undo.length) return; PE.redo.push(snap()); restore(PE.undo.pop()); afterChange(); }
  function redo() { if (!PE.redo.length) return; PE.undo.push(snap()); restore(PE.redo.pop()); afterChange(); }
  function syncUndo() { ["pe-undo", "pe-ed-undo"].forEach(function (id) { var b = $(id); if (b) b.disabled = !PE.undo.length; }); ["pe-redo", "pe-ed-redo"].forEach(function (id) { var b = $(id); if (b) b.disabled = !PE.redo.length; }); }
  function afterChange() { syncUndo(); render(); if (ED.on) { var p = edPage(); if (!p) edClose(); else { ED.sel = null; ED.ms = []; edLoad(); } } }

  // ---------- dokumen sumber ----------
  function jsDoc(d) { if (!JS[d]) JS[d] = loadPdfJs().then(function (L) { return L.getDocument({ data: PE.docs[d].bytes.slice(0) }).promise; }); return JS[d]; }
  function libDoc(d) { if (!LIB[d]) LIB[d] = loadPdfLib().then(function (L) { return L.PDFDocument.load(PE.docs[d].bytes, { ignoreEncryption: true }); }); return LIB[d]; }
  var readBuf = function (f) { return new Promise(function (ok, no) { var r = new FileReader(); r.onload = function () { ok(new Uint8Array(r.result)); }; r.onerror = function () { no(r.error); }; r.readAsArrayBuffer(f); }); };

  async function imageToPdf(file) {
    var L = await loadPdfLib(), doc = await L.PDFDocument.create(), bytes = await readBuf(file), img;
    try {
      if (/jpe?g$/i.test(file.type) || /\.jpe?g$/i.test(file.name)) img = await doc.embedJpg(bytes);
      else if (/png$/i.test(file.type) || /\.png$/i.test(file.name)) img = await doc.embedPng(bytes);
    } catch (e) { img = null; }
    if (!img) {
      var url = URL.createObjectURL(file), im = await new Promise(function (ok, no) { var x = new Image(); x.onload = function () { ok(x); }; x.onerror = function () { no(new Error("Gambar tidak bisa dibaca")); }; x.src = url; });
      var c = document.createElement("canvas"); c.width = im.naturalWidth; c.height = im.naturalHeight; var g = c.getContext("2d"); g.fillStyle = "#fff"; g.fillRect(0, 0, c.width, c.height); g.drawImage(im, 0, 0); URL.revokeObjectURL(url);
      img = await doc.embedJpg(await canvasJpg(c, 0.9));
    }
    var land = img.width > img.height, W = land ? 842 : 595, H = W * img.height / img.width;
    doc.addPage([W, H]).drawImage(img, { x: 0, y: 0, width: W, height: H });
    return new Uint8Array(await doc.save());
  }
  function canvasJpg(c, q) { return new Promise(function (ok, no) { c.toBlob(function (b) { if (!b) return no(new Error("Gagal membuat gambar")); b.arrayBuffer().then(function (a) { ok(new Uint8Array(a)); }); }, "image/jpeg", q || 0.9); }); }

  async function addBytes(bytes, name) {
    var d = PE.docs.length;
    var hs = bytes.length; for (var hi = 0; hi < bytes.length; hi += 509) hs = (hs * 31 + bytes[hi]) | 0;
    PE.docs.push({ bytes: bytes, name: name, hash: bytes.length + ":" + hs });
    var doc;
    try { doc = await jsDoc(d); } catch (e) {
      PE.docs[d] = { bytes: new Uint8Array(0), name: name, bad: true }; delete JS[d];
      if (e && (e.name === "PasswordException" || /password/i.test(e.message || ""))) throw new Error("\"" + name + "\" dikunci password — buka kuncinya dulu (mis. cetak ulang ke PDF), lalu unggah lagi");
      throw new Error("\"" + name + "\" bukan PDF yang valid atau file rusak");
    }
    if (PE.pages.length + doc.numPages > MAX_PAGES) throw new Error("Maksimal " + MAX_PAGES + " halaman per sesi");
    var out = [];
    for (var i = 1; i <= doc.numPages; i++) {
      var pg = await doc.getPage(i), v = pg.view;
      out.push({ id: "p" + (++PE.uid), d: d, i: i - 1, r0: ((pg.rotate || 0) % 360 + 360) % 360, rot: 0, w: Math.abs(v[2] - v[0]), h: Math.abs(v[3] - v[1]), ops: [] });
    }
    return out;
  }

  // PDF terenkripsi: password pembuka → minta password; hanya kunci izin → dibuka otomatis agar bisa diedit
  async function prepBytes(bytes, name) {
    if (!hasEncrypt(bytes)) return bytes;
    var needPw = false;
    try { var Lj = await loadPdfJs(), t = await Lj.getDocument({ data: bytes.slice(0) }).promise; t.destroy(); } catch (e) { needPw = e && (e.name === "PasswordException" || /password/i.test(e.message || "")); if (!needPw) return bytes; }
    if (needPw) return unlockBytes(bytes, name);
    try { busy("Membuka kunci izin…", 30, "read"); return await qpdf(["--decrypt", "/in.pdf", "/out.pdf"], bytes); } catch (e) { console.warn("buka izin:", e.message); return bytes; }
  }
  async function addFiles(files, at) {
    files = Array.from(files || []).filter(Boolean);
    if (!files.length) return;
    var size = files.reduce(function (a, f) { return a + f.size; }, 0) + PE.docs.reduce(function (a, d) { return a + (d.bytes ? d.bytes.length : 0); }, 0);
    if (size > MAX_MB * 1048576) return toast("Total file maksimal " + MAX_MB + " MB", "error", 6000);
    busy("Menyiapkan file…", 5, "read");
    try {
      var first = !PE.pages.length, add = [];
      for (var k = 0; k < files.length; k++) {
        var f = files[k], isPdf = /pdf$/i.test(f.type) || /\.pdf$/i.test(f.name), isImg = /^image\//.test(f.type) || /\.(jpe?g|png|webp|gif|bmp)$/i.test(f.name);
        if (!isPdf && !isImg) { toast("\"" + f.name + "\" dilewati — hanya PDF / JPG / PNG", "error", 5000); continue; }
        busy("Membaca " + f.name + (files.length > 1 ? " (" + (k + 1) + "/" + files.length + ")" : "") + "…", 10 + 80 * k / files.length, "read");
        var bytes = isPdf ? await readBuf(f) : await imageToPdf(f);
        if (isPdf) { bytes = await prepBytes(bytes, f.name); if (!bytes) { toast("\"" + f.name + "\" dilewati", "info"); continue; } busy("Membaca " + f.name + "…", 10 + 80 * k / files.length, "read"); }
        var pages = await addBytes(bytes, f.name);
        add = add.concat(pages);
        if (first && k === 0) PE.base = safeName(f.name) || "Dokumen";
      }
      if (add.length) {
        pushUndo();
        var pos = at == null ? PE.pages.length : at;
        PE.pages.splice.apply(PE.pages, [pos, 0].concat(add));
        if (ED.on && at != null) toast(add.length + " halaman disisipkan setelah halaman " + at, "success");
      }
    } catch (e) { toast(e.message, "error", 7000); }
    busy(null); PE.insAt = null;
    render(); if (ED.on) { stripReset(); edStrip(); edLoad(); }
  }

  function hideDz() { var d = $("pe-dz"); if (d) d.classList.add("hidden"); }
  // ---------- render halaman (pdf.js) ----------
  async function renderBase(p, cssW, dpr) {
    var doc = await jsDoc(p.d), pg = await doc.getPage(p.i + 1), D = dims(p);
    var vp = pg.getViewport({ scale: cssW / D.w * (dpr || 1), rotation: D.t });
    var c = document.createElement("canvas"); c.width = Math.max(1, Math.round(vp.width)); c.height = Math.max(1, Math.round(vp.height));
    var g = c.getContext("2d"); g.fillStyle = "#fff"; g.fillRect(0, 0, c.width, c.height);
    await pg.render({ canvasContext: g, viewport: vp }).promise;
    return c;
  }
  var TQ = [], TBUSY = 0, SEEN = new Set();
  var IO = typeof IntersectionObserver !== "undefined" ? new IntersectionObserver(function (es) { es.forEach(function (en) { if (en.isIntersecting && en.target.__p) { IO.unobserve(en.target); thumb(en.target.__p, en.target); } }); }, { rootMargin: "600px 0px" }) : null;
  function thumbKey(p) { return p.d + ":" + p.i + ":" + dims(p).t + ":" + (p.ops.length ? JSON.stringify(p.ops).length + ":" + hashStr(JSON.stringify(p.ops)) : 0); }
  function hashStr(s) { var h = 0; for (var i = 0; i < s.length; i++) h = (h * 31 + s.charCodeAt(i)) | 0; return h; }
  function thumb(p, img) {
    var k = thumbKey(p);
    if (THUMB[k]) { img.src = THUMB[k]; return; }
    TQ.push({ p: p, img: img, k: k }); pumpThumbs();
  }
  function pumpThumbs() {
    while (TBUSY < 2 && TQ.length) {
      var job = TQ.shift();
      if (THUMB[job.k]) { job.img.src = THUMB[job.k]; continue; }
      if (!job.img.isConnected) continue;
      TBUSY++;
      (async function (j) {
        try {
          var c = await renderBase(j.p, 150, 1.6);
          if (j.p.ops.length) drawOps(c.getContext("2d"), j.p.ops, c.width / dims(j.p).w);
          THUMB[j.k] = c.toDataURL("image/jpeg", 0.8);
        } catch (e) { THUMB[j.k] = ""; }
        if (j.img.isConnected) j.img.src = THUMB[j.k];
        TBUSY--; pumpThumbs();
      })(job);
    }
  }

  // ---------- teks ----------
  var MC = document.createElement("canvas").getContext("2d");
  function cssFont(o, scale) { var f = fontOf(o.font); return (o.i ? "italic " : "") + (o.b ? "700 " : "400 ") + (o.size * (scale || 1)) + "px " + fontCss(f); }
  function wrap(text, maxW, measure) {
    var out = [];
    String(text || "").split("\n").forEach(function (para) {
      var tokens = para.match(/\S+|\s+/g) || [""], line = "";
      tokens.forEach(function (tk) {
        var cand = line + tk;
        if (measure(cand.replace(/\s+$/, "")) <= maxW) { line = cand; return; }
        if (/^\s+$/.test(tk)) { out.push(line.replace(/\s+$/, "")); line = ""; return; }
        if (line.trim()) { out.push(line.replace(/\s+$/, "")); line = ""; }
        if (measure(tk) <= maxW) { line = tk; return; }
        var cur = "";
        Array.from(tk).forEach(function (ch) { if (cur && measure(cur + ch) > maxW) { out.push(cur); cur = ch; } else cur += ch; });
        line = cur;
      });
      out.push(line.replace(/\s+$/, ""));
    });
    return out;
  }
  function textLines(o) { MC.font = cssFont(o, 1); return wrap(o.text, Math.max(4, o.w - 4), function (s) { return MC.measureText(s).width; }); }
  var LH = 1.25, PAD = 2;
  function textH(o, lines) { return Math.max(1, (lines || textLines(o)).length) * o.size * LH + PAD * 2; }
  var baseY = function (o, k) { return PAD + k * o.size * LH + o.size * 0.82 + (o.size * LH - o.size) / 2; };

  // ---------- gambar objek ke canvas (pratinjau, gambar mini, raster) ----------
  function hexA(h, a) { h = String(h || "#000").replace("#", ""); if (h.length === 3) h = h.replace(/./g, "$&$&"); var n = parseInt(h, 16); return "rgba(" + (n >> 16 & 255) + "," + (n >> 8 & 255) + "," + (n & 255) + "," + (a == null ? 1 : a) + ")"; }
  function drawOps(g, ops, k, opt) {
    ops.forEach(function (o) {
      if (opt && opt.skipErase && o.t === "erase") return;
      if (opt && opt.onlyErase && o.t !== "erase") return;
      if (opt && opt.hide === o) return;
      g.save(); g.scale(k, k);
      var al = o.op == null ? 1 : o.op;
      if (o.t === "erase" || o.t === "mask") { g.fillStyle = o.col || "#fff"; g.fillRect(o.x, o.y, o.w, o.h); }
      else if (o.t === "note") {
        var nx = o.x, ny = o.y, nw = o.w, nh = o.h, f = nw * 0.3;
        g.shadowColor = "rgba(0,0,0,.25)"; g.shadowBlur = 3; g.shadowOffsetY = 1;
        g.fillStyle = o.c || "#f59e0b"; g.beginPath(); g.moveTo(nx + 2, ny); g.lineTo(nx + nw - 2, ny); g.quadraticCurveTo(nx + nw, ny, nx + nw, ny + 2); g.lineTo(nx + nw, ny + nh - f); g.lineTo(nx + nw - f, ny + nh); g.lineTo(nx + 2, ny + nh); g.quadraticCurveTo(nx, ny + nh, nx, ny + nh - 2); g.lineTo(nx, ny + 2); g.quadraticCurveTo(nx, ny, nx + 2, ny); g.fill();
        g.shadowBlur = 0; g.shadowOffsetY = 0; g.fillStyle = "rgba(255,255,255,.85)"; for (var li = 0; li < 3; li++) g.fillRect(nx + nw * 0.2, ny + nh * (0.28 + li * 0.18), nw * (li === 2 ? 0.4 : 0.6), Math.max(0.8, nh * 0.07));
        g.fillStyle = "rgba(0,0,0,.18)"; g.beginPath(); g.moveTo(nx + nw, ny + nh - f); g.lineTo(nx + nw - f, ny + nh - f); g.lineTo(nx + nw - f, ny + nh); g.fill();
      }
      else if (o.t === "link") { if (opt && opt.ed) { g.fillStyle = "rgba(37,99,235,.08)"; g.fillRect(o.x, o.y, o.w, o.h); g.strokeStyle = "#2563eb"; g.lineWidth = 1.2 / k; g.setLineDash([4 / k, 3 / k]); g.strokeRect(o.x, o.y, o.w, o.h); g.setLineDash([]); g.font = "700 " + 10 / k + "px sans-serif"; g.fillStyle = "#2563eb"; g.fillText("🔗 " + (o.url ? o.url.replace(/^https?:\/\//, "").slice(0, 30) : "ke hal " + o.page), o.x + 3 / k, o.y - 3 / k); } }
      else if (o.t === "img") {
        var im = IMGS[o.ref];
        g.translate(o.x + o.w / 2, o.y + o.h / 2); g.rotate((o.a || 0) * Math.PI / 180); g.globalAlpha = al;
        if (im && im.el) g.drawImage(im.el, -o.w / 2, -o.h / 2, o.w, o.h); else { g.fillStyle = "#e2e8f0"; g.fillRect(-o.w / 2, -o.h / 2, o.w, o.h); }
      }
      else if (o.t === "text") {
        var lines = textLines(o), cx = o.x + o.w / 2, cy = o.y + o.h / 2;
        g.translate(cx, cy); g.rotate((o.a || 0) * Math.PI / 180); g.translate(-o.w / 2, -o.h / 2);
        if (o.bg) { g.fillStyle = hexA(o.bg, al); g.fillRect(0, 0, o.w, o.h); }
        g.font = cssFont(o, 1); g.fillStyle = hexA(o.c, al); g.textBaseline = "alphabetic";
        lines.forEach(function (ln, i) {
          var lw = g.measureText(ln).width, x = o.al === "c" ? (o.w - lw) / 2 : o.al === "r" ? o.w - PAD - lw : PAD, y = baseY(o, i);
          g.fillText(ln, x, y);
          if (o.u && ln) { g.fillRect(x, y + o.size * 0.12, lw, Math.max(0.5, o.size * 0.06)); }
        });
      } else {
        g.globalAlpha = al; g.strokeStyle = o.c; g.fillStyle = o.c; g.lineWidth = o.lw; g.lineCap = "round"; g.lineJoin = "round";
        if (o.t === "hl") g.globalCompositeOperation = "multiply";
        if (o.t === "pen" || o.t === "hl") { g.beginPath(); o.pts.forEach(function (q, i) { i ? g.lineTo(q[0], q[1]) : g.moveTo(q[0], q[1]); }); if (o.pts.length === 1) g.lineTo(o.pts[0][0] + 0.1, o.pts[0][1]); g.stroke(); }
        else if (o.t === "line" || o.t === "arrow") {
          g.beginPath(); g.moveTo(o.x1, o.y1); g.lineTo(o.x2, o.y2); g.stroke();
          if (o.t === "arrow") { var hd = arrowHead(o); g.beginPath(); g.moveTo(hd[0][0], hd[0][1]); g.lineTo(hd[1][0], hd[1][1]); g.lineTo(hd[2][0], hd[2][1]); g.closePath(); g.fill(); }
        }
        else if (o.t === "rect") g.strokeRect(o.x, o.y, o.w, o.h);
        else if (o.t === "ellipse") { g.beginPath(); g.ellipse(o.x + o.w / 2, o.y + o.h / 2, Math.abs(o.w / 2), Math.abs(o.h / 2), 0, 0, Math.PI * 2); g.stroke(); }
        else if (o.t === "check") { var c = checkPts(o); g.lineWidth = o.w * 0.14; g.beginPath(); g.moveTo(c[0][0], c[0][1]); g.lineTo(c[1][0], c[1][1]); g.lineTo(c[2][0], c[2][1]); g.stroke(); }
      }
      g.restore();
    });
  }
  function arrowHead(o) {
    var L = Math.max(8, o.lw * 4), a = Math.atan2(o.y2 - o.y1, o.x2 - o.x1), s = 0.45;
    return [[o.x2, o.y2], [o.x2 - L * Math.cos(a - s), o.y2 - L * Math.sin(a - s)], [o.x2 - L * Math.cos(a + s), o.y2 - L * Math.sin(a + s)]];
  }
  var checkPts = function (o) { return [[o.x + o.w * 0.08, o.y + o.w * 0.55], [o.x + o.w * 0.4, o.y + o.w * 0.86], [o.x + o.w * 0.94, o.y + o.w * 0.12]]; };

  // ---------- susun PDF hasil ----------
  async function rasterErase(p, dpi, q) {
    var D = dims(p), sc = Math.min((dpi || DPI) / 72, 3200 / Math.max(D.w, D.h));
    var c = await renderBase(p, D.w * sc, 1);
    drawOps(c.getContext("2d"), p.ops, c.width / D.w, { onlyErase: true });
    var b = await canvasJpg(c, q || 0.9); c.width = c.height = 0; return b;
  }
  var tick = function () { return new Promise(function (r) { setTimeout(r, 0); }); };
  var hasErase = function (list) { return list.some(function (p) { return p.ops.some(function (o) { return o.t === "erase"; }); }); };
  var MB = function (n) { return n < 1048576 ? Math.max(1, Math.round(n / 1024)) + " KB" : (n / 1048576).toFixed(1).replace(".", ",") + " MB"; };
  // susun PDF; bila melebihi batas & ada halaman "hapus area" → susun ulang dengan kualitas hemat
  async function buildSized(list, title, limitMB, onp) {
    var b = await buildPdf(list, title, onp);
    if (limitMB && b.length > limitMB * 1048576 && hasErase(list)) b = await buildPdf(list, title, onp, { dpi: 130, q: 0.72 });
    if (limitMB && b.length > limitMB * 1048576 && (PE.comp || 0) < 2) { var b2 = await buildPdf(list, title, onp, { comp: 2 }); if (b2.length < b.length) b = b2; }   // terlalu besar → kompres otomatis
    if (limitMB && b.length > limitMB * 1048576) throw new Error("Ukuran " + MB(b.length) + " melebihi batas " + limitMB + " MB — pecah menjadi file yang lebih kecil");
    return b;
  }
  function rgbOf(L, h) { h = String(h || "#000").replace("#", ""); if (h.length === 3) h = h.replace(/./g, "$&$&"); var n = parseInt(h, 16); return L.rgb((n >> 16 & 255) / 255, (n >> 8 & 255) / 255, (n & 255) / 255); }
  async function pdfFont(L, out, cache, o) {
    var f = fontOf(o.font), b = !!o.b, it = !!o.i, key = f.k + b + it;
    if (!cache[key]) {
      if (f.std) cache[key] = await out.embedFont(L.StandardFonts[f.std[(b ? 1 : 0) + (it ? 2 : 0)]]);
      else {
        if (!cache._fk) { await loadJs("https://cdn.jsdelivr.net/npm/@pdf-lib/fontkit@1.1.1/dist/fontkit.umd.min.js"); out.registerFontkit(window.fontkit); cache._fk = 1; }
        cache[key] = await out.embedFont(await fontBytes(f, b, it), { subset: true });
      }
    }
    return cache[key];
  }
  function stdSafe(font, s, isStd) {
    if (!isStd) return s;
    var set = font.__cs || (font.__cs = new Set(font.getCharacterSet ? font.getCharacterSet() : []));
    var map = { "‘": "'", "’": "'", "“": '"', "”": '"', "–": "-", "—": "-", "…": "...", " ": " " };
    return Array.from(s).map(function (ch) { if (set.size && set.has(ch.codePointAt(0))) return ch; if (map[ch]) return map[ch]; return set.size ? "?" : ch; }).join("");
  }
  async function drawOpPdf(L, out, page, o, Dh, cache) {
    var al = o.op == null ? 1 : o.op, y = function (v) { return Dh - v; };
    if (o.t === "text") {
      if (!String(o.text || "").trim() && !o.bg) return;
      var font = await pdfFont(L, out, cache, o), isStd = !!fontOf(o.font).std;
      var lines = textLines(o), a = (o.a || 0) * Math.PI / 180, cs = Math.cos(a), sn = Math.sin(a), cx = o.x + o.w / 2, cy = o.y + o.h / 2;
      var tp = function (u, v) { var dx = u - o.w / 2, dy = v - o.h / 2; return [cx + dx * cs - dy * sn, cy + dx * sn + dy * cs]; };
      var rot = L.degrees(-(o.a || 0));
      if (o.bg) { var bl = tp(0, o.h); page.drawRectangle({ x: bl[0], y: y(bl[1]), width: o.w, height: o.h, color: rgbOf(L, o.bg), opacity: al, rotate: rot }); }
      lines.forEach(function (ln, i) {
        var t = stdSafe(font, ln, isStd); if (!t) return;
        var lw = font.widthOfTextAtSize(t, o.size), u = o.al === "c" ? (o.w - lw) / 2 : o.al === "r" ? o.w - PAD - lw : PAD, v = baseY(o, i), p0 = tp(u, v);
        page.drawText(t, { x: p0[0], y: y(p0[1]), size: o.size, font: font, color: rgbOf(L, o.c), opacity: al, rotate: rot });
        if (o.u) { var th = Math.max(0.5, o.size * 0.06), q = tp(u, v + o.size * 0.12 + th); page.drawRectangle({ x: q[0], y: y(q[1]), width: lw, height: th, color: rgbOf(L, o.c), opacity: al, rotate: rot }); }
      });
      return;
    }
    if (o.t === "mask") { page.drawRectangle({ x: o.x, y: y(o.y + o.h), width: o.w, height: o.h, color: rgbOf(L, o.col || "#ffffff") }); return; }
    if (o.t === "img") {
      var im = IMGS[o.ref]; if (!im) return;
      cache.imgs = cache.imgs || {};
      if (!cache.imgs[o.ref]) cache.imgs[o.ref] = im.mime === "image/png" ? await out.embedPng(im.bytes) : await out.embedJpg(im.bytes);
      var ia = (o.a || 0) * Math.PI / 180, ic = Math.cos(ia), is = Math.sin(ia), icx = o.x + o.w / 2, icy = o.y + o.h / 2, ibl = [icx + (-o.w / 2) * ic - (o.h / 2) * is, icy + (-o.w / 2) * is + (o.h / 2) * ic];
      page.drawImage(cache.imgs[o.ref], { x: ibl[0], y: y(ibl[1]), width: o.w, height: o.h, opacity: al, rotate: L.degrees(-(o.a || 0)) });
      return;
    }
    var col = rgbOf(L, o.c), common = { borderColor: col, borderWidth: o.lw, borderOpacity: al };
    if (L.LineCapStyle) common.borderLineCap = L.LineCapStyle.Round;
    if (o.t === "hl" && L.BlendMode) common.blendMode = L.BlendMode.Multiply;
    var path = function (pts) { return pts.map(function (q, i) { return (i ? "L" : "M") + q[0].toFixed(2) + " " + q[1].toFixed(2); }).join(" "); };
    if (o.t === "pen" || o.t === "hl") { var pts = o.pts.length === 1 ? [o.pts[0], [o.pts[0][0] + 0.1, o.pts[0][1]]] : o.pts; page.drawSvgPath(path(pts), Object.assign({ x: 0, y: Dh }, common)); }
    else if (o.t === "line" || o.t === "arrow") {
      page.drawSvgPath(path([[o.x1, o.y1], [o.x2, o.y2]]), Object.assign({ x: 0, y: Dh }, common));
      if (o.t === "arrow") page.drawSvgPath(path(arrowHead(o)) + " Z", { x: 0, y: Dh, color: col, opacity: al });
    }
    else if (o.t === "rect") page.drawRectangle({ x: Math.min(o.x, o.x + o.w), y: y(Math.max(o.y, o.y + o.h)), width: Math.abs(o.w), height: Math.abs(o.h), borderColor: col, borderWidth: o.lw, borderOpacity: al });
    else if (o.t === "ellipse") page.drawEllipse({ x: o.x + o.w / 2, y: y(o.y + o.h / 2), xScale: Math.abs(o.w / 2), yScale: Math.abs(o.h / 2), borderColor: col, borderWidth: o.lw, borderOpacity: al });
    else if (o.t === "check") page.drawSvgPath(path(checkPts(o)), Object.assign({ x: 0, y: Dh }, common, { borderWidth: o.w * 0.14 }));
  }
  var LIBF = {};
  function libFlat(d) { if (!LIBF[d]) LIBF[d] = loadPdfLib().then(async function (L) { var doc = await L.PDFDocument.load(PE.docs[d].bytes, { ignoreEncryption: true }); try { var fm = doc.getForm(); if (fm.getFields().length) { fm.updateFieldAppearances && fm.updateFieldAppearances(); fm.flatten(); } } catch (e) { console.warn("ratakan formulir:", e.message); } return doc; }); return LIBF[d]; }
  // sumber halaman untuk dirakit: formulir yang diisi → diterapkan & diratakan; opsi ratakan (Gabung)
  var LIBX = {};
  function getSrc(d, flat) {
    var fv = PE.form && PE.form[d], has = fv && Object.keys(fv).length;
    if (!has) return flat ? libFlat(d) : libDoc(d);
    var k = d + ":" + JSON.stringify(fv);
    if (!LIBX[k]) LIBX[k] = loadPdfLib().then(async function (L) {
      var doc = await L.PDFDocument.load(PE.docs[d].bytes, { ignoreEncryption: true }), fm = doc.getForm();
      Object.keys(fv).forEach(function (nm) {
        var v = fv[nm];
        try {
          var f = fm.getField(nm), T = f.constructor && f.constructor.name;
          if (f instanceof L.PDFTextField) { f.setText(String(v == null ? "" : v)); }
          else if (f instanceof L.PDFCheckBox) { v ? f.check() : f.uncheck(); }
          else if (f instanceof L.PDFRadioGroup) { if (v) f.select(String(v)); else f.clear(); }
          else if (f instanceof L.PDFDropdown) { if (v) f.select(String(v)); else f.clear(); }
          else if (f instanceof L.PDFOptionList) { if (v) f.select(String(v)); }
          void T;
        } catch (e) { console.warn("isi kolom " + nm + ":", e.message); }
      });
      try { fm.updateFieldAppearances(await doc.embedFont(L.StandardFonts.Helvetica)); } catch (e) { }
      try { fm.flatten(); } catch (e) { console.warn("ratakan:", e.message); }
      return doc;
    });
    return LIBX[k];
  }
  var hasFormVals = function (d) { var fv = PE.form && PE.form[d]; return !!(fv && Object.keys(fv).length); };
  // kata-kata dari satu baris (posisi tampilan) — untuk lapisan teks tak terlihat & sensor
  function wordsOf(l) {
    if (l.words) return l.words;
    var f = fontOf(l.mf.font); MC.font = (l.mf.i ? "italic " : "") + (l.mf.b ? "700 " : "400 ") + l.size + "px " + fontCss(f);
    var full = MC.measureText(l.str).width || 1, sc = l.w / full, out = [], re = /\S+/g, m;
    while ((m = re.exec(l.str))) { var a = MC.measureText(l.str.slice(0, m.index)).width * sc, b = MC.measureText(l.str.slice(0, m.index + m[0].length)).width * sc; out.push({ s: m[0], cs: m.index, x: l.x + a, w: Math.max(1, b - a), top: l.top, h: l.h, base: l.base }); }
    return out;
  }
  var ovl = function (a, b) { return Math.max(0, Math.min(a.x + a.w, b.x + b.w) - Math.max(a.x, b.x)) * Math.max(0, Math.min(a.y + a.h, b.y + b.h) - Math.max(a.y, b.y)); };
  // teks tak terlihat di atas halaman gambar (scan / disensor / dikompres) → PDF tetap bisa dicari & disalin; kata yang disensor TIDAK ikut
  async function drawInvisible(L, out, page, p, Dh, cache, lines) {
    if (!lines || !lines.length) return;
    var font = cache._hv || (cache._hv = await out.embedFont(L.StandardFonts.Helvetica));
    var er = p.ops.filter(function (o) { return o.t === "erase"; }), done = {}; p.ops.forEach(function (o) { if (o.key) done[o.key] = 1; });
    lines.forEach(function (l) {
      if (done[l.key]) return;
      wordsOf(l).forEach(function (w) {
        var wb = { x: w.x, y: w.top, w: w.w, h: w.h };
        if (er.some(function (e) { return ovl(e, wb) > wb.w * wb.h * 0.25; })) return;
        var t = stdSafe(font, w.s, true); if (!t.trim()) return;
        var fw = font.widthOfTextAtSize(t, 10) || 1, size = Math.max(1, Math.min(w.h * 1.6, 10 * w.w / fw));
        try { page.drawText(t, { x: w.x, y: Dh - w.base, size: size, font: font, opacity: 0 }); } catch (e) { }
      });
    });
  }
  // halaman berisi gambar (scan / foto) → kandidat dikompres
  var IMGQ = {};
  async function hasImage(p) {
    var k = pkey(p); if (IMGQ[k] != null) return IMGQ[k];
    try { var Lj = await loadPdfJs(), doc = await jsDoc(p.d), pg = await doc.getPage(p.i + 1), ol = await pg.getOperatorList(), O = Lj.OPS, I = [O.paintImageXObject, O.paintInlineImageXObject, O.paintJpegXObject, O.paintImageXObjectRepeat].filter(function (x) { return x != null; }); IMGQ[k] = ol.fnArray.some(function (f) { return I.indexOf(f) >= 0; }); } catch (e) { IMGQ[k] = false; }
    return IMGQ[k];
  }
  var COMP = { 1: { dpi: 150, q: 0.72, t: "Seimbang" }, 2: { dpi: 110, q: 0.55, t: "Maksimal" } };
  async function buildPdf(list, title, onp, opt) {
    opt = opt || {};
    if (!opt.raw && isMerge()) opt = Object.assign({ flatten: PE.mopt.flatten, a4: PE.mopt.a4, marks: list.__marks }, opt);
    var comp = opt.comp != null ? opt.comp : (opt.raw ? 0 : PE.comp || 0);
    if (comp && !opt.noCmp) {   // kompres: rakit 2 versi, pakai yang lebih kecil
      var c1 = await buildPdf(list, title, onp, Object.assign({}, opt, { comp: comp, noCmp: 1 }));
      var c0 = await buildPdf(list, title, null, Object.assign({}, opt, { comp: 0 }));
      LASTCMP = { before: c0.length, after: Math.min(c0.length, c1.length) };
      return c1.length < c0.length ? c1 : c0;
    }
    var flat = !!opt.flatten;
    var L = await loadPdfLib(), out = await L.PDFDocument.create(), cache = {}, plain = {}, copied = {}, links = [];
    var need = []; for (var z = 0; z < list.length; z++) { var pz = list[z]; need[z] = !pz.blank && (pz.ops.length || !!OCR[pkey(pz)] || (comp && await hasImage(pz))); }
    list.forEach(function (p, ix) { if (!p.blank && !need[ix]) (plain[p.d] = plain[p.d] || []).push(p.i); });
    for (var dk in plain) copied[dk] = await out.copyPages(await getSrc(+dk, flat || hasFormVals(+dk)), plain[dk]);
    var used = {};
    for (var n = 0; n < list.length; n++) {
      var p = list[n], D = dims(p);
      if (p.blank) { out.addPage([p.w, p.h]); if (onp) onp(n + 1, list.length); continue; }
      if (!need[n]) { var u = used[p.d] = (used[p.d] || 0); var cp = copied[p.d][u]; used[p.d] = u + 1; cp.setRotation(L.degrees(D.t)); out.addPage(cp); }
      else {
        var src = await getSrc(p.d, flat || hasFormVals(p.d)), np = out.addPage([D.w, D.h]);
        var raster = p.ops.some(function (o) { return o.t === "erase"; }) || (comp && await hasImage(p));
        if (raster) { var cq = COMP[comp] || {}; var img = await out.embedJpg(await rasterErase(p, cq.dpi || opt.dpi, cq.q || opt.q)); np.drawImage(img, { x: 0, y: 0, width: D.w, height: D.h }); }
        else {
          var sp = src.getPage(p.i), cb = sp.getCropBox(), W = cb.width, H = cb.height;
          if (hasContents(sp)) {
            var emb = await out.embedPage(sp, { left: cb.x, bottom: cb.y, right: cb.x + W, top: cb.y + H });
            var pos = { 0: [0, 0], 90: [0, W], 180: [W, H], 270: [H, 0] }[D.t];
            np.drawPage(emb, { x: pos[0], y: pos[1], width: W, height: H, rotate: L.degrees(-D.t) });
          }
        }
        if (raster || OCR[pkey(p)]) { var ln = []; try { ln = await pageLines(p); } catch (e) { } if (raster || !TXT[pkey(p)] || !TXT[pkey(p)].length) await drawInvisible(L, out, np, p, D.h, cache, ln); }
        for (var j = 0; j < p.ops.length; j++) {
          var o = p.ops[j];
          if (o.t === "erase") continue;
          if (o.t === "note" || o.t === "link") { annotPdf(L, out, np, o, D.h, links, list.length); continue; }
          await drawOpPdf(L, out, np, o, D.h, cache);
        }
      }
      if (onp) onp(n + 1, list.length);
      if (n % 4 === 3 || p.ops.length) await tick();   // beri napas ke layar (HP tidak macet)
    }
    if (links.length) { var pgs = out.getPages(); links.forEach(function (k) { var tp = pgs[Math.max(0, Math.min(pgs.length - 1, k.to - 1))]; k.dict.set(L.PDFName.of("Dest"), out.context.obj([tp.ref, L.PDFName.of("XYZ"), L.PDFNull, L.PDFNull, L.PDFNull])); }); }
    if (opt.a4) out = await toA4(L, out);
    if (opt.marks && opt.marks.length) { try { addOutline(L, out, opt.marks); } catch (e) { console.warn("bookmark:", e.message); } }
    try { out.setTitle(title || "Dokumen"); out.setProducer("STARLITE VM · PDF Tools"); out.setCreator("STARLITE VM"); } catch (e) { }
    return new Uint8Array(await out.save({ useObjectStreams: true }));
  }
  var LASTCMP = null;
  // catatan (sticky note) & tautan → anotasi PDF asli
  function annotPdf(L, out, page, o, Dh, links, total) {
    var ctx = out.context, rect = [o.x, Dh - o.y - o.h, o.x + o.w, Dh - o.y], col = String(o.c || "#f59e0b").replace("#", ""), n = parseInt(col.length === 3 ? col.replace(/./g, "$&$&") : col, 16);
    var C = [(n >> 16 & 255) / 255, (n >> 8 & 255) / 255, (n & 255) / 255], d;
    if (o.t === "note") d = ctx.obj({ Type: "Annot", Subtype: "Text", Rect: rect, Contents: L.PDFHexString.fromText(o.text || ""), T: L.PDFHexString.fromText(o.by || "STARLITE VM"), Name: "Comment", C: C, F: 4, Open: false });
    else {
      d = ctx.obj({ Type: "Annot", Subtype: "Link", Rect: rect, Border: [0, 0, 0], F: 4 });
      if (o.url) d.set(L.PDFName.of("A"), ctx.obj({ S: "URI", URI: L.PDFString.of(o.url) }));
      else if (o.page) links.push({ dict: d, to: Math.min(total, o.page) });
    }
    page.node.addAnnot(ctx.register(d));
  }
  function hasContents(pg) { try { var c = pg.node.Contents(); if (!c) return false; if (c.size && c.size() === 0) return false; return true; } catch (e) { return false; } }
  // samakan ukuran semua halaman ke A4 (potret / lanskap mengikuti halaman), isi diskalakan & ditengahkan
  async function toA4(L, src) {
    var out = await L.PDFDocument.create(), pages = src.getPages();
    for (var i = 0; i < pages.length; i++) {
      var pg = pages[i], cb = pg.getCropBox(), W = cb.width, H = cb.height, r = ((pg.getRotation().angle % 360) + 360) % 360, Dw = r % 180 ? H : W, Dh = r % 180 ? W : H;
      var land = Dw > Dh, TW = land ? 841.89 : 595.28, TH = land ? 595.28 : 841.89, sc = Math.min(TW / Dw, TH / Dh);
      var np = out.addPage([TW, TH]);
      if (!hasContents(pg)) continue;   // halaman kosong → cukup halaman A4 kosong
      var emb = await out.embedPage(pg, { left: cb.x, bottom: cb.y, right: cb.x + W, top: cb.y + H });
      var ox = (TW - Dw * sc) / 2, oy = (TH - Dh * sc) / 2, pos = { 0: [0, 0], 90: [0, W], 180: [W, H], 270: [H, 0] }[r];
      np.drawPage(emb, { x: ox + pos[0] * sc, y: oy + pos[1] * sc, width: W * sc, height: H * sc, rotate: L.degrees(-r) });
    }
    return out;
  }
  // bookmark (outline) per file — judul = nama file
  function addOutline(L, doc, marks) {
    var ctx = doc.context, pages = doc.getPages(), root = ctx.nextRef(), refs = marks.map(function () { return ctx.nextRef(); });
    marks.forEach(function (m, i) {
      var pg = pages[Math.min(m.index, pages.length - 1)];
      var dict = { Title: L.PDFHexString.fromText(String(m.title).slice(0, 120)), Parent: root, Dest: [pg.ref, L.PDFName.of("Fit")] };
      if (i > 0) dict.Prev = refs[i - 1]; if (i < refs.length - 1) dict.Next = refs[i + 1];
      ctx.assign(refs[i], ctx.obj(dict));
    });
    ctx.assign(root, ctx.obj({ Type: "Outlines", First: refs[0], Last: refs[refs.length - 1], Count: refs.length }));
    doc.catalog.set(L.PDFName.of("Outlines"), root); doc.catalog.set(L.PDFName.of("PageMode"), L.PDFName.of("UseOutlines"));
  }

  // ---------- file hasil (segmen) ----------
  var isEdit = function () { return PE.mode === "edit"; }, isMerge = function () { return PE.mode === "merge"; };
  var MODE_T = { split: "Split PDF", merge: "Gabung PDF", edit: "Edit PDF", conv: "Konversi File" };
  async function switchMode(m) {
    if (m === PE.mode || PE.lock) return;
    if (ED.on) edClose();
    if (isMerge() && PE.pages.length) {   // hasil gabungan dibawa ke mode berikutnya sesuai urutan & pilihan halaman
      var ml = mergedPages(); if (ml.length) { pushUndo(); await applyMerged(ml); }
    }
    PE.mode = m; PE.sel.clear(); PE.mf = false;
    var t = $("pe-ttl").textContent; if (/^((Split|Gabung|Edit) PDF|Konversi File)$/.test(t)) $("pe-ttl").textContent = MODE_T[m];
    if (isMerge()) syncMfiles();
    render();
  }
  // ---------- Gabung PDF ----------
  function syncMfiles() {
    var used = {}; PE.pages.forEach(function (p) { used[p.d] = 1; });
    PE.mfiles = PE.mfiles.filter(function (f) { return used[f.d]; });
    Object.keys(used).map(Number).sort(function (a, b) { return a - b; }).forEach(function (d) { if (!PE.mfiles.some(function (f) { return f.d === d; })) PE.mfiles.push({ d: d, name: safeName(String(PE.docs[d].name).replace(/\.(jpe?g|png|webp|gif|bmp)$/i, "")) || "File " + (d + 1), range: "", rot: 0 }); });
  }
  function pagesOf(f) { return PE.pages.filter(function (p) { return p.d === f.d; }); }
  function parseRange(txt, n) {
    var t = String(txt || "").trim(); if (!t) return { idx: Array.from({ length: n }, function (_, i) { return i; }) };
    var out = [], bad = "";
    t.split(/[,;]+/).forEach(function (part) {
      var m = part.trim().match(/^(\d+)?\s*(-)?\s*(\d+)?$/); if (!part.trim()) return;
      if (!m || (!m[1] && !m[3])) { bad = part.trim(); return; }
      var a = m[1] ? +m[1] : 1, b = m[2] ? (m[3] ? +m[3] : n) : a;
      if (a < 1 || b > n || a > b) { bad = part.trim(); return; }
      for (var q = a; q <= b; q++) out.push(q - 1);
    });
    return { idx: out, bad: bad };
  }
  function mergedPages() {
    var O = PE.mopt, groups = PE.mfiles.map(function (f) {
      var all = pagesOf(f), r = parseRange(f.range, all.length);
      return { f: f, pages: r.idx.map(function (i) { var c = clone(all[i]); c.id = all[i].id + "~" + f.d + "~" + i; if (f.rot) rotOps(c, f.rot); return c; }) };
    }).filter(function (g) { return g.pages.length; });
    var list = [], marks = [];
    if (O.inter && groups.length === 2) {
      var A = groups[0].pages, B = groups[1].pages.slice(); if (O.interRev) B.reverse();
      for (var i = 0; i < Math.max(A.length, B.length); i++) { if (A[i]) list.push(A[i]); if (B[i]) list.push(B[i]); }
      marks.push({ title: groups[0].f.name, index: 0 });
    } else groups.forEach(function (g) {
      if (O.blank && list.length % 2 === 1) { var last = list[list.length - 1], D = dims(last); list.push({ blank: true, id: "blank" + list.length, w: D.w, h: D.h, r0: 0, rot: 0, ops: [], d: -1, i: -1 }); }
      marks.push({ title: g.f.name, index: list.length });
      list = list.concat(g.pages);
    });
    list.__marks = O.marks ? marks : null;
    return list;
  }
  async function applyMerged(ml) {   // pakai urutan gabungan sebagai daftar halaman (halaman kosong dibuat sebagai PDF kecil)
    var pages = [];
    for (var i = 0; i < ml.length; i++) {
      var p = ml[i];
      if (p.blank) { if (!PE.blankDoc) { var L = await loadPdfLib(), bd = await L.PDFDocument.create(); bd.addPage([p.w, p.h]); var by = new Uint8Array(await bd.save()); PE.docs.push({ bytes: by, name: "Halaman kosong", hash: "blank" }); PE.blankDoc = PE.docs.length - 1; } pages.push({ id: "p" + (++PE.uid), d: PE.blankDoc, i: 0, r0: 0, rot: 0, w: p.w, h: p.h, ops: [] }); }
      else { var c = clone(p); c.id = "p" + (++PE.uid); pages.push(c); }
    }
    PE.pages = pages; PE.cuts = new Set(); PE.mfiles.forEach(function (f) { f.range = ""; f.rot = 0; }); PE.mopt.inter = false; PE.mopt.blank = false;
    return pages;
  }
  function segs() {
    var out = [], cur = null;
    if (isEdit()) { out = PE.pages.length ? [{ key: PE.pages[0].id, pages: PE.pages.slice(), start: 0, no: 1, color: COLORS[0] }] : []; return out; }
    if (isMerge()) { var ml = mergedPages(); return ml.length ? [{ key: "merge", pages: ml, start: 0, no: 1, color: COLORS[5] }] : []; }
    PE.pages.forEach(function (p, ix) { if (!cur || PE.cuts.has(p.id)) { cur = { key: p.id, pages: [], start: ix }; out.push(cur); } cur.pages.push(p); });
    out.forEach(function (s, i) { s.no = i + 1; s.color = COLORS[i % COLORS.length]; });
    return out;
  }
  var fmtD = function () { var d = new Date(), z = function (n) { return ("0" + n).slice(-2); }; return z(d.getDate()) + "-" + z(d.getMonth() + 1) + "-" + d.getFullYear(); };
  function pairRows(pr) {
    if (!pr) return [];
    var k = N(pr.key), L = (typeof STATE !== "undefined" && STATE.takeover) || [];
    if (pr.mode === "spk") return L.filter(function (t) { return N(t.att_spk) === k; });
    if (pr.mode === "bap") return L.filter(function (t) { return emp(t.att_spk) && N(t.bap_no) === k; });
    return L.filter(function (t) { return emp(t.att_spk) && emp(t.bap_no) && N(t.po) === k; });
  }
  function uniq(a) { return a.filter(function (v, i) { return !emp(v) && a.indexOf(v) === i; }); }
  function vars(s, total) {
    var rows = pairRows(PE.pairs[s.key]), a = rows[0] || {};
    var pad = String(s.no); if (total >= 10 && s.no < 10) pad = "0" + pad;
    return { no: pad, nama: PE.base, tanggal: fmtD(), PO: uniq(rows.map(function (r) { return r.po; })).join("_"), BAP: uniq(rows.map(function (r) { return r.bap_no; })).join("_"), SPK: a.att_spk && !/^https?:/i.test(a.att_spk) ? a.att_spk : "", Stasiun: a.stasiun || "", Mitra: a.after || "", hal: s.pages.length };
  }
  function defPattern(n) { return PE.pattern || (n > 1 ? (PE.lock ? "{nama} - bagian {no}" : "{nama} - {no}") : "{nama}"); }
  function applyPattern(pat, s, total) {
    var v = vars(s, total);
    var t = String(pat).replace(/\{(\w+)\}/g, function (m, k) { var key = Object.keys(v).filter(function (x) { return x.toLowerCase() === k.toLowerCase(); })[0]; return key ? v[key] : m; });
    return safeName(t.replace(/\s*-\s*-\s*/g, " - ").replace(/^\s*-\s*|\s*-\s*$/g, "")) || (PE.base + " - " + s.no);
  }
  function nameOf(s, total) {
    if (isMerge()) return PE.mopt.outName || ("Gabungan " + (PE.mfiles[0] ? PE.mfiles[0].name : "PDF") + (PE.mfiles.length > 1 ? " +" + (PE.mfiles.length - 1) : "")); return PE.names[s.key] != null ? PE.names[s.key] : applyPattern(defPattern(total), s, total); }
  function finalNames(list) {
    var seen = {}, all = list || segs();
    return all.map(function (s) { var n = safeName(nameOf(s, all.length)) || PE.base, k = n.toLowerCase(), i = 1; while (seen[k]) { k = (n + " (" + (++i) + ")").toLowerCase(); } seen[k] = 1; return i > 1 ? n + " (" + i + ")" : n; });
  }

  // ---------- cari data takeover ----------
  function groupOf(t) { if (!emp(t.att_spk) && !/^https?:/i.test(t.att_spk)) return { mode: "spk", key: String(t.att_spk).trim() }; if (!emp(t.bap_no)) return { mode: "bap", key: String(t.bap_no).trim() }; return { mode: "po", key: String(t.po).trim() }; }
  function findGroups(q) {
    var nq = N(q), lq = String(q || "").trim().toLowerCase(), G = new Map();
    if (lq.length < 2) return [];
    ((typeof STATE !== "undefined" && STATE.takeover) || []).forEach(function (t) {
      var ids = [t.att_spk, t.bap_no, t.po], txt = [t.stasiun, t.before, t.after, t.region];
      var exact = ids.some(function (v) { return !emp(v) && N(v) === nq; });
      if (!(exact || ids.some(function (v) { return !emp(v) && N(v).indexOf(nq) >= 0; }) || txt.some(function (v) { return String(v || "").toLowerCase().indexOf(lq) >= 0; }))) return;
      var g = groupOf(t), id = g.mode + ":" + N(g.key), o = G.get(id);
      if (!o) G.set(id, o = { mode: g.mode, key: g.key, exact: false });
      if (exact) o.exact = true;
    });
    return Array.from(G.values()).sort(function (a, b) { return (b.exact - a.exact) || String(a.key).localeCompare(String(b.key)); }).slice(0, 25);
  }
  var MODE = { spk: "SPK", bap: "BAP", po: "PO" };
  function pairLabel(pr) { var r = pairRows(pr), pos = uniq(r.map(function (x) { return x.po; })); return '<span class="pe-tag">' + MODE[pr.mode] + "</span> <b>" + E(pr.key) + "</b> <span style=\"color:var(--pe-mute)\">· " + pos.length + " PO" + (r[0] && r[0].stasiun ? " · " + E(r[0].stasiun) : "") + "</span>"; }
  function sugHtml(list) {
    if (!list.length) return '<div style="padding:8px;color:var(--pe-mute)">Tidak ada data yang cocok</div>';
    return list.map(function (g, i) { var r = pairRows(g), a = r[0] || {}, pos = uniq(r.map(function (x) { return x.po; })); return '<button type="button" data-g="' + i + '"><span class="pe-tag">' + MODE[g.mode] + "</span> <b>" + E(g.key) + "</b><small>" + E([a.stasiun, a.region, a.after].filter(function (v) { return !emp(v); }).join(" · ")) + "</small><small>PO " + E(pos.slice(0, 4).join(", ") + (pos.length > 4 ? " +" + (pos.length - 4) : "")) + "</small></button>"; }).join("");
  }
  function bindSearch(input, box, onPick) {
    var list = [], t = null;
    input.addEventListener("input", function () {
      clearTimeout(t); t = setTimeout(function () {
        list = findGroups(input.value);
        if (!input.value.trim()) { box.classList.add("hidden"); return; }
        box.innerHTML = sugHtml(list); box.classList.remove("hidden");
        box.querySelectorAll("[data-g]").forEach(function (b) { b.onmousedown = function (e) { e.preventDefault(); onPick(list[+b.dataset.g]); }; });
      }, 120);
    });
    input.addEventListener("blur", function () { setTimeout(function () { box.classList.add("hidden"); }, 150); });
  }

  // ---------- kerangka tampilan ----------
  function shell() {
    var el = $("pe");
    if (el) return el;
    el = document.createElement("div"); el.id = "pe"; el.className = "hidden";
    el.innerHTML = '<div class="pe-top" id="pe-top">'
      + '<button class="pe-b ic" id="pe-close" title="Tutup"><i class="fa-solid fa-xmark"></i></button>'
      + '<div class="pe-title"><b id="pe-ttl">Split &amp; Edit PDF</b><small id="pe-sub">Pecah, rapikan, dan kirim PDF tanpa keluar aplikasi</small></div>'
      + '<div class="pe-modes" id="pe-modes" role="tablist"><i class="pe-mode-ind"></i><button data-mode="split" role="tab"><i class="fa-solid fa-scissors"></i><span>Split</span></button><button data-mode="merge" role="tab"><i class="fa-solid fa-object-group"></i><span>Gabung</span></button><button data-mode="edit" role="tab"><i class="fa-solid fa-pen-to-square"></i><span>Edit</span></button><button data-mode="conv" role="tab"><i class="fa-solid fa-right-left"></i><span>Konversi</span></button></div>'
      + '<span class="pe-saved hidden" id="pe-saved" title="Pekerjaan tersimpan otomatis di perangkat ini — aman bila tab tertutup"><i class="fa-solid fa-cloud-arrow-down"></i><span class="tx">Tersimpan di perangkat</span></span>'
      + '<span class="pe-badges" id="pe-badges"></span>'
      + '<span class="pe-lock hidden" id="pe-lock"><i class="fa-solid fa-lock mr-1"></i>Mode Split saja</span>'
      + '<button class="pe-b" id="pe-undo" title="Urungkan (Ctrl+Z)" disabled><i class="fa-solid fa-rotate-left"></i><span class="tx">Urungkan</span></button>'
      + '<button class="pe-b" id="pe-redo" title="Ulangi (Ctrl+Y)" disabled><i class="fa-solid fa-rotate-right"></i><span class="tx">Ulangi</span></button>'
      + '<button class="pe-b" id="pe-add" title="Tambah PDF / gambar"><i class="fa-solid fa-plus"></i><span class="tx">Tambah file</span></button>'
      + '<button class="pe-b" id="pe-dl"><i class="fa-solid fa-download"></i><span class="tx">Unduh</span></button>'
      + '<button class="pe-b pri" id="pe-send"><i class="fa-solid fa-paper-plane"></i><span class="tx">Kirim / Simpan</span><i class="fa-solid fa-chevron-down" style="font-size:9px"></i></button>'
      + "</div>"
      + '<div class="pe-body"><aside class="pe-files" id="pe-files"></aside><main class="pe-main"><div class="pe-bar" id="pe-bar"></div><div class="pe-grid" id="pe-grid"></div></main>'
      + '<div class="pe-mtab"><button id="pe-mt-p" class="on"><i class="fa-regular fa-copy"></i>Halaman</button><button id="pe-mt-f"><i class="fa-solid fa-scissors"></i>File hasil</button></div></div>'
      + '<input type="file" id="pe-in" class="hidden" multiple accept="application/pdf,.pdf,image/png,image/jpeg,.jpg,.jpeg,.png">';
    document.body.appendChild(el);
    $("pe-close").onclick = peClose;
    el.querySelectorAll("#pe-modes [data-mode]").forEach(function (b) { b.onclick = function () { switchMode(b.dataset.mode); }; });
    $("pe-undo").onclick = undo; $("pe-redo").onclick = redo;
    $("pe-add").onclick = function () { PE.insAt = null; $("pe-in").click(); };
    $("pe-in").onchange = function () { var f = this.files; addFiles(f, PE.insAt); this.value = ""; };
    $("pe-dl").onclick = function (e) { dlMenu(e.currentTarget); };
    $("pe-send").onclick = function (e) { sendMenu(e.currentTarget); };
    $("pe-mt-p").onclick = function () { PE.mf = false; render(); };
    $("pe-mt-f").onclick = function () { PE.mf = true; render(); };
    var dzv = document.createElement("div"); dzv.className = "pe-dz hidden"; dzv.id = "pe-dz";
    dzv.innerHTML = '<div class="in">' + DROP_ILLU + '<b>Lepas untuk menambahkan file</b><small>PDF, JPG atau PNG — halaman baru ditaruh di akhir</small></div>';
    el.appendChild(dzv);
    var dc = 0, hasFiles = function (e) { return e.dataTransfer && Array.from(e.dataTransfer.types || []).indexOf("Files") >= 0; };
    el.addEventListener("dragenter", function (e) { if (!hasFiles(e) || PE.lock || ED.on || PE.drag) return; dc++; if (PE.pages.length) dzv.classList.remove("hidden"); });
    el.addEventListener("dragleave", function (e) { if (!hasFiles(e)) return; dc = Math.max(0, dc - 1); if (!dc) dzv.classList.add("hidden"); });
    el.addEventListener("dragover", function (e) { if (hasFiles(e) && !PE.lock && !ED.on) e.preventDefault(); });
    el.addEventListener("drop", function (e) { dc = 0; dzv.classList.add("hidden"); if (!hasFiles(e) || PE.lock || ED.on) return; e.preventDefault(); if (e.dataTransfer.files.length) { if (isConv()) cvAuto(Array.from(e.dataTransfer.files)); else addFiles(e.dataTransfer.files); } });
    document.addEventListener("keydown", function (e) {
      if (!PE.open || ED.edit) return;
      var tag = (e.target.tagName || "").toLowerCase(); if ((tag === "input" || tag === "textarea" || tag === "select") && e.key !== "Escape") return;
      if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === "z") { e.preventDefault(); e.shiftKey ? redo() : undo(); }
      else if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === "y") { e.preventDefault(); redo(); }
      else if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === "d" && ED.on && (ED.sel || msOn())) { e.preventDefault(); msOn() ? msDup() : edDup(); }
      else if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === "f" && ED.on) { e.preventDefault(); edAct("find"); }
      else if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === "a" && ED.on) { e.preventDefault(); msAll(); }
      else if (ED.on && !e.ctrlKey && !e.metaKey && !e.altKey && e.key.length === 1 && TOOLS.some(function (t) { return t[3] && t[3].toLowerCase() === e.key.toLowerCase(); })) { pickTool(TOOLS.filter(function (t) { return t[3] && t[3].toLowerCase() === e.key.toLowerCase(); })[0][0]); }
      else if (ED.on && (e.key === "PageDown" || e.key === "PageUp")) { e.preventDefault(); edGo(e.key === "PageDown" ? 1 : -1); }
      else if (ED.on && (ED.sel || msOn()) && /^Arrow/.test(e.key)) { e.preventDefault(); var st = e.shiftKey ? 10 : 1; if (!ED.nudge) pushUndo(); clearTimeout(ED.nudge); ED.nudge = setTimeout(function () { ED.nudge = null; renderSoon(); }, 600); (msOn() ? ED.ms : [ED.sel]).forEach(function (o) { moveOp(o, e.key === "ArrowLeft" ? -st : e.key === "ArrowRight" ? st : 0, e.key === "ArrowUp" ? -st : e.key === "ArrowDown" ? st : 0); }); edDraw(); }
      else if (e.key === "Delete" || e.key === "Backspace") { if (ED.on) { if (msOn()) { e.preventDefault(); msDel(); } else if (ED.sel) { e.preventDefault(); edDelSel(); } } else if (PE.sel.size) { e.preventDefault(); delPages(); } }
      else if (e.key === "Escape") { var md = document.querySelector("#pe .pe-modal:last-of-type"); if (md && !md.dataset.busy) { md.remove(); return; } if (document.querySelector(".pe-menu")) closeMenus(); else if (ED.on && !$("pe-mpop").classList.contains("hidden")) hidePop(); else if (ED.on && $("pe-find") && !$("pe-find").classList.contains("hidden")) findClose(); else if (ED.on && (ED.sel || msOn())) { ED.sel = null; ED.ms = []; edProps(); edDraw(); } else if (ED.on) edClose(); }
    });
    return el;
  }

  function render() {
    if (!PE.open) return;
    var el = $("pe");
    if (isMerge()) syncMfiles();
    el.classList.toggle("mf", !!PE.mf && !isEdit()); el.classList.toggle("m-edit", isEdit()); el.classList.toggle("m-split", PE.mode === "split"); el.classList.toggle("m-merge", isMerge()); el.classList.toggle("m-conv", isConv());
    var md = $("pe-modes"); md.classList.toggle("hidden", PE.lock); md.dataset.m = PE.mode; md.querySelectorAll("[data-mode]").forEach(function (b) { b.classList.toggle("on", b.dataset.mode === PE.mode); b.setAttribute("aria-selected", b.dataset.mode === PE.mode); });
    $("pe-mt-p").classList.toggle("on", !PE.mf); $("pe-mt-f").classList.toggle("on", !!PE.mf);
    $("pe-lock").classList.toggle("hidden", !PE.lock);
    $("pe-badges").innerHTML = (PE.comp ? '<button class="pe-bdg" data-bd="comp" title="Ubah kompres"><i class="fa-solid fa-compress"></i>Kompres ' + COMP[PE.comp].t + "</button>" : "") + (PE.pw ? '<button class="pe-bdg am" data-bd="pw" title="Ubah kunci"><i class="fa-solid fa-lock"></i>Terkunci</button>' : "");
    $("pe-badges").querySelectorAll("[data-bd]").forEach(function (b) { b.onclick = function () { b.dataset.bd === "comp" ? compModal() : pwModal(); }; });
    $("pe-add").classList.toggle("hidden", PE.lock);
    var has = PE.pages.length > 0;
    $("pe-dl").disabled = !has; $("pe-send").disabled = !has;
    var S = segs();
    $("pe-sub").textContent = isMerge() ? (has ? PE.mfiles.length + " file → " + (S[0] ? S[0].pages.length : 0) + " halaman gabungan" : "Satukan beberapa PDF / gambar menjadi satu file")
      : has ? PE.base + " · " + PE.pages.length + " halaman" + (isEdit() ? "" : " → " + S.length + " file") : (isEdit() ? "Edit teks asli, deteksi TTD & stempel, tulis, gambar" : "Pecah satu PDF menjadi banyak file bernama custom");
    $("pe-mt-f").innerHTML = isMerge() ? '<i class="fa-solid fa-sliders"></i>Opsi gabung' : '<i class="fa-solid fa-scissors"></i>File hasil (' + S.length + ")";
    try { el.style.setProperty("--pe-topH", $("pe-top").offsetHeight + "px"); } catch (e) { }
    if (isConv()) { $("pe-bar").innerHTML = '<span class="cv-bar"><i class="fa-solid fa-right-left"></i><b>Konversi File</b><span>PDF ⇄ Word · Excel · JPG/PNG · Teks · OCR · Kompres · Password</span></span>'; renderConv($("pe-grid")); renderConvOut($("pe-files")); $("pe-sub").textContent = "Ubah format file tanpa keluar aplikasi"; $("pe-mt-p").innerHTML = '<i class="fa-solid fa-right-left"></i>Konversi'; $("pe-mt-f").innerHTML = '<i class="fa-solid fa-box-archive"></i>Hasil (' + PE.conv.length + ")"; syncUndo(); return; }
    $("pe-mt-p").innerHTML = '<i class="fa-regular fa-copy"></i>Halaman';
    renderBar(); renderGrid(S); renderFiles(S); syncUndo(); autosave();
  }

  // alur antar fitur: hasil satu fitur bisa langsung dilanjutkan di fitur lain (halaman & editan ikut terbawa)
  function flowHtml() {
    if (PE.lock || !PE.pages.length) return "";
    var B = { edit: ["fa-pen-to-square", isMerge() ? "Edit hasil gabungan" : "Edit halaman"], split: ["fa-scissors", isMerge() ? "Pecah hasil gabungan" : "Pecah jadi beberapa file"], merge: ["fa-object-group", "Gabung dengan file lain"] };
    var list = PE.mode === "split" ? ["merge"] : isMerge() ? ["edit", "split"] : ["split", "merge"];
    return '<span class="pe-flow"><label>Lanjut ke</label>' + list.map(function (k) { return '<button class="pe-b" data-flow="' + k + '"><i class="fa-solid ' + B[k][0] + '"></i>' + B[k][1] + "</button>"; }).join("") + "</span>";
  }
  function bindFlow(bar) {
    bar.querySelectorAll("[data-flow]").forEach(function (b) { b.onclick = async function () {
      var k = b.dataset.flow;
      if (k === "merge") { PE.insAt = null; $("pe-in").click(); await switchMode("merge"); toast("Pilih file yang mau digabung — dokumen ini (beserta editannya) jadi file pertama", "info", 5000); return; }
      if (k === "edit" && PE.mode === "split") { var id = PE.sel.size ? selected()[0].id : PE.pages[0].id; edOpen(id); return; }
      var from = PE.mode; await switchMode(k);
      toast(k === "edit" ? "Lanjut edit — urutan & pilihan halaman ikut terbawa" : (from === "merge" ? "Hasil gabungan siap dipecah — klik gunting di antara halaman atau isi rentang" : "Klik gunting di antara halaman untuk memecah — semua editan ikut terbawa"), "success", 5000);
    }; });
  }
  function renderBar() {
    var bar = $("pe-bar"), n = PE.sel.size, has = PE.pages.length > 0;
    if (!has) { bar.innerHTML = '<span style="color:var(--pe-mute)">Belum ada file.</span>'; return; }
    if (isMerge()) {
      bar.innerHTML = '<label>Urutkan</label><button class="pe-b" data-sort="az" title="Nama A–Z (angka diurutkan wajar: 2 sebelum 10)"><i class="fa-solid fa-arrow-down-a-z"></i>A–Z</button><button class="pe-b" data-sort="za"><i class="fa-solid fa-arrow-up-z-a"></i>Z–A</button><button class="pe-b" data-sort="rev" title="Balik urutan"><i class="fa-solid fa-right-left"></i>Balik</button>'
        + '<span class="sep"></span><span style="color:var(--pe-mute);font-size:11px"><i class="fa-solid fa-grip-vertical"></i> Seret kartu untuk mengatur urutan · isi kolom halaman untuk memilih sebagian</span>' + flowHtml();
      bindFlow(bar);
      bar.querySelectorAll("[data-sort]").forEach(function (b) { b.onclick = function () { pushUndo(); var k = b.dataset.sort, col = new Intl.Collator("id", { numeric: true, sensitivity: "base" }); if (k === "rev") PE.mfiles.reverse(); else PE.mfiles.sort(function (a, c) { return (k === "az" ? 1 : -1) * col.compare(a.name, c.name); }); render(); }; });
      return;
    }
    var L = PE.lock;
    var dis = n ? "" : "disabled";
    bar.innerHTML = '<button class="pe-b" id="pe-b-all"><i class="fa-regular fa-square-check"></i>' + (n === PE.pages.length ? "Batal pilih" : "Pilih semua") + "</button>"
      + (n ? '<span class="pe-chip" style="--c:#4f46e5">' + n + " dipilih</span>" : "")
      + (L ? "" : '<button class="pe-b" id="pe-b-rl" ' + dis + '><i class="fa-solid fa-rotate-left"></i>Putar kiri</button><button class="pe-b" id="pe-b-rr" ' + dis + '><i class="fa-solid fa-rotate-right"></i>Putar kanan</button>'
        + '<button class="pe-b" id="pe-b-dup" ' + dis + '><i class="fa-regular fa-clone"></i>Duplikat</button>'
        + '<button class="pe-b" id="pe-b-ml" title="Geser halaman terpilih ke kiri" ' + dis + '><i class="fa-solid fa-arrow-left"></i>Geser</button><button class="pe-b" id="pe-b-mr" title="Geser halaman terpilih ke kanan" ' + dis + '>Geser<i class="fa-solid fa-arrow-right"></i></button>')
      + '<button class="pe-b red" id="pe-b-del" ' + (n && n < PE.pages.length ? "" : "disabled") + '><i class="fa-regular fa-trash-can"></i>Hapus</button>'
      + (L ? "" : '<button class="pe-b pri" id="pe-b-ed"><i class="fa-solid fa-pen-ruler"></i>Edit halaman</button>')
      + (isEdit() ? "" : '<span class="sep"></span><label>Pecah</label>'
      + '<input id="pe-rg" placeholder="mis. 1-3, 4, 5-8" style="width:140px" title="Rentang halaman per file">'
      + '<button class="pe-b" id="pe-b-rg">Terapkan</button>'
      + '<button class="pe-b" id="pe-b-n" title="Pecah tiap N halaman">Tiap <input id="pe-nn" type="number" min="1" value="2" style="width:48px;height:24px;padding:2px 4px" onclick="event.stopPropagation()"> hal</button>'
      + '<button class="pe-b" id="pe-b-1">Per halaman</button>'
      + '<button class="pe-b" id="pe-b-0" ' + (PE.cuts.size ? "" : "disabled") + '>Satukan</button>') + flowHtml();
    bindFlow(bar);
    var on = function (id, f) { var b = $(id); if (b) b.onclick = f; };
    on("pe-b-all", function () { if (PE.sel.size === PE.pages.length) PE.sel.clear(); else PE.pages.forEach(function (p) { PE.sel.add(p.id); }); render(); });
    on("pe-b-rl", function () { rotatePages(-90); }); on("pe-b-rr", function () { rotatePages(90); });
    on("pe-b-dup", dupPages); on("pe-b-del", delPages);
    on("pe-b-ml", function () { movePages(-1); }); on("pe-b-mr", function () { movePages(1); });
    on("pe-b-ed", function () { var id = PE.sel.size ? PE.pages.filter(function (p) { return PE.sel.has(p.id); })[0].id : PE.pages[0].id; edOpen(id); });
    on("pe-b-rg", function () { splitRanges($("pe-rg").value); });
    if ($("pe-rg")) $("pe-rg").onkeydown = function (e) { if (e.key === "Enter") splitRanges(this.value); };
    on("pe-b-n", function () { var n = Math.max(1, parseInt(($("pe-nn") || {}).value, 10) || 1); pushUndo(); PE.cuts = new Set(PE.pages.filter(function (p, i) { return i && i % n === 0; }).map(function (p) { return p.id; })); render(); });
    on("pe-b-1", function () { pushUndo(); PE.cuts = new Set(PE.pages.slice(1).map(function (p) { return p.id; })); render(); });
    on("pe-b-0", function () { pushUndo(); PE.cuts.clear(); render(); });
  }

  var DROP_ILLU = '<svg class="pe-illu" viewBox="0 0 160 120" aria-hidden="true">'
    + '<g class="pg2"><rect x="70" y="18" width="58" height="74" rx="7" fill="#e0e7ff" stroke="#a5b4fc" stroke-width="1.5"/><rect x="78" y="30" width="42" height="26" rx="4" fill="#c7d2fe"/><circle cx="88" cy="39" r="4" fill="#818cf8"/><path d="M80 54l11-10 8 7 7-5 12 8z" fill="#818cf8"/><rect x="78" y="62" width="34" height="4" rx="2" fill="#c7d2fe"/><rect x="78" y="71" width="26" height="4" rx="2" fill="#c7d2fe"/></g>'
    + '<g class="pg1"><path d="M32 12h40l16 16v66a8 8 0 0 1-8 8H32a8 8 0 0 1-8-8V20a8 8 0 0 1 8-8z" fill="#fff" stroke="#cbd5e1" stroke-width="1.5"/><path d="M72 12v12a4 4 0 0 0 4 4h12" fill="#f1f5f9" stroke="#cbd5e1" stroke-width="1.5"/><rect x="34" y="40" width="40" height="4" rx="2" fill="#e2e8f0"/><rect x="34" y="50" width="44" height="4" rx="2" fill="#e2e8f0"/><rect x="34" y="60" width="32" height="4" rx="2" fill="#e2e8f0"/><rect x="22" y="72" width="34" height="18" rx="5" fill="#e11d48"/><text x="39" y="85" text-anchor="middle" font-size="10" font-weight="800" fill="#fff" font-family="Arial, sans-serif">PDF</text></g>'
    + '<g class="arw"><circle cx="118" cy="92" r="17" fill="#4f46e5"/><path d="M118 100V84m-7 7l7-7 7 7" stroke="#fff" stroke-width="3" fill="none" stroke-linecap="round" stroke-linejoin="round"/></g></svg>';
  function renderGrid(S) {
    var grid = $("pe-grid");
    if (PE.pages.length && isMerge()) return renderMerge(grid);
    if (!PE.pages.length) {
      grid.innerHTML = '<div class="pe-empty"><label class="pe-drop" id="pe-drop" for="pe-in" tabindex="0">' + DROP_ILLU
        + '<b class="pe-drop-t">' + { edit: "Tarik &amp; lepas PDF yang mau diedit", split: "Tarik &amp; lepas PDF yang mau dipecah", merge: "Tarik &amp; lepas semua PDF / gambar yang mau digabung" }[PE.mode] + '</b><span class="pe-drop-s">atau</span>'
        + '<span class="pe-b pri pe-drop-btn"><i class="fa-solid fa-folder-open"></i>Pilih file dari perangkat</span>'
        + '<span class="pe-chips"><span>PDF</span><span>JPG</span><span>PNG</span><span>bisa beberapa file</span><span>maks ' + MAX_MB + " MB · " + MAX_PAGES + ' hal</span></span></label>'
        + '<p class="pe-safe"><i class="fa-solid fa-shield-halved"></i>Semua proses berjalan di perangkat ini. File tidak diunggah sebelum Anda menekan Kirim / Simpan.</p><div id="pe-draft"></div></div>';
      if (PE.origin.kind === "tab") getDraft().then(function (d) {
        var box = $("pe-draft"); if (!box || !d || PE.pages.length) return;
        box.innerHTML = '<div class="pe-draft"><i class="fa-solid fa-clock-rotate-left"></i><span><b>Lanjutkan pekerjaan terakhir?</b><small>' + E(d.base) + " · " + d.n + " halaman" + (d.mode === "split" || !d.mode ? " → " + d.files + " file" : "") + " · " + MODE_T[d.mode || "split"] + " · " + new Date(d.at).toLocaleString("id-ID", { day: "2-digit", month: "short", hour: "2-digit", minute: "2-digit" }) + '</small></span><button class="pe-b pri" data-r>Lanjutkan</button><button class="pe-b" data-d>Buang</button></div>';
        box.querySelector("[data-r]").onclick = function () { restoreDraft(d); };
        box.querySelector("[data-d]").onclick = function () { clearDraft(); box.innerHTML = ""; };
      });
      var dz = $("pe-drop");
      dz.ondragover = function (e) { e.preventDefault(); dz.classList.add("over"); };
      dz.ondragleave = function () { dz.classList.remove("over"); };
      dz.ondrop = function (e) { e.preventDefault(); e.stopPropagation(); dz.classList.remove("over"); hideDz(); addFiles(e.dataTransfer.files); };
      dz.onkeydown = function (e) { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); $("pe-in").click(); } };
      return;
    }
    var segOf = {}; S.forEach(function (s) { s.pages.forEach(function (p) { segOf[p.id] = s; }); });
    grid.innerHTML = "";
    PE.pages.forEach(function (p, ix) {
      var s = segOf[p.id], first = s.pages[0] === p, D = dims(p);
      var card = document.createElement("div");
      card.className = "pe-card" + (PE.sel.has(p.id) ? " sel" : "") + (first && ix ? " cutOn" : "") + (SEEN.has(p.id) ? "" : " new");
      SEEN.add(p.id); if (!SEEN.has("_n")) card.style.animationDelay = Math.min(ix, 20) * 25 + "ms";
      card.style.setProperty("--c", s.color);
      card.dataset.id = p.id;
      card.innerHTML = (first && !isEdit() ? '<span class="fl">File ' + s.no + "</span>" : "")
        + (ix && !isEdit() ? '<button class="cut" title="' + (first ? "Gabungkan dengan file sebelumnya" : "Mulai file baru dari halaman ini") + '"><i class="fa-solid fa-scissors"></i></button>' : "")
        + '<div class="th"><img alt="" draggable="false"><span class="ck"><i class="fa-solid fa-check"></i></span>'
        + '<span class="tools">' + (PE.lock ? "" : '<button data-a="ed" title="Edit halaman ini"><i class="fa-solid fa-pen"></i></button>') + '<button data-a="vw" title="Lihat besar"><i class="fa-solid fa-magnifying-glass-plus"></i></button></span>'
        + (p.ops.length ? '<span class="mk">diedit</span>' : "") + "</div>"
        + '<div class="ft">Hal ' + (ix + 1) + "<span>· " + (PE.docs.length > 1 ? E(String(PE.docs[p.d].name).slice(0, 14)) + " h" + (p.i + 1) : "asli " + (p.i + 1)) + (p.rot ? " · ↻" + p.rot + "°" : "") + "</span></div>";
      var img = card.querySelector("img"); img.style.aspectRatio = D.w + "/" + D.h;
      card.querySelector(".th").onclick = function (e) {
        if (PE.suppressClick && Date.now() - PE.suppressClick < 500) return;
        var a = e.target.closest("[data-a]");
        if (a) { e.stopPropagation(); if (a.dataset.a === "ed") edOpen(p.id); else viewPage(p.id); return; }
        if (e.shiftKey && PE.last >= 0) { var a0 = Math.min(PE.last, ix), b0 = Math.max(PE.last, ix); for (var q = a0; q <= b0; q++) PE.sel.add(PE.pages[q].id); }
        else if (PE.sel.has(p.id)) PE.sel.delete(p.id); else PE.sel.add(p.id);
        PE.last = ix; render();
      };
      card.querySelector(".th").ondblclick = function () { if (!PE.lock) edOpen(p.id); };
      var cut = card.querySelector(".cut");
      if (cut) cut.onclick = function (e) { e.stopPropagation(); pushUndo(); if (PE.cuts.has(p.id)) PE.cuts.delete(p.id); else PE.cuts.add(p.id); render(); };
      if (!PE.lock) touchDrag(card, p);
      if (!PE.lock) {
        card.draggable = true;
        card.ondragstart = function (e) { PE.drag = PE.sel.has(p.id) ? PE.pages.filter(function (x) { return PE.sel.has(x.id); }).map(function (x) { return x.id; }) : [p.id]; card.classList.add("drag"); try { e.dataTransfer.setData("text/plain", p.id); e.dataTransfer.effectAllowed = "move"; } catch (er) { } };
        card.ondragend = function () { card.classList.remove("drag"); PE.drag = null; document.querySelectorAll(".pe-card.dropL").forEach(function (c) { c.classList.remove("dropL"); }); };
        card.ondragover = function (e) { if (!PE.drag) return; e.preventDefault(); document.querySelectorAll(".pe-card.dropL").forEach(function (c) { if (c !== card) c.classList.remove("dropL"); }); card.classList.add("dropL"); };
        card.ondrop = function (e) {
          if (!PE.drag) return; e.preventDefault(); e.stopPropagation();
          var ids = PE.drag; if (ids.indexOf(p.id) >= 0) return;
          pushUndo();
          var moving = PE.pages.filter(function (x) { return ids.indexOf(x.id) >= 0; });
          PE.pages = PE.pages.filter(function (x) { return ids.indexOf(x.id) < 0; });
          var at = PE.pages.indexOf(p); PE.pages.splice.apply(PE.pages, [at, 0].concat(moving));
          PE.drag = null; render();
        };
      }
      grid.appendChild(card);
      var tk = thumbKey(p);
      if (THUMB[tk]) img.src = THUMB[tk]; else { img.__p = p; IO ? IO.observe(img) : thumb(p, img); }
    });
    SEEN.add("_n");
    if (!PE.lock) {
      var add = document.createElement("div"); add.className = "pe-card";
      add.innerHTML = '<label class="th" for="pe-in" style="border:2px dashed var(--pe-line);box-shadow:none;background:none;flex-direction:column;gap:6px;color:var(--pe-mute)"><i class="fa-solid fa-plus" style="font-size:22px"></i><b style="font-size:11px">Tambah PDF / gambar</b></label>';
      add.querySelector("label").onclick = function () { PE.insAt = null; };
      grid.appendChild(add);
    }
  }

  // HP / layar sentuh: tekan lama ±0,35 detik pada halaman lalu geser
  var TD = null;
  function touchDrag(card, p) {
    card.addEventListener("touchstart", function (e) {
      if (e.touches.length !== 1 || e.target.closest("button")) return;
      var t0 = e.touches[0], sx = t0.clientX, sy = t0.clientY;
      TD = { p: p, card: card, sx: sx, sy: sy, on: false, timer: setTimeout(function () {
        if (!TD) return; TD.on = true; try { navigator.vibrate && navigator.vibrate(12); } catch (er) { }
        TD.ids = PE.sel.has(p.id) ? PE.pages.filter(function (x) { return PE.sel.has(x.id); }).map(function (x) { return x.id; }) : [p.id];
        card.classList.add("drag");
        var g = document.createElement("div"); g.className = "pe-ghost"; var im = card.querySelector("img"); g.innerHTML = (im && im.src ? '<img src="' + im.src + '">' : "") + (TD.ids.length > 1 ? "<b>" + TD.ids.length + "</b>" : ""); document.body.appendChild(g); TD.ghost = g; moveGhost(sx, sy);
      }, 350) };
    }, { passive: true });
  }
  function moveGhost(x, y) { if (TD && TD.ghost) { TD.ghost.style.left = x + "px"; TD.ghost.style.top = y + "px"; } }
  function tdTarget(x, y) { var el = document.elementFromPoint(x, y); return el && el.closest ? el.closest(".pe-card") : null; }
  document.addEventListener("touchmove", function (e) {
    if (!TD) return;
    var t = e.touches[0];
    if (!TD.on) { if (Math.abs(t.clientX - TD.sx) + Math.abs(t.clientY - TD.sy) > 10) { clearTimeout(TD.timer); TD = null; } return; }
    e.preventDefault();
    if (TD.ghost) TD.ghost.style.display = "none";
    var tg = tdTarget(t.clientX, t.clientY); if (TD.ghost) TD.ghost.style.display = "";
    moveGhost(t.clientX, t.clientY);
    document.querySelectorAll(".pe-card.dropL").forEach(function (c) { if (c !== tg) c.classList.remove("dropL"); });
    if (tg && tg !== TD.card) tg.classList.add("dropL");
    TD.tg = tg;
    var grid = $("pe-grid"), r = grid.getBoundingClientRect();   // gulir otomatis di tepi
    TD.vy = t.clientY < r.top + 60 ? -12 : t.clientY > r.bottom - 60 ? 12 : 0;
    if (TD.vy && !TD.scr) TD.scr = setInterval(function () { if (!TD || !TD.vy) return; grid.scrollTop += TD.vy; }, 16);
  }, { passive: false });
  function tdEnd() {
    if (!TD) return; var d = TD; TD = null; clearTimeout(d.timer); clearInterval(d.scr);
    if (!d.on) return;
    if (d.ghost) d.ghost.remove(); d.card.classList.remove("drag");
    document.querySelectorAll(".pe-card.dropL").forEach(function (c) { c.classList.remove("dropL"); });
    var tg = d.tg; if (!tg) return;
    var tid = tg.dataset.id, ids = d.ids;
    if (tid && ids.indexOf(tid) >= 0) return;
    pushUndo();
    var moving = PE.pages.filter(function (x) { return ids.indexOf(x.id) >= 0; });
    PE.pages = PE.pages.filter(function (x) { return ids.indexOf(x.id) < 0; });
    var at = tid ? PE.pages.findIndex(function (x) { return x.id === tid; }) : PE.pages.length;
    PE.pages.splice.apply(PE.pages, [at < 0 ? PE.pages.length : at, 0].concat(moving));
    PE.suppressClick = Date.now(); render();
  }
  document.addEventListener("touchend", tdEnd); document.addEventListener("touchcancel", tdEnd);

  function renderMerge(grid) {
    var F = PE.mfiles, hashes = {}, sizes = {};
    F.forEach(function (f) { var h = PE.docs[f.d].hash; hashes[h] = (hashes[h] || 0) + 1; var p0 = pagesOf(f)[0]; if (p0) { var D = dims(p0), k = Math.round(D.w) + "x" + Math.round(D.h); sizes[k] = (sizes[k] || 0) + 1; } });
    var common = Object.keys(sizes).sort(function (a, b) { return sizes[b] - sizes[a]; })[0];
    grid.innerHTML = '<div class="pe-mlist">' + F.map(function (f, i) {
      var all = pagesOf(f), r = parseRange(f.range, all.length), p0 = all[0], D = p0 ? dims(p0) : { w: 595, h: 842 }, sk = Math.round(D.w) + "x" + Math.round(D.h), mb = PE.docs[f.d].bytes.length;
      var warn = (hashes[PE.docs[f.d].hash] > 1 ? '<span class="w"><i class="fa-solid fa-clone"></i>Duplikat</span>' : "") + (sk !== common && !PE.mopt.a4 ? '<span class="w"><i class="fa-solid fa-ruler-combined"></i>Ukuran beda</span>' : "") + (r.bad ? '<span class="w r"><i class="fa-solid fa-triangle-exclamation"></i>Rentang salah: ' + E(r.bad) + "</span>" : "");
      return '<div class="pe-mf' + (SEEN.has("f" + f.d) ? "" : " new") + '" data-i="' + i + '" draggable="true"><span class="no">' + (i + 1) + '</span><span class="grip"><i class="fa-solid fa-grip-vertical"></i></span>'
        + '<div class="th"><img alt="" style="aspect-ratio:' + D.w + "/" + D.h + ";transform:rotate(" + f.rot + 'deg)"><span class="cnt">' + r.idx.length + (r.idx.length !== all.length ? "/" + all.length : "") + " hal</span></div>"
        + '<div class="info"><input class="nm" data-nm="' + i + '" value="' + E(f.name) + '" title="Nama file (dipakai sebagai judul bookmark)"><small>' + all.length + " halaman · " + Math.round(D.w * 0.3528) + "×" + Math.round(D.h * 0.3528) + " mm · " + MB(mb) + "</small>"
        + '<div class="rg"><input data-rg="' + i + '" value="' + E(f.range) + '" placeholder="Semua halaman"><button class="pe-b" data-pick="' + i + '" title="Pilih halaman secara visual"><i class="fa-regular fa-images"></i>Pilih</button></div>' + (warn ? '<div class="ws">' + warn + "</div>" : "") + "</div>"
        + '<div class="acts"><button class="pe-b" data-med="' + i + '" title="Edit isi file ini (teks, TTD, coretan…)"><i class="fa-solid fa-pen-to-square"></i>Edit</button><button class="pe-b" data-mv="' + i + '|-1" ' + (i ? "" : "disabled") + '><i class="fa-solid fa-arrow-up"></i>Naik</button><button class="pe-b" data-mv="' + i + '|1" ' + (i < F.length - 1 ? "" : "disabled") + '><i class="fa-solid fa-arrow-down"></i>Turun</button><button class="pe-b" data-rot="' + i + '" title="Putar semua halaman file ini"><i class="fa-solid fa-rotate-right"></i>Putar</button><button class="pe-b red" data-rm="' + i + '" title="Keluarkan dari gabungan"><i class="fa-solid fa-xmark"></i>Keluarkan</button></div></div>';
    }).join("") + '<label class="pe-madd" for="pe-in"><i class="fa-solid fa-plus"></i><span><b>Tambah file</b><small>PDF, JPG atau PNG — boleh beberapa sekaligus</small></span></label></div>';
    F.forEach(function (f) { SEEN.add("f" + f.d); });
    grid.querySelectorAll(".pe-mf").forEach(function (card) {
      var f = F[+card.dataset.i], p0 = pagesOf(f)[0], img = card.querySelector("img");
      if (p0) { var tk = thumbKey(p0); if (THUMB[tk]) img.src = THUMB[tk]; else thumb(p0, img); }
      card.ondragstart = function (e) { if (e.target.closest("input,button")) { e.preventDefault(); return; } PE.mdrag = +card.dataset.i; card.classList.add("drag"); try { e.dataTransfer.setData("text/plain", "m"); e.dataTransfer.effectAllowed = "move"; } catch (er) { } };
      card.ondragend = function () { PE.mdrag = null; card.classList.remove("drag"); grid.querySelectorAll(".dropT").forEach(function (c) { c.classList.remove("dropT"); }); };
      card.ondragover = function (e) { if (PE.mdrag == null) return; e.preventDefault(); grid.querySelectorAll(".dropT").forEach(function (c) { if (c !== card) c.classList.remove("dropT"); }); card.classList.add("dropT"); };
      card.ondrop = function (e) { if (PE.mdrag == null) return; e.preventDefault(); e.stopPropagation(); var from = PE.mdrag, to = +card.dataset.i; PE.mdrag = null; if (from === to) return; pushUndo(); var it = PE.mfiles.splice(from, 1)[0]; PE.mfiles.splice(to, 0, it); render(); };
    });
    grid.querySelectorAll("[data-nm]").forEach(function (inp) { inp.onchange = function () { pushUndo(); F[+inp.dataset.nm].name = safeName(inp.value) || F[+inp.dataset.nm].name; render(); }; });
    grid.querySelectorAll("[data-rg]").forEach(function (inp) { inp.onchange = function () { pushUndo(); F[+inp.dataset.rg].range = inp.value.replace(/\s+/g, ""); render(); }; inp.onkeydown = function (e) { if (e.key === "Enter") inp.blur(); }; });
    grid.querySelectorAll("[data-mv]").forEach(function (b) { b.onclick = function () { var a = b.dataset.mv.split("|"), i = +a[0], j = i + +a[1]; if (j < 0 || j >= F.length) return; pushUndo(); var t = F[i]; F[i] = F[j]; F[j] = t; render(); }; });
    grid.querySelectorAll("[data-rot]").forEach(function (b) { b.onclick = function () { pushUndo(); var f = F[+b.dataset.rot]; f.rot = (f.rot + 90) % 360; render(); }; });
    grid.querySelectorAll("[data-rm]").forEach(function (b) { b.onclick = function () { var f = F[+b.dataset.rm]; pushUndo(); PE.pages = PE.pages.filter(function (p) { return p.d !== f.d; }); PE.mfiles.splice(+b.dataset.rm, 1); render(); toast("\"" + f.name + "\" dikeluarkan — Urungkan untuk mengembalikan", "info"); }; });
    grid.querySelectorAll("[data-pick]").forEach(function (b) { b.onclick = function () { pickPages(F[+b.dataset.pick]); }; });
    grid.querySelectorAll("[data-med]").forEach(function (b) { b.onclick = function () { var f = F[+b.dataset.med], all = pagesOf(f), r = parseRange(f.range, all.length), p0 = all[r.idx[0] || 0]; if (p0) edOpen(p0.id); }; });
  }
  function pickPages(f) {
    var all = pagesOf(f), r = parseRange(f.range, all.length), on = new Set(r.idx);
    var m = modal('<i class="fa-regular fa-images" style="color:#7c3aed"></i> Pilih halaman · ' + E(f.name), '<div class="pe-pick-bar"><button class="pe-b" data-all>Semua</button><button class="pe-b" data-none>Kosongkan</button><button class="pe-b" data-odd>Ganjil</button><button class="pe-b" data-even>Genap</button><span id="pe-pick-n" style="margin-left:auto;font-weight:800"></span></div><div class="pe-pick" id="pe-pick"></div>', '<button class="pe-b" data-c>Batal</button><button class="pe-b pri" data-ok><i class="fa-solid fa-check"></i>Pakai pilihan</button>', 820);
    var box = m.querySelector("#pe-pick");
    box.innerHTML = all.map(function (p, i) { var D = dims(p); return '<button class="pe-pk" data-k="' + i + '"><img alt="" style="aspect-ratio:' + D.w + "/" + D.h + '"><span>' + (i + 1) + "</span><i class=\"fa-solid fa-check\"></i></button>"; }).join("");
    var sync = function () { box.querySelectorAll(".pe-pk").forEach(function (b) { b.classList.toggle("on", on.has(+b.dataset.k)); }); m.querySelector("#pe-pick-n").textContent = on.size + " / " + all.length + " halaman"; };
    box.querySelectorAll(".pe-pk").forEach(function (b) { var p = all[+b.dataset.k], im = b.querySelector("img"), tk = thumbKey(p); if (THUMB[tk]) im.src = THUMB[tk]; else thumb(p, im); b.onclick = function () { var k = +b.dataset.k; if (on.has(k)) on.delete(k); else on.add(k); sync(); }; });
    var setAll = function (fn) { on = new Set(); all.forEach(function (_, i) { if (fn(i)) on.add(i); }); sync(); };
    m.querySelector("[data-all]").onclick = function () { setAll(function () { return true; }); }; m.querySelector("[data-none]").onclick = function () { setAll(function () { return false; }); };
    m.querySelector("[data-odd]").onclick = function () { setAll(function (i) { return i % 2 === 0; }); }; m.querySelector("[data-even]").onclick = function () { setAll(function (i) { return i % 2 === 1; }); };
    m.querySelector("[data-c]").onclick = function () { m.remove(); };
    m.querySelector("[data-ok]").onclick = function () {
      if (!on.size) return toast("Pilih minimal 1 halaman", "error");
      var idx = Array.from(on).sort(function (a, b) { return a - b; }), parts = [], st = idx[0], pv = idx[0];
      for (var q = 1; q <= idx.length; q++) { if (idx[q] === pv + 1) { pv = idx[q]; continue; } parts.push(st === pv ? String(st + 1) : (st + 1) + "-" + (pv + 1)); st = pv = idx[q]; }
      pushUndo(); f.range = idx.length === all.length ? "" : parts.join(","); m.remove(); render();
    };
    sync();
  }
  function renderMergeOpts(box) {
    var O = PE.mopt, S = segs(), n = S[0] ? S[0].pages.length : 0, est = PE.mfiles.reduce(function (a, f) { var all = pagesOf(f), r = parseRange(f.range, all.length); return a + PE.docs[f.d].bytes.length * (all.length ? r.idx.length / all.length : 0); }, 0);
    var opt = function (k, t, sm, dis) { return '<label class="pe-tog' + (dis ? " dis" : "") + '"><input type="checkbox" data-o="' + k + '" ' + (O[k] ? "checked" : "") + (dis ? " disabled" : "") + '><span class="sw"></span><span><b>' + t + "</b><small>" + sm + "</small></span></label>"; };
    var warns = [];
    var hs = {}; PE.mfiles.forEach(function (f) { var h = PE.docs[f.d].hash; if (hs[h]) warns.push("\"" + f.name + "\" sama persis dengan \"" + hs[h] + "\""); else hs[h] = f.name; });
    PE.mfiles.forEach(function (f) { var r = parseRange(f.range, pagesOf(f).length); if (r.bad) warns.push("Rentang \"" + r.bad + "\" pada \"" + f.name + "\" tidak valid"); });
    if (n > MAX_PAGES) warns.push("Total " + n + " halaman melebihi batas " + MAX_PAGES);
    box.innerHTML = '<div class="pe-files-h"><b style="font-size:13px;font-weight:800">Hasil gabungan</b>'
      + '<div class="pe-msum"><div><b>' + PE.mfiles.length + "</b><small>file</small></div><div><b>" + n + "</b><small>halaman</small></div><div><b>±" + MB(est) + '</b><small>perkiraan</small></div></div>'
      + '<label style="font-weight:700;color:var(--pe-mute);font-size:11px">Nama file hasil</label><div class="pe-nm"><input id="pe-mname" value="' + E(nameOf({}, 1)) + '"><span>.pdf</span></div></div>'
      + '<div class="pe-files-l">'
      + opt("marks", "Bookmark per file", "Judul bookmark = nama file, memudahkan lompat antar dokumen")
      + opt("flatten", "Ratakan isian formulir", "Isian form jadi permanen & mencegah bentrok nama kolom antar file")
      + opt("a4", "Samakan ukuran ke A4", "Halaman beda ukuran (F4, Letter, foto) diskalakan rapi ke A4")
      + opt("blank", "Tiap file mulai di halaman ganjil", "Sisipkan halaman kosong bila perlu — rapi untuk cetak bolak-balik", O.inter)
      + opt("inter", "Selang-seling 2 file", "Untuk hasil scan depan & belakang terpisah: 1A, 1B, 2A, 2B…", PE.mfiles.length !== 2)
      + (O.inter ? opt("interRev", "Balik urutan file kedua", "Scanner biasanya menghasilkan sisi belakang dari halaman terakhir") : "")
      + (warns.length ? '<div class="pe-mwarn"><b><i class="fa-solid fa-triangle-exclamation"></i> Perlu dicek</b>' + warns.map(function (w) { return "<small>" + E(w) + "</small>"; }).join("") + "</div>" : "")
      + '<button class="pe-b pri pe-mgo" id="pe-mgo" ' + (n && n <= MAX_PAGES && !warns.some(function (w) { return /tidak valid|melebihi/.test(w); }) ? "" : "disabled") + '><i class="fa-solid fa-object-group"></i>Gabungkan &amp; unduh</button>'
      + '<button class="pe-b" id="pe-medit"><i class="fa-solid fa-pen-to-square"></i>Lanjut edit hasil gabungan</button></div>';
    box.querySelectorAll("[data-o]").forEach(function (c) { c.onchange = function () { pushUndo(); PE.mopt[c.dataset.o] = c.checked; if (c.dataset.o === "inter" && c.checked) PE.mopt.blank = false; render(); }; });
    var nm = box.querySelector("#pe-mname"); nm.onchange = function () { PE.mopt.outName = safeName(nm.value); render(); };
    box.querySelector("#pe-mgo").onclick = function () { dlOne(0); };
    box.querySelector("#pe-medit").onclick = function () { switchMode("edit"); toast("Hasil gabungan siap diedit", "success"); };
  }
  function renderFiles(S) {
    if (isMerge() && PE.pages.length) return renderMergeOpts($("pe-files"));
    var box = $("pe-files");
    if (!PE.pages.length) { box.innerHTML = '<div style="padding:16px;color:var(--pe-mute)">File hasil akan muncul di sini.</div>'; return; }
    var focusId = document.activeElement && document.activeElement.dataset ? document.activeElement.dataset.k : null, focusT = focusId ? document.activeElement.dataset.t : null;
    var names = finalNames(S), dup = {};
    S.forEach(function (s) { var k = safeName(nameOf(s, S.length)).toLowerCase(); dup[k] = (dup[k] || 0) + 1; });
    box.innerHTML = '<div class="pe-files-h"><div style="display:flex;align-items:center;gap:6px"><b style="font-size:13px;font-weight:800;flex:1">File hasil (' + S.length + ")</b>"
      + (S.length > 1 ? '<button class="pe-b" id="pe-zip" style="height:28px"><i class="fa-solid fa-file-zipper"></i>ZIP</button>' : "") + "</div>"
      + '<label style="font-weight:700;color:var(--pe-mute);font-size:11px">Pola nama (bebas, bisa pakai variabel)</label>'
      + '<div style="display:flex;gap:6px"><input id="pe-pat" value="' + E(defPattern(S.length)) + '" style="flex:1"><button class="pe-b" id="pe-pat-go" style="height:30px">Terapkan</button></div>'
      + '<div class="pe-vars">' + ["{nama}", "{no}", "{tanggal}", "{PO}", "{BAP}", "{SPK}", "{Stasiun}", "{Mitra}"].map(function (v) { return "<button data-v=\"" + v + "\">" + v + "</button>"; }).join("") + "</div></div>"
      + '<div class="pe-files-l">' + S.map(function (s, i) {
        var a = s.start + 1, b = s.start + s.pages.length, pr = PE.pairs[s.key], k = safeName(nameOf(s, S.length)).toLowerCase();
        return '<div class="pe-file' + (dup[k] > 1 ? " dup" : "") + '" style="--c:' + s.color + '" data-key="' + s.key + '">'
          + '<div class="pe-file-h"><b>File ' + s.no + "</b><small>" + s.pages.length + " hal · " + (a === b ? "hal " + a : "hal " + a + "–" + b) + '</small><span style="flex:1"></span>' + (PE.lock ? "" : '<button class="pe-b" data-fed="' + i + '" title="Edit isi file ini" style="height:26px;padding:0 8px"><i class="fa-solid fa-pen-to-square"></i>Edit</button>') + '<button class="pe-b" data-dl="' + i + '" title="Unduh file ini" style="height:26px;padding:0 8px"><i class="fa-solid fa-download"></i>Unduh</button></div>'
          + '<div class="pe-nm"><input data-k="' + s.key + '" data-t="nm" value="' + E(nameOf(s, S.length)) + '" placeholder="Nama file"><span>.pdf</span></div>'
          + (dup[k] > 1 ? '<small style="color:#d97706;font-weight:700"><i class="fa-solid fa-triangle-exclamation mr-1"></i>Nama sama dengan file lain — akan diberi akhiran (2)</small>' : "")
          + (pr ? '<div class="pe-pair">' + pairLabel(pr) + '<button class="x" data-unpair="' + s.key + '" title="Lepas"><i class="fa-solid fa-xmark"></i></button></div>'
            : '<div class="pe-sug"><input data-k="' + s.key + '" data-t="pr" placeholder="Pasangkan data: PO / No BAP / No SPK / stasiun…" style="width:100%"><div class="pe-sug-l hidden"></div></div>')
          + "</div>";
      }).join("") + "</div>";
    box.querySelectorAll('input[data-t="nm"]').forEach(function (inp) {
      inp.oninput = function () { PE.names[inp.dataset.k] = inp.value; };
      inp.onchange = function () { pushUndo(); PE.names[inp.dataset.k] = safeName(inp.value); render(); };
    });
    box.querySelectorAll('input[data-t="pr"]').forEach(function (inp) {
      bindSearch(inp, inp.nextElementSibling, function (g) {
        pushUndo(); PE.pairs[inp.dataset.k] = { mode: g.mode, key: g.key };
        if (PE.names[inp.dataset.k] == null && /\{(PO|BAP|SPK|Stasiun|Mitra)\}/i.test(defPattern(S.length))) { }
        render();
      });
    });
    box.querySelectorAll("[data-unpair]").forEach(function (b) { b.onclick = function () { pushUndo(); delete PE.pairs[b.dataset.unpair]; render(); }; });
    box.querySelectorAll("[data-dl]").forEach(function (b) { b.onclick = function () { dlOne(+b.dataset.dl); }; });
    box.querySelectorAll("[data-fed]").forEach(function (b) { b.onclick = function () { edOpen(S[+b.dataset.fed].pages[0].id); }; });
    box.querySelectorAll("[data-v]").forEach(function (b) { b.onclick = function () { var p = $("pe-pat"), s0 = p.selectionStart == null ? p.value.length : p.selectionStart; p.value = p.value.slice(0, s0) + b.dataset.v + p.value.slice(p.selectionEnd == null ? s0 : p.selectionEnd); p.focus(); }; });
    var go = function () { pushUndo(); PE.pattern = $("pe-pat").value.trim() || ""; S.forEach(function (s) { delete PE.names[s.key]; }); render(); toast("Pola nama diterapkan ke " + S.length + " file", "success"); };
    $("pe-pat-go").onclick = go; $("pe-pat").onkeydown = function (e) { if (e.key === "Enter") go(); };
    var z = $("pe-zip"); if (z) z.onclick = dlZip;
    if (focusId && focusT === "nm") { var f = box.querySelector('input[data-t="nm"][data-k="' + focusId + '"]'); if (f) { f.focus(); var l = f.value.length; f.setSelectionRange(l, l); } }
  }

  // ---------- aksi halaman ----------
  var selected = function () { return PE.pages.filter(function (p) { return PE.sel.has(p.id); }); };
  function rotOps(p, delta) {
    var steps = ((delta / 90) % 4 + 4) % 4;
    for (var s = 0; s < steps; s++) {
      var H = dims(p).h, f = function (x, y) { return [H - y, x]; };
      p.ops.forEach(function (o) {
        if (o.pts) o.pts = o.pts.map(function (q) { return f(q[0], q[1]); });
        if (o.x1 != null) { var a = f(o.x1, o.y1), b = f(o.x2, o.y2); o.x1 = a[0]; o.y1 = a[1]; o.x2 = b[0]; o.y2 = b[1]; }
        if (o.x != null && o.t !== "check") {
          if (o.t === "text" || o.t === "img") { var c = f(o.x + o.w / 2, o.y + o.h / 2); o.x = c[0] - o.w / 2; o.y = c[1] - o.h / 2; o.a = ((o.a || 0) + 90) % 360; }
          else { var p1 = f(o.x, o.y), p2 = f(o.x + o.w, o.y + o.h); o.x = Math.min(p1[0], p2[0]); o.y = Math.min(p1[1], p2[1]); o.w = Math.abs(p2[0] - p1[0]); o.h = Math.abs(p2[1] - p1[1]); }
        }
        if (o.t === "check") { var cc = f(o.x + o.w / 2, o.y + o.w / 2); o.x = cc[0] - o.w / 2; o.y = cc[1] - o.w / 2; }
      });
      p.rot = (p.rot + 90) % 360;
    }
  }
  function rotatePages(delta) { var L = selected(); if (!L.length) return; pushUndo(); L.forEach(function (p) { rotOps(p, delta); }); render(); }
  function dupPages() {
    var L = selected(); if (!L.length) return; pushUndo();
    var last = PE.pages.indexOf(L[L.length - 1]) + 1, cp = L.map(function (p) { var c = clone(p); c.id = "p" + (++PE.uid); return c; });
    PE.pages.splice.apply(PE.pages, [last, 0].concat(cp)); PE.sel = new Set(cp.map(function (p) { return p.id; })); render();
  }
  function delPages() {
    var L = selected(); if (!L.length) return;
    if (L.length >= PE.pages.length) return toast("Minimal 1 halaman harus tersisa", "error");
    pushUndo();
    L.forEach(function (p) {
      var i = PE.pages.indexOf(p);
      if (PE.cuts.has(p.id)) { PE.cuts.delete(p.id); var nx = PE.pages[i + 1]; if (nx && !PE.sel.has(nx.id)) PE.cuts.add(nx.id); }
      if (i === 0) { var nx2 = PE.pages[1]; if (nx2) { if (PE.names[p.id] != null && PE.names[nx2.id] == null) PE.names[nx2.id] = PE.names[p.id]; if (PE.pairs[p.id] && !PE.pairs[nx2.id]) PE.pairs[nx2.id] = PE.pairs[p.id]; PE.cuts.delete(nx2.id); } }
      PE.pages.splice(i, 1);
    });
    PE.sel.clear(); render();
  }
  function movePages(dir) {
    var L = selected(); if (!L.length) return; pushUndo();
    var arr = PE.pages.slice();
    if (dir < 0) { for (var i = 1; i < arr.length; i++) if (PE.sel.has(arr[i].id) && !PE.sel.has(arr[i - 1].id)) { var t = arr[i - 1]; arr[i - 1] = arr[i]; arr[i] = t; } }
    else { for (var j = arr.length - 2; j >= 0; j--) if (PE.sel.has(arr[j].id) && !PE.sel.has(arr[j + 1].id)) { var u = arr[j + 1]; arr[j + 1] = arr[j]; arr[j] = u; } }
    PE.pages = arr; render();
  }
  function splitRanges(txt) {
    var n = PE.pages.length, parts = String(txt || "").split(/[,;]+/).map(function (s) { return s.trim(); }).filter(Boolean), starts = [];
    if (!parts.length) return toast("Isi rentang halaman, mis. 1-3, 4, 5-8", "error");
    var used = [];
    for (var i = 0; i < parts.length; i++) {
      var m = parts[i].match(/^(\d+)\s*(?:-\s*(\d+))?$/);
      if (!m) return toast("Format salah: \"" + parts[i] + "\"", "error");
      var a = +m[1], b = m[2] ? +m[2] : a;
      if (a < 1 || b > n || a > b) return toast("Rentang \"" + parts[i] + "\" di luar 1–" + n, "error");
      for (var q = a; q <= b; q++) { if (used[q]) return toast("Halaman " + q + " dipakai dua kali", "error"); used[q] = 1; }
      starts.push({ a: a, b: b });
    }
    pushUndo();
    var keep = [];
    starts.forEach(function (r) { for (var q = r.a; q <= r.b; q++) keep.push(PE.pages[q - 1]); });
    var rest = PE.pages.filter(function (p) { return keep.indexOf(p) < 0; });
    PE.cuts = new Set(); var idx = 0;
    starts.forEach(function (r, k) { if (k) PE.cuts.add(keep[idx].id); idx += r.b - r.a + 1; });
    if (rest.length) {
      PE.pages = keep.concat(rest); PE.cuts.add(rest[0].id);
      toast(rest.length + " halaman di luar rentang dijadikan file terakhir — hapus bila tidak perlu", "info", 7000);
    } else PE.pages = keep;
    render();
  }
  async function viewPage(id) {
    var p = PE.pages.filter(function (x) { return x.id === id; })[0]; if (!p) return;
    var m = modal('<i class="fa-regular fa-file"></i> Halaman ' + (PE.pages.indexOf(p) + 1), '<div style="display:flex;justify-content:center"><i class="fa-solid fa-circle-notch fa-spin"></i></div>', "", 900);
    try { var w = Math.min(860, innerWidth - 60), c = await renderBase(p, w, Math.min(2, devicePixelRatio || 1)); drawOps(c.getContext("2d"), p.ops, c.width / dims(p).w); c.style.width = "100%"; c.style.maxWidth = w + "px"; c.style.boxShadow = "0 2px 12px #0003"; var bd = m.querySelector(".bd > div"); bd.innerHTML = ""; bd.appendChild(c); } catch (e) { m.querySelector(".bd").textContent = e.message; }
  }

  // ---------- menu, modal, proses ----------
  function closeMenus() { document.querySelectorAll(".pe-menu").forEach(function (m) { m.remove(); }); }
  function menu(anchor, items) {
    closeMenus();
    var m = document.createElement("div"); m.className = "pe-menu";
    m.innerHTML = items.filter(Boolean).map(function (it, i) { return '<button data-i="' + i + '" ' + (it.dis ? "disabled" : "") + '><i class="fa-solid ' + it.ic + '"></i><span>' + it.t + (it.s ? "<small>" + it.s + "</small>" : "") + "</span></button>"; }).join("");
    document.body.appendChild(m);
    var L = items.filter(Boolean);
    m.querySelectorAll("[data-i]").forEach(function (b) { b.onclick = function () { closeMenus(); L[+b.dataset.i].fn(); }; });
    var r = anchor.getBoundingClientRect();
    m.style.top = Math.min(innerHeight - m.offsetHeight - 8, r.bottom + 4) + "px";
    m.style.left = Math.max(8, Math.min(innerWidth - m.offsetWidth - 8, r.right - m.offsetWidth)) + "px";
    setTimeout(function () { document.addEventListener("click", function h(e) { if (!m.contains(e.target)) { m.remove(); document.removeEventListener("click", h, true); } }, true); }, 0);
  }
  function modal(title, body, foot, w) {
    var m = document.createElement("div"); m.className = "pe-modal";
    m.innerHTML = '<div class="box" style="' + (w ? "width:min(" + w + "px,100%)" : "") + '"><div class="hd"><b>' + title + '</b><button class="pe-b ic" data-x><i class="fa-solid fa-xmark"></i></button></div><div class="bd">' + body + "</div>" + (foot ? '<div class="fo">' + foot + "</div>" : "") + "</div>";
    ($("pe") || document.body).appendChild(m);
    m.querySelector("[data-x]").onclick = function () { if (!m.dataset.busy) m.remove(); };
    m.onclick = function (e) { if (e.target === m && !m.dataset.busy) m.remove(); };
    return m;
  }
  var BUSY = null;
  function busy(text, pct, mode) {
    if (text == null) { if (BUSY) { var b = BUSY; BUSY = null; b.classList.add("out"); setTimeout(function () { b.remove(); }, 180); } return; }
    mode = mode || (/unggah|kirim|simpan|drive|supabase/i.test(text) ? "send" : "read");
    if (!BUSY) {
      BUSY = document.createElement("div"); BUSY.className = "pe-busy";
      BUSY.innerHTML = '<div class="bx"><div class="pe-anim"><div class="pe-sheet s3"></div><div class="pe-sheet s2"></div><div class="pe-sheet s1"><i></i><i></i><i></i><i></i><b class="scan"></b></div>'
        + '<div class="pe-cloud"><svg viewBox="0 0 48 32"><path d="M14 30h22a10 10 0 0 0 1-20 13 13 0 0 0-25 3A8.5 8.5 0 0 0 14 30z" fill="#e0e7ff" stroke="#818cf8" stroke-width="2"/><path d="M24 25V14m-5 5l5-5 5 5" stroke="#4f46e5" stroke-width="2.6" fill="none" stroke-linecap="round" stroke-linejoin="round"/></svg></div></div>'
        + '<p class="tt"></p><div class="bar"><i></i></div><small class="pc"></small></div>';
      (PE.open && $("pe") ? $("pe") : document.body).appendChild(BUSY);
    }
    BUSY.dataset.mode = mode;
    BUSY.querySelector(".tt").textContent = text;
    if (pct != null) { var v = Math.max(2, Math.min(100, pct)); BUSY.querySelector(".bar i").style.width = v + "%"; BUSY.querySelector(".pc").textContent = Math.round(v) + "%"; }
  }
  function saveBlob(bytes, name, type) { var u = URL.createObjectURL(new Blob([bytes], { type: type || "application/pdf" })), a = document.createElement("a"); a.href = u; a.download = name; document.body.appendChild(a); a.click(); a.remove(); setTimeout(function () { URL.revokeObjectURL(u); }, 30000); }

  async function buildAll(prefix) {
    var S = segs(), names = finalNames(S), out = [], total = PE.pages.length, done = 0;
    for (var i = 0; i < S.length; i++) {
      out.push({ seg: S[i], name: names[i] + ".pdf", bytes: await buildPdf(S[i].pages, names[i], function () { done++; busy((prefix || "Menyusun PDF") + "… " + done + "/" + total + " hal", done / total * 100); }) });
    }
    return out;
  }
  async function dlOne(i) {
    var S = segs(), s = S[i], nm = finalNames(S)[i];
    busy("Menyusun " + nm + "…", 10);
    try { var b0 = await buildPdf(s.pages, nm, function (a, b) { busy("Menyusun " + nm + "… " + a + "/" + b, a / b * 100); }); if (PE.pw) busy("Mengunci dengan password…", 98); saveBlob(await finalPdf(b0), nm + ".pdf"); dlNote(); } catch (e) { toast("Gagal: " + e.message, "error", 8000); }
    busy(null);
  }
  async function dlZip() {
    busy("Menyusun PDF…", 3);
    try {
      var files = await buildAll();
      if (PE.pw) { busy("Mengunci dengan password…", 95); for (var fi = 0; fi < files.length; fi++) files[fi].bytes = await finalPdf(files[fi].bytes); }
      if (files.length === 1) { saveBlob(files[0].bytes, files[0].name); }
      else {
        busy("Membuat ZIP…", 96);
        await loadJs("https://cdnjs.cloudflare.com/ajax/libs/jszip/3.10.1/jszip.min.js");
        var z = new window.JSZip(); files.forEach(function (f) { z.file(f.name, f.bytes); });
        saveBlob(await z.generateAsync({ type: "uint8array" }), safeName(PE.base) + " (" + files.length + " file).zip", "application/zip");
      }
    } catch (e) { toast("Gagal: " + e.message, "error", 8000); }
    busy(null);
  }
  async function dlMerged() {
    busy("Menyusun PDF…", 5);
    try { saveBlob(await finalPdf(await buildPdf(PE.pages, PE.base, function (a, b) { busy("Menyusun PDF… " + a + "/" + b, a / b * 100); })), safeName(PE.base) + ".pdf"); dlNote(); } catch (e) { toast("Gagal: " + e.message, "error", 8000); }
    busy(null);
  }
  function dlNote() { if (LASTCMP && PE.comp && LASTCMP.after < LASTCMP.before) toast("Dikompres: " + MB(LASTCMP.before) + " → " + MB(LASTCMP.after) + (PE.pw ? " · dikunci password" : ""), "success", 5000); else if (PE.pw) toast("File diunduh terkunci password", "success"); LASTCMP = null; }
  function dlMenu(a) {
    var S = segs(), one = isEdit() || isMerge() || S.length < 2;
    menu(a, [
      one ? { ic: "fa-file-pdf", t: "Unduh PDF", s: finalNames(S)[0] + ".pdf", fn: function () { dlOne(0); } } : { ic: "fa-file-zipper", t: "Unduh semua (ZIP)", s: S.length + " file hasil pecah", fn: dlZip },
      one ? null : { ic: "fa-file-pdf", t: "Unduh digabung jadi 1 PDF", s: "semua halaman, tanpa pecahan", fn: dlMerged },
      { ic: "fa-compress", t: "Kompres PDF", s: PE.comp ? "aktif · " + COMP[PE.comp].t : "perkecil ukuran file", fn: compModal },
      { ic: "fa-lock", t: "Kunci dengan password", s: PE.pw ? "aktif untuk unduhan" : "lindungi file yang diunduh", fn: pwModal },
      { ic: "fa-file-image", t: "Unduh sebagai gambar", s: "JPG / PNG per halaman", fn: imgModal },
      { ic: "fa-file-word", t: "Unduh sebagai Word (.docx)", s: "teks bisa diedit / tampilan persis", fn: docxModal },
      { ic: "fa-file-excel", t: "Unduh sebagai Excel (.xlsx)", s: "tabel & angka per halaman", fn: exportXlsx }
    ]);
  }
  function sendMenu(a) {
    var o = PE.origin;
    if (isMerge()) return menu(a, [
      { ic: "fa-download", t: "Gabungkan & unduh", s: nameOf({}, 1) + ".pdf", fn: function () { dlOne(0); } },
      { ic: "fa-cloud-arrow-up", t: "Submit PDF…", s: "pasangkan ke PO / BAP / SPK + jenis dokumen", fn: submitMass, dis: !(typeof canUpload === "function" ? canUpload() : true) },
      { ic: "fa-file-signature", t: "Kirim ke Signing Document", s: "minta tanda tangan untuk hasil gabungan", fn: toSigning, dis: !(typeof can === "function" && can("sirkulir")) },
      { ic: "fa-pen-to-square", t: "Lanjut edit", s: "edit teks, TTD & stempel di hasil gabungan", fn: function () { switchMode("edit"); } }
    ]);
    if (isEdit()) return menu(a, [
      o.kind === "mig" ? { ic: "fa-floppy-disk", t: "Simpan sebagai BA pengajuan", s: "ganti BA di sheet Migrasi IKR (kolom M) · BA lama tetap di Drive", fn: backToForm } : null,
      o.kind === "submit" ? { ic: "fa-arrow-turn-down", t: "Pakai di form Submit PDF", s: "kembali ke form dengan PDF hasil edit", fn: backToForm } : null,
      o.kind === "sgw" ? { ic: "fa-arrow-turn-down", t: "Pakai di Signing Document", s: "kembali ke langkah unggah", fn: backToForm } : null,
      { ic: "fa-cloud-arrow-up", t: "Submit PDF…", s: "pasangkan ke PO / BAP / SPK + jenis dokumen", fn: submitMass, dis: !(typeof canUpload === "function" ? canUpload() : true) },
      o.kind === "sgw" ? null : { ic: "fa-file-signature", t: "Kirim ke Signing Document", s: "buat permintaan tanda tangan dari PDF ini", fn: toSigning, dis: !(typeof can === "function" && can("sirkulir")) }
    ]);
    menu(a, [
      o.kind === "mig" ? { ic: "fa-floppy-disk", t: "Simpan sebagai BA pengajuan", s: "semua halaman digabung jadi 1 file", fn: backToForm } : null,
      o.kind === "submit" ? { ic: "fa-arrow-turn-down", t: "Pakai di form Submit PDF", s: "semua halaman digabung jadi 1 file", fn: backToForm } : null,
      o.kind === "sgw" ? { ic: "fa-arrow-turn-down", t: "Pakai di Signing Document", s: "semua halaman digabung jadi 1 file", fn: backToForm } : null,
      o.kind === "signing" ? { ic: "fa-brands fa-google-drive", t: "Simpan ke Drive…", s: "pilih: file utuh atau file hasil pecah", fn: driveSave } : null,
      { ic: "fa-cloud-arrow-up", t: "Submit PDF massal…", s: "tiap file → PO / BAP / SPK + jenis dokumen", fn: submitMass, dis: !(typeof canUpload === "function" ? canUpload() : true) }
    ]);
  }

  async function toSigning() {
    var S0 = segs(), nm = isMerge() ? finalNames(S0)[0] : safeName(PE.base) || "Dokumen";
    busy("Menyusun PDF…", 5);
    try {
      var bytes = await buildPdf(isMerge() ? S0[0].pages : PE.pages, nm, function (a, b) { busy("Menyusun PDF… " + a + "/" + b, a / b * 100); });
      var file = new File([bytes], nm + ".pdf", { type: "application/pdf" });
      busy(null); peClose(true);
      try { switchTab("sirkulir"); } catch (e) { }
      setTimeout(function () { try { sgNew(); setTimeout(function () { sgPickPdf(file); }, 120); toast("PDF hasil edit siap ditandatangani — lanjutkan isi penanda tangan", "success"); } catch (e) { toast("Gagal membuka Signing: " + e.message, "error"); } }, 300);
    } catch (e) { busy(null); toast("Gagal: " + e.message, "error", 8000); }
  }
  // ---------- kembali ke form (Rapikan PDF) ----------
  async function backToForm() {
    var nm = safeName(PE.base) || "Dokumen";
    busy("Menyusun PDF…", 5);
    try {
      var bytes = await buildPdf(PE.pages, nm, function (a, b) { busy("Menyusun PDF… " + a + "/" + b, a / b * 100); });
      var file = new File([bytes], nm + ".pdf", { type: "application/pdf" });
      busy(null);
      var k = PE.origin.kind; peClose(true);
      if (k === "submit") { if (typeof onUpFile === "function") onUpFile([file]); toast("PDF hasil rapikan dipakai di form Submit", "success"); }
      else if (k === "sgw") { if (typeof sgPickPdf === "function") sgPickPdf(file); toast("PDF hasil rapikan dipakai di Signing Document", "success"); }
      else if (k === "mig" && typeof window.__migBaSave === "function") window.__migBaSave(file, PE.origin.id);
    } catch (e) { busy(null); toast("Gagal: " + e.message, "error", 8000); }
  }

  // ---------- Submit PDF massal ----------
  function upTypes() { return ((typeof DOC_TYPES !== "undefined" && DOC_TYPES) || []).filter(function (t) { try { return can("up_" + t.key); } catch (e) { return true; } }); }
  function submitMass() {
    var S = segs(), names = finalNames(S), types = upTypes();
    if (!types.length) return toast("Akun Anda tidak memiliki akses Submit PDF", "error");
    var guess = function (nm) { var n = String(nm).toUpperCase(); return /BASTM|SERAH TERIMA/.test(n) ? "BASTM" : /CANCEL/.test(n) && !/BAP/.test(n) ? "BA_CANCEL" : /BAP/.test(n) ? "BAP_PO" : ""; };
    var T = S.map(function (s, i) { return { s: s, name: names[i], type: guess(names[i]), st: "" }; });
    var m = modal('<i class="fa-solid fa-cloud-arrow-up" style="color:#059669"></i> ' + (isEdit() ? "Submit PDF" : "Submit PDF massal · " + S.length + " file"),
      '<p style="color:var(--pe-mute);font-size:11.5px">Setiap file diunggah ke Google Drive (folder per No SPK / No BAP / PO) dan link-nya masuk ke kolom jenis dokumen di Data Mitra Takeover; status otomatis Done.</p><div id="pe-sm-l" style="display:flex;flex-direction:column;gap:8px"></div>',
      '<button class="pe-b" data-c>Batal</button><button class="pe-b pri" id="pe-sm-go"><i class="fa-solid fa-paper-plane"></i>Kirim semua</button>', 860);
    m.querySelector("[data-c]").onclick = function () { if (!m.dataset.busy) m.remove(); };
    var draw = function () {
      var L = m.querySelector("#pe-sm-l");
      L.innerHTML = T.map(function (r, i) {
        var pr = PE.pairs[r.s.key];
        return '<div class="pe-row" style="border-left:4px solid ' + r.s.color + '"><div><b style="font-weight:800">' + E(r.name) + '.pdf</b><br><small style="color:var(--pe-mute)">' + r.s.pages.length + " halaman</small></div>"
          + "<div>" + (pr ? '<div class="pe-pair">' + pairLabel(pr) + '<button class="x" data-up="' + i + '"><i class="fa-solid fa-xmark"></i></button></div>' : '<div class="pe-sug"><input data-q="' + i + '" placeholder="Cari PO / No BAP / No SPK…" style="width:100%"><div class="pe-sug-l hidden"></div></div>') + "</div>"
          + '<select data-ty="' + i + '"><option value="">Jenis dokumen…</option>' + types.map(function (t) { return '<option value="' + t.key + '" ' + (r.type === t.key ? "selected" : "") + ">" + E(t.label) + "</option>"; }).join("") + "</select>"
          + '<div class="st" data-st="' + i + '">' + (r.st || "") + "</div></div>";
      }).join("");
      L.querySelectorAll("[data-q]").forEach(function (inp) { bindSearch(inp, inp.nextElementSibling, function (g) { PE.pairs[T[+inp.dataset.q].s.key] = { mode: g.mode, key: g.key }; draw(); render(); }); });
      L.querySelectorAll("[data-up]").forEach(function (b) { b.onclick = function () { delete PE.pairs[T[+b.dataset.up].s.key]; draw(); render(); }; });
      L.querySelectorAll("[data-ty]").forEach(function (s) { s.onchange = function () { T[+s.dataset.ty].type = s.value; }; });
    };
    draw();
    m.querySelector("#pe-sm-go").onclick = async function () {
      var bad = T.filter(function (r) { return !r.done && (!PE.pairs[r.s.key] || !r.type || !pairRows(PE.pairs[r.s.key]).length); });
      if (bad.length) return toast("Lengkapi pasangan data & jenis dokumen untuk semua file (" + bad.length + " belum)", "error", 6000);
      var go = this; go.disabled = true; m.dataset.busy = 1;
      var ok = 0, fail = 0, lim = (typeof BACKEND !== "undefined" && BACKEND.MAX_MB) || 20, inflight = [];
      var stOf = function (i) { return function (h) { T[i].st = h; var el = m.querySelector('[data-st="' + i + '"]'); if (el) el.innerHTML = h; }; };
      var failed = function (i, e) { fail++; T[i].err = e.message; stOf(i)('<span style="color:#e11d48" title="' + E(e.message) + '"><i class="fa-solid fa-circle-xmark"></i> gagal</span><br><small style="color:#e11d48;font-weight:600">' + E(e.message).slice(0, 90) + "</small>"); };
      for (var i = 0; i < T.length; i++) {
        var r = T[i]; if (r.done) { ok++; continue; }
        var st = stOf(i); r.err = "";
        st('<i class="fa-solid fa-circle-notch fa-spin"></i> menyusun');
        var bytes;
        try { bytes = await buildSized(r.s.pages, r.name, lim); } catch (e) { failed(i, e); continue; }
        while (inflight.length >= 2) await Promise.race(inflight);   // maksimal 2 unggahan bersamaan
        st('<i class="fa-solid fa-circle-notch fa-spin"></i> mengirim · ' + MB(bytes.length));
        (function (i, r, bytes) {
          var job = uploadOne(PE.pairs[r.s.key], r.type, r.name + ".pdf", bytes).then(function (res) { r.done = true; ok++; stOf(i)('<a href="' + E(res.url) + '" target="_blank" rel="noopener" style="color:#059669"><i class="fa-solid fa-circle-check"></i> terkirim</a>'); }, function (e) { failed(i, e); })
            .then(function () { var k = inflight.indexOf(job); if (k >= 0) inflight.splice(k, 1); });
          inflight.push(job);
        })(i, r, bytes);
      }
      await Promise.all(inflight);
      delete m.dataset.busy; go.disabled = false;
      try { renderDashboard(); saveSnapshot(); applyDocFilters(false); applyTakeoverFilters(false); } catch (e) { }
      if (fail) { go.innerHTML = '<i class="fa-solid fa-rotate"></i>Ulangi yang gagal (' + fail + ")"; toast(ok + " terkirim, " + fail + " gagal: " + (T.filter(function (r) { return r.err && !r.done; })[0] || {}).err, "error", 9000); }
      else { go.outerHTML = '<button class="pe-b pri" data-ok><i class="fa-solid fa-check"></i>Selesai</button>'; m.querySelector("[data-ok]").onclick = function () { m.remove(); }; toast("Semua " + ok + " file terkirim ke Submit PDF", "success", 7000); }
    };
  }
  async function uploadOne(pr, type, fileName, bytes) {
    var rows = pairRows(pr), t = rows[0], D = DOC[type];
    if (!t || !D) throw new Error("Data tidak ditemukan");
    var body = { noSpk: pr.mode === "spk" ? t.att_spk : "", noBap: pr.mode === "bap" ? t.bap_no : "", poKey: pr.mode === "po" ? t.po : "", docType: type, po: t.po, stasiun: t.stasiun, mitra: t.after, fileName: fileName, fileBase64: bytesToB64(bytes), uploader: currentUser ? currentUser.name : "-" };
    var r;
    try { r = await callApi("upload", body, 3e5); } catch (e) { if (/login|akses|dinonaktifkan/i.test(e.message)) throw e; r = await callApi("upload", body, 3e5); }
    if (!r || !r.ok) throw new Error((r && r.error) || "Upload gagal");
    rows.forEach(function (e) {
      try {
        e.links || (e.links = []); e.links[D.col - CONFIG.LINK_COLS.startIndex] = r.url;
        if (emp(e[D.field])) e[D.field] = r.cellText || r.fileName;
        if (D.statusField && r.statusValue && !isDone(e[D.statusField]) && !isCancel(e[D.statusField])) e[D.statusField] = r.statusValue;
        e.st = computeStatus(e.k, e.l, e.m, e.status_to);
      } catch (er) { }
    });
    try { UP.history.unshift({ time: new Date(), spk: MODE[pr.mode] + " " + pr.key, type: D.label, name: r.fileName, url: r.url, folder: r.folderUrl, rows: r.rows }); } catch (e) { }
    return r;
  }

  // ---------- Signing Selesai → simpan ke Drive ----------
  function driveSave() {
    var S = segs(), names = finalNames(S), choice = S.length > 1 ? "split" : "whole";
    var m = modal('<i class="fa-brands fa-google-drive" style="color:#0f9d58"></i> Simpan ke Drive',
      '<p style="color:var(--pe-mute);font-size:11.5px">Dokumen: <b>' + E(PE.base) + "</b> · " + PE.pages.length + " halaman → " + S.length + " file</p>"
      + '<label class="pe-opt" data-o="whole"><input type="radio" name="pe-o" value="whole"><span><b class="ot">File utuh</b><small>Drive tidak berubah. Hasil pecah cukup diunduh atau di-Submit.</small></span></label>'
      + '<label class="pe-opt" data-o="split"><input type="radio" name="pe-o" value="split"><span><b class="ot">File hasil pecah</b><small>' + S.length + ' file disimpan ke folder <b>Hasil Split</b> di Drive dengan nama custom. File utuh tidak dihapus, dipindah ke subfolder <b>Asli</b> sebagai bukti TTD.</small></span></label>'
      + '<div id="pe-ds-names" style="font-size:11px;color:var(--pe-mute)">' + names.map(function (n, i) { return '<div><span style="color:' + S[i].color + '">●</span> ' + E(n) + ".pdf · " + S[i].pages.length + " hal</div>"; }).join("") + "</div>"
      + '<div id="pe-ds-res" class="pe-res"></div>',
      '<button class="pe-b" data-c>Batal</button><button class="pe-b pri" id="pe-ds-go"><i class="fa-solid fa-floppy-disk"></i>Simpan</button>', 560);
    var set = function (v) { choice = v; m.querySelectorAll(".pe-opt").forEach(function (o) { o.classList.toggle("on", o.dataset.o === v); o.querySelector("input").checked = o.dataset.o === v; }); m.querySelector("#pe-ds-names").style.display = v === "split" ? "" : "none"; };
    m.querySelectorAll(".pe-opt").forEach(function (o) { o.onclick = function () { set(o.dataset.o); }; });
    set(choice);
    m.querySelector("[data-c]").onclick = function () { if (!m.dataset.busy) m.remove(); };
    m.querySelector("#pe-ds-go").onclick = async function () {
      if (choice === "whole") { m.remove(); toast("File utuh tetap di Drive tanpa perubahan", "info"); return; }
      if (S.length < 2) return toast("Pecah dokumen dulu menjadi 2 file atau lebih", "error");
      var go = this; go.disabled = true; m.dataset.busy = 1;
      try {
        var files = await buildAll("Menyusun file hasil pecah");
        var big = files.filter(function (f) { return f.bytes.length > 45 * 1048576; })[0];
        if (big) throw new Error(big.name + " " + MB(big.bytes.length) + " — terlalu besar (maks 45 MB per file)");
        var r = await saveSplit(PE.origin.id, files);
        busy(null);
        try { if (r.doc && typeof sgUpsert === "function") sgUpsert(r.doc); } catch (e) { }
        m.querySelector("#pe-ds-res").innerHTML = '<div style="padding:10px;border-radius:10px;background:#10b98118"><b style="color:#059669"><i class="fa-solid fa-circle-check"></i> ' + (r.splits || []).length + ' file tersimpan di Drive</b>' + (r.via === "supabase" ? ' <small style="color:var(--pe-mute)">· dibantu Supabase</small>' : "") + '<br><a href="' + E(r.folderUrl) + '" target="_blank" rel="noopener">Buka folder hasil split</a> · file utuh ada di subfolder <b>Asli</b></div>';
        go.outerHTML = '<button class="pe-b pri" data-ok><i class="fa-solid fa-check"></i>Selesai</button>';
        m.querySelector("[data-ok]").onclick = function () { m.remove(); };
        toast("Hasil split tersimpan di Drive", "success", 7000);
      } catch (e) { busy(null); go.disabled = false; toast("Gagal menyimpan: " + e.message, "error", 9000); }
      delete m.dataset.busy;
    };
  }
  async function saveSplit(id, files) {
    var list = files.map(function (f, i) { return { name: f.name, path: (i + 1) + ".pdf" }; }), ticket = "", via = "direct";
    // 1) unggah paralel ke Supabase Storage (sementara) → Apps Script menarik ke Drive server-ke-server
    try {
      if (typeof sbOn === "function" && sbOn() && typeof sbOwner === "function") {
        busy("Menyiapkan unggahan…", 5);
        var tk = await sbOwner("sg_split_ticket", {}, 3e4); ticket = tk.ticket;
        var done = 0, total = files.length, base = SB.url + "/storage/v1/object/sg-split/" + encodeURIComponent(ticket) + "/";
        var h = { apikey: SB.key, "Content-Type": "application/pdf", "x-upsert": "true" }; if (/^eyJ/.test(SB.key)) h.Authorization = "Bearer " + SB.key;
        var put = async function (i) { var res = await fetch(base + list[i].path, { method: "POST", headers: h, body: files[i].bytes }); if (!res.ok) { var t = ""; try { t = (await res.json()).message || ""; } catch (e) { } throw new Error("Storage " + res.status + " " + t); } done++; busy("Mengunggah ke Supabase… " + done + "/" + total, 10 + 60 * done / total); };
        var q = files.map(function (f, i) { return i; }), workers = [];
        for (var w = 0; w < Math.min(4, q.length); w++) workers.push((async function () { while (q.length) await put(q.shift()); })());
        await Promise.all(workers);
        via = "supabase";
      }
    } catch (e) { console.warn("Supabase Storage tidak dipakai:", e.message); ticket = ""; via = "direct"; }
    busy("Menyimpan ke Google Drive…", 75);
    var body = { id: id, files: list.map(function (f, i) { return via === "supabase" ? { name: f.name, path: f.path } : { name: f.name, b64: bytesToB64(files[i].bytes) }; }) };
    if (via === "supabase") body.ticket = ticket;
    var r;
    try { r = await callApi("sign.split", body, 36e4); if (!r || !r.ok) throw new Error((r && r.error) || "Gagal menyimpan"); }
    catch (e) {
      if (via === "supabase") { try { var hd = { apikey: SB.key, "Content-Type": "application/json" }; if (/^eyJ/.test(SB.key)) hd.Authorization = "Bearer " + SB.key; fetch(SB.url + "/storage/v1/object/sg-split", { method: "DELETE", headers: hd, body: JSON.stringify({ prefixes: list.map(function (f) { return ticket + "/" + f.path; }) }) }); } catch (er) { } }
      throw e;
    }
    r.via = via;
    return r;
  }

  // ===================== deteksi teks asli (seperti Nitro Pro) =====================
  var TXT = {}, TXTI = {}, OCR = {};
  function mapFont(name, fam) {
    var n = String(name || "").replace(/^[A-Z]{6}\+/, ""), f = String(fam || "");
    var k = /courier|mono|consol|lucida ?console/i.test(n) || /monospace/i.test(f) ? "Courier"
      : /calibri|carlito/i.test(n) ? "Carlito"
      : /roboto/i.test(n) ? "Roboto" : /open ?sans/i.test(n) ? "Open Sans" : /poppins/i.test(n) ? "Poppins"
      : /times|serif|roman|garamond|georgia|cambria|book ?antiqua|palatino|minion/i.test(n) && !/sans/i.test(n) || (/serif/i.test(f) && !/sans/i.test(f)) ? "Times"
      : /arimo|liberation ?sans/i.test(n) ? "Arimo" : "Helvetica";
    return { font: k, b: /bold|black|heavy|semibold|demi|,bold/i.test(n), i: /italic|oblique|,italic/i.test(n) };
  }
  var pkey = function (p) { return p.d + ":" + p.i + ":" + dims(p).t; };
  // teks asli PDF; bila halaman hasil scan sudah di-OCR → pakai hasil OCR
  async function pageLines(p) { var nat = await nativeLines(p), k = pkey(p); return !nat.length && OCR[k] ? OCR[k] : nat; }
  async function nativeLines(p) {
    var D = dims(p), key = p.d + ":" + p.i + ":" + D.t;
    if (TXT[key]) return TXT[key];
    var L = await loadPdfJs(), doc = await jsDoc(p.d), pg = await doc.getPage(p.i + 1);
    var vp = pg.getViewport({ scale: 1, rotation: D.t }), tc = await pg.getTextContent(), items = [];
    tc.items.forEach(function (it) {
      if (!it.str || !it.str.trim()) return;
      var tx = L.Util.transform(vp.transform, it.transform), size = Math.hypot(tx[2], tx[3]);
      if (size < 3 || Math.abs(Math.atan2(tx[1], tx[0])) > 0.04) return;   // hanya teks mendatar
      var st = tc.styles[it.fontName] || {}, asc = st.ascent || 0.8, desc = st.descent || -0.2, fo = null;
      try { if (pg.commonObjs.has(it.fontName)) fo = pg.commonObjs.get(it.fontName); } catch (e) { }
      var mf = mapFont(fo && fo.name, st.fontFamily); if (fo && fo.bold) mf.b = true; if (fo && fo.italic) mf.i = true;
      items.push({ x: tx[4], base: tx[5], w: Math.max(1, it.width), size: size, asc: asc, desc: desc, str: it.str, mf: mf });
    });
    items.sort(function (a, b) { return Math.abs(a.base - b.base) > Math.min(a.size, b.size) * 0.3 ? a.base - b.base : a.x - b.x; });
    TXTI[key] = items.map(function (it) { return { x: it.x, base: it.base, w: it.w, size: it.size, str: it.str }; });
    var lines = [], cur = null;
    items.forEach(function (it) {
      var gap = cur ? it.x - (cur.x + cur.w) : 0;
      if (cur && Math.abs(it.base - cur.base) < Math.min(it.size, cur.size) * 0.3 && Math.abs(it.size - cur.size) < cur.size * 0.2 && gap < cur.size * 0.9 && gap > -cur.size * 0.5) {
        cur.str += (gap > cur.size * 0.18 && !/\s$/.test(cur.str) && !/^\s/.test(it.str) ? " " : "") + it.str;
        cur.w = Math.max(cur.w, it.x + it.w - cur.x);
      } else { cur = { x: it.x, base: it.base, w: it.w, size: it.size, asc: it.asc, desc: it.desc, str: it.str, mf: it.mf }; lines.push(cur); }
    });
    lines.forEach(function (l, i) { l.key = key + "#" + i; l.str = l.str.replace(/\s+/g, " ").trim(); l.top = l.base - l.size * Math.min(1, l.asc); l.h = l.size * (Math.min(1, l.asc) - Math.max(-0.35, l.desc)); });
    TXT[key] = lines.filter(function (l) { return l.str; });
    return TXT[key];
  }
  function inkColor(l, cv, DD) {
    var c = cv || ED.base; if (!c) return "#000000";
    try {
      var s = c.width / (DD || dims(edPage())).w, x0 = Math.max(0, Math.floor(l.x * s)), y0 = Math.max(0, Math.floor(l.top * s)), w = Math.max(1, Math.min(c.width - x0, Math.ceil(l.w * s))), h = Math.max(1, Math.min(c.height - y0, Math.ceil(l.h * s)));
      var d = c.getContext("2d").getImageData(x0, y0, w, h).data, min = 999, px = [];
      for (var i = 0; i < d.length; i += 4) { var lum = 0.3 * d[i] + 0.59 * d[i + 1] + 0.11 * d[i + 2]; px.push(lum); if (lum < min) min = lum; }
      var acc = [0, 0, 0], n = 0;
      for (var j = 0, q = 0; j < d.length; j += 4, q++) if (px[q] <= min + 12) { acc[0] += d[j]; acc[1] += d[j + 1]; acc[2] += d[j + 2]; n++; }
      if (!n || min > 200) return "#000000";
      if (Math.max(acc[0], acc[1], acc[2]) / n < 70) return "#000000";   // abu sangat gelap = hitam (efek anti-alias)
      return "#" + acc.map(function (v) { return ("0" + Math.round(v / n).toString(16)).slice(-2); }).join("");
    } catch (e) { return "#000000"; }
  }
  // kotak teks hasil edit melebar mengikuti isi (seperti Nitro), baru membungkus di tepi halaman
  function fitW(o, pp) {
    var p = pp || edPage(), D = p ? dims(p) : { w: 9999 };
    MC.font = cssFont(o, 1);
    var widest = String(o.text || "").split("\n").reduce(function (m, ln) { return Math.max(m, MC.measureText(ln).width); }, 0);
    o.w = Math.max(o.minW || 20, Math.min(widest + PAD * 2 + 2, D.w - o.x - 2));
    o.h = textH(o);
  }
  function lineAt(pt) { var L = ED.lines || [], tol = 2 / ED.k; for (var i = 0; i < L.length; i++) { var l = L[i]; if (pt.x >= l.x - tol && pt.x <= l.x + l.w + tol && pt.y >= l.top - tol && pt.y <= l.top + l.h + tol) return l; } return null; }
  // satu baris teks asli → [penutup, kotak teks baru] (font, ukuran, warna & latar disamakan)
  async function lineOps(p, l, txt, cv, DD) {
    var f = fontOf(l.mf.font); await webFont(f, l.mf.b, l.mf.i);
    var size = Math.round(l.size * 2) / 2, bg = sampleBg({ x: l.x - 1, y: l.top - 1, w: l.w + 2, h: l.h + 2 }, cv, DD), col = inkColor(l, cv, DD);
    var t = { t: "text", x: l.x - PAD, y: 0, w: 10, text: txt, font: l.mf.font, size: size, b: l.mf.b, i: l.mf.i, u: false, al: "l", c: col, bg: "", op: 1, a: 0, src: l.key, orig: l.str };
    t.y = l.base - baseY(t, 0);
    t.autoW = true; t.minW = l.w + PAD * 2; fitW(t, p);
    var cover = ED.st.tmode === "perm" ? { t: "erase", fill: "auto", col: bg } : { t: "mask", col: bg };
    Object.assign(cover, { x: l.x - 1.5, y: l.top - 1.5, w: l.w + 3, h: l.h + 3, key: l.key });
    return [cover, t];
  }
  async function editLine(l) {
    var p = edPage(); if (!p) return;
    var done = p.ops.filter(function (o) { return o.t === "text" && o.src === l.key; })[0];
    if (done) { ED.sel = done; edProps(); edText(done); return; }
    var two = await lineOps(p, l, l.str), t = two[1];
    pushUndo(); p.ops.push(two[0], t); ED.sel = t; edProps(); edText(t, false, true); renderSoon();
  }

  // ===================== deteksi tanda tangan & stempel =====================
  // 1) gambar yang tertanam di PDF (TTD/stempel digital, hasil Signing) lewat daftar operator pdf.js
  // 2) tinta berwarna (biru / ungu / merah / hijau) pada halaman hasil scan — dikelompokkan, lalu diklasifikasi
  var MARKS = {};
  async function imageBoxes(p) {
    var L = await loadPdfJs(), doc = await jsDoc(p.d), pg = await doc.getPage(p.i + 1), D = dims(p);
    var vp = pg.getViewport({ scale: 1, rotation: D.t }), ops = await pg.getOperatorList(), O = L.OPS, U = L.Util;
    var ctm = [1, 0, 0, 1, 0, 0], st = [], out = [];
    var IMG = [O.paintImageXObject, O.paintInlineImageXObject, O.paintImageMaskXObject, O.paintImageXObjectRepeat, O.paintJpegXObject].filter(function (x) { return x != null; });
    for (var i = 0; i < ops.fnArray.length; i++) {
      var fn = ops.fnArray[i], a = ops.argsArray[i];
      if (fn === O.save) st.push(ctm.slice());
      else if (fn === O.restore) ctm = st.pop() || ctm;
      else if (fn === O.transform) ctm = U.transform(ctm, a);
      else if (fn === O.paintFormXObjectBegin) { st.push(ctm.slice()); if (a && a[0] && a[0].length === 6) ctm = U.transform(ctm, a[0]); }
      else if (fn === O.paintFormXObjectEnd) ctm = st.pop() || ctm;
      else if (IMG.indexOf(fn) >= 0) {
        var m = U.transform(vp.transform, ctm), pts = [[0, 0], [1, 0], [0, 1], [1, 1]].map(function (q) { return [m[0] * q[0] + m[2] * q[1] + m[4], m[1] * q[0] + m[3] * q[1] + m[5]]; });
        var xs = pts.map(function (q) { return q[0]; }), ys = pts.map(function (q) { return q[1]; }), b = { x: Math.min.apply(null, xs), y: Math.min.apply(null, ys) };
        b.w = Math.max.apply(null, xs) - b.x; b.h = Math.max.apply(null, ys) - b.y;
        if (b.w > 12 && b.h > 8 && b.w * b.h < D.w * D.h * 0.45) out.push(b);
      }
    }
    return out;
  }
  function inkStats(data, W, x0, y0, w, h) {
    var n = 0, ink = 0, col = 0, hue = { b: 0, r: 0, g: 0, k: 0 };
    for (var y = y0; y < y0 + h; y++) for (var x = x0; x < x0 + w; x++) {
      var i = (y * W + x) * 4, r = data[i], g = data[i + 1], b = data[i + 2], mx = Math.max(r, g, b), mn = Math.min(r, g, b), lum = 0.3 * r + 0.59 * g + 0.11 * b; n++;
      if (lum > 215) continue; ink++;
      var sat = mx ? (mx - mn) / mx : 0;
      if (sat > 0.25) { col++; if (b >= r && b >= g) hue.b++; else if (r >= g && r >= b) hue.r++; else hue.g++; } else hue.k++;
    }
    return { fill: n ? ink / n : 0, colored: ink ? col / ink : 0, hue: hue };
  }
  async function detectMarks(p) {
    var D = dims(p), sc = Math.min(2, 1000 / Math.max(D.w, D.h)), c = await renderBase(p, D.w * sc, 1);
    var W = c.width, H = c.height, data = c.getContext("2d", { willReadFrequently: true }).getImageData(0, 0, W, H).data;
    var found = [], lines = [];
    try { lines = await pageLines(p); } catch (e) { }
    // (1) gambar tertanam
    var imgs = []; try { imgs = await imageBoxes(p); } catch (e) { }
    imgs.forEach(function (b) {
      var s = inkStats(data, W, Math.max(0, Math.floor(b.x * sc)), Math.max(0, Math.floor(b.y * sc)), Math.max(1, Math.min(W - Math.floor(b.x * sc), Math.ceil(b.w * sc))), Math.max(1, Math.min(H - Math.floor(b.y * sc), Math.ceil(b.h * sc))));
      var asp = b.w / b.h, kind = s.fill > 0.55 ? "gambar" : (s.colored > 0.45 && asp > 0.65 && asp < 1.55 ? "stempel" : asp >= 1.3 && s.fill < 0.35 ? "ttd" : s.colored > 0.4 ? "stempel" : "gambar");
      found.push({ x: b.x, y: b.y, w: b.w, h: b.h, kind: kind, src: "img", conf: kind === "gambar" ? 0.6 : 0.9 });
    });
    // (2) tinta berwarna (scan): sel 4px → komponen terhubung
    var cs = 4, gw = Math.ceil(W / cs), gh = Math.ceil(H / cs), cell = new Uint8Array(gw * gh);
    for (var y = 0; y < H; y += 2) for (var x = 0; x < W; x += 2) {
      var i = (y * W + x) * 4, r = data[i], g = data[i + 1], bl = data[i + 2], mx = Math.max(r, g, bl), mn = Math.min(r, g, bl);
      if (mx < 245 && mx - mn > 45 && (mx - mn) / (mx || 1) > 0.28 && 0.3 * r + 0.59 * g + 0.11 * bl < 215) cell[((y / cs) | 0) * gw + ((x / cs) | 0)]++;
    }
    var on = new Uint8Array(gw * gh); for (var q = 0; q < on.length; q++) on[q] = cell[q] >= 2 ? 1 : 0;
    var R = 3, dil = new Uint8Array(gw * gh);   // dilatasi agar goresan TTD yang terputus menjadi satu
    for (var cy = 0; cy < gh; cy++) for (var cx = 0; cx < gw; cx++) if (on[cy * gw + cx]) for (var yy = Math.max(0, cy - R); yy <= Math.min(gh - 1, cy + R); yy++) for (var xx = Math.max(0, cx - R); xx <= Math.min(gw - 1, cx + R); xx++) dil[yy * gw + xx] = 1;
    var seen = new Uint8Array(gw * gh);
    for (var s0 = 0; s0 < dil.length; s0++) {
      if (!dil[s0] || seen[s0]) continue;
      var stack = [s0], x0 = 1e9, y0 = 1e9, x1 = -1, y1 = -1, cnt = 0; seen[s0] = 1;
      while (stack.length) { var v = stack.pop(), vx = v % gw, vy = (v / gw) | 0; if (on[v]) { cnt++; if (vx < x0) x0 = vx; if (vy < y0) y0 = vy; if (vx > x1) x1 = vx; if (vy > y1) y1 = vy; }
        [v - 1, v + 1, v - gw, v + gw].forEach(function (nb) { if (nb >= 0 && nb < dil.length && !seen[nb] && dil[nb] && Math.abs((nb % gw) - vx) <= 1) { seen[nb] = 1; stack.push(nb); } }); }
      if (x1 < 0) continue;
      var bx = x0 * cs / sc, by = y0 * cs / sc, bw = (x1 - x0 + 1) * cs / sc, bh = (y1 - y0 + 1) * cs / sc;
      if (bw < 22 || bh < 10 || bw * bh < 450 || bw * bh > D.w * D.h * 0.5) continue;
      var st2 = inkStats(data, W, x0 * cs, y0 * cs, Math.min(W - x0 * cs, (x1 - x0 + 1) * cs), Math.min(H - y0 * cs, (y1 - y0 + 1) * cs));
      // tinta berwarna pada teks biasa (mis. judul biru) → cocok dengan garis teks PDF → abaikan
      var textHit = lines.some(function (l) { var ix = Math.max(0, Math.min(l.x + l.w, bx + bw) - Math.max(l.x, bx)), iy = Math.max(0, Math.min(l.top + l.h, by + bh) - Math.max(l.top, by)); return ix * iy > bw * bh * 0.5; });
      if (textHit) continue;
      var asp2 = bw / bh, round = asp2 > 0.7 && asp2 < 1.45 && bw >= 45, kind2 = round && st2.fill > 0.06 ? "stempel" : "ttd";
      var conf = Math.min(0.97, 0.55 + Math.min(0.25, cnt / 400) + (kind2 === "stempel" ? (round ? 0.15 : 0) : (asp2 > 1.4 && st2.fill < 0.3 ? 0.15 : 0)));
      found.push({ x: bx - 3, y: by - 3, w: bw + 6, h: bh + 6, kind: kind2, src: "ink", conf: conf, hue: st2.hue.b >= st2.hue.r ? "biru" : "merah" });
    }
    // gabung yang tumpang tindih (utamakan gambar tertanam)
    found.sort(function (a, b) { return (a.src === "img" ? 0 : 1) - (b.src === "img" ? 0 : 1); });
    var res = [];
    found.forEach(function (m) { var dup = res.some(function (r) { var ix = Math.max(0, Math.min(r.x + r.w, m.x + m.w) - Math.max(r.x, m.x)), iy = Math.max(0, Math.min(r.y + r.h, m.y + m.h) - Math.max(r.y, m.y)); return ix * iy > Math.min(r.w * r.h, m.w * m.h) * 0.5; }); if (!dup) res.push(m); });
    res.forEach(function (m, i) { m.id = p.id + ":m" + i; });
    c.width = c.height = 0;
    return res;
  }
  async function runDetect(force) {
    var p = edPage(); if (!p) return;
    var key = thumbKey({ d: p.d, i: p.i, r0: p.r0, rot: p.rot, ops: [] });
    if (MARKS[key] && !force) { ED.marks = MARKS[key]; edDraw(); edProps(); return; }
    var sc = $("pe-scan"); if (sc) { sc.classList.remove("on"); void sc.offsetWidth; sc.classList.add("on"); }
    ED.marks = null; ED.detecting = true; edProps();
    var t0 = Date.now();
    try { var m = await detectMarks(p); MARKS[key] = m; if (edPage() === p) ED.marks = m; } catch (e) { console.warn(e); ED.marks = []; toast("Deteksi gagal: " + e.message, "error"); }
    var wait = Math.max(0, 900 - (Date.now() - t0)); await new Promise(function (r) { setTimeout(r, wait); });   // biarkan animasi pindai selesai
    ED.detecting = false; if (sc) sc.classList.remove("on");
    ED.markAnim = Date.now(); animMarks(); edProps();
    var n = (ED.marks || []).filter(function (x) { return x.kind !== "gambar"; }).length;
    if (ED.tool === "mark") toast(n ? n + " tanda tangan / stempel ditemukan — klik untuk mengolahnya" : (ED.marks && ED.marks.length ? "Hanya gambar/logo yang ditemukan" : "Tidak ada tanda tangan / stempel di halaman ini"), n ? "success" : "info", 4000);
  }
  function animMarks() { var f = function () { edDraw(); if (Date.now() - ED.markAnim < 700) requestAnimationFrame(f); }; requestAnimationFrame(f); setTimeout(edDraw, 720); }
  var MK = { ttd: ["Tanda tangan", "#2563eb"], stempel: ["Stempel", "#db2777"], gambar: ["Gambar / logo", "#0891b2"], paraf: ["Paraf", "#7c3aed"] };
  function drawMarks(g, k, p) {
    if (ED.tool !== "mark" || !ED.marks) return;
    var t = Math.min(1, (Date.now() - (ED.markAnim || 0)) / 600);
    g.save(); g.scale(k, k);
    ED.marks.forEach(function (m, i) {
      var tt = Math.max(0, Math.min(1, t * 1.6 - i * 0.12)), e = 1 - Math.pow(1 - tt, 3); if (e <= 0) return;
      var c = MK[m.kind][1], hv = ED.hoverMark === m, pad = (1 - e) * 10;
      g.globalAlpha = e; g.fillStyle = c + (hv ? "26" : "12"); g.fillRect(m.x - pad, m.y - pad, m.w + pad * 2, m.h + pad * 2);
      g.strokeStyle = c; g.lineWidth = (hv ? 2 : 1.4) / ED.k; g.setLineDash(hv ? [] : [6 / ED.k, 3 / ED.k]); g.strokeRect(m.x - pad, m.y - pad, m.w + pad * 2, m.h + pad * 2); g.setLineDash([]);
      var lab = MK[m.kind][0] + " · " + Math.round(m.conf * 100) + "%", fs = 10 / ED.k; g.font = "700 " + fs + "px 'Plus Jakarta Sans', sans-serif";
      var lw = g.measureText(lab).width + 10 / ED.k, lh = 16 / ED.k, ly = m.y - lh - 3 / ED.k < 0 ? m.y + m.h + 3 / ED.k : m.y - lh - 3 / ED.k;
      g.fillStyle = c; g.beginPath(); if (g.roundRect) g.roundRect(m.x, ly, lw, lh, 4 / ED.k); else g.rect(m.x, ly, lw, lh); g.fill();
      g.fillStyle = "#fff"; g.fillText(lab, m.x + 5 / ED.k, ly + lh * 0.72);
    });
    g.restore();
  }
  function markAt(pt) { var M = ED.tool === "mark" && ED.marks || []; for (var i = M.length - 1; i >= 0; i--) { var m = M[i]; if (pt.x >= m.x && pt.x <= m.x + m.w && pt.y >= m.y - 18 / ED.k && pt.y <= m.y + m.h) return m; } return null; }
  function hidePop() { var mp = $("pe-mpop"); if (mp) { mp.classList.add("hidden"); mp.innerHTML = ""; } }
  function markPop(m) {
    var mp = $("pe-mpop"); if (!mp) return;
    var c = MK[m.kind];
    mp.innerHTML = '<div class="hd"><span class="dot" style="background:' + c[1] + '"></span><b>' + c[0] + '</b><small>' + Math.round(m.conf * 100) + "% yakin · " + Math.round(m.w * 0.3528) + "×" + Math.round(m.h * 0.3528) + ' mm</small><button data-a="x" class="x"><i class="fa-solid fa-xmark"></i></button></div>'
      + '<button data-a="obj"><i class="fa-solid fa-up-down-left-right"></i><span><b>Jadikan objek</b><small>bisa digeser, diubah ukuran, diputar</small></span></button>'
      + '<button data-a="all"><i class="fa-solid fa-layer-group"></i><span><b>Tempel ke halaman lain</b><small>paraf / stempel di semua halaman</small></span></button>'
      + '<button data-a="lib"><i class="fa-solid fa-book-bookmark"></i><span><b>Simpan ke pustaka</b><small>pakai lagi di dokumen lain</small></span></button>'
      + '<button data-a="dl"><i class="fa-solid fa-download"></i><span><b>Unduh PNG transparan</b><small>latar putih dibuang</small></span></button>'
      + '<button data-a="del" class="red"><i class="fa-solid fa-eraser"></i><span><b>Hapus permanen</b><small>bersihkan dari dokumen</small></span></button>';
    mp.classList.remove("hidden");
    var k = ED.k, pw = $("pe-ed-paper").offsetWidth, left = (m.x + m.w) * k + 10; if (left + mp.offsetWidth > pw - 4) left = Math.max(4, m.x * k - mp.offsetWidth - 10);
    mp.style.left = left + "px"; mp.style.top = Math.max(4, Math.min($("pe-ed-paper").offsetHeight - mp.offsetHeight - 4, m.y * k)) + "px";
    mp.querySelectorAll("[data-a]").forEach(function (b) { b.onpointerdown = function (e) { e.stopPropagation(); }; b.onclick = function (e) { e.stopPropagation(); markAct(m, b.dataset.a); }; });
  }
  // potong area halaman beresolusi tinggi → PNG transparan
  async function regionPng(p, box, mode) {
    var D = dims(p), doc = await jsDoc(p.d), pg = await doc.getPage(p.i + 1), s = Math.min(4, 1400 / Math.max(box.w, box.h));
    var vp = pg.getViewport({ scale: s, rotation: D.t, offsetX: -box.x * s, offsetY: -box.y * s });
    var c = document.createElement("canvas"); c.width = Math.max(1, Math.ceil(box.w * s)); c.height = Math.max(1, Math.ceil(box.h * s));
    var g = c.getContext("2d", { willReadFrequently: true }); g.fillStyle = "#fff"; g.fillRect(0, 0, c.width, c.height);
    await pg.render({ canvasContext: g, viewport: vp }).promise;
    var d = g.getImageData(0, 0, c.width, c.height), a = d.data;
    for (var i = 0; i < a.length; i += 4) {
      var r = a[i], gg = a[i + 1], b = a[i + 2], mx = Math.max(r, gg, b), mn = Math.min(r, gg, b), l = (r + gg + b) / 3, sat = mx ? (mx - mn) / mx : 0;
      if (mode === "color" && sat < 0.18 && l > 90) { a[i + 3] = 0; continue; }   // stempel/TTD berwarna: buang teks hitam & latar
      if (mn > 232 && l > 238) a[i + 3] = 0; else if (l > 200 && mn > 190) a[i + 3] = Math.round(a[i + 3] * (238 - l) / 38);
    }
    g.putImageData(d, 0, 0);
    var bytes = await canvasPng(c); c.width = c.height = 0; return bytes;
  }
  async function markAct(m, act) {
    var p = edPage(); if (!p) return;
    if (act === "x") return hidePop();
    hidePop();
    var mode = m.src === "ink" ? "color" : "white";
    try {
      if (act === "del") { pushUndo(); var bg = sampleBg(m); p.ops.push({ t: "erase", x: m.x, y: m.y, w: m.w, h: m.h, fill: "auto", col: bg }); dropMark(m); edDraw(); renderSoon(); toast(MK[m.kind][0] + " dihapus dari halaman ini", "success"); return; }
      busy("Mengambil " + MK[m.kind][0].toLowerCase() + "…", 40, "read");
      var bytes = await regionPng(p, m, mode);
      busy(null);
      if (act === "dl") { saveBlob(bytes, MK[m.kind][0] + " - " + (safeName(PE.base) || "dokumen") + ".png", "image/png"); return; }
      if (act === "lib") { await libAdd({ kind: m.kind, bytes: bytes, name: MK[m.kind][0] + " · " + (safeName(PE.base) || "dokumen") }); toast("Tersimpan di Pustaka TTD & stempel", "success"); return; }
      var id = await regImage(bytes, "image/png");
      var o = { t: "img", ref: id, x: m.x, y: m.y, w: m.w, h: m.h, op: 1, a: 0 };
      if (act === "obj") { pushUndo(); p.ops.push({ t: "mask", x: m.x, y: m.y, w: m.w, h: m.h, col: sampleBg(m), key: m.id }, o); dropMark(m); ED.tool = "sel"; ED.sel = o; edTools(); edProps(); edDraw(); renderSoon(); fxPop(); toast("Sekarang bisa digeser, diubah ukuran & diputar", "success"); return; }
      if (act === "all") { stampAll(o, true); }
    } catch (e) { busy(null); toast("Gagal: " + e.message, "error"); }
  }
  function dropMark(m) { if (ED.marks) ED.marks = ED.marks.filter(function (x) { return x !== m; }); }
  // tempel objek gambar ke halaman lain di posisi yang sama (paraf / stempel semua halaman)
  function stampAll(o, fromMark) {
    var cur = edPage(), others = PE.pages.filter(function (p) { return p !== cur; });
    if (!others.length) return toast("Dokumen hanya punya 1 halaman", "info");
    var m = modal('<i class="fa-solid fa-layer-group" style="color:#4f46e5"></i> Tempel ke halaman lain',
      '<p style="color:var(--pe-mute);font-size:11.5px">Gambar ditempel di posisi yang sama (menyesuaikan ukuran halaman). Cocok untuk paraf atau stempel di setiap halaman.</p>'
      + '<div class="pe-seg3"><label><input type="radio" name="pe-sa" value="all" checked> Semua halaman lain (' + others.length + ')</label><label><input type="radio" name="pe-sa" value="odd"> Halaman ganjil</label><label><input type="radio" name="pe-sa" value="even"> Halaman genap</label><label><input type="radio" name="pe-sa" value="rg"> Rentang <input id="pe-sa-rg" placeholder="mis. 2-5, 8" style="width:120px"></label></div>',
      '<button class="pe-b" data-c>Batal</button><button class="pe-b pri" id="pe-sa-go"><i class="fa-solid fa-stamp"></i>Tempel</button>', 480);
    m.querySelector("[data-c]").onclick = function () { m.remove(); };
    m.querySelector("#pe-sa-go").onclick = function () {
      var v = m.querySelector('input[name="pe-sa"]:checked').value, sel = [];
      if (v === "rg") { var txt = m.querySelector("#pe-sa-rg").value, nums = []; String(txt).split(/[,;]+/).forEach(function (part) { var mm = part.trim().match(/^(\d+)\s*(?:-\s*(\d+))?$/); if (mm) for (var q = +mm[1]; q <= +(mm[2] || mm[1]); q++) nums.push(q); }); sel = nums.map(function (n) { return PE.pages[n - 1]; }).filter(function (p) { return p && p !== cur; }); }
      else sel = PE.pages.filter(function (p, i) { return p !== cur && (v === "all" || (v === "odd" ? i % 2 === 0 : i % 2 === 1)); });
      if (!sel.length) return toast("Tidak ada halaman yang cocok", "error");
      pushUndo();
      var D0 = dims(cur);
      if (fromMark && cur.ops.indexOf(o) < 0) cur.ops.push(clone(o));
      sel.forEach(function (p) { var D = dims(p), sx = D.w / D0.w, sy = D.h / D0.h, c = clone(o); c.x = o.x * sx; c.y = o.y * sy; c.w = o.w * Math.min(sx, sy); c.h = o.h * Math.min(sx, sy); p.ops.push(c); });
      m.remove(); edDraw(); render(); edStrip(); toast("Ditempel ke " + sel.length + " halaman", "success");
    };
  }
  // ---------- pustaka TTD & stempel (tersimpan di perangkat) ----------
  async function libGet() { try { return (await kv("get", "lib")) || []; } catch (e) { return []; } }
  async function libAdd(it) { var L = await libGet(); L.unshift({ id: "L" + Date.now().toString(36), kind: it.kind || "gambar", name: it.name || "Gambar", bytes: it.bytes, mime: it.mime || "image/png", at: Date.now() }); await kv("put", "lib", L.slice(0, 40)); }
  async function libPanel() {
    var L = await libGet();
    var m = modal('<i class="fa-solid fa-book-bookmark" style="color:#4f46e5"></i> Pustaka TTD & stempel',
      '<p style="color:var(--pe-mute);font-size:11.5px">Tersimpan di perangkat ini. Klik untuk menaruh di halaman. Tambah dari hasil deteksi (menu Deteksi TTD & stempel) atau unggah gambar.</p><div class="pe-lib" id="pe-lib"></div>',
      '<label class="pe-b"><input type="file" accept="image/png,image/jpeg" class="hidden" id="pe-lib-in"><i class="fa-solid fa-upload"></i>Unggah gambar</label><button class="pe-b" data-sg style="margin-right:auto"><i class="fa-solid fa-signature"></i>Buat tanda tangan</button><button class="pe-b" data-c>Tutup</button>', 620);
    m.querySelector("[data-c]").onclick = function () { m.remove(); };
    m.querySelector("[data-sg]").onclick = function () { m.remove(); signPad(); };
    var urls = [];
    var draw = function () {
      var box = m.querySelector("#pe-lib");
      box.innerHTML = L.length ? L.map(function (it, i) { var u = URL.createObjectURL(new Blob([it.bytes], { type: it.mime || "image/png" })); urls.push(u); return '<div class="pe-lib-it" data-i="' + i + '"><img src="' + u + '"><b>' + E(it.name) + '</b><small>' + (MK[it.kind] || MK.gambar)[0] + '</small><button class="x" data-del="' + i + '" title="Hapus dari pustaka"><i class="fa-solid fa-xmark"></i></button></div>'; }).join("") : '<div class="pe-lib-empty"><i class="fa-solid fa-signature"></i><b>Pustaka masih kosong</b><small>Deteksi TTD / stempel di dokumen lalu pilih "Simpan ke pustaka", atau unggah gambar.</small></div>';
      box.querySelectorAll(".pe-lib-it").forEach(function (el) { el.onclick = async function (e) { if (e.target.closest("[data-del]")) return; var it = L[+el.dataset.i]; m.remove(); var id = await regImage(it.bytes, it.mime || "image/png"); placeImg(id); }; });
      box.querySelectorAll("[data-del]").forEach(function (b) { b.onclick = async function (e) { e.stopPropagation(); L.splice(+b.dataset.del, 1); await kv("put", "lib", L); draw(); }; });
    };
    draw();
    m.querySelector("#pe-lib-in").onchange = async function () { var f = this.files[0]; this.value = ""; if (!f) return; try { var id = await fileToImage(f), nid = await knockWhite(id); await libAdd({ kind: "gambar", name: f.name.replace(/\.[^.]+$/, ""), bytes: IMGS[nid].bytes }); L = await libGet(); draw(); toast("Ditambahkan ke pustaka (latar putih dibuang)", "success"); } catch (e) { toast(e.message, "error"); } };
  }
  function placeImg(id, at) {
    var p = edPage(); if (!p) return; var im = IMGS[id], D = dims(p);
    var w = Math.min(D.w * 0.3, im.w * 0.6), h = w * im.h / im.w; if (h > D.h * 0.3) { h = D.h * 0.3; w = h * im.w / im.h; }
    var cx = at ? at.x : D.w / 2, cy = at ? at.y : D.h / 2, o = { t: "img", ref: id, x: Math.max(0, cx - w / 2), y: Math.max(0, cy - h / 2), w: w, h: h, op: 1, a: 0 };
    pushUndo(); p.ops.push(o); ED.sel = o; ED.tool = "sel"; edTools(); edProps(); edDraw(); renderSoon(); fxPop();
  }

  // ===================== editor halaman =====================
  var ED = { on: false, id: null, tool: "sel", sel: null, k: 1, zoom: 1, base: null, drag: null, edit: null,
    st: { tmode: "cover", c: "#111827", lw: 2.5, op: 1, hlc: "#facc15", hlw: 14, fill: "#ffffff", font: "Helvetica", size: 12, b: false, i: false, u: false, al: "l", tc: "#111827", bg: "", top: 1, a: 0 } };
  // pita alat (ribbon) mendatar: tab berlabel → tombol ikon + teks. "@" = aksi sekali klik (bukan alat).
  var RIB = [
    { k: "teks", t: "Teks", ic: "fa-font", it: [["tedit", "fa-i-cursor", "Edit teks asli", "E"], ["text", "fa-font", "Tambah teks", "T"], ["@find", "fa-magnifying-glass", "Cari & ganti", "F"], "|", ["@ocr", "fa-glasses", "OCR scan → teks", ""], ["form", "fa-rectangle-list", "Isi formulir", "U"]] },
    { k: "ttd", t: "TTD & Stempel", ic: "fa-signature", it: [["@sign", "fa-signature", "Buat tanda tangan", "S"], ["mark", "fa-stamp", "Deteksi TTD & stempel", "D"], ["@lib", "fa-book-bookmark", "Pustaka", "L"], ["@img", "fa-image", "Sisipkan gambar", "I"]] },
    { k: "coret", t: "Coret & Bentuk", ic: "fa-pen", it: [["pen", "fa-pen", "Pena", "P"], ["hl", "fa-highlighter", "Stabilo", "H"], ["line", "fa-minus", "Garis", "G"], ["arrow", "fa-arrow-right-long", "Panah", "A"], ["rect", "fa-regular fa-square", "Kotak", "R"], ["ellipse", "fa-regular fa-circle", "Lingkaran", "O"], ["check", "fa-check", "Centang", "C"], ["rub", "fa-delete-left", "Hapus coretan", ""]] },
    { k: "kom", t: "Catatan & Tautan", ic: "fa-comment-dots", it: [["note", "fa-note-sticky", "Catatan", "N"], ["link", "fa-link", "Tautan", "K"], ["@notes", "fa-list-ul", "Daftar catatan", ""]] },
    { k: "hapus", t: "Hapus & Sensor", ic: "fa-eraser", it: [["erase", "fa-eraser", "Hapus area", "X"], ["@redact", "fa-user-secret", "Sensor kata / data", ""]] },
    { k: "hal", t: "Halaman", ic: "fa-file-lines", it: [["@pnum", "fa-list-ol", "Nomor, header & footer", ""], ["@wm", "fa-droplet", "Watermark", ""], "|", ["@rotl", "fa-rotate-left", "Putar kiri", ""], ["@rotr", "fa-rotate-right", "Putar kanan", ""], ["@pdup", "fa-regular fa-clone", "Duplikat", ""], ["@pdel", "fa-regular fa-trash-can", "Hapus halaman", ""], "|", ["crop", "fa-crop-simple", "Potong (crop)", ""], ["@size", "fa-up-right-and-down-left-from-center", "Ubah ukuran", ""], "|", ["@pins", "fa-file-circle-plus", "Sisipkan file", ""], ["@pcut", "fa-scissors", "Pecah di sini", ""], ["@pmerge", "fa-object-group", "Gabung file lain", ""], ["@cmp", "fa-code-compare", "Bandingkan versi", ""]] },
    { k: "out", t: "Simpan & Ekspor", ic: "fa-file-export", it: [["@dlpdf", "fa-file-pdf", "Unduh PDF", ""], ["@comp", "fa-file-zipper", "Kompres", ""], ["@pw", "fa-lock", "Kunci password", ""], "|", ["@toimg", "fa-file-image", "Ke gambar", ""], ["@todocx", "fa-file-word", "Ke Word", ""], ["@toxlsx", "fa-file-excel", "Ke Excel", ""]] }
  ];
  var TOOLS = [].concat.apply([["sel", "fa-arrow-pointer", "Pilih", "V"]], RIB.map(function (g) { return g.it.filter(function (t) { return t !== "|"; }); }));
  var tabOf = function (t) { var r = RIB.filter(function (g) { return g.it.some(function (x) { return x[0] === t; }); })[0]; return r ? r.k : null; };
  var faI = function (c) { return c.indexOf("fa-regular") === 0 ? c : "fa-solid " + c; };
  function ribBtn(t) { if (t === "|") return '<span class="pe-rsep"></span>'; var act = t[0][0] === "@"; return '<button class="pe-rt' + (t[0] === "@pdel" ? " red" : "") + '" ' + (act ? 'data-act="' + t[0].slice(1) + '"' : 'data-tool="' + t[0] + '"') + ' title="' + E(t[2]) + (t[3] ? " (" + t[3] + ")" : "") + '"><i class="' + faI(t[1]) + '"></i><span>' + E(t[2]) + "</span></button>"; }
  var edPage = function () { return PE.pages.filter(function (p) { return p.id === ED.id; })[0]; };
  function edShell() {
    var el = $("pe-ed"); if (el) return el;
    el = document.createElement("div"); el.id = "pe-ed"; el.className = "hidden";
    el.innerHTML = '<div class="pe-top pe-ed-top"><button class="pe-b" id="pe-ed-back"><i class="fa-solid fa-arrow-left"></i><span class="tx" id="pe-ed-backt">Semua halaman</span></button>'
      + '<div class="pe-title"><b id="pe-ed-t">Edit halaman</b><small id="pe-ed-s"></small></div>'
      + '<button class="pe-b" id="pe-ed-undo" title="Urungkan (Ctrl+Z)"><i class="fa-solid fa-rotate-left"></i><span class="tx">Urungkan</span></button><button class="pe-b" id="pe-ed-redo" title="Ulangi (Ctrl+Y)"><i class="fa-solid fa-rotate-right"></i><span class="tx">Ulangi</span></button>'
      + '<button class="pe-b pri" id="pe-ed-done"><i class="fa-solid fa-check"></i><span class="tx">Selesai</span></button></div>'
      + '<nav class="pe-rib" id="pe-ed-tools"><div class="pe-rib-tabs" role="tablist" id="pe-rib-tabs"><i class="pe-rib-ind"></i>' + RIB.map(function (g) { return '<button role="tab" data-rt="' + g.k + '"><i class="fa-solid ' + g.ic + '"></i><span>' + g.t + "</span></button>"; }).join("") + '</div>'
      + '<div class="pe-rib-row"><button class="pe-rt pin" data-tool="sel" title="Pilih, geser & atur objek (V) · Shift+klik / tarik kotak untuk memilih banyak"><i class="fa-solid fa-arrow-pointer"></i><span>Pilih</span></button><span class="pe-rsep"></span>'
      + RIB.map(function (g) { return '<div class="pe-rib-g" data-g="' + g.k + '">' + g.it.map(ribBtn).join("") + "</div>"; }).join("") + "</div></nav>"
      + '<div class="pe-ed-body"><div class="pe-ed-main"><div class="pe-props" id="pe-ed-props"></div>'
      + '<div class="pe-stage" id="pe-ed-stage"><div class="pe-paper" id="pe-ed-paper"><canvas class="bs"></canvas><canvas class="ov"></canvas><div class="pe-scan" id="pe-scan"></div><div class="pe-qbar hidden" id="pe-qbar"></div><div class="pe-mpop hidden" id="pe-mpop"></div></div></div>'
      + '<div class="pe-nav"><button class="pe-b ic" id="pe-ed-prev" title="Halaman sebelumnya (PgUp)"><i class="fa-solid fa-chevron-left"></i></button><span class="pg" id="pe-ed-pg">1 / 1</span><button class="pe-b ic" id="pe-ed-next" title="Halaman berikutnya (PgDn)"><i class="fa-solid fa-chevron-right"></i></button>'
      + '<span class="sep"></span><button class="pe-b ic" id="pe-ed-zo" title="Perkecil"><i class="fa-solid fa-minus"></i></button><button class="pe-b zl" id="pe-ed-zl" title="Kembali ke ukuran pas">100%</button><button class="pe-b ic" id="pe-ed-zi" title="Perbesar"><i class="fa-solid fa-plus"></i></button></div>'
      + '<div class="pe-hint" id="pe-ed-hint"></div></div>'
      + '<aside class="pe-strip" id="pe-strip"></aside></div>';
    $("pe").appendChild(el);
    $("pe-ed-back").onclick = edClose; $("pe-ed-done").onclick = edClose;
    $("pe-ed-prev").onclick = function () { edGo(-1); }; $("pe-ed-next").onclick = function () { edGo(1); };
    $("pe-ed-undo").onclick = function () { edCommitText(); undo(); }; $("pe-ed-redo").onclick = function () { edCommitText(); redo(); };
    $("pe-ed-zi").onclick = function () { ED.zoom = Math.min(3, ED.zoom * 1.25); edLoad(); }; $("pe-ed-zo").onclick = function () { ED.zoom = Math.max(0.4, ED.zoom / 1.25); edLoad(); };
    $("pe-ed-zl").onclick = function () { ED.zoom = 1; edLoad(); };
    el.querySelectorAll("[data-tool]").forEach(function (b) { b.onclick = function () { pickTool(b.dataset.tool); }; });
    el.querySelectorAll("#pe-rib-tabs [data-rt]").forEach(function (b) { b.onclick = function () { ED.tab = b.dataset.rt; ribSync(); var first = RIB.filter(function (g) { return g.k === ED.tab; })[0].it.filter(function (t) { return t !== "|" && t[0][0] !== "@"; })[0]; if (first && tabOf(ED.tool) !== ED.tab && ED.tool !== "sel") pickTool(first[0]); }; });
    el.querySelectorAll(".pe-rib [data-act]").forEach(function (b) { b.onclick = function () { edAct(b.dataset.act, b); }; });
    var ii = document.createElement("input"); ii.type = "file"; ii.id = "pe-img-in"; ii.className = "hidden"; ii.accept = "image/png,image/jpeg,image/webp,image/gif,image/bmp,.png,.jpg,.jpeg,.webp"; el.appendChild(ii);
    ii.onchange = async function () {
      var f = ii.files && ii.files[0]; ii.value = ""; if (!f) { ED.replace = null; return; }
      var o = ED.replace; ED.replace = null;
      if (o && edPage() && edPage().ops.indexOf(o) >= 0) { try { busy("Memuat gambar…", 40); var id = await fileToImage(f), im = IMGS[id]; pushUndo(); o.ref = id; var cx = o.x + o.w / 2, cy = o.y + o.h / 2; o.h = o.w * im.h / im.w; o.x = cx - o.w / 2; o.y = cy - o.h / 2; busy(null); edDraw(); edProps(); } catch (e) { busy(null); toast(e.message, "error"); } return; }
      edAddImage(f, ED.imgAt);
    };
    var stg = el.querySelector("#pe-ed-stage");
    stg.addEventListener("dragover", function (e) { if (e.dataTransfer && Array.from(e.dataTransfer.types || []).indexOf("Files") >= 0) { e.preventDefault(); e.stopPropagation(); stg.classList.add("over"); } });
    stg.addEventListener("dragleave", function () { stg.classList.remove("over"); });
    stg.addEventListener("drop", function (e) {
      stg.classList.remove("over");
      var f = e.dataTransfer && Array.from(e.dataTransfer.files || []).filter(function (x) { return /^image\//.test(x.type) || /\.(png|jpe?g|webp|gif|bmp)$/i.test(x.name); })[0];
      if (!f) return; e.preventDefault(); e.stopPropagation();
      var r = el.querySelector("#pe-ed-paper").getBoundingClientRect(); edAddImage(f, { x: (e.clientX - r.left) / ED.k, y: (e.clientY - r.top) / ED.k });
    });
    document.addEventListener("paste", function (e) {
      if (!ED.on || ED.edit || !e.clipboardData) return;
      var it = Array.from(e.clipboardData.items || []).filter(function (x) { return x.kind === "file" && /^image\//.test(x.type); })[0];
      if (!it) return; e.preventDefault(); var f = it.getAsFile(); if (f) edAddImage(f, null);
    });
    var ov = el.querySelector("canvas.ov");
    ov.addEventListener("pointerdown", edDown); ov.addEventListener("pointermove", edMove); ov.addEventListener("pointerup", edUp); ov.addEventListener("pointercancel", edUp);
    ov.addEventListener("dblclick", function (e) { var pt = edPt(e), o = hit(pt); if (o && o.t === "note") { ED.sel = o; notePop(o); } else if (o && o.t === "link") { ED.sel = o; linkPop(o); } else if (o && o.t === "text") { ED.sel = o; edText(o); } else if (!o && ED.tool !== "tedit") { var ln = lineAt(pt); if (ln) editLine(ln); } });
    var rt; addEventListener("resize", function () { if (!ED.on) return; clearTimeout(rt); rt = setTimeout(edLoad, 150); });
    return el;
  }
  function pickTool(t) {
    edCommitText(); hidePop();
    if (t[0] === "@") return edAct(t.slice(1));
    if (t === "img") { ED.imgAt = null; $("pe-img-in").click(); return; }
    if (t === "lib") { libPanel(); return; }
    ED.tool = t; ED.sel = null; ED.ms = []; if (t !== "crop") ED.crop = null; if (tabOf(t)) ED.tab = tabOf(t); edTools(); edProps(); edDraw();
    var fl = $("pe-formL"); if (fl) fl.classList.toggle("on", t === "form");
    if (t === "mark") runDetect(false);
  }
  function edOpen(id) { if (PE.lock) return; edShell(); ED.on = true; ED.id = id; ED.sel = null; ED.ms = []; ED.zoom = 1; if (!ED.tab) ED.tab = "teks"; if (!ED.toolSet) { ED.tool = "tedit"; ED.toolSet = 1; } var el = $("pe-ed"); el.classList.remove("hidden"); el.classList.remove("in"); void el.offsetWidth; el.classList.add("in"); $("pe-ed-backt").textContent = "Kembali ke " + MODE_T[PE.mode]; edTools(); edProps(); edStrip(); edLoad(); }
  function edClose() { edCommitText(); hidePop(); findClose(); ED.on = false; ED.sel = null; ED.ms = []; var el = $("pe-ed"); if (el) el.classList.add("hidden"); render(); }
  function edGo(d) { var i = PE.pages.indexOf(edPage()) + d; if (i < 0 || i >= PE.pages.length) return; edGoTo(PE.pages[i].id, d); }
  function edGoTo(id, dir) {
    edCommitText(); hidePop(); if (id === ED.id) return;
    ED.id = id; ED.sel = null; ED.ms = []; ED.guides = null;
    var pp = $("pe-ed-paper"); if (pp) { pp.classList.remove("slideL", "slideR"); void pp.offsetWidth; pp.classList.add(dir < 0 ? "slideR" : "slideL"); }
    $("pe-ed-stage").scrollTop = 0; edStrip(); edLoad(); if (ED.tool === "mark") runDetect(false);
  }
  // strip gambar mini halaman di sisi kanan editor
  function edStrip() {
    var st = $("pe-strip"); if (!st) return;
    if (st.dataset.n !== String(PE.pages.length) || st.dataset.sig !== PE.pages.map(function (p) { return p.id; }).join(",")) {
      st.dataset.n = PE.pages.length; st.dataset.sig = PE.pages.map(function (p) { return p.id; }).join(",");
      st.innerHTML = PE.pages.map(function (p, i) { var D = dims(p); return '<button class="pe-sp" data-id="' + p.id + '"><img alt="" style="aspect-ratio:' + D.w + "/" + D.h + '"><span>' + (i + 1) + "</span></button>"; }).join("");
      st.querySelectorAll(".pe-sp").forEach(function (b) { var p = PE.pages.filter(function (x) { return x.id === b.dataset.id; })[0]; var im = b.querySelector("img"), tk = thumbKey(p); if (THUMB[tk]) im.src = THUMB[tk]; else { im.__p = p; IO ? IO.observe(im) : thumb(p, im); } b.onclick = function () { var a = PE.pages.indexOf(edPage()), z = PE.pages.indexOf(p); edGoTo(p.id, z < a ? -1 : 1); }; });
    }
    st.querySelectorAll(".pe-sp").forEach(function (b) { var on = b.dataset.id === ED.id; b.classList.toggle("on", on); if (on) { var p = edPage(), im = b.querySelector("img"), tk = thumbKey(p); if (THUMB[tk] && im.getAttribute("src") !== THUMB[tk]) im.src = THUMB[tk]; else if (!THUMB[tk]) thumb(p, im); try { b.scrollIntoView({ block: "nearest", behavior: "smooth" }); } catch (e) { } } });
  }
  async function edLoad() {
    var p = edPage(); if (!p) return;
    var D = dims(p), i = PE.pages.indexOf(p), stage = $("pe-ed-stage");
    $("pe-ed-t").textContent = safeName(PE.base) || "Edit PDF"; $("pe-ed-pg").textContent = (i + 1) + " / " + PE.pages.length; $("pe-ed-zl").textContent = Math.round(ED.zoom * 100) + "%";
    $("pe-ed-s").textContent = "Halaman " + (i + 1) + " · " + Math.round(D.w * 0.3528) + " × " + Math.round(D.h * 0.3528) + " mm · " + (p.ops.length ? p.ops.length + " objek" : "belum ada perubahan");
    $("pe-ed-prev").disabled = i <= 0; $("pe-ed-next").disabled = i >= PE.pages.length - 1;
    var avail = Math.max(240, stage.clientWidth - 48);
    var cssW = Math.min(avail, D.w > D.h ? 1000 : 780) * ED.zoom;   // lebar tetap (tidak berubah saat panel properti berganti) — cukup besar untuk mengedit teks
    if (innerWidth < 900) cssW = avail * ED.zoom;
    var paper = $("pe-ed-paper"), dpr = Math.min(2, devicePixelRatio || 1), key = thumbKey({ d: p.d, i: p.i, r0: p.r0, rot: p.rot, ops: [] }) + ":" + Math.round(cssW);
    paper.style.width = cssW + "px"; paper.style.height = cssW * D.h / D.w + "px";
    ED.k = cssW / D.w;
    var bs = paper.querySelector("canvas.bs"), ov = paper.querySelector("canvas.ov");
    ov.width = Math.round(cssW * dpr); ov.height = Math.round(cssW * D.h / D.w * dpr); ED.dpr = dpr;
    edDraw();
    if (ED.baseKey !== key) {
      var my = ED.loadSeq = (ED.loadSeq || 0) + 1;
      try { var c = await renderBase(p, cssW, dpr); if (my !== ED.loadSeq) return; bs.width = c.width; bs.height = c.height; bs.getContext("2d").drawImage(c, 0, 0); ED.base = c; ED.baseKey = key; } catch (e) { toast("Gagal menampilkan halaman: " + e.message, "error"); }
    }
    ED.lines = []; edDraw(); syncUndo();
    try { var my2 = ED.loadSeq; var ln = await pageLines(p); if (edPage() === p && my2 === ED.loadSeq) { ED.lines = ln; edDraw(); edProps(); edTools(); } } catch (e) { console.warn("deteksi teks:", e); }
    try { await formLayer(); if (edPage() === p && ED.fields && ED.fields.length && !ED.formTold && ED.tool !== "form") { ED.formTold = 1; toast("Halaman ini punya " + ED.fields.length + " kolom isian — pilih Teks → Isi formulir untuk mengisinya", "info", 6000); } if (ED.tool === "form") edProps(); } catch (e) { console.warn("formulir:", e); }
  }
  function touchMode() { var ovc = document.querySelector("#pe-ed-paper canvas.ov"); if (ovc) ovc.style.touchAction = TAPT.test(ED.tool) ? "pan-x pan-y" : "none"; var sg = $("pe-ed-stage"); if (sg) sg.dataset.tool = ED.tool; }
  function ribSync() { touchMode();
    var tabs = $("pe-rib-tabs"); if (!tabs) return; var tb = ED.tab || "teks", ix = RIB.map(function (g) { return g.k; }).indexOf(tb), on = tabs.querySelector('[data-rt="' + tb + '"]');
    tabs.querySelectorAll("[data-rt]").forEach(function (b) { b.classList.toggle("on", b.dataset.rt === tb); b.setAttribute("aria-selected", b.dataset.rt === tb); b.classList.toggle("has", b.dataset.rt === tabOf(ED.tool) && b.dataset.rt !== tb); });
    var ind = tabs.querySelector(".pe-rib-ind"); if (on && ind) { ind.style.width = on.offsetWidth + "px"; ind.style.transform = "translateX(" + on.offsetLeft + "px)"; }
    document.querySelectorAll("#pe-ed-tools .pe-rib-g").forEach(function (g) { var sh = g.dataset.g === tb; if (sh && g.classList.contains("hidden")) { g.classList.remove("hidden"); g.classList.remove("in"); void g.offsetWidth; g.classList.add("in"); } else if (!sh) g.classList.add("hidden"); });
    void ix;
  }
  function edTools() { document.querySelectorAll("#pe-ed-tools [data-tool]").forEach(function (b) { b.classList.toggle("on", b.dataset.tool === ED.tool); }); ribSync(); var H = { mark: "Deteksi TTD & stempel: tanda tangan (biru), stempel (merah muda) dan gambar tertanam ditandai otomatis. Klik kotaknya untuk mengolah.", tedit: "Edit Teks: teks asli diberi garis biru — klik barisnya, ketik perubahan, klik di luar untuk selesai. Font, ukuran & warna disamakan otomatis.", sel: "Klik objek untuk memilih, geser untuk memindah, tarik sudut kanan bawah untuk mengubah ukuran. Klik dua kali teks untuk mengedit.", text: "Klik di halaman untuk menulis teks.", erase: "Tarik kotak di area yang ingin dihapus permanen (termasuk PDF berisi gambar / JPG).", pen: "Tarik untuk menggambar bebas.", hl: "Tarik untuk menandai dengan stabilo.", line: "Tarik untuk membuat garis.", arrow: "Tarik untuk membuat panah.", rect: "Tarik untuk membuat kotak.", ellipse: "Tarik untuk membuat lingkaran / elips.", check: "Klik untuk menaruh tanda centang.", rub: "Klik atau sapukan pada coretan / bentuk untuk menghapusnya.", note: "Klik di halaman untuk menempel catatan.", link: "Tarik kotak untuk membuat tautan.", crop: "Tarik kotak area yang dipertahankan.", form: "Klik kolom untuk mengisi." }; $("pe-ed-hint").textContent = H[ED.tool] || ""; }

  function swatches(cur, key) { return PAL.map(function (c) { return '<button class="pe-sw ' + (String(cur).toLowerCase() === c ? "on" : "") + '" data-sw="' + key + '" data-c="' + c + '" style="background:' + c + '"></button>'; }).join("") + '<input type="color" data-col="' + key + '" value="' + (cur && cur[0] === "#" && cur.length === 7 ? cur : "#111827") + '">'; }
  function edProps() {
    var P = $("pe-ed-props"), o = ED.sel, t = o ? o.t : ED.tool, st = ED.st, h = "";
    if (msOn()) {
      var AL = [["l", "fa-align-left", "Kiri"], ["c", "fa-align-center", "Tengah"], ["r", "fa-align-right", "Kanan"], ["t", "fa-arrow-up-long", "Atas"], ["m", "fa-grip-lines", "Tengah ↕"], ["b", "fa-arrow-down-long", "Bawah"]];
      P.innerHTML = '<span class="pe-chip" style="--c:#4f46e5">' + ED.ms.length + ' objek dipilih</span><label>Ratakan</label>' + AL.map(function (a) { return '<button class="pe-b" data-al2="' + a[0] + '" style="height:28px"><i class="fa-solid ' + a[1] + '"></i>' + a[2] + "</button>"; }).join("")
        + '<label>Jarak sama</label><button class="pe-b" data-al2="dh" style="height:28px"><i class="fa-solid fa-arrows-left-right"></i>Mendatar</button><button class="pe-b" data-al2="dv" style="height:28px"><i class="fa-solid fa-arrows-up-down"></i>Tegak</button>'
        + '<span style="flex:1"></span><button class="pe-b" data-mdup style="height:28px"><i class="fa-regular fa-clone"></i>Duplikat</button><button class="pe-b red" data-mdel style="height:28px"><i class="fa-regular fa-trash-can"></i>Hapus</button>';
      P.querySelectorAll("[data-al2]").forEach(function (b) { b.onclick = function () { msAlign(b.dataset.al2); }; });
      P.querySelector("[data-mdup]").onclick = msDup; P.querySelector("[data-mdel]").onclick = msDel;
      return;
    }
    var v = function (k, d) { return o ? (o[k] == null ? d : o[k]) : d; };
    if (t === "text") {
      var font = v("font", st.font), size = v("size", st.size), c = v("c", st.tc), bg = v("bg", st.bg), opv = v("op", st.top), a = v("a", st.a);
      h = '<label>Font</label><select data-p="font">' + FONTS.map(function (f) { return '<option value="' + f.k + '" ' + (f.k === font ? "selected" : "") + ">" + E(f.label) + "</option>"; }).join("") + "</select>"
        + '<label>Ukuran</label><input type="number" data-p="size" min="5" max="120" step="1" value="' + size + '" style="width:58px">'
        + '<button class="pe-b ic ' + (v("b", st.b) ? "on" : "") + '" data-tg="b" title="Tebal"><b>B</b></button><button class="pe-b ic ' + (v("i", st.i) ? "on" : "") + '" data-tg="i" title="Miring"><i style="font-family:serif">I</i></button><button class="pe-b ic ' + (v("u", st.u) ? "on" : "") + '" data-tg="u" title="Garis bawah"><u>U</u></button>'
        + ["l", "c", "r"].map(function (x) { return '<button class="pe-b ic ' + (v("al", st.al) === x ? "on" : "") + '" data-al="' + x + '" title="Rata ' + { l: "kiri", c: "tengah", r: "kanan" }[x] + '"><i class="fa-solid fa-align-' + { l: "left", c: "center", r: "right" }[x] + '"></i></button>'; }).join("")
        + '<label>Warna</label>' + swatches(c, "c")
        + '<label>Latar</label><button class="pe-b ' + (bg ? "" : "on") + '" data-nobg style="height:28px">Tanpa</button><input type="color" data-col="bg" value="' + (bg || "#fff59d") + '">'
        + '<label>Transparansi</label><input type="range" data-p="op" min="0.1" max="1" step="0.05" value="' + opv + '" style="width:80px">'
        + '<label>Putar</label><input type="number" data-p="a" min="-180" max="360" step="5" value="' + a + '" style="width:58px"><button class="pe-b" data-rot="90" style="height:28px" title="Putar 90°"><i class="fa-solid fa-rotate-right"></i>Putar 90°</button>';
    } else if (t === "img") {
      var im = o && IMGS[o.ref], clean = !!(im && im.orig);
      h = '<label>Transparansi</label><input type="range" data-p="op" min="0.1" max="1" step="0.05" value="' + v("op", 1) + '" style="width:90px">'
        + '<button class="pe-b" data-rot="90" style="height:28px" title="Putar 90°"><i class="fa-solid fa-rotate-right"></i>Putar 90°</button>'
        + '<button class="pe-b ' + (clean ? "on" : "") + '" data-knock style="height:30px" title="Buat latar putih jadi transparan — cocok untuk stempel / tanda tangan hasil scan"><i class="fa-solid fa-wand-magic-sparkles"></i>Hapus latar putih</button>'
        + '<button class="pe-b" data-fit style="height:30px" title="Kembalikan rasio asli gambar"><i class="fa-solid fa-expand"></i>Rasio asli</button>'
        + '<button class="pe-b" data-repl style="height:30px"><i class="fa-solid fa-arrow-right-arrow-left"></i>Ganti gambar</button>'
        + '<span style="color:var(--pe-mute);font-size:11px">Tarik sudut: rasio tetap · tahan Shift: bebas</span>';
    } else if (t === "erase") {
      var f = v("fill", st.fill);
      h = '<label>Isi area</label>' + [["#ffffff", "Putih"], ["#000000", "Hitam (redaksi)"], ["auto", "Warna latar otomatis"]].map(function (x) { return '<button class="pe-b ' + (f === x[0] ? "on" : "") + '" data-fill="' + x[0] + '" style="height:28px">' + x[1] + "</button>"; }).join("")
        + '<span style="color:var(--pe-mute);font-size:11px"><i class="fa-solid fa-shield-halved mr-1"></i>Permanen: isi di bawah kotak dihapus dari file. Halaman ini disimpan sebagai gambar (teksnya tidak bisa dicari).</span>';
    } else if (t === "mark") {
      var M = ED.marks || [], nT = M.filter(function (x) { return x.kind === "ttd"; }).length, nS = M.filter(function (x) { return x.kind === "stempel"; }).length, nG = M.filter(function (x) { return x.kind === "gambar"; }).length;
      h = ED.detecting ? '<span class="pe-scan-txt"><i class="fa-solid fa-satellite-dish"></i>Memindai halaman…</span>'
        : '<span style="font-weight:700"><i class="fa-solid fa-stamp" style="color:#db2777"></i> ' + (M.length ? '<span class="pe-chip" style="--c:#2563eb">' + nT + ' tanda tangan</span><span class="pe-chip" style="--c:#db2777">' + nS + ' stempel</span>' + (nG ? '<span class="pe-chip" style="--c:#0891b2">' + nG + " gambar</span>" : "") : "Tidak ditemukan TTD / stempel") + "</span>"
        + '<button class="pe-b" data-rescan style="height:28px"><i class="fa-solid fa-rotate"></i>Pindai ulang</button><span style="color:var(--pe-mute);font-size:11px">Klik kotak hasil deteksi untuk memindah, menempel ke semua halaman, menyimpan, atau menghapus.</span>';
    } else if (t === "tedit") {
      var n = (ED.lines || []).length;
      h = '<span style="font-weight:700;color:' + (n ? "#0891b2" : "#d97706") + '"><i class="fa-solid ' + (n ? "fa-i-cursor" : "fa-triangle-exclamation") + ' mr-1"></i>' + (n ? n + " baris teks terdeteksi" + (ED.lines[0] && ED.lines[0].ocr ? " (OCR)" : "") + " — klik untuk mengedit" : "Halaman ini hasil scan / gambar — belum ada teks") + "</span>" + (n ? "" : '<button class="pe-b pri" data-ocr style="height:28px"><i class="fa-solid fa-glasses"></i>Jalankan OCR</button>')
        + '<label style="margin-left:6px">Teks lama</label>'
        + '<button class="pe-b ' + (ED.st.tmode !== "perm" ? "on" : "") + '" data-tm="cover" style="height:28px" title="Ditutup warna latar · halaman tetap tajam & teks lain bisa dicari">Tutup rapi</button>'
        + '<button class="pe-b ' + (ED.st.tmode === "perm" ? "on" : "") + '" data-tm="perm" style="height:28px" title="Benar-benar dihapus dari file · halaman disimpan sebagai gambar">Hapus permanen</button>';
    } else if (t === "note") {
      h = '<label>Warna catatan</label>' + NOTEC.map(function (c) { return '<button class="pe-sw ' + ((o ? o.c : st.nc || NOTEC[0]) === c ? "on" : "") + '" data-nc2="' + c + '" style="background:' + c + '"></button>'; }).join("") + '<span class="mute" style="color:var(--pe-mute);font-size:11px">Klik di halaman untuk menempel catatan · klik dua kali untuk membuka. Catatan tersimpan sebagai komentar PDF asli (terlihat di Acrobat / browser).</span>' + (o ? '<button class="pe-b" data-opn style="height:28px"><i class="fa-solid fa-pen"></i>Buka catatan</button>' : "");
    } else if (t === "link") {
      h = '<span style="color:var(--pe-mute);font-size:11px"><i class="fa-solid fa-link" style="color:#2563eb"></i> Tarik kotak di atas teks / gambar yang ingin dijadikan tautan — ke situs web, email, atau halaman lain di dokumen ini.</span>' + (o ? '<b style="font-size:11px">' + E(o.url || (o.page ? "→ halaman " + o.page : "")) + '</b><button class="pe-b" data-opn style="height:28px"><i class="fa-solid fa-pen"></i>Ubah tujuan</button>' : "");
    } else if (t === "crop") {
      var c0 = ED.crop;
      h = (c0 ? '<span class="pe-chip" style="--c:#059669">' + Math.round(c0.w * 0.3528) + " × " + Math.round(c0.h * 0.3528) + " mm</span>" : '<span style="color:var(--pe-mute);font-size:11px">Tarik kotak area yang <b>dipertahankan</b> — bagian di luar kotak dibuang.</span>')
        + '<button class="pe-b" data-cr="auto" style="height:28px"><i class="fa-solid fa-wand-magic-sparkles"></i>Potong otomatis</button><button class="pe-b" data-cr="autoAll" style="height:28px">Otomatis semua halaman</button>'
        + (c0 ? '<span class="sep" style="width:1px;height:20px;background:var(--pe-line)"></span><button class="pe-b pri" data-cr="cur" style="height:28px"><i class="fa-solid fa-crop-simple"></i>Potong halaman ini</button><button class="pe-b" data-cr="all" style="height:28px">Potong semua halaman</button><button class="pe-b" data-cr="x" style="height:28px">Batal</button>' : "");
    } else if (t === "form") {
      var nf = (ED.fields || []).length, filled = PE.form && edPage() && PE.form[edPage().d] ? Object.keys(PE.form[edPage().d]).length : 0;
      h = nf ? '<span style="font-weight:700;color:#7c3aed"><i class="fa-solid fa-rectangle-list"></i> ' + nf + " kolom isian di halaman ini" + (filled ? " · " + filled + " sudah diubah" : "") + '</span><span style="color:var(--pe-mute);font-size:11px">Klik kolom untuk mengisi · Tab = kolom berikutnya. Saat disimpan, isian dibuat permanen (diratakan).</span>' + (filled ? '<button class="pe-b" data-fclr style="height:28px"><i class="fa-solid fa-eraser"></i>Kosongkan isian</button>' : "")
        : '<span style="color:#d97706;font-weight:700"><i class="fa-solid fa-circle-info"></i> Halaman ini tidak punya kolom isian.</span><span style="color:var(--pe-mute);font-size:11px">Untuk formulir cetak (garis titik-titik), pakai <b>Tambah teks</b> lalu ketik di atas garisnya.</span><button class="pe-b" data-totext style="height:28px"><i class="fa-solid fa-font"></i>Tambah teks</button>';
    } else if (t === "sel" || t === "rub") {
      h = '<span style="color:var(--pe-mute)">' + (t === "sel" ? "Klik objek untuk mengatur · Shift+klik atau tarik kotak untuk memilih banyak · Ctrl+A pilih semua" : "Klik coretan / bentuk yang ingin dihapus.") + "</span>";
    } else {
      var isHl = t === "hl", col = v("c", isHl ? st.hlc : st.c), lw = v("lw", isHl ? st.hlw : st.lw), opv2 = v("op", isHl ? 0.4 : st.op);
      h = '<label>Warna</label>' + swatches(col, "c")
        + (t === "check" ? '<label>Ukuran</label><input type="range" data-p="w" min="8" max="60" step="1" value="' + v("w", 18) + '" style="width:100px">' : '<label>Tebal</label><input type="range" data-p="lw" min="0.5" max="' + (isHl ? 40 : 16) + '" step="0.5" value="' + lw + '" style="width:100px">')
        + (isHl ? "" : '<label>Transparansi</label><input type="range" data-p="op" min="0.1" max="1" step="0.05" value="' + opv2 + '" style="width:80px">');
    }
    if (o) h += '<span style="flex:1"></span><button class="pe-b red" data-delo style="height:28px"><i class="fa-regular fa-trash-can"></i>Hapus objek</button>';
    P.innerHTML = h;
    var setv = function (k, val, live) {
      var map = { c: t === "text" ? "tc" : t === "hl" ? "hlc" : "c", lw: t === "hl" ? "hlw" : "lw", op: t === "text" ? "top" : "op" };
      if (t !== "hl" || k !== "op") ED.st[map[k] || k] = val;
      if (o) { if (!live && !ED.propUndo) { pushUndo(); } ED.propUndo = !!live; o[k] = val; if (o.t === "text") { if (o.autoW) fitW(o); o.h = textH(o); if (k === "font") webFont(fontOf(val), o.b, o.i).then(function () { o.h = textH(o); edDraw(); if (ED.edit) edTextStyle(); }); } edDraw(); if (ED.edit) edTextStyle(); }
    };
    P.querySelectorAll("[data-p]").forEach(function (inp) {
      var num = inp.type !== "select-one";
      inp.oninput = function () { setv(inp.dataset.p, num ? parseFloat(inp.value) : inp.value, true); };
      inp.onchange = function () { ED.propUndo = false; setv(inp.dataset.p, num ? parseFloat(inp.value) : inp.value, false); ED.propUndo = false; renderSoon(); };
    });
    P.querySelectorAll("[data-sw]").forEach(function (b) { b.onclick = function () { setv("c", b.dataset.c); renderSoon(); edProps(); }; });
    P.querySelectorAll("[data-col]").forEach(function (inp) { inp.oninput = function () { setv(inp.dataset.col, inp.value, true); }; inp.onchange = function () { ED.propUndo = false; setv(inp.dataset.col, inp.value); ED.propUndo = false; renderSoon(); edProps(); }; });
    P.querySelectorAll("[data-tg]").forEach(function (b) { b.onclick = function () { var k = b.dataset.tg, cur = o ? !!o[k] : !!ED.st[k]; setv(k, !cur); if (k !== "u") webFont(fontOf(o ? o.font : ED.st.font), o ? o.b : ED.st.b, o ? o.i : ED.st.i).then(function () { if (o) o.h = textH(o); edDraw(); if (ED.edit) edTextStyle(); }); renderSoon(); edProps(); }; });
    P.querySelectorAll("[data-al]").forEach(function (b) { b.onclick = function () { setv("al", b.dataset.al); renderSoon(); edProps(); }; });
    P.querySelectorAll("[data-fill]").forEach(function (b) { b.onclick = function () { if (o) { pushUndo(); o.fill = b.dataset.fill; o.col = b.dataset.fill === "auto" ? sampleBg(o) : b.dataset.fill; edDraw(); renderSoon(); } ED.st.fill = b.dataset.fill; edProps(); }; });
    var nb = P.querySelector("[data-nobg]"); if (nb) nb.onclick = function () { setv("bg", ""); renderSoon(); edProps(); };
    var rb = P.querySelector("[data-rot]"); if (rb) rb.onclick = function () { var cur = o ? (o.a || 0) : ED.st.a; setv("a", (cur + 90) % 360); renderSoon(); edProps(); };
    var dl = P.querySelector("[data-delo]"); if (dl) dl.onclick = edDelSel;
    var rsc = P.querySelector("[data-rescan]"); if (rsc) rsc.onclick = function () { runDetect(true); };
    P.querySelectorAll("[data-nc2]").forEach(function (b) { b.onclick = function () { ED.st.nc = b.dataset.nc2; if (o && o.t === "note") { pushUndo(); o.c = b.dataset.nc2; edDraw(); } edProps(); }; });
    var opn = P.querySelector("[data-opn]"); if (opn && o) opn.onclick = function () { o.t === "note" ? notePop(o) : linkPop(o); };
    P.querySelectorAll("[data-cr]").forEach(function (b) { b.onclick = function () { var v = b.dataset.cr; if (v === "x") { ED.crop = null; edDraw(); edProps(); return; } cropApply(v); }; });
    var fcl = P.querySelector("[data-fclr]"); if (fcl) fcl.onclick = formClear;
    var tt = P.querySelector("[data-totext]"); if (tt) tt.onclick = function () { pickTool("text"); };
    var ocb = P.querySelector("[data-ocr]"); if (ocb) ocb.onclick = function () { ocrModal(); };
    P.querySelectorAll("[data-tm]").forEach(function (b) { b.onclick = function () { ED.st.tmode = b.dataset.tm; edProps(); }; });
    P.querySelectorAll("[data-ord]").forEach(function (b) { b.onclick = function () { edOrder(+b.dataset.ord); }; });
    var kn = P.querySelector("[data-knock]"); if (kn && o) kn.onclick = async function () { var im = IMGS[o.ref]; pushUndo(); if (im && im.orig) o.ref = im.orig; else { busy("Menghapus latar putih…", 50); try { o.ref = await knockWhite(o.ref); } catch (e) { toast(e.message, "error"); } busy(null); } edDraw(); edProps(); renderSoon(); };
    var ft = P.querySelector("[data-fit]"); if (ft && o) ft.onclick = function () { var im = IMGS[o.ref]; if (!im) return; pushUndo(); var cx = o.x + o.w / 2, cy = o.y + o.h / 2; o.h = o.w * im.h / im.w; o.x = cx - o.w / 2; o.y = cy - o.h / 2; edDraw(); };
    var rp = P.querySelector("[data-repl]"); if (rp && o) rp.onclick = function () { ED.replace = o; $("pe-img-in").click(); };
    var du = P.querySelector("[data-dupo]"); if (du) du.onclick = function () { var p = edPage(); pushUndo(); var c = clone(o); moveOp(c, 12, 12); p.ops.push(c); ED.sel = c; edDraw(); renderSoon(); edProps(); };
  }
  var rs = null; function renderSoon() { clearTimeout(rs); rs = setTimeout(function () { var p = edPage(); if (p) $("pe-ed-s").textContent = $("pe-ed-s").textContent.replace(/·.*$/, "· " + (p.ops.length ? p.ops.length + " objek" : "belum ada perubahan")); }, 50); }
  async function edAddImage(file, at) {
    var p = edPage(); if (!p) return;
    if (file.size > 15 * 1048576) return toast("Ukuran gambar maksimal 15 MB", "error");
    try {
      busy("Memuat gambar…", 40);
      var id = await fileToImage(file), im = IMGS[id], D = dims(p);
      var w = Math.min(D.w * 0.45, im.w * 0.75), h = w * im.h / im.w;
      if (h > D.h * 0.6) { h = D.h * 0.6; w = h * im.w / im.h; }
      var cx = at ? at.x : D.w / 2, cy = at ? at.y : D.h / 2;
      var o = { t: "img", ref: id, x: Math.max(0, Math.min(D.w - w, cx - w / 2)), y: Math.max(0, Math.min(D.h - h, cy - h / 2)), w: w, h: h, op: 1, a: 0 };
      pushUndo(); p.ops.push(o); ED.sel = o; ED.tool = "sel";
      busy(null); edTools(); edProps(); edDraw(); renderSoon(); fxPop();
      toast("Gambar ditambahkan — geser untuk memindah, tarik sudut untuk mengubah ukuran", "success", 4000);
    } catch (e) { busy(null); toast(e.message, "error"); }
  }
  function fxPop() { var pp = $("pe-ed-paper"); if (!pp) return; pp.classList.remove("pop"); void pp.offsetWidth; pp.classList.add("pop"); }
  function edOrder(dir) { var p = edPage(), o = ED.sel; if (!p || !o) return; var i = p.ops.indexOf(o); if (i < 0) return; pushUndo(); p.ops.splice(i, 1); if (dir > 0) p.ops.push(o); else { var k = 0; while (k < p.ops.length && p.ops[k].t === "erase") k++; p.ops.splice(k, 0, o); } edDraw(); }
  function edDelSel() { var p = edPage(); if (!p || !ED.sel) return; pushUndo(); p.ops.splice(p.ops.indexOf(ED.sel), 1); ED.sel = null; edDraw(); edProps(); renderSoon(); }

  // gambar overlay editor
  function edDraw() {
    var p = edPage(), ov = document.querySelector("#pe-ed-paper canvas.ov"); if (!p || !ov) return;
    var g = ov.getContext("2d"), k = ED.k * ED.dpr;
    g.clearRect(0, 0, ov.width, ov.height);
    drawOps(g, p.ops, k, { hide: ED.edit ? ED.edit.o : null, ed: 1 });
    if (ED.temp) drawOps(g, [ED.temp], k);
    if ((ED.tool === "tedit" || ED.hoverLine) && ED.lines && ED.lines.length) {
      var doneK = {}; p.ops.forEach(function (o) { if (o.key) doneK[o.key] = 1; });
      g.save(); g.scale(k, k); g.lineWidth = 1 / ED.k;
      ED.lines.forEach(function (l) {
        if (doneK[l.key]) return;
        var hv = ED.hoverLine === l;
        if (ED.tool !== "tedit" && !hv) return;
        g.fillStyle = hv ? "rgba(8,145,178,.16)" : "rgba(8,145,178,.05)"; g.fillRect(l.x - 1, l.top - 1, l.w + 2, l.h + 2);
        g.strokeStyle = hv ? "rgba(8,145,178,.95)" : "rgba(8,145,178,.45)"; g.setLineDash(hv ? [] : [3 / ED.k, 2 / ED.k]); g.strokeRect(l.x - 1, l.top - 1, l.w + 2, l.h + 2);
      });
      g.restore();
    }
    drawMarks(g, k, p); drawFind(g, k, p);
    if (ED.guides) { g.save(); g.scale(k, k); g.strokeStyle = "#ec4899"; g.lineWidth = 1 / ED.k; g.setLineDash([5 / ED.k, 4 / ED.k]); var D = dims(p); ED.guides.forEach(function (gd) { g.beginPath(); if (gd.x != null) { g.moveTo(gd.x, 0); g.lineTo(gd.x, D.h); } else { g.moveTo(0, gd.y); g.lineTo(D.w, gd.y); } g.stroke(); }); g.restore(); }
    if (ED.hoverOp && ED.hoverOp !== ED.sel && p.ops.indexOf(ED.hoverOp) >= 0 && ED.tool === "sel") { var hb = bbox(ED.hoverOp); g.save(); g.scale(k, k); g.strokeStyle = "rgba(79,70,229,.45)"; g.lineWidth = 1 / ED.k; g.strokeRect(hb.x - 2, hb.y - 2, hb.w + 4, hb.h + 4); g.restore(); }
    if (ED.tool === "crop" && ED.crop) { var Dk = dims(p), cr = ED.crop; g.save(); g.scale(k, k); g.fillStyle = "rgba(15,23,42,.5)"; g.fillRect(0, 0, Dk.w, cr.y); g.fillRect(0, cr.y + cr.h, Dk.w, Dk.h - cr.y - cr.h); g.fillRect(0, cr.y, cr.x, cr.h); g.fillRect(cr.x + cr.w, cr.y, Dk.w - cr.x - cr.w, cr.h); g.strokeStyle = "#10b981"; g.lineWidth = 2 / ED.k; g.strokeRect(cr.x, cr.y, cr.w, cr.h); g.lineWidth = 1 / ED.k; g.setLineDash([3 / ED.k, 3 / ED.k]); for (var gi = 1; gi < 3; gi++) { g.beginPath(); g.moveTo(cr.x + cr.w * gi / 3, cr.y); g.lineTo(cr.x + cr.w * gi / 3, cr.y + cr.h); g.moveTo(cr.x, cr.y + cr.h * gi / 3); g.lineTo(cr.x + cr.w, cr.y + cr.h * gi / 3); g.stroke(); } g.restore(); }
    if (ED.box) { g.save(); g.scale(k, k); g.fillStyle = "rgba(79,70,229,.08)"; g.strokeStyle = "#4f46e5"; g.lineWidth = 1 / ED.k; g.setLineDash([4 / ED.k, 3 / ED.k]); g.fillRect(ED.box.x, ED.box.y, ED.box.w, ED.box.h); g.strokeRect(ED.box.x, ED.box.y, ED.box.w, ED.box.h); g.restore(); }
    if (msOn()) {
      ED.ms = ED.ms.filter(function (q) { return p.ops.indexOf(q) >= 0; });
      var G = msBox(); g.save(); g.scale(k, k); g.lineWidth = 1.2 / ED.k; g.strokeStyle = "#4f46e5";
      ED.ms.forEach(function (q) { var bq = bbox(q); g.setLineDash([]); g.fillStyle = "rgba(79,70,229,.06)"; g.fillRect(bq.x - 2, bq.y - 2, bq.w + 4, bq.h + 4); g.strokeRect(bq.x - 2, bq.y - 2, bq.w + 4, bq.h + 4); });
      if (G) { g.setLineDash([6 / ED.k, 4 / ED.k]); g.strokeRect(G.x - 6, G.y - 6, G.w + 12, G.h + 12); g.setLineDash([]); var lab = ED.ms.length + " objek"; g.font = "700 " + 10 / ED.k + "px sans-serif"; var lw = g.measureText(lab).width + 10 / ED.k; g.fillStyle = "#4f46e5"; g.fillRect(G.x - 6, G.y - 6 - 16 / ED.k, lw, 15 / ED.k); g.fillStyle = "#fff"; g.fillText(lab, G.x - 6 + 5 / ED.k, G.y - 6 - 5 / ED.k); }
      g.restore();
    }
    var o = ED.sel;
    if (o && p.ops.indexOf(o) >= 0) {
      var b = bbox(o), W = o.w, H = o.t === "check" ? o.w : o.h;
      g.save(); g.scale(k, k); g.lineWidth = 1.5 / ED.k; g.strokeStyle = "#4f46e5"; g.shadowColor = "rgba(79,70,229,.35)"; g.shadowBlur = 6 * ED.dpr;
      if (rotatable(o) || o.x != null) { var cs = [toWorld(o, -2, -2), toWorld(o, W + 2, -2), toWorld(o, W + 2, H + 2), toWorld(o, -2, H + 2)]; g.beginPath(); g.moveTo(cs[0][0], cs[0][1]); cs.slice(1).forEach(function (c) { g.lineTo(c[0], c[1]); }); g.closePath(); g.stroke(); }
      else g.strokeRect(b.x - 2, b.y - 2, b.w + 4, b.h + 4);
      g.shadowBlur = 0;
      handlesOf(o).forEach(function (hd) {
        var r = 4.5 / ED.k;
        if (hd.id === "rot") { g.beginPath(); g.moveTo(hd.top[0], hd.top[1]); g.lineTo(hd.p[0], hd.p[1]); g.stroke(); g.beginPath(); g.arc(hd.p[0], hd.p[1], r * 1.4, 0, Math.PI * 2); g.fillStyle = "#fff"; g.fill(); g.stroke(); g.beginPath(); g.arc(hd.p[0], hd.p[1], r * 0.55, 0, Math.PI * 2); g.fillStyle = "#4f46e5"; g.fill(); return; }
        g.fillStyle = "#fff"; g.beginPath(); g.rect(hd.p[0] - r, hd.p[1] - r, r * 2, r * 2); g.fill(); g.stroke();
      });
      if (ED.drag && ED.drag.mode === "rot" && ED.drag.moved) { g.font = 600 * 0 + 11 / ED.k + "px sans-serif"; g.fillStyle = "#4f46e5"; g.fillText(Math.round(o.a || 0) + "°", o.x + W / 2 + 14 / ED.k, o.y - 30 / ED.k); }
      g.restore();
    }
    qbar();
  }
  function bbox(o) {
    if (o.pts) { var xs = o.pts.map(function (q) { return q[0]; }), ys = o.pts.map(function (q) { return q[1]; }), pad = o.lw / 2; return { x: Math.min.apply(null, xs) - pad, y: Math.min.apply(null, ys) - pad, w: Math.max.apply(null, xs) - Math.min.apply(null, xs) + 2 * pad, h: Math.max.apply(null, ys) - Math.min.apply(null, ys) + 2 * pad }; }
    if (o.x1 != null) return { x: Math.min(o.x1, o.x2) - o.lw, y: Math.min(o.y1, o.y2) - o.lw, w: Math.abs(o.x2 - o.x1) + 2 * o.lw, h: Math.abs(o.y2 - o.y1) + 2 * o.lw };
    if (o.t === "check") return { x: o.x, y: o.y, w: o.w, h: o.w };
    return { x: o.x, y: o.y, w: o.w, h: o.h };
  }
  var rotatable = function (o) { return o.t === "text" || o.t === "img"; };
  function handlesOf(o) {
    if (!resizable(o)) return [];
    var W = o.w, H = o.t === "check" ? o.w : o.h, ids = o.t === "check" ? ["se"] : o.t === "text" ? ["w", "e"] : ["nw", "n", "ne", "e", "se", "s", "sw", "w"];
    var loc = { nw: [0, 0], n: [W / 2, 0], ne: [W, 0], e: [W, H / 2], se: [W, H], s: [W / 2, H], sw: [0, H], w: [0, H / 2] };
    var out = ids.map(function (id) { return { id: id, p: toWorld(o, loc[id][0], loc[id][1]) }; });
    if (rotatable(o)) out.push({ id: "rot", p: toWorld(o, W / 2, -26 / ED.k), top: toWorld(o, W / 2, 0) });
    return out;
  }
  function toWorld(o, u, v) { var W = o.w, H = o.t === "check" ? o.w : o.h, a = rotatable(o) ? (o.a || 0) * Math.PI / 180 : 0, dx = u - W / 2, dy = v - H / 2; return [o.x + W / 2 + dx * Math.cos(a) - dy * Math.sin(a), o.y + H / 2 + dx * Math.sin(a) + dy * Math.cos(a)]; }
  function handleAt(o, pt) { var hs = handlesOf(o), r = 9 / ED.k; for (var i = hs.length - 1; i >= 0; i--) if (Math.hypot(pt.x - hs[i].p[0], pt.y - hs[i].p[1]) <= r) return hs[i].id; return null; }
  var CURS = { nw: "nwse-resize", se: "nwse-resize", ne: "nesw-resize", sw: "nesw-resize", n: "ns-resize", s: "ns-resize", e: "ew-resize", w: "ew-resize", rot: "grab" };
  function snapMove(o, o0, dx, dy, free) {
    ED.guides = null; if (free) return [dx, dy];
    var p = edPage(), D = dims(p), b = bbox(o0), thr = 6 / ED.k;
    var X = [0, D.w / 2, D.w], Y = [0, D.h / 2, D.h];
    p.ops.forEach(function (q) { if (q === ED.sel || q.t === "mask") return; var bb = bbox(q); X.push(bb.x, bb.x + bb.w / 2, bb.x + bb.w); Y.push(bb.y, bb.y + bb.h / 2, bb.y + bb.h); });
    var best = function (vals, targets) { var r = null; vals.forEach(function (v) { targets.forEach(function (t) { var d = t - v; if (Math.abs(d) <= thr && (!r || Math.abs(d) < Math.abs(r.d))) r = { d: d, t: t }; }); }); return r; };
    var sx = best([b.x + dx, b.x + b.w / 2 + dx, b.x + b.w + dx], X), sy = best([b.y + dy, b.y + b.h / 2 + dy, b.y + b.h + dy], Y), g = [];
    if (sx) { dx += sx.d; g.push({ x: sx.t }); } if (sy) { dy += sy.d; g.push({ y: sy.t }); }
    ED.guides = g.length ? g : null; return [dx, dy];
  }
  function resizeOp(s, b0, hid, dx, dy, free) {
    if (s.t === "check") { s.w = Math.max(6, b0.w + Math.max(dx, dy)); return; }
    var a = rotatable(s) ? (s.a || 0) * Math.PI / 180 : 0, ux = dx * Math.cos(-a) - dy * Math.sin(-a), uy = dx * Math.sin(-a) + dy * Math.cos(-a);
    var L = 0, T = 0, R = b0.w, B = b0.h;
    if (/w/.test(hid)) L += ux; if (/e/.test(hid)) R += ux; if (/^n/.test(hid)) T += uy; if (/^s/.test(hid)) B += uy;
    var min = s.t === "text" ? 24 : 6;
    if (R - L < min) { if (/w/.test(hid)) L = R - min; else R = L + min; }
    if (B - T < min) { if (/^n/.test(hid)) T = B - min; else B = T + min; }
    if (s.t === "img" && hid.length === 2 && !free) {   // sudut gambar: rasio tetap
      var r0 = b0.w / b0.h, nw = R - L, nh = B - T;
      if (nw / nh > r0) { nw = nh * r0; if (/w/.test(hid)) L = R - nw; else R = L + nw; } else { nh = nw / r0; if (/^n/.test(hid)) T = B - nh; else B = T + nh; }
    }
    var nw2 = R - L, nh2 = s.t === "text" ? b0.h : B - T, cxl = (L + R) / 2 - b0.w / 2, cyl = (s.t === "text" ? b0.h / 2 : (T + B) / 2) - b0.h / 2;
    var cx = b0.x + b0.w / 2 + cxl * Math.cos(a) - cyl * Math.sin(a), cy = b0.y + b0.h / 2 + cxl * Math.sin(a) + cyl * Math.cos(a);
    s.w = nw2; if (s.t === "text") { s.autoW = false; s.h = textH(s); } else s.h = nh2;
    s.x = cx - s.w / 2; s.y = cy - (s.t === "text" ? b0.h : s.h) / 2;
    if (s.t === "erase" && s.fill === "auto") s.col = sampleBg(s);
  }
  // bilah aksi cepat yang melayang di atas objek terpilih
  function qbar() {
    var q = $("pe-qbar"), o = ED.sel, p = edPage(); if (!q) return;
    var mpo = $("pe-mpop");
    if (!o || !p || p.ops.indexOf(o) < 0 || (ED.drag && ED.drag.moved) || ED.edit || (mpo && !mpo.classList.contains("hidden"))) { q.classList.add("hidden"); return; }
    var b = bbox(o), k = ED.k;
    if (rotatable(o) && o.a) { var cs = [toWorld(o, 0, 0), toWorld(o, o.w, 0), toWorld(o, 0, o.h), toWorld(o, o.w, o.h)]; var xs = cs.map(function (c) { return c[0]; }), ys = cs.map(function (c) { return c[1]; }); b = { x: Math.min.apply(null, xs), y: Math.min.apply(null, ys), w: Math.max.apply(null, xs) - Math.min.apply(null, xs), h: 0 }; }
    var sig = o.t + (o.t === "text" ? 1 : 0) + "v2";
    if (q.dataset.sig !== sig) {
      q.dataset.sig = sig;
      q.innerHTML = (o.t === "text" || o.t === "note" || o.t === "link" ? '<button data-q="edit" title="Edit"><i class="fa-solid ' + (o.t === "text" ? "fa-i-cursor" : "fa-pen") + '"></i><b>' + (o.t === "note" ? "Buka catatan" : o.t === "link" ? "Ubah tujuan" : "Edit") + "</b></button>" : "")
        + '<button data-q="dup" title="Duplikat (Ctrl+D)"><i class="fa-regular fa-clone"></i><b>Duplikat</b></button><button data-q="front" title="Bawa ke depan"><i class="fa-solid fa-arrow-up-wide-short"></i><b>Depan</b></button><button data-q="back" title="Kirim ke belakang"><i class="fa-solid fa-arrow-down-short-wide"></i><b>Belakang</b></button>'
        + (o.t === "img" ? '<button data-q="all" title="Tempel ke halaman lain (paraf / stempel semua halaman)"><i class="fa-solid fa-layer-group"></i><b>Semua hal.</b></button><button data-q="lib" title="Simpan gambar ini ke pustaka"><i class="fa-solid fa-book-bookmark"></i><b>Simpan</b></button>' : "")
        + '<span></span><button data-q="del" class="red" title="Hapus (Del)"><i class="fa-regular fa-trash-can"></i><b>Hapus</b></button>';
      q.querySelectorAll("[data-q]").forEach(function (bt) { bt.onpointerdown = function (e) { e.stopPropagation(); }; bt.onclick = function (e) { e.stopPropagation(); var o2 = ED.sel; if (!o2) return; var a = bt.dataset.q; if (a === "edit") { if (o2.t === "note") notePop(o2); else if (o2.t === "link") linkPop(o2); else edText(o2); } else if (a === "dup") edDup(); else if (a === "front") edOrder(1); else if (a === "back") edOrder(-1); else if (a === "del") edDelSel(); else if (a === "all") stampAll(o2); else if (a === "lib") { var im = IMGS[o2.ref]; if (im) libAdd({ kind: "gambar", bytes: im.bytes, mime: im.mime, name: "Gambar · " + (safeName(PE.base) || "dokumen") }).then(function () { toast("Tersimpan di Pustaka TTD & stempel", "success"); }); } }; });
    }
    q.classList.remove("hidden");
    var top = b.y * k - q.offsetHeight - (rotatable(o) ? 40 : 12);
    q.style.left = Math.max(4, Math.min($("pe-ed-paper").offsetWidth - q.offsetWidth - 4, (b.x + b.w / 2) * k - q.offsetWidth / 2)) + "px";
    q.style.top = (top < 4 ? (b.y + (b.h || 0)) * k + 14 : top) + "px";
  }
  // ---------- pilih banyak objek: Shift+klik, tarik kotak, Ctrl+A ----------
  var msOn = function () { return !!(ED.ms && ED.ms.length > 1); };
  function msBox() { if (!ED.ms || !ED.ms.length) return null; var bs = ED.ms.map(bbox), x0 = Math.min.apply(null, bs.map(function (b) { return b.x; })), y0 = Math.min.apply(null, bs.map(function (b) { return b.y; })), x1 = Math.max.apply(null, bs.map(function (b) { return b.x + b.w; })), y1 = Math.max.apply(null, bs.map(function (b) { return b.y + b.h; })); return { x: x0, y: y0, w: x1 - x0, h: y1 - y0 }; }
  function msToggle(h) { var L = msOn() ? ED.ms.slice() : (ED.sel ? [ED.sel] : []), i = L.indexOf(h); if (i >= 0) L.splice(i, 1); else L.push(h); if (L.length > 1) { ED.ms = L; ED.sel = null; } else { ED.ms = []; ED.sel = L[0] || null; } edProps(); edDraw(); }
  function msAll() { var p = edPage(); if (!p) return; edCommitText(); var L = p.ops.filter(function (o) { return o.t !== "mask"; }); if (!L.length) return toast("Belum ada objek di halaman ini", "info"); if (ED.tool !== "sel") { ED.tool = "sel"; edTools(); } if (L.length === 1) { ED.sel = L[0]; ED.ms = []; } else { ED.sel = null; ED.ms = L; } edProps(); edDraw(); }
  function msDel() { var p = edPage(); if (!p || !msOn()) return; pushUndo(); var n = ED.ms.length; p.ops = p.ops.filter(function (o) { return ED.ms.indexOf(o) < 0; }); ED.ms = []; edProps(); edDraw(); renderSoon(); toast(n + " objek dihapus — Ctrl+Z untuk mengembalikan", "info"); }
  function msDup() { var p = edPage(); if (!p || !msOn()) return; pushUndo(); var cs = ED.ms.map(function (o) { var c = clone(o); delete c.src; delete c.key; moveOp(c, 12, 12); p.ops.push(c); return c; }); ED.ms = cs; edProps(); edDraw(); renderSoon(); }
  function msAlign(k) {
    var G = msBox(); if (!G) return; pushUndo();
    if (k === "dh" || k === "dv") {
      var hz = k === "dh", L = ED.ms.slice().sort(function (a, b) { var A = bbox(a), B = bbox(b); return hz ? A.x - B.x : A.y - B.y; });
      if (L.length < 3) { PE.undo.pop(); syncUndo(); return toast("Perlu minimal 3 objek untuk meratakan jarak", "info"); }
      var tot = L.reduce(function (s, o) { var b = bbox(o); return s + (hz ? b.w : b.h); }, 0), gap = ((hz ? G.w : G.h) - tot) / (L.length - 1), cur = hz ? G.x : G.y;
      L.forEach(function (o) { var b = bbox(o); if (hz) moveOp(o, cur - b.x, 0); else moveOp(o, 0, cur - b.y); cur += (hz ? b.w : b.h) + gap; });
    } else ED.ms.forEach(function (o) { var b = bbox(o); moveOp(o, k === "l" ? G.x - b.x : k === "c" ? G.x + G.w / 2 - b.x - b.w / 2 : k === "r" ? G.x + G.w - b.x - b.w : 0, k === "t" ? G.y - b.y : k === "m" ? G.y + G.h / 2 - b.y - b.h / 2 : k === "b" ? G.y + G.h - b.y - b.h : 0); });
    edDraw(); renderSoon();
  }
  function edDup() { var p = edPage(), o = ED.sel; if (!p || !o) return; pushUndo(); var c = clone(o); delete c.src; delete c.key; moveOp(c, 12, 12); p.ops.push(c); ED.sel = c; edDraw(); edProps(); renderSoon(); }
  var resizable = function (o) { return o.t === "text" || o.t === "img" || o.t === "rect" || o.t === "ellipse" || o.t === "erase" || o.t === "check" || o.t === "link"; };
  function handlePt(o) { if (o.t === "check") return [o.x + o.w, o.y + o.w]; if ((o.t === "text" || o.t === "img") && o.a) { var a = o.a * Math.PI / 180, dx = o.w / 2, dy = o.h / 2; return [o.x + o.w / 2 + dx * Math.cos(a) - dy * Math.sin(a), o.y + o.h / 2 + dx * Math.sin(a) + dy * Math.cos(a)]; } return [o.x + o.w, o.y + o.h]; }
  function distSeg(p, a, b) { var dx = b[0] - a[0], dy = b[1] - a[1], l = dx * dx + dy * dy, t = l ? Math.max(0, Math.min(1, ((p.x - a[0]) * dx + (p.y - a[1]) * dy) / l)) : 0; return Math.hypot(p.x - a[0] - t * dx, p.y - a[1] - t * dy); }
  function hitOp(o, pt, tol) {
    if (o.pts) { if (o.pts.length === 1) return Math.hypot(pt.x - o.pts[0][0], pt.y - o.pts[0][1]) <= o.lw / 2 + tol; for (var i = 1; i < o.pts.length; i++) if (distSeg(pt, o.pts[i - 1], o.pts[i]) <= o.lw / 2 + tol) return true; return false; }
    if (o.x1 != null) return distSeg(pt, [o.x1, o.y1], [o.x2, o.y2]) <= o.lw / 2 + tol || (o.t === "arrow" && Math.hypot(pt.x - o.x2, pt.y - o.y2) < o.lw * 4 + tol);
    if ((o.t === "text" || o.t === "img") && o.a) { var a = -o.a * Math.PI / 180, cx = o.x + o.w / 2, cy = o.y + o.h / 2, dx = pt.x - cx, dy = pt.y - cy, ux = dx * Math.cos(a) - dy * Math.sin(a), uy = dx * Math.sin(a) + dy * Math.cos(a); return Math.abs(ux) <= o.w / 2 + tol && Math.abs(uy) <= o.h / 2 + tol; }
    if (o.t === "rect" || o.t === "ellipse") { var b = bbox(o), inside = pt.x >= b.x - tol && pt.x <= b.x + b.w + tol && pt.y >= b.y - tol && pt.y <= b.y + b.h + tol; if (!inside) return false; if (o.t === "rect") return pt.x <= b.x + o.lw + tol * 1.5 || pt.x >= b.x + b.w - o.lw - tol * 1.5 || pt.y <= b.y + o.lw + tol * 1.5 || pt.y >= b.y + b.h - o.lw - tol * 1.5 || ED.tool === "sel"; return true; }
    var bb = bbox(o); return pt.x >= bb.x - tol && pt.x <= bb.x + bb.w + tol && pt.y >= bb.y - tol && pt.y <= bb.y + bb.h + tol;
  }
  function hit(pt, filter) { var p = edPage(), tol = 5 / ED.k; for (var i = p.ops.length - 1; i >= 0; i--) { var o = p.ops[i]; if (o.t === "mask" || (filter && !filter(o))) continue; if (hitOp(o, pt, tol)) return o; } return null; }
  function moveOp(o, dx, dy) { if (o.pts) o.pts = o.pts.map(function (q) { return [q[0] + dx, q[1] + dy]; }); if (o.x1 != null) { o.x1 += dx; o.x2 += dx; o.y1 += dy; o.y2 += dy; } if (o.x != null) { o.x += dx; o.y += dy; } }
  function edPt(e) { var r = e.target.getBoundingClientRect(); return { x: (e.clientX - r.left) / ED.k, y: (e.clientY - r.top) / ED.k }; }
  function sampleBg(o, cv, DD) {
    var c = cv || ED.base; if (!c) return "#ffffff";
    try {
      var g = c.getContext("2d"), s = c.width / (DD || dims(edPage())).w, x0 = Math.max(0, Math.floor(o.x * s) - 3), y0 = Math.max(0, Math.floor(o.y * s) - 3), x1 = Math.min(c.width - 1, Math.ceil((o.x + o.w) * s) + 3), y1 = Math.min(c.height - 1, Math.ceil((o.y + o.h) * s) + 3);
      var acc = [0, 0, 0], n = 0, add = function (x, y, w, h) { if (w <= 0 || h <= 0) return; var d = g.getImageData(x, y, w, h).data; for (var i = 0; i < d.length; i += 4) { acc[0] += d[i]; acc[1] += d[i + 1]; acc[2] += d[i + 2]; n++; } };
      add(x0, y0, x1 - x0, 3); add(x0, y1 - 3, x1 - x0, 3); add(x0, y0, 3, y1 - y0); add(x1 - 3, y0, 3, y1 - y0);
      if (!n) return "#ffffff";
      return "#" + acc.map(function (v) { return ("0" + Math.round(v / n).toString(16)).slice(-2); }).join("");
    } catch (e) { return "#ffffff"; }
  }

  var PTR = new Map();
  function pinchDist() { var a = Array.from(PTR.values()); return Math.hypot(a[0].x - a[1].x, a[0].y - a[1].y); }
  function edDown(e) {
    var p = edPage(); if (!p || e.button > 0) return;
    e.preventDefault();   // cegah fokus pindah dari kotak teks
    PTR.set(e.pointerId, { x: e.clientX, y: e.clientY });
    if (PTR.size === 2) {   // mulai cubit: batalkan goresan / geseran yang sedang berjalan
      if (ED.drag && ED.drag.o0 && ED.drag.moved && ED.sel) { Object.keys(ED.drag.o0).forEach(function (k) { ED.sel[k] = clone(ED.drag.o0[k]); }); PE.undo.pop(); syncUndo(); }
      ED.temp = null; ED.drag = null;
      var st0 = $("pe-ed-stage"); ED.pinch = { d0: pinchDist(), z0: ED.zoom, sl: st0.scrollLeft, stp: st0.scrollTop };
      edDraw(); return;
    }
    if (PTR.size > 2 || ED.pinch) return;
    // HP: alat ketuk (edit teks, deteksi, catatan, dll.) → satu jari tetap bisa menggulir; aksi dijalankan saat ketukan dilepas
    if (e.pointerType === "touch" && TAPT.test(ED.tool) && !(ED.sel && handleAt(ED.sel, edPt(e)))) { ED.tap = { x: e.clientX, y: e.clientY, id: e.pointerId, target: e.target, t0: Date.now() }; return; }
    if (ED.edit) { edCommitText(); return; }
    var pt = edPt(e), st = ED.st, t = ED.tool;
    try { e.target.setPointerCapture(e.pointerId); } catch (er) { }
    ED.drag = { x: pt.x, y: pt.y, moved: false };
    if (t === "sel" || (ED.sel && handleAt(ED.sel, pt))) {
      var o = ED.sel, hid = o ? handleAt(o, pt) : null;
      if (hid) { ED.drag.mode = hid === "rot" ? "rot" : "resize"; ED.drag.hid = hid; ED.drag.o0 = clone(o); return; }
      var h = hit(pt);
      if (e.shiftKey && h && t === "sel") { msToggle(h); ED.drag = null; return; }
      if (msOn() && h && ED.ms.indexOf(h) >= 0) { ED.drag.mode = "mmove"; ED.drag.o0s = ED.ms.map(clone); return; }
      ED.ms = []; ED.sel = h; edProps(); edDraw();
      if (h) { ED.drag.mode = "move"; ED.drag.o0 = clone(h); }
      else if (e.pointerType === "touch") { var sg = $("pe-ed-stage"); ED.drag.mode = "pan"; ED.drag.cx = e.clientX; ED.drag.cy = e.clientY; ED.drag.sl = sg.scrollLeft; ED.drag.st = sg.scrollTop; }
      else if (t === "sel") { ED.drag.mode = "box"; ED.box = { x: pt.x, y: pt.y, w: 0, h: 0 }; }
      return;
    }
    if (t === "rub") { ED.drag.mode = "rub"; edRub(pt); return; }
    if (t === "mark") {
      ED.drag = null; var mk = markAt(pt);
      if (mk) { markPop(mk); return; }
      var hx2 = hit(pt); hidePop(); if (hx2) { ED.sel = hx2; edProps(); edDraw(); }
      return;
    }
    if (t === "tedit") {
      ED.drag = null;
      var hx = hit(pt, function (o) { return o.t === "text"; });
      if (hx) { ED.sel = hx; edProps(); edText(hx); return; }
      var ln = lineAt(pt);
      if (ln) editLine(ln);
      else { ED.sel = null; edProps(); edDraw(); if (!(ED.lines && ED.lines.length)) toast("Halaman ini tidak punya teks asli (hasil scan / gambar). Gunakan Tambah teks + Hapus area.", "info", 4000); }
      return;
    }
    if (t === "text") {
      var ht = hit(pt, function (o) { return o.t === "text"; });
      if (ht) { ED.sel = ht; edProps(); edText(ht); ED.drag = null; return; }
      pushUndo();
      var nt = { t: "text", x: pt.x, y: pt.y - st.size * 0.8, w: Math.min(260, dims(p).w - pt.x - 6), text: "", font: st.font, size: st.size, b: st.b, i: st.i, u: st.u, al: st.al, c: st.tc, bg: st.bg, op: st.top, a: st.a };
      nt.w = Math.max(60, nt.w); if (nt.x + nt.w > dims(p).w) nt.x = Math.max(0, dims(p).w - nt.w - 4);
      nt.h = textH(nt); p.ops.push(nt); ED.sel = nt; edProps(); edText(nt, true); ED.drag = null; return;
    }
    if (t === "check") { pushUndo(); var ck = { t: "check", x: pt.x - 9, y: pt.y - 12, w: 18, c: st.c, lw: 2, op: st.op }; p.ops.push(ck); ED.sel = ck; ED.tool = "sel"; edTools(); edProps(); edDraw(); renderSoon(); ED.drag = null; return; }
    if (t === "pen" || t === "hl") { ED.temp = { t: t, pts: [[pt.x, pt.y]], c: t === "hl" ? st.hlc : st.c, lw: t === "hl" ? st.hlw : st.lw, op: t === "hl" ? 0.4 : st.op }; ED.drag.mode = "draw"; edDraw(); return; }
    if (t === "line" || t === "arrow") { ED.temp = { t: t, x1: pt.x, y1: pt.y, x2: pt.x, y2: pt.y, c: st.c, lw: st.lw, op: st.op }; ED.drag.mode = "draw"; return; }
    if (t === "note") { pushUndo(); var no = { t: "note", x: Math.max(0, pt.x - 9), y: Math.max(0, pt.y - 9), w: 18, h: 18, text: "", c: st.nc || NOTEC[0], by: uName() }; p.ops.push(no); ED.sel = no; ED.drag = null; edDraw(); notePop(no, true); return; }
    if (t === "crop") { ED.drag.mode = "crop"; ED.crop = { x: pt.x, y: pt.y, w: 0, h: 0 }; edDraw(); return; }
    if (t === "form") { ED.drag = null; return; }
    if (t === "link") { ED.temp = { t: "link", x: pt.x, y: pt.y, w: 0, h: 0, c: "#2563eb", url: "", page: 0 }; ED.drag.mode = "draw"; return; }
    if (t === "rect" || t === "ellipse" || t === "erase") { ED.temp = t === "erase" ? { t: "erase", x: pt.x, y: pt.y, w: 0, h: 0, fill: st.fill, col: st.fill === "auto" ? "#e2e8f0" : st.fill } : { t: t, x: pt.x, y: pt.y, w: 0, h: 0, c: st.c, lw: st.lw, op: st.op }; ED.drag.mode = "draw"; return; }
  }
  function edMove(e) {
    if (PTR.has(e.pointerId)) PTR.set(e.pointerId, { x: e.clientX, y: e.clientY });
    if (ED.pinch) { if (PTR.size === 2) { var sc = pinchDist() / ED.pinch.d0, z = Math.max(0.4, Math.min(4, ED.pinch.z0 * sc)); ED.pinch.z = z; $("pe-ed-paper").style.transform = "scale(" + (z / ED.pinch.z0) + ")"; } return; }
    var d = ED.drag;
    if (!d) {
      if (e.pointerType === "touch") return;
      var hp0 = edPt(e), cur = "";
      if (ED.sel) { var hh = handleAt(ED.sel, hp0); if (hh) cur = CURS[hh]; }
      if (ED.tool === "tedit") { var hl = lineAt(hp0); if (hl !== ED.hoverLine) { ED.hoverLine = hl; edDraw(); } if (!cur && hl) cur = "text"; }
      else if (ED.tool === "sel") { var ho = hit(hp0); if (ho !== ED.hoverOp) { ED.hoverOp = ho; edDraw(); } if (!cur && ho) cur = "move"; }
      else if (ED.tool === "mark") { var hm = markAt(hp0); if (hm !== ED.hoverMark) { ED.hoverMark = hm; edDraw(); } if (hm) cur = "pointer"; }
      else if (/^(pen|hl|line|arrow|rect|ellipse|erase|check|text|note|link|crop)$/.test(ED.tool)) cur = "crosshair";
      e.target.style.cursor = cur; return;
    }
    if (d.mode === "pan") { var sg = $("pe-ed-stage"); sg.scrollLeft = d.sl - (e.clientX - d.cx); sg.scrollTop = d.st - (e.clientY - d.cy); return; }
    var pt = edPt(e), p = edPage(), dx = pt.x - d.x, dy = pt.y - d.y;
    if (Math.abs(dx) + Math.abs(dy) > 1.5 / ED.k) { if (!d.moved && (d.mode === "move" || d.mode === "resize" || d.mode === "mmove")) pushUndo(); d.moved = true; }
    if (d.mode === "crop") { var Dc = dims(p), cx0 = Math.max(0, Math.min(d.x, pt.x)), cy0 = Math.max(0, Math.min(d.y, pt.y)); ED.crop = { x: cx0, y: cy0, w: Math.min(Dc.w, Math.max(d.x, pt.x)) - cx0, h: Math.min(Dc.h, Math.max(d.y, pt.y)) - cy0 }; edDraw(); return; }
    if (d.mode === "box") { ED.box = { x: Math.min(d.x, pt.x), y: Math.min(d.y, pt.y), w: Math.abs(dx), h: Math.abs(dy) }; edDraw(); return; }
    if (d.mode === "mmove") { if (d.moved) { ED.ms.forEach(function (o, i) { var o0 = d.o0s[i]; Object.keys(o0).forEach(function (k) { o[k] = clone(o0[k]); }); moveOp(o, dx, dy); }); edDraw(); } return; }
    if (d.mode === "move" && d.moved) { var o = ED.sel, o0 = d.o0; Object.keys(o0).forEach(function (k) { o[k] = clone(o0[k]); }); var sn = snapMove(o, o0, dx, dy, e.altKey); moveOp(o, sn[0], sn[1]); edDraw(); }
    else if (d.mode === "rot" && d.moved) {
      var ro = ED.sel, rc = toWorld(ro, ro.w / 2, ro.h / 2), ang = Math.atan2(pt.y - rc[1], pt.x - rc[0]) * 180 / Math.PI + 90;
      ang = ((ang % 360) + 360) % 360; if (!e.shiftKey) { var sn15 = Math.round(ang / 15) * 15; if (Math.abs(sn15 - ang) < 4) ang = sn15 % 360; }
      ro.a = Math.round(ang * 10) / 10; edDraw(); if (ED.edit) edTextStyle();
    }
    else if (d.mode === "resize" && d.moved && d.hid) { resizeOp(ED.sel, d.o0, d.hid, dx, dy, e.shiftKey); edDraw(); if (ED.edit) edTextStyle(); }
    else if (d.mode === "resize" && d.moved) {
      var s = ED.sel, b0 = d.o0;
      if (s.t === "check") s.w = Math.max(6, b0.w + Math.max(dx, dy));
      else if (s.t === "text") { var a = -(s.a || 0) * Math.PI / 180, ux = dx * Math.cos(a) - dy * Math.sin(a); s.autoW = false; s.w = Math.max(24, b0.w + ux); s.h = textH(s); }
      else if (s.t === "img") {
        var ra = -(s.a || 0) * Math.PI / 180, rx = dx * Math.cos(ra) - dy * Math.sin(ra), ry = dx * Math.sin(ra) + dy * Math.cos(ra);
        var nw = Math.max(8, b0.w + rx), nh = Math.max(8, b0.h + ry);
        if (!e.shiftKey) { var r0 = b0.w / b0.h; if (Math.abs(rx) * b0.h >= Math.abs(ry) * b0.w) nh = nw / r0; else nw = nh * r0; }
        var c0 = Math.cos(-ra), s0 = Math.sin(-ra), ddx = (nw - b0.w) / 2, ddy = (nh - b0.h) / 2;   // sudut kiri atas tetap
        s.w = nw; s.h = nh; s.x = b0.x + b0.w / 2 + ddx * c0 - ddy * s0 - nw / 2 + (0); s.y = b0.y + b0.h / 2 + ddx * s0 + ddy * c0 - nh / 2;
      }
      else { s.w = Math.max(3, b0.w + dx); s.h = Math.max(3, b0.h + dy); if (s.t === "erase" && s.fill === "auto") s.col = sampleBg(s); }
      edDraw(); if (ED.edit) edTextStyle();
    }
    else if (d.mode === "rub") edRub(pt);
    else if (d.mode === "draw" && ED.temp) {
      var tp = ED.temp;
      if (tp.pts) { var last = tp.pts[tp.pts.length - 1]; if (Math.hypot(pt.x - last[0], pt.y - last[1]) > 1.2 / ED.k) tp.pts.push([+pt.x.toFixed(2), +pt.y.toFixed(2)]); }
      else if (tp.x1 != null) { tp.x2 = pt.x; tp.y2 = pt.y; if (e.shiftKey) { var ang = Math.round(Math.atan2(tp.y2 - tp.y1, tp.x2 - tp.x1) / (Math.PI / 4)) * Math.PI / 4, len = Math.hypot(tp.x2 - tp.x1, tp.y2 - tp.y1); tp.x2 = tp.x1 + len * Math.cos(ang); tp.y2 = tp.y1 + len * Math.sin(ang); } }
      else { tp.x = Math.min(d.x, pt.x); tp.y = Math.min(d.y, pt.y); tp.w = Math.abs(pt.x - d.x); tp.h = Math.abs(pt.y - d.y); if (e.shiftKey && tp.t !== "erase") { var m = Math.max(tp.w, tp.h); tp.w = tp.h = m; } }
      edDraw();
    }
  }
  var TAPT = /^(tedit|mark|text|note|check|form)$/;
  function edUp(e) {
    PTR.delete(e.pointerId);
    if (ED.tap && e.pointerId === ED.tap.id) {
      var tp0 = ED.tap; ED.tap = null;
      if (e.type === "pointercancel" || Math.hypot(e.clientX - tp0.x, e.clientY - tp0.y) > 10 || Date.now() - tp0.t0 > 700) return;
      var fk = { clientX: tp0.x, clientY: tp0.y, target: tp0.target, pointerId: -7, button: 0, pointerType: "tap", shiftKey: false, altKey: false, preventDefault: function () { } };
      edDown(fk); edUp(fk); return;
    }
    if (ED.pinch) { if (PTR.size < 2) { var z = ED.pinch.z; ED.pinch = null; ED.drag = null; $("pe-ed-paper").style.transform = ""; if (z) { ED.zoom = z; edLoad(); } } return; }
    var d = ED.drag; ED.drag = null; ED.guides = null; if (!d) return;
    var p = edPage();
    if (d.mode === "crop") { if (ED.crop && (ED.crop.w < 8 || ED.crop.h < 8)) ED.crop = null; edDraw(); edProps(); return; }
    if (d.mode === "box") { var bx = ED.box; ED.box = null; if (bx && bx.w * ED.k > 4 && bx.h * ED.k > 4) { var got = p.ops.filter(function (o) { if (o.t === "mask") return false; var b = bbox(o); return b.x < bx.x + bx.w && b.x + b.w > bx.x && b.y < bx.y + bx.h && b.y + b.h > bx.y; }); if (got.length === 1) { ED.sel = got[0]; ED.ms = []; } else if (got.length > 1) { ED.sel = null; ED.ms = got; } } edProps(); edDraw(); return; }
    if (d.mode === "mmove") { edDraw(); if (d.moved) renderSoon(); return; }
    if (d.mode === "rot" || (d.mode === "resize" && d.hid)) { edDraw(); if (d.moved) { renderSoon(); edProps(); } return; }
    if (d.mode === "draw" && ED.temp) {
      var tp = ED.temp, ok = tp.pts ? true : tp.x1 != null ? Math.hypot(tp.x2 - tp.x1, tp.y2 - tp.y1) > 3 : tp.w > 3 && tp.h > 3;
      ED.temp = null;
      if (ok) { pushUndo(); if (tp.t === "erase" && tp.fill === "auto") tp.col = sampleBg(tp); p.ops.push(tp); if (tp.t === "erase" || tp.t === "rect" || tp.t === "ellipse" || tp.t === "link") ED.sel = tp; if (tp.t === "erase") edProps(); if (tp.t === "link") { edDraw(); linkPop(tp, true); return; } }
      edDraw(); renderSoon();
    } else if (d.mode === "move" || d.mode === "resize") { edDraw(); if (d.moved) renderSoon(); }
  }
  function edRub(pt) { var p = edPage(), o = hit(pt, function (o) { return o.t !== "text" && o.t !== "erase"; }); if (o) { if (!ED.rubbed) { pushUndo(); ED.rubbed = true; setTimeout(function () { ED.rubbed = false; }, 400); } p.ops.splice(p.ops.indexOf(o), 1); edDraw(); renderSoon(); } }

  // kotak teks
  function edText(o, fresh, fromLine) {
    edCommitText();
    var paper = $("pe-ed-paper"), ta = document.createElement("textarea");
    ta.className = "pe-ta"; ta.value = o.text || ""; ta.spellcheck = false; ta.placeholder = "Ketik teks…";
    paper.appendChild(ta);
    ED.edit = { o: o, ta: ta, fresh: !!fresh, before: JSON.stringify(o), fromLine: !!fromLine };
    if (!fresh) pushUndo();
    edTextStyle(); edDraw();
    webFont(fontOf(o.font), o.b, o.i).then(function () { o.h = textH(o); edTextStyle(); });
    ta.addEventListener("input", function () { o.text = ta.value; if (o.autoW) fitW(o); else o.h = textH(o); edTextStyle(); });
    ta.addEventListener("keydown", function (e) { if (e.key === "Escape") { e.preventDefault(); edCommitText(); } e.stopPropagation(); });
    ta.addEventListener("pointerdown", function (e) { e.stopPropagation(); });
    ta.focus();
    setTimeout(function () { if (document.activeElement !== ta) ta.focus(); var l = ta.value.length; ta.setSelectionRange(l, l); }, 0);
  }
  function edTextStyle() {
    var ed = ED.edit; if (!ed) return; var o = ed.o, ta = ed.ta, k = ED.k;
    Object.assign(ta.style, { left: o.x * k + "px", top: o.y * k + "px", width: o.w * k + "px", height: Math.max(o.h, o.size * LH + PAD * 2) * k + 2 + "px", font: cssFont(o, k), color: o.c, textAlign: { l: "left", c: "center", r: "right" }[o.al || "l"], textDecoration: o.u ? "underline" : "none", padding: PAD * k + "px", lineHeight: o.size * LH * k + "px", background: o.bg || "#ffffffcc", opacity: o.op == null ? 1 : Math.max(0.35, o.op), transform: o.a ? "rotate(" + o.a + "deg)" : "none" });
  }
  function edCommitText() {
    var ed = ED.edit; if (!ed) return; ED.edit = null;
    var o = ed.o, p = edPage();
    o.text = ed.ta.value.replace(/\s+$/, ""); ed.ta.remove();
    if (ed.fromLine && p && o.text === o.orig && JSON.stringify(o) === ed.before) {   // tidak ada perubahan → kembalikan teks asli
      p.ops = p.ops.filter(function (x) { return x !== o && !(x.key && x.key === o.src); }); if (ED.sel === o) ED.sel = null;
      PE.undo.pop(); PE.undo.pop(); syncUndo(); edDraw(); edProps(); renderSoon(); return;
    }
    if (!o.text && !o.bg && p) { var i = p.ops.indexOf(o); if (i >= 0) p.ops.splice(i, 1); if (ED.sel === o) ED.sel = null; if (ed.fresh) { PE.undo.pop(); syncUndo(); } }
    else { o.h = textH(o); if (!ed.fresh && JSON.stringify(o) === ed.before) { PE.undo.pop(); syncUndo(); } }
    edDraw(); edProps(); renderSoon();
  }

  // ===================== aksi pita (ribbon) =====================
  function stripReset() { var st = $("pe-strip"); if (st) st.dataset.sig = ""; }
  function edAct(a) {
    edCommitText(); hidePop();
    var p = edPage(); if (!p) return;
    var ix = PE.pages.indexOf(p);
    if (a === "img") { ED.imgAt = null; $("pe-img-in").click(); return; }
    if (a === "lib") return libPanel();
    if (a === "sign") return signPad();
    if (a === "find" || a === "redact") return findOpen(a === "find" ? "replace" : "redact");
    if (a === "pnum") return pnumModal();
    if (a === "ocr") return ocrModal();
    if (a === "notes") return notesList();
    if (a === "size") return sizeModal();
    if (a === "cmp") return compareOpen();
    if (a === "comp") return compModal();
    if (a === "pw") return pwModal();
    if (a === "toimg") return imgModal();
    if (a === "todocx") return docxModal();
    if (a === "toxlsx") return exportXlsx();
    if (a === "dlpdf") { edCommitText(); return isEdit() || isMerge() || segs().length < 2 ? dlOne(0) : dlZip(); }
    if (a === "wm") return wmModal();
    if (a === "rotl" || a === "rotr") { pushUndo(); rotOps(p, a === "rotl" ? -90 : 90); ED.sel = null; ED.ms = []; stripReset(); render(); edStrip(); edLoad(); fxPop(); return; }
    if (a === "pdup") { pushUndo(); var c = clone(p); c.id = "p" + (++PE.uid); PE.pages.splice(ix + 1, 0, c); render(); stripReset(); edGoTo(c.id, 1); toast("Halaman " + (ix + 1) + " diduplikat (beserta semua editannya)", "success"); return; }
    if (a === "pdel") {
      if (PE.pages.length < 2) return toast("Minimal 1 halaman harus tersisa", "error");
      var nb = PE.pages[ix + 1] || PE.pages[ix - 1]; PE.sel = new Set([p.id]); delPages(); stripReset(); ED.id = null; edGoTo(nb.id, 1);
      toast("Halaman " + (ix + 1) + " dihapus — Urungkan (Ctrl+Z) untuk mengembalikan", "info"); return;
    }
    if (a === "pins") { PE.insAt = ix + 1; PE.insNote = ix + 1; $("pe-in").click(); return; }
    if (a === "pcut") return cutHere(p);
    if (a === "pmerge") { PE.insAt = null; $("pe-in").click(); edClose(); switchMode("merge"); toast("Pilih file yang mau digabung — dokumen ini (beserta editannya) jadi file pertama", "info", 5000); return; }
  }
  async function cutHere(p) {
    var ix = PE.pages.indexOf(p);
    if (isMerge()) { var ml = mergedPages(); ix = ml.findIndex(function (x) { return String(x.id).indexOf(p.id + "~") === 0; }); }
    if (ix <= 0) return toast("Ini halaman pertama — buka halaman lain sebagai awal file baru", "info");
    edClose();
    if (isMerge()) { await switchMode("split"); pushUndo(); if (PE.pages[ix]) PE.cuts.add(PE.pages[ix].id); }
    else { pushUndo(); PE.cuts.add(p.id); if (PE.mode !== "split") await switchMode("split"); }
    render(); toast("Dipecah mulai halaman " + (ix + 1) + " — atur nama tiap file di panel kanan", "success", 5000);
  }

  // ===================== cari & ganti · sensor · stabilo (semua halaman) =====================
  var FD = { mode: "replace", q: "", cs: false, ww: false, re: null, reName: "", hits: [], cur: -1, seq: 0 };
  var REDACT_PRESET = [
    ["email", "Email", /[\w.+-]+@[\w-]+(?:\.[\w-]+)+/g],
    ["hp", "No. HP", /(?:\+62|62|0)8\d(?:[\s-]?\d){6,11}/g],
    ["nik", "NIK 16 digit", /(?<!\d)\d{16}(?!\d)/g],
    ["angka", "Angka panjang (rekening / NPWP)", /(?<![\d])\d(?:[\d.\- ]{6,})\d(?![\d])/g]
  ];
  function findOpen(mode) {
    var main = document.querySelector("#pe-ed .pe-ed-main"), el = $("pe-find"); if (!main) return;
    if (!el) { el = document.createElement("div"); el.id = "pe-find"; el.className = "pe-find hidden"; main.appendChild(el); }
    var first = el.classList.contains("hidden"); FD.mode = mode; if (mode === "replace") { FD.re = null; FD.reName = ""; }
    var red = mode === "redact";
    el.innerHTML = '<div class="hd"><i class="fa-solid ' + (red ? "fa-user-secret" : "fa-magnifying-glass") + '"></i><b>' + (red ? "Sensor kata / data" : "Cari & ganti") + '</b><button class="x" data-x title="Tutup (Esc)"><i class="fa-solid fa-xmark"></i></button></div>'
      + '<div class="pe-fseg"><button data-m="replace" class="' + (red ? "" : "on") + '"><i class="fa-solid fa-arrow-right-arrow-left"></i>Cari &amp; ganti</button><button data-m="redact" class="' + (red ? "on" : "") + '"><i class="fa-solid fa-user-secret"></i>Sensor</button></div>'
      + '<label>Cari di semua halaman</label><div class="row"><input id="pe-fq" placeholder="' + (red ? "kata / nama / nomor yang disensor" : "mis. nama, tanggal, nomor") + '" value="' + E(FD.re ? "" : FD.q) + '"><button class="pe-b ' + (FD.cs ? "on" : "") + '" data-cs title="Huruf besar/kecil harus sama">Aa</button><button class="pe-b ' + (FD.ww ? "on" : "") + '" data-ww title="Hanya kata utuh">Kata utuh</button></div>'
      + (red ? '<label>Atau sensor otomatis</label><div class="pe-fpre">' + REDACT_PRESET.map(function (r) { return '<button data-pre="' + r[0] + '" class="' + (FD.reName === r[0] ? "on" : "") + '">' + r[1] + "</button>"; }).join("") + "</div>"
        : '<label>Ganti dengan</label><input id="pe-fr" placeholder="teks pengganti (boleh kosong untuk menghapus kata)">')
      + '<div class="sum" id="pe-fsum"></div><div class="list" id="pe-flist"></div>'
      + '<div class="ft">' + (red ? '<button class="pe-b pri pe-red" data-go="redact"><i class="fa-solid fa-user-secret"></i>Sensor semua</button>' : '<button class="pe-b pri" data-go="replace"><i class="fa-solid fa-arrow-right-arrow-left"></i>Ganti semua</button>') + '<button class="pe-b" data-go="hl"><i class="fa-solid fa-highlighter"></i>Stabilo semua</button></div>'
      + (red ? '<p class="note"><i class="fa-solid fa-shield-halved"></i>Sensor = kotak hitam permanen: teks di bawahnya benar-benar dibuang dari file (halaman terkait disimpan sebagai gambar).</p>' : '<p class="note"><i class="fa-solid fa-circle-info"></i>Font, ukuran & warna teks pengganti disamakan otomatis. Halaman scan: jalankan <b>OCR scan</b> dulu (tab Teks) agar teksnya bisa dicari.</p>');
    if (first) { el.classList.remove("hidden"); el.classList.remove("in"); void el.offsetWidth; el.classList.add("in"); }
    el.querySelector("[data-x]").onclick = findClose;
    el.querySelectorAll("[data-m]").forEach(function (b) { b.onclick = function () { findOpen(b.dataset.m); }; });
    var q = el.querySelector("#pe-fq"), t = null;
    q.oninput = function () { FD.q = q.value; FD.re = null; FD.reName = ""; el.querySelectorAll("[data-pre]").forEach(function (x) { x.classList.remove("on"); }); clearTimeout(t); t = setTimeout(fdRun, 220); };
    q.onkeydown = function (e) { e.stopPropagation(); if (e.key === "Enter") { e.preventDefault(); if (FD.hits.length) fdGo((FD.cur + (e.shiftKey ? -1 : 1) + FD.hits.length) % FD.hits.length); } if (e.key === "Escape") findClose(); };
    var r = el.querySelector("#pe-fr"); if (r) r.onkeydown = function (e) { e.stopPropagation(); if (e.key === "Escape") findClose(); };
    el.querySelector("[data-cs]").onclick = function () { FD.cs = !FD.cs; this.classList.toggle("on", FD.cs); fdRun(); };
    el.querySelector("[data-ww]").onclick = function () { FD.ww = !FD.ww; this.classList.toggle("on", FD.ww); fdRun(); };
    el.querySelectorAll("[data-pre]").forEach(function (b) { b.onclick = function () { var on = FD.reName !== b.dataset.pre; el.querySelectorAll("[data-pre]").forEach(function (x) { x.classList.remove("on"); }); if (on) { var pr = REDACT_PRESET.filter(function (x) { return x[0] === b.dataset.pre; })[0]; FD.re = pr[2]; FD.reName = pr[0]; b.classList.add("on"); q.value = ""; } else { FD.re = null; FD.reName = ""; } fdRun(); }; });
    el.querySelectorAll("[data-go]").forEach(function (b) { b.onclick = function () { fdApply(b.dataset.go); }; });
    setTimeout(function () { q.focus(); q.select(); }, 30);
    fdRun();
  }
  function findClose() { var el = $("pe-find"); if (!el || el.classList.contains("hidden")) return; el.classList.add("hidden"); FD.hits = []; FD.cur = -1; FD.seq++; edDraw(); }
  var findOn = function () { var el = $("pe-find"); return !!el && !el.classList.contains("hidden"); };
  function fdRegex() {
    if (FD.re) return new RegExp(FD.re.source, "g");
    var q = FD.q; if (!q || !q.trim()) return null;
    var esc = q.replace(/[.*+?^${}()|[\]\\]/g, "\\$&").replace(/\s+/g, "\\s+");
    try { if (FD.ww) return new RegExp("(?<![\\p{L}\\p{N}])" + esc + "(?![\\p{L}\\p{N}])", "gu" + (FD.cs ? "" : "i")); } catch (e) { }
    return new RegExp(esc, "g" + (FD.cs ? "" : "i"));
  }
  function covered(p, b) { return p.ops.some(function (o) { if (o.t !== "erase") return false; var ix = Math.max(0, Math.min(o.x + o.w, b.x + b.w) - Math.max(o.x, b.x)), iy = Math.max(0, Math.min(o.y + o.h, b.y + b.h) - Math.max(o.y, b.y)); return ix * iy >= b.w * b.h * 0.7; }); }
  async function fdRun() {
    var re = fdRegex(), my = ++FD.seq, S = $("pe-fsum"); FD.hits = []; FD.cur = -1;
    if (!re) { fdList(); edDraw(); return; }
    if (S) S.innerHTML = '<i class="fa-solid fa-circle-notch fa-spin"></i> Mencari di ' + PE.pages.length + " halaman…";
    var hits = [];
    for (var n = 0; n < PE.pages.length; n++) {
      var p = PE.pages[n], lines = [];
      try { lines = await pageLines(p); } catch (e) { }
      if (my !== FD.seq) return;
      var doneK = {}; p.ops.forEach(function (o) { if (o.key) doneK[o.key] = 1; });
      lines.forEach(function (l) { if (doneK[l.key]) return; re.lastIndex = 0; var m; while ((m = re.exec(l.str))) { if (!m[0].length) { re.lastIndex++; continue; } var h = { p: p, l: l, s: m.index, n: m[0].length, txt: l.str }; if (!covered(p, hitBox(h))) hits.push(h); } });
      p.ops.forEach(function (o) { if (o.t !== "text" || !o.text) return; re.lastIndex = 0; var m; while ((m = re.exec(o.text))) { if (!m[0].length) { re.lastIndex++; continue; } hits.push({ p: p, o: o, s: m.index, n: m[0].length, txt: o.text }); } });
      if (n % 6 === 5) { if (S) S.innerHTML = '<i class="fa-solid fa-circle-notch fa-spin"></i> Mencari… ' + (n + 1) + " / " + PE.pages.length; await tick(); if (my !== FD.seq) return; }
    }
    FD.hits = hits; fdList(); edDraw();
    var onCur = hits.filter(function (h) { return h.p === edPage(); })[0];
    if (hits.length && !onCur) fdGo(0, true); else if (onCur) FD.cur = hits.indexOf(onCur), fdList();
  }
  function hitBox(h) {
    if (h.o) { var o = h.o, ls = textLines(o), acc = 0, li = 0; for (; li < ls.length; li++) { if (h.s < acc + ls[li].length + 1) break; acc += ls[li].length + 1; } li = Math.min(li, ls.length - 1); MC.font = cssFont(o, 1); var ln = ls[li] || "", st = Math.max(0, h.s - acc), x0 = MC.measureText(ln.slice(0, st)).width, x1 = MC.measureText(ln.slice(0, st + h.n)).width, lw = MC.measureText(ln).width, off = o.al === "c" ? (o.w - lw) / 2 : o.al === "r" ? o.w - PAD - lw : PAD; return o.a ? { x: o.x, y: o.y, w: o.w, h: o.h } : { x: o.x + off + x0 - 0.5, y: o.y + PAD + li * o.size * LH, w: Math.max(2, x1 - x0 + 1), h: o.size * LH }; }
    var l = h.l, f = fontOf(l.mf.font); MC.font = (l.mf.i ? "italic " : "") + (l.mf.b ? "700 " : "400 ") + l.size + "px " + fontCss(f);
    var full = MC.measureText(l.str).width || 1, sc = l.w / full, a = MC.measureText(l.str.slice(0, h.s)).width * sc, b = MC.measureText(l.str.slice(0, h.s + h.n)).width * sc;
    return { x: l.x + a - 0.6, y: l.top - 0.6, w: b - a + 1.2, h: l.h + 1.2 };
  }
  function fdList() {
    var L = $("pe-flist"), S = $("pe-fsum"); if (!L || !S) return;
    var np = new Set(FD.hits.map(function (h) { return h.p.id; })).size, red = FD.mode === "redact";
    S.innerHTML = !FD.q.trim() && !FD.re ? '<span class="mute">' + (red ? "Ketik kata atau pilih sensor otomatis" : "Ketik kata yang dicari — semua halaman dipindai") + "</span>"
      : FD.hits.length ? "<b>" + FD.hits.length + "</b> hasil di <b>" + np + "</b> halaman" + (FD.cur >= 0 ? '<span class="mute"> · ' + (FD.cur + 1) + "/" + FD.hits.length + " · Enter = berikutnya</span>" : "")
      : '<span class="mute">Tidak ditemukan</span>';
    L.innerHTML = FD.hits.slice(0, 400).map(function (h, i) {
      var a = Math.max(0, h.s - 22), z = h.s + h.n + 28, ctx = (a ? "…" : "") + E(h.txt.slice(a, h.s)) + "<mark>" + E(h.txt.substr(h.s, h.n)) + "</mark>" + E(h.txt.slice(h.s + h.n, z)) + (z < h.txt.length ? "…" : "");
      return '<div class="it' + (i === FD.cur ? " on" : "") + '" data-h="' + i + '"><span class="pg">Hal ' + (PE.pages.indexOf(h.p) + 1) + '</span><span class="cx">' + ctx + '</span><button data-one="' + i + '" title="' + (red ? "Sensor yang ini saja" : "Ganti yang ini saja") + '">' + (red ? "Sensor" : "Ganti") + "</button></div>";
    }).join("") + (FD.hits.length > 400 ? '<div class="mute" style="padding:6px">+' + (FD.hits.length - 400) + " hasil lain</div>" : "");
    L.querySelectorAll("[data-h]").forEach(function (it) { it.onclick = function (e) { if (e.target.closest("[data-one]")) return; fdGo(+it.dataset.h); }; });
    L.querySelectorAll("[data-one]").forEach(function (b) { b.onclick = function () { fdApply(FD.mode, [FD.hits[+b.dataset.one]]); }; });
    var on = L.querySelector(".it.on"); if (on) try { on.scrollIntoView({ block: "nearest" }); } catch (e) { }
  }
  function fdGo(i, quiet) {
    var h = FD.hits[i]; if (!h) return; FD.cur = i;
    if (h.p.id !== ED.id) edGoTo(h.p.id, PE.pages.indexOf(h.p) < PE.pages.indexOf(edPage()) ? -1 : 1);
    var b = hitBox(h), st = $("pe-ed-stage"), pp = $("pe-ed-paper");
    if (st && pp && !quiet) setTimeout(function () { var y = pp.offsetTop + b.y * ED.k - st.clientHeight / 3; try { st.scrollTo({ top: Math.max(0, y), behavior: "smooth" }); } catch (e) { st.scrollTop = y; } }, 40);
    FD.flash = Date.now(); var f = function () { edDraw(); if (Date.now() - FD.flash < 900) requestAnimationFrame(f); }; requestAnimationFrame(f);
    fdList();
  }
  function drawFind(g, k, p) {
    if (!findOn() || !FD.hits.length) return;
    g.save(); g.scale(k, k);
    var t = Math.min(1, (Date.now() - (FD.flash || 0)) / 900);
    FD.hits.forEach(function (h, i) {
      if (h.p !== p) return; var b = hitBox(h), cur = i === FD.cur;
      g.fillStyle = cur ? "rgba(249,115,22,.35)" : (FD.mode === "redact" ? "rgba(15,23,42,.18)" : "rgba(250,204,21,.38)"); g.fillRect(b.x, b.y, b.w, b.h);
      if (cur) { g.strokeStyle = "#ea580c"; g.lineWidth = 1.6 / ED.k; var pad = (1 - t) * 8; g.globalAlpha = 1; g.strokeRect(b.x - pad, b.y - pad, b.w + pad * 2, b.h + pad * 2); }
    });
    g.restore();
  }
  async function fdApply(kind, list) {
    list = (list || FD.hits).filter(Boolean); if (!list.length) return toast("Tidak ada hasil untuk diterapkan", "info");
    if (kind === "replace" && !$("pe-fr")) return;
    var rep = kind === "replace" ? $("pe-fr").value : "", n = list.length;
    pushUndo(); busy(kind === "redact" ? "Menyensor…" : kind === "hl" ? "Menandai…" : "Mengganti teks…", 10, kind === "redact" ? "write" : "read");
    try {
      var byLine = new Map(), byOp = new Map(), cvs = {};
      list.forEach(function (h) { if (h.o) { if (!byOp.has(h.o)) byOp.set(h.o, { p: h.p, hs: [] }); byOp.get(h.o).hs.push(h); } else { var k = h.l.key; if (!byLine.has(k)) byLine.set(k, { p: h.p, l: h.l, hs: [] }); byLine.get(k).hs.push(h); } });
      var cut = function (str, hs, by) { hs.slice().sort(function (a, b) { return b.s - a.s; }).forEach(function (h) { str = str.slice(0, h.s) + (typeof by === "function" ? by(h) : by) + str.slice(h.s + h.n); }); return str; };
      var G = Array.from(byLine.values()), done = 0;
      for (var i = 0; i < G.length; i++) {
        var g = G[i], p = g.p;
        if (kind === "replace") {
          var cv = cvs[p.id]; if (!cv) { var D = dims(p); cv = cvs[p.id] = p === edPage() && ED.base ? { c: ED.base, D: D } : { c: await renderBase(p, Math.min(1400, D.w * 1.6), 1), D: D, tmp: 1 }; }
          var two = await lineOps(p, g.l, cut(g.l.str, g.hs, rep), cv.c, cv.D); p.ops.push(two[0], two[1]);
        } else g.hs.forEach(function (h) {
          var b = hitBox(h);
          if (kind === "redact") p.ops.push({ t: "erase", x: b.x - 0.6, y: b.y - 0.4, w: b.w + 1.2, h: b.h + 0.8, fill: "#000000", col: "#000000" });
          else { var r = b.h / 2, y = b.y + r; p.ops.push({ t: "hl", pts: b.w > b.h ? [[b.x + r, y], [b.x + b.w - r, y]] : [[b.x + b.w / 2, y]], c: "#facc15", lw: b.h, op: 0.4 }); }
        });
        done += g.hs.length; if (i % 4 === 3) { busy("Memproses " + done + " / " + n + "…", 10 + 85 * done / n); await tick(); }
      }
      byOp.forEach(function (g, o) {
        if (kind === "replace") o.text = cut(o.text, g.hs, rep);
        else if (kind === "redact") o.text = cut(o.text, g.hs, function (h) { return new Array(h.n + 1).join("X"); });
        else g.hs.forEach(function (h) { var b = hitBox(h), r = b.h / 2; g.p.ops.push({ t: "hl", pts: [[b.x + r, b.y + r], [b.x + Math.max(r, b.w - r), b.y + r]], c: "#facc15", lw: b.h, op: 0.4 }); });
        if (o.t === "text") { if (o.autoW) fitW(o, g.p); o.h = textH(o); }
      });
      Object.keys(cvs).forEach(function (k) { if (cvs[k].tmp) cvs[k].c.width = cvs[k].c.height = 0; });
    } catch (e) { busy(null); toast("Gagal: " + e.message, "error"); return; }
    busy(null); ED.sel = null; ED.ms = [];
    render(); stripReset(); edStrip(); edDraw(); renderSoon();
    toast((kind === "redact" ? n + " data disensor permanen" : kind === "hl" ? n + " hasil ditandai stabilo" : n + " hasil diganti" + (rep ? " dengan \"" + rep + "\"" : " (dihapus)")) + " — Ctrl+Z untuk membatalkan", "success", 5000);
    fdRun();
  }

  // ===================== buat tanda tangan: gambar · ketik · unggah =====================
  var SIGF = ["Dancing Script", "Great Vibes", "Allura"];
  function trimCanvas(c, pad) {
    var g = c.getContext("2d"), W = c.width, H = c.height, d = g.getImageData(0, 0, W, H).data, x0 = W, y0 = H, x1 = -1, y1 = -1;
    for (var y = 0; y < H; y++) for (var x = 0; x < W; x++) if (d[(y * W + x) * 4 + 3] > 10) { if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y; }
    if (x1 < 0) return null;
    var o = document.createElement("canvas"); o.width = x1 - x0 + 1 + pad * 2; o.height = y1 - y0 + 1 + pad * 2;
    o.getContext("2d").drawImage(c, x0, y0, x1 - x0 + 1, y1 - y0 + 1, pad, pad, x1 - x0 + 1, y1 - y0 + 1); return o;
  }
  function signPad() {
    var SG = { tab: "draw", col: "#1e3a8a", lw: 3, strokes: [], font: SIGF[0], up: null };
    var cols = [["#111827", "Hitam"], ["#1e3a8a", "Biru"], ["#b91c1c", "Merah"]];
    var colRow = '<div class="pe-sgcol">' + cols.map(function (c) { return '<button data-sc="' + c[0] + '" class="' + (c[0] === SG.col ? "on" : "") + '"><i style="background:' + c[0] + '"></i>' + c[1] + "</button>"; }).join("") + "</div>";
    var nm = ""; try { nm = (currentUser && (currentUser.name || currentUser.nama)) || ""; } catch (e) { }
    var m = modal('<i class="fa-solid fa-signature" style="color:#db2777"></i> Buat tanda tangan / paraf',
      '<div class="pe-sgtabs"><button data-st="draw" class="on"><i class="fa-solid fa-pen-nib"></i>Gambar</button><button data-st="type"><i class="fa-solid fa-keyboard"></i>Ketik</button><button data-st="up"><i class="fa-solid fa-upload"></i>Unggah foto</button></div>'
      + '<div class="pe-sgp" data-p="draw"><div class="pe-sgpad" id="pe-sgpad"><canvas id="pe-sgc"></canvas><span class="ln"></span><span class="ph" id="pe-sgph"><i class="fa-solid fa-pen-nib"></i> Tanda tangan di sini — pakai mouse, pena, atau jari</span></div>'
      + '<div class="pe-sgrow">' + colRow + '<label>Tebal</label><input type="range" id="pe-sglw" min="1.5" max="7" step="0.5" value="3" style="width:90px"><span style="flex:1"></span><button class="pe-b" id="pe-sgun" style="height:28px"><i class="fa-solid fa-rotate-left"></i>Urungkan goresan</button><button class="pe-b" id="pe-sgcl" style="height:28px"><i class="fa-regular fa-trash-can"></i>Bersihkan</button></div></div>'
      + '<div class="pe-sgp hidden" data-p="type"><input id="pe-sgn" placeholder="Ketik nama Anda" value="' + E(nm) + '" style="width:100%;height:36px;font-size:14px"><div class="pe-sgfonts" id="pe-sgf"></div><div class="pe-sgrow">' + colRow + "</div></div>"
      + '<div class="pe-sgp hidden" data-p="up"><label class="pe-sgup" id="pe-sgupl"><input type="file" accept="image/*" class="hidden" id="pe-sgu"><i class="fa-solid fa-cloud-arrow-up"></i><b>Pilih foto / scan tanda tangan</b><small>Foto di kertas putih — latar putih otomatis dibuang</small></label><div class="pe-sgprev hidden" id="pe-sgprev"><img id="pe-sgimg" alt=""><button class="pe-b" id="pe-sgre" style="height:28px"><i class="fa-solid fa-arrow-rotate-right"></i>Ganti foto</button></div></div>'
      + '<div class="pe-sgopt"><label class="pe-tog"><input type="checkbox" id="pe-sgsave" checked><span class="sw"></span><span><b>Simpan ke pustaka</b><small>pakai lagi kapan saja dari Pustaka</small></span></label><label>Jenis <select id="pe-sgk"><option value="ttd">Tanda tangan</option><option value="paraf">Paraf</option></select></label></div>',
      '<button class="pe-b" data-c>Batal</button><button class="pe-b pri" id="pe-sggo"><i class="fa-solid fa-check"></i>Taruh di halaman</button>', 640);
    m.querySelector("[data-c]").onclick = function () { m.remove(); };
    var cv = m.querySelector("#pe-sgc"), pad = m.querySelector("#pe-sgpad"), ph = m.querySelector("#pe-sgph"), dpr = Math.min(3, devicePixelRatio || 1), g = cv.getContext("2d");
    var size = function () { var w = pad.clientWidth, h = pad.clientHeight; cv.width = Math.round(w * dpr); cv.height = Math.round(h * dpr); cv.style.width = w + "px"; cv.style.height = h + "px"; redraw(); };
    function strokeOn(ctx, s, sc, col) {
      ctx.save(); ctx.scale(sc, sc); ctx.fillStyle = ctx.strokeStyle = col; ctx.lineCap = "round"; ctx.lineJoin = "round";
      var P = s.pts; if (P.length === 1) { ctx.beginPath(); ctx.arc(P[0][0], P[0][1], s.lw * 0.6, 0, Math.PI * 2); ctx.fill(); ctx.restore(); return; }
      var w = s.lw;
      for (var i = 1; i < P.length; i++) {   // tebal mengikuti kecepatan (goresan cepat lebih tipis) + kurva halus
        var a = P[i - 1], b = P[i], dt = Math.max(1, b[2] - a[2]), v = Math.hypot(b[0] - a[0], b[1] - a[1]) / dt, tw = s.lw * Math.max(0.45, Math.min(1.25, 1.3 - v * 0.35)) * (b[3] ? 0.6 + b[3] * 0.8 : 1);
        w = w * 0.7 + tw * 0.3; ctx.lineWidth = w;
        var m0 = i > 1 ? [(P[i - 2][0] + a[0]) / 2, (P[i - 2][1] + a[1]) / 2] : a, m1 = [(a[0] + b[0]) / 2, (a[1] + b[1]) / 2];
        ctx.beginPath(); ctx.moveTo(m0[0], m0[1]); ctx.quadraticCurveTo(a[0], a[1], m1[0], m1[1]); ctx.stroke();
        if (i === P.length - 1) { ctx.beginPath(); ctx.moveTo(m1[0], m1[1]); ctx.lineTo(b[0], b[1]); ctx.stroke(); }
      }
      ctx.restore();
    }
    function redraw() { g.clearRect(0, 0, cv.width, cv.height); SG.strokes.forEach(function (s) { strokeOn(g, s, dpr, SG.col); }); ph.classList.toggle("hidden", SG.strokes.length > 0); }
    var cur = null, pos = function (e) { var r = cv.getBoundingClientRect(); return [e.clientX - r.left, e.clientY - r.top, e.timeStamp || Date.now(), e.pointerType === "pen" ? e.pressure || 0.5 : 0]; };
    cv.addEventListener("pointerdown", function (e) { e.preventDefault(); cv.setPointerCapture(e.pointerId); cur = { lw: SG.lw, pts: [pos(e)] }; SG.strokes.push(cur); redraw(); });
    cv.addEventListener("pointermove", function (e) { if (!cur) return; var q = pos(e), l = cur.pts[cur.pts.length - 1]; if (Math.hypot(q[0] - l[0], q[1] - l[1]) < 1.2) return; cur.pts.push(q); redraw(); });
    var end = function () { cur = null; }; cv.addEventListener("pointerup", end); cv.addEventListener("pointercancel", end);
    cv.style.touchAction = "none";
    m.querySelector("#pe-sglw").oninput = function () { SG.lw = +this.value; };
    m.querySelector("#pe-sgun").onclick = function () { SG.strokes.pop(); redraw(); };
    m.querySelector("#pe-sgcl").onclick = function () { SG.strokes = []; redraw(); };
    var fbox = m.querySelector("#pe-sgf"), nmIn = m.querySelector("#pe-sgn");
    var drawFonts = function () { var t = nmIn.value.trim() || "Tanda Tangan"; fbox.innerHTML = SIGF.map(function (f) { return '<button data-f="' + f + '" class="' + (f === SG.font ? "on" : "") + '" style="font-family:\'PE ' + f + '\',cursive;color:' + SG.col + '">' + E(t) + "<small>" + f + "</small></button>"; }).join(""); fbox.querySelectorAll("[data-f]").forEach(function (b) { b.onclick = function () { SG.font = b.dataset.f; drawFonts(); }; }); };
    Promise.all(SIGF.map(function (f) { return webFont(fontOf(f), false, false); })).then(drawFonts); drawFonts();
    nmIn.oninput = drawFonts; nmIn.onkeydown = function (e) { e.stopPropagation(); };
    m.querySelectorAll("[data-sc]").forEach(function (b) { b.onclick = function () { SG.col = b.dataset.sc; m.querySelectorAll("[data-sc]").forEach(function (x) { x.classList.toggle("on", x.dataset.sc === SG.col); }); redraw(); drawFonts(); }; });
    var upIn = m.querySelector("#pe-sgu");
    upIn.onchange = async function () { var f = upIn.files[0]; upIn.value = ""; if (!f) return; try { busy("Membersihkan latar…", 50, "read"); var id = await fileToImage(f), nid = await knockWhite(id); SG.up = nid; m.querySelector("#pe-sgimg").src = IMGS[nid].url; m.querySelector("#pe-sgprev").classList.remove("hidden"); m.querySelector("#pe-sgupl").classList.add("hidden"); } catch (e) { toast(e.message, "error"); } busy(null); };
    m.querySelector("#pe-sgre").onclick = function () { upIn.click(); };
    m.querySelectorAll("[data-st]").forEach(function (b) { b.onclick = function () { SG.tab = b.dataset.st; m.querySelectorAll("[data-st]").forEach(function (x) { x.classList.toggle("on", x === b); }); m.querySelectorAll(".pe-sgp").forEach(function (p) { p.classList.toggle("hidden", p.dataset.p !== SG.tab); }); if (SG.tab === "draw") size(); if (SG.tab === "type") nmIn.focus(); }; });
    setTimeout(size, 30);
    m.querySelector("#pe-sggo").onclick = async function () {
      var kind = m.querySelector("#pe-sgk").value, keep = m.querySelector("#pe-sgsave").checked, bytes = null, mime = "image/png";
      try {
        if (SG.tab === "draw") {
          if (!SG.strokes.length) return toast("Tanda tangani dulu di kotak", "error");
          var hi = document.createElement("canvas"), S = 3; hi.width = cv.width / dpr * S; hi.height = cv.height / dpr * S;
          SG.strokes.forEach(function (s) { strokeOn(hi.getContext("2d"), s, S, SG.col); });
          var t1 = trimCanvas(hi, 8); if (!t1) return toast("Tanda tangan kosong", "error"); bytes = await canvasPng(t1);
        } else if (SG.tab === "type") {
          var txt = nmIn.value.trim(); if (!txt) return toast("Ketik nama dulu", "error");
          await webFont(fontOf(SG.font), false, false);
          var tc = document.createElement("canvas"), tg = tc.getContext("2d"), fs = 160; tg.font = fs + "px 'PE " + SG.font + "', cursive"; tc.width = Math.ceil(tg.measureText(txt).width + fs); tc.height = Math.ceil(fs * 1.9);
          tg.font = fs + "px 'PE " + SG.font + "', cursive"; tg.fillStyle = SG.col; tg.textBaseline = "middle"; tg.fillText(txt, fs * 0.4, tc.height / 2);
          var t2 = trimCanvas(tc, 10); if (!t2) return; bytes = await canvasPng(t2);
        } else {
          if (!SG.up) return toast("Pilih foto tanda tangan dulu", "error"); bytes = IMGS[SG.up].bytes; mime = IMGS[SG.up].mime;
        }
        var id = await regImage(bytes, mime); m.remove(); placeImg(id);
        if (keep) { await libAdd({ kind: kind, bytes: bytes, mime: mime, name: (kind === "paraf" ? "Paraf" : "Tanda tangan") + (nm ? " · " + nm : "") }); }
        toast((kind === "paraf" ? "Paraf" : "Tanda tangan") + " ditaruh — geser ke posisinya" + (keep ? " · tersimpan di Pustaka" : "") + ". Untuk semua halaman: pilih lalu klik \"Semua hal.\"", "success", 6000);
      } catch (e) { toast("Gagal: " + e.message, "error"); }
    };
  }

  // ===================== nomor halaman, header & footer =====================
  var PN_FMT = ["{n}", "Halaman {n}", "Halaman {n} dari {N}", "{n} / {N}", "- {n} -", "Hal. {n}"];
  var POS = { tl: "Atas kiri", tc: "Atas tengah", tr: "Atas kanan", bl: "Bawah kiri", bc: "Bawah tengah", br: "Bawah kanan" };
  var isAuto = function (o) { return /^(pn|hdr|ftr)$/.test(o.grp || ""); };
  function pnumModal() {
    var S = segs(), multi = PE.mode === "split" && S.length > 1, has = PE.pages.some(function (p) { return p.ops.some(isAuto); });
    var P = PE.pnum = PE.pnum || { on: true, fmt: "Halaman {n} dari {N}", pos: "bc", start: 1, skip: false, per: multi, size: 9, font: "Helvetica", c: "#334155", hdr: "", hal: "r", ftr: "", fal: "l" };
    var sel = function (id, obj, cur) { return '<select id="' + id + '">' + Object.keys(obj).map(function (k) { return '<option value="' + k + '" ' + (k === cur ? "selected" : "") + ">" + obj[k] + "</option>"; }).join("") + "</select>"; };
    var AL = { l: "Kiri", c: "Tengah", r: "Kanan" };
    var cp = edPage() || PE.pages[0], D = dims(cp), th = THUMB[thumbKey(cp)] || "";
    var m = modal('<i class="fa-solid fa-list-ol" style="color:#059669"></i> Nomor halaman, header &amp; footer',
      '<div class="pe-pn"><div class="pe-pn-f">'
      + '<label class="pe-tog"><input type="checkbox" id="pn-on" ' + (P.on ? "checked" : "") + '><span class="sw"></span><span><b>Nomor halaman</b><small>ditulis di setiap halaman</small></span></label>'
      + '<div class="g2"><div><label>Format</label><select id="pn-fmt">' + PN_FMT.map(function (f) { return '<option ' + (f === P.fmt ? "selected" : "") + ">" + f + "</option>"; }).join("") + '</select></div><div><label>Posisi</label>' + sel("pn-pos", POS, P.pos) + "</div></div>"
      + '<div class="g2"><div><label>Mulai dari</label><input type="number" id="pn-st" min="0" value="' + P.start + '"></div><div><label>Ukuran</label><input type="number" id="pn-sz" min="6" max="24" value="' + P.size + '"></div></div>'
      + '<label class="chk"><input type="checkbox" id="pn-skip" ' + (P.skip ? "checked" : "") + "> Lewati halaman pertama (sampul)</label>"
      + (multi ? '<label class="chk"><input type="checkbox" id="pn-per" ' + (P.per ? "checked" : "") + "> Mulai ulang di tiap file hasil split (" + S.length + " file)</label>" : "")
      + '<hr><label>Header (atas)</label><div class="g2b"><input id="pn-hdr" placeholder="mis. {nama}" value="' + E(P.hdr) + '">' + sel("pn-hal", AL, P.hal) + "</div>"
      + '<label>Footer (bawah)</label><div class="g2b"><input id="pn-ftr" placeholder="mis. Dicetak {tanggal}" value="' + E(P.ftr) + '">' + sel("pn-fal", AL, P.fal) + "</div>"
      + '<div class="pe-vars">' + ["{n}", "{N}", "{nama}", "{file}", "{tanggal}"].map(function (v) { return "<button data-v=\"" + v + "\">" + v + "</button>"; }).join("") + "</div>"
      + '<div class="g2"><div><label>Font</label><select id="pn-font">' + ["Helvetica", "Times", "Arimo", "Carlito", "Roboto"].map(function (f) { return '<option value="' + f + '" ' + (f === P.font ? "selected" : "") + ">" + fontOf(f).label + "</option>"; }).join("") + '</select></div><div><label>Warna</label><input type="color" id="pn-c" value="' + P.c + '"></div></div>'
      + '</div><div class="pe-pn-pv"><div class="pe-pv" id="pn-pv" style="aspect-ratio:' + D.w + "/" + D.h + (th ? ";background-image:url(" + th + ")" : "") + '"></div><small>Pratinjau halaman ini</small></div></div>',
      (has ? '<button class="pe-b red" data-rm style="margin-right:auto"><i class="fa-regular fa-trash-can"></i>Hapus semua</button>' : "") + '<button class="pe-b" data-c>Batal</button><button class="pe-b pri" data-ok><i class="fa-solid fa-check"></i>Terapkan ke ' + PE.pages.length + " halaman</button>", 760);
    if (!th) thumb(cp, { set src(v) { var pv = m.querySelector("#pn-pv"); if (pv && v) pv.style.backgroundImage = "url(" + v + ")"; }, get isConnected() { return true; } });
    var read = function () {
      P.on = m.querySelector("#pn-on").checked; P.fmt = m.querySelector("#pn-fmt").value; P.pos = m.querySelector("#pn-pos").value; P.start = parseInt(m.querySelector("#pn-st").value, 10) || 0; P.size = Math.max(6, Math.min(24, +m.querySelector("#pn-sz").value || 9));
      P.skip = m.querySelector("#pn-skip").checked; var pe = m.querySelector("#pn-per"); P.per = pe ? pe.checked : false;
      P.hdr = m.querySelector("#pn-hdr").value; P.hal = m.querySelector("#pn-hal").value; P.ftr = m.querySelector("#pn-ftr").value; P.fal = m.querySelector("#pn-fal").value; P.font = m.querySelector("#pn-font").value; P.c = m.querySelector("#pn-c").value;
    };
    var pv = function () {
      read(); var box = m.querySelector("#pn-pv"), H = box.clientHeight || 300, k = H / D.h, ix = Math.max(0, PE.pages.indexOf(cp)), items = pnItems(P, ix, PE.pages.length, PE.base);
      box.innerHTML = items.map(function (it) { var top = it.pos[0] === "t"; return '<span style="' + (top ? "top" : "bottom") + ":" + 18 * k + "px;left:" + 22 * k + "px;right:" + 22 * k + "px;text-align:" + { l: "left", c: "center", r: "right" }[it.al] + ";font-size:" + Math.max(6, P.size * k) + "px;color:" + P.c + ";font-family:" + fontCss(fontOf(P.font)) + '">' + E(it.text) + "</span>"; }).join("");
    };
    m.querySelectorAll("input,select").forEach(function (x) { x.addEventListener("input", pv); x.addEventListener("change", pv); x.addEventListener("keydown", function (e) { e.stopPropagation(); }); });
    var last = null; m.querySelectorAll("#pn-hdr,#pn-ftr").forEach(function (x) { x.addEventListener("focus", function () { last = x; }); });
    m.querySelectorAll("[data-v]").forEach(function (b) { b.onclick = function () { var t = last || m.querySelector("#pn-ftr"), s0 = t.selectionStart == null ? t.value.length : t.selectionStart; t.value = t.value.slice(0, s0) + b.dataset.v + t.value.slice(s0); t.focus(); pv(); }; });
    setTimeout(pv, 30);
    m.querySelector("[data-c]").onclick = function () { m.remove(); };
    var rm = m.querySelector("[data-rm]"); if (rm) rm.onclick = function () { pushUndo(); PE.pages.forEach(function (p) { p.ops = p.ops.filter(function (o) { return !isAuto(o); }); }); m.remove(); afterBulk("Nomor halaman, header & footer dihapus"); };
    m.querySelector("[data-ok]").onclick = function () {
      read(); if (!P.on && !P.hdr.trim() && !P.ftr.trim()) return toast("Aktifkan nomor halaman atau isi header / footer", "error");
      pushUndo(); PE.pages.forEach(function (p) { p.ops = p.ops.filter(function (o) { return !isAuto(o); }); });
      var groups = P.per && multi ? segs().map(function (s, i) { return { pages: s.pages, name: finalNames()[i] }; }) : [{ pages: PE.pages, name: PE.base }], cnt = 0;
      groups.forEach(function (gp) { gp.pages.forEach(function (p, i) { pnItems(P, i, gp.pages.length, gp.name).forEach(function (it) { var D2 = dims(p), M = 22, o = { t: "text", x: M, y: 0, w: D2.w - M * 2, text: it.text, font: P.font, size: P.size, b: false, i: false, u: false, al: it.al, c: P.c, bg: "", op: 1, a: 0, grp: it.grp }; o.h = textH(o); o.y = it.pos[0] === "t" ? 18 : D2.h - 18 - o.h; p.ops.push(o); cnt++; }); }); });
      webFont(fontOf(P.font), false, false).then(function () { if (ED.on) edDraw(); });
      m.remove(); afterBulk(cnt ? "Ditambahkan ke " + PE.pages.length + " halaman" : "Tidak ada yang ditambahkan");
    };
  }
  function pnItems(P, i, total, name) {
    if (P.skip && i === 0) return [];
    var n = P.start + i - (P.skip ? 1 : 0), N = P.start + total - 1 - (P.skip ? 1 : 0), v = { n: n, N: N, nama: PE.base, file: name || PE.base, tanggal: fmtD() };
    var fill = function (t) { return String(t).replace(/\{(n|N|nama|file|tanggal)\}/g, function (m, k) { return v[k]; }); }, out = [];
    if (P.on) out.push({ text: fill(P.fmt), pos: P.pos, al: P.pos[1] === "l" ? "l" : P.pos[1] === "r" ? "r" : "c", grp: "pn" });
    if (P.hdr.trim()) out.push({ text: fill(P.hdr), pos: "t" + P.hal, al: P.hal, grp: "hdr" });
    if (P.ftr.trim()) out.push({ text: fill(P.ftr), pos: "b" + P.fal, al: P.fal, grp: "ftr" });
    return out;
  }
  function afterBulk(msg) { ED.sel = null; ED.ms = []; render(); if (ED.on) { stripReset(); edStrip(); edDraw(); renderSoon(); } toast(msg + " — Ctrl+Z untuk membatalkan", "success", 4500); }

  // ===================== watermark =====================
  function wmModal() {
    var W = PE.wm = PE.wm || { text: "RAHASIA", c: "#dc2626", op: 0.16, scale: 0.7, ang: 315, rg: "" };
    var has = PE.pages.some(function (p) { return p.ops.some(function (o) { return o.grp === "wm"; }); });
    var cp = edPage() || PE.pages[0], D = dims(cp), th = THUMB[thumbKey(cp)] || "";
    var m = modal('<i class="fa-solid fa-droplet" style="color:#0891b2"></i> Watermark',
      '<div class="pe-pn"><div class="pe-pn-f"><label>Teks watermark</label><input id="wm-t" value="' + E(W.text) + '" maxlength="60">'
      + '<div class="pe-vars">' + ["RAHASIA", "SALINAN", "DRAFT", "ASLI", "CONFIDENTIAL", "TIDAK UNTUK DIEDARKAN"].map(function (v) { return "<button data-wv=\"" + v + "\">" + v + "</button>"; }).join("") + "</div>"
      + '<label>Warna</label><div class="pe-sgcol">' + [["#dc2626", "Merah"], ["#64748b", "Abu"], ["#1d4ed8", "Biru"], ["#111827", "Hitam"]].map(function (c) { return '<button data-wc="' + c[0] + '" class="' + (c[0] === W.c ? "on" : "") + '"><i style="background:' + c[0] + '"></i>' + c[1] + "</button>"; }).join("") + "</div>"
      + '<div class="g2"><div><label>Transparansi</label><input type="range" id="wm-op" min="0.05" max="0.6" step="0.01" value="' + W.op + '"></div><div><label>Ukuran</label><input type="range" id="wm-sc" min="0.25" max="1" step="0.05" value="' + W.scale + '"></div></div>'
      + '<label>Arah</label><div class="pe-sgcol"><button data-wa="315" class="' + (W.ang === 315 ? "on" : "") + '"><i class="fa-solid fa-slash" style="background:none;color:inherit;transform:scaleX(-1)"></i>Diagonal</button><button data-wa="0" class="' + (W.ang === 0 ? "on" : "") + '"><i class="fa-solid fa-minus" style="background:none;color:inherit"></i>Mendatar</button></div>'
      + '<label>Halaman</label><input id="wm-rg" placeholder="Semua halaman · atau mis. 1-3, 5" value="' + E(W.rg) + '">'
      + '</div><div class="pe-pn-pv"><div class="pe-pv" id="wm-pv" style="aspect-ratio:' + D.w + "/" + D.h + (th ? ";background-image:url(" + th + ")" : "") + '"></div><small>Pratinjau halaman ini</small></div></div>',
      (has ? '<button class="pe-b red" data-rm style="margin-right:auto"><i class="fa-regular fa-trash-can"></i>Hapus watermark</button>' : "") + '<button class="pe-b" data-c>Batal</button><button class="pe-b pri" data-ok><i class="fa-solid fa-droplet"></i>Pasang watermark</button>', 760);
    if (!th) thumb(cp, { set src(v) { var pv = m.querySelector("#wm-pv"); if (pv && v) pv.style.backgroundImage = "url(" + v + ")"; }, get isConnected() { return true; } });
    var read = function () { W.text = m.querySelector("#wm-t").value.trim(); W.op = +m.querySelector("#wm-op").value; W.scale = +m.querySelector("#wm-sc").value; W.rg = m.querySelector("#wm-rg").value.trim(); };
    var pv = function () { read(); var box = m.querySelector("#wm-pv"), H = box.clientHeight || 300, k = H / D.h, o = wmOp(W, D); box.innerHTML = o ? '<span style="left:' + (o.x * k) + "px;top:" + (o.y * k) + "px;width:" + (o.w * k) + "px;font:700 " + (o.size * k) + "px Helvetica,Arial,sans-serif;line-height:" + (o.h * k) + "px;color:" + W.c + ";opacity:" + W.op + ";transform:rotate(" + o.a + 'deg);text-align:center;white-space:nowrap">' + E(o.text) + "</span>" : ""; };
    m.querySelectorAll("input").forEach(function (x) { x.addEventListener("input", pv); x.addEventListener("keydown", function (e) { e.stopPropagation(); }); });
    m.querySelectorAll("[data-wv]").forEach(function (b) { b.onclick = function () { m.querySelector("#wm-t").value = b.dataset.wv; pv(); }; });
    m.querySelectorAll("[data-wc]").forEach(function (b) { b.onclick = function () { W.c = b.dataset.wc; m.querySelectorAll("[data-wc]").forEach(function (x) { x.classList.toggle("on", x === b); }); pv(); }; });
    m.querySelectorAll("[data-wa]").forEach(function (b) { b.onclick = function () { W.ang = +b.dataset.wa; m.querySelectorAll("[data-wa]").forEach(function (x) { x.classList.toggle("on", x === b); }); pv(); }; });
    setTimeout(pv, 30);
    m.querySelector("[data-c]").onclick = function () { m.remove(); };
    var rm = m.querySelector("[data-rm]"); if (rm) rm.onclick = function () { pushUndo(); PE.pages.forEach(function (p) { p.ops = p.ops.filter(function (o) { return o.grp !== "wm"; }); }); m.remove(); afterBulk("Watermark dihapus"); };
    m.querySelector("[data-ok]").onclick = function () {
      read(); if (!W.text) return toast("Isi teks watermark", "error");
      var r = parseRange(W.rg, PE.pages.length); if (r.bad) return toast("Rentang \"" + r.bad + "\" tidak valid", "error");
      pushUndo(); PE.pages.forEach(function (p) { p.ops = p.ops.filter(function (o) { return o.grp !== "wm"; }); });
      r.idx.forEach(function (i) { var p = PE.pages[i], o = wmOp(W, dims(p)); if (o) p.ops.push(o); });
      m.remove(); afterBulk("Watermark dipasang di " + r.idx.length + " halaman");
    };
  }
  function wmOp(W, D) {
    if (!W.text) return null;
    var o = { t: "text", text: W.text, font: "Helvetica", size: 100, b: true, i: false, u: false, al: "c", c: W.c, bg: "", op: W.op, a: W.ang, grp: "wm" };
    MC.font = cssFont(o, 1); var w100 = MC.measureText(W.text).width || 1, span = (W.ang ? Math.hypot(D.w, D.h) : D.w) * W.scale;
    o.size = Math.max(10, Math.min(260, Math.round(100 * span / w100))); MC.font = cssFont(o, 1);
    o.w = MC.measureText(W.text).width + PAD * 2 + 6; o.h = textH(o); o.x = D.w / 2 - o.w / 2; o.y = D.h / 2 - o.h / 2;
    return o;
  }

  // ===================== v17 · OCR, formulir, crop/ukuran, catatan/tautan, kompres, password, konversi, bandingkan =====================
  var uName = function () { try { return (currentUser && (currentUser.name || currentUser.nama || currentUser.email)) || "STARLITE VM"; } catch (e) { return "STARLITE VM"; } };
  var listNow = function () { return isMerge() ? (segs()[0] || { pages: [] }).pages : PE.pages; };
  function radioRow(name, items, cur) { return '<div class="pe-seg3">' + items.map(function (it) { return '<label><input type="radio" name="' + name + '" value="' + it[0] + '" ' + (it[0] === cur ? "checked" : "") + "> <span><b>" + it[1] + "</b>" + (it[2] ? "<small>" + it[2] + "</small>" : "") + "</span></label>"; }).join("") + "</div>"; }
  var rv = function (m, name) { var x = m.querySelector('input[name="' + name + '"]:checked'); return x ? x.value : ""; };
  function pickRange(txt) { var r = parseRange(txt, PE.pages.length); if (r.bad) { toast("Rentang \"" + r.bad + "\" tidak valid", "error"); return null; } return r.idx.map(function (i) { return PE.pages[i]; }); }

  // ---------- OCR (tesseract.js, Indonesia + Inggris) ----------
  var TESS = null, OCRP = null;
  function tess() {
    if (!TESS) TESS = (async function () {
      await loadJs("https://cdn.jsdelivr.net/npm/tesseract.js@5.1.1/dist/tesseract.min.js");
      return window.Tesseract.createWorker(["ind", "eng"], 1, { workerPath: "https://cdn.jsdelivr.net/npm/tesseract.js@5.1.1/dist/worker.min.js", corePath: "https://cdn.jsdelivr.net/npm/tesseract.js-core@5.1.1", logger: function (m) { if (OCRP) OCRP(m); } });
    })().catch(function (e) { TESS = null; throw new Error("Mesin OCR gagal dimuat — periksa koneksi internet (" + (e && e.message || e) + ")"); });
    return TESS;
  }
  function ocrLines(data, sc, p) {
    var k = pkey(p), out = [];
    (data.lines || []).forEach(function (ln, i) {
      if (!ln.words || !ln.words.length || ln.confidence < 30) return;
      var top = ln.bbox.y0 / sc, h = (ln.bbox.y1 - ln.bbox.y0) / sc, base = ln.baseline && ln.baseline.y0 > 0 ? (ln.baseline.y0 + ln.baseline.y1) / 2 / sc : top + h * 0.8, str = "", ws = [];
      ln.words.forEach(function (w) { var t = String(w.text || "").trim(); if (!t) return; if (str) str += " "; ws.push({ s: t, cs: str.length, x: w.bbox.x0 / sc, w: Math.max(1, (w.bbox.x1 - w.bbox.x0) / sc), top: top, h: h, base: base }); str += t; });
      if (!str.trim()) return;
      var x = ln.bbox.x0 / sc, size = Math.max(5, Math.min(72, (base - top) * 1.32));
      out.push({ key: k + "#o" + i, str: str, x: x, w: (ln.bbox.x1 - ln.bbox.x0) / sc, top: top, h: h, base: base, size: size, asc: 0.8, desc: -0.2, mf: { font: "Helvetica", b: false, i: false }, words: ws, ocr: true, conf: ln.confidence });
    });
    return out;
  }
  async function ocrModal() {
    var cur = edPage(), noT = [];
    busy("Memeriksa halaman…", 30, "read");
    for (var i = 0; i < PE.pages.length; i++) { var nl = []; try { nl = await nativeLines(PE.pages[i]); } catch (e) { } if (!nl.length) noT.push(PE.pages[i]); }
    busy(null);
    var done = PE.pages.filter(function (p) { return OCR[pkey(p)]; }).length;
    var m = modal('<i class="fa-solid fa-glasses" style="color:#0891b2"></i> OCR · ubah scan jadi teks',
      '<p class="pe-mp">OCR membaca teks pada halaman hasil scan / foto, sehingga bisa <b>dicari, diedit, disensor, disalin</b>, dan PDF hasilnya <b>bisa dicari</b>. Bahasa: Indonesia + Inggris. Diproses di perangkat ini.</p>'
      + '<div class="pe-msum"><div><b>' + PE.pages.length + '</b><small>halaman</small></div><div><b>' + noT.length + '</b><small>tanpa teks (scan)</small></div><div><b>' + done + '</b><small>sudah di-OCR</small></div></div>'
      + radioRow("pe-oc", [["cur", "Halaman ini saja", "halaman " + (PE.pages.indexOf(cur) + 1)], ["scan", "Semua halaman scan (" + noT.length + ")", "halaman yang belum punya teks"], ["all", "Semua halaman (" + PE.pages.length + ")", "termasuk yang sudah punya teks — hasil OCR hanya dipakai bila teks asli kosong"]], noT.length > 1 ? "scan" : "cur")
      + '<p class="pe-mp mute"><i class="fa-solid fa-circle-info"></i> Pertama kali butuh mengunduh data bahasa (±15 MB), berikutnya tersimpan di perangkat. ±3–8 detik per halaman.</p>',
      '<button class="pe-b" data-c>Batal</button><button class="pe-b pri" data-ok><i class="fa-solid fa-glasses"></i>Jalankan OCR</button>', 560);
    m.querySelector("[data-c]").onclick = function () { m.remove(); };
    m.querySelector("[data-ok]").onclick = function () { var v = rv(m, "pe-oc"), L = v === "cur" ? [cur] : v === "scan" ? noT : PE.pages.slice(); m.remove(); if (!L.length) return toast("Tidak ada halaman scan — semua sudah punya teks", "info"); runOcr(L); };
  }
  async function runOcr(pages) {
    var n = pages.length, k = 0, found = 0;
    busy("Menyiapkan mesin OCR…", 2, "read");
    try {
      OCRP = function (m) { if (m.status === "recognizing text") busy("Membaca teks halaman " + (PE.pages.indexOf(pages[k]) + 1) + " (" + (k + 1) + "/" + n + ")…", 5 + 95 * (k + (m.progress || 0)) / n, "read"); else if (/load|init/.test(m.status) && k === 0) busy("Menyiapkan OCR: " + m.status.replace("loading", "memuat").replace("initializing", "menyiapkan").replace("language traineddata", "data bahasa").replace("tesseract", "mesin") + "…", 2 + 3 * (m.progress || 0), "read"); };
      var w = await tess();
      for (k = 0; k < n; k++) {
        var p = pages[k], D = dims(p), sc = Math.min(300 / 72, 3000 / Math.max(D.w, D.h)), c = await renderBase(p, D.w * sc, 1);
        var res = await w.recognize(c); c.width = c.height = 0;
        OCR[pkey(p)] = ocrLines(res.data, sc, p); found += OCR[pkey(p)].length;
        await tick();
      }
    } catch (e) { OCRP = null; busy(null); return toast(e.message, "error", 8000); }
    OCRP = null; busy(null); autosave();
    if (ED.on) { var cp = edPage(); ED.lines = cp ? await pageLines(cp) : []; edDraw(); edProps(); edTools(); }
    toast("OCR selesai: " + found + " baris teks dari " + n + " halaman — kini bisa dicari, diedit & disensor. PDF hasilnya juga bisa dicari.", "success", 7000);
    if (findOn()) fdRun();
  }

  // ---------- isi formulir PDF ----------
  var FORMF = {};
  async function formFields(p) {
    var k = pkey(p); if (FORMF[k]) return FORMF[k];
    try {
      var doc = await jsDoc(p.d), pg = await doc.getPage(p.i + 1), D = dims(p), vp = pg.getViewport({ scale: 1, rotation: D.t }), an = await pg.getAnnotations();
      FORMF[k] = an.filter(function (a) { return a.subtype === "Widget" && a.fieldName && !a.pushButton && !a.hidden; }).map(function (a) {
        var r = vp.convertToViewportRectangle(a.rect);
        return { name: a.fieldName, type: a.fieldType, check: !!a.checkBox, radio: !!a.radioButton, exp: a.exportValue || a.buttonValue || "", opts: (a.options || []).map(function (o) { return { v: o.exportValue, t: o.displayValue }; }), multi: !!a.multiLine, ro: !!a.readOnly, val: a.fieldValue, max: a.maxLen || 0, x: Math.min(r[0], r[2]), y: Math.min(r[1], r[3]), w: Math.abs(r[2] - r[0]), h: Math.abs(r[3] - r[1]) };
      });
    } catch (e) { FORMF[k] = []; }
    return FORMF[k];
  }
  var fval = function (p, f) { var fv = PE.form && PE.form[p.d]; return fv && fv[f.name] != null ? fv[f.name] : (f.check ? (f.val && f.val !== "Off") : f.val == null ? "" : f.val); };
  function setF(p, name, v) { PE.form = PE.form || {}; if (!ED.formUndo) { pushUndo(); ED.formUndo = 1; setTimeout(function () { ED.formUndo = 0; }, 1200); } var fv = PE.form[p.d] = PE.form[p.d] || {}; fv[name] = v; autosave(); renderSoon(); }
  async function formLayer() {
    var p = edPage(), paper = $("pe-ed-paper"); if (!p || !paper) return;
    var lay = $("pe-formL"); if (!lay) { lay = document.createElement("div"); lay.id = "pe-formL"; lay.className = "pe-formL"; paper.insertBefore(lay, paper.querySelector(".pe-scan")); }
    var F = await formFields(p); if (edPage() !== p) return; ED.fields = F;
    var k = ED.k;
    lay.classList.toggle("on", ED.tool === "form");
    lay.innerHTML = F.map(function (f, i) {
      var v = fval(p, f), st = "left:" + f.x * k + "px;top:" + f.y * k + "px;width:" + f.w * k + "px;height:" + f.h * k + "px;font-size:" + Math.max(8, Math.min(f.h * 0.7, 14) * k) + "px";
      if (f.ro) return '<div class="ro" style="' + st + '" title="' + E(f.name) + ' (hanya baca)"></div>';
      if (f.check) return '<label class="ck" style="' + st + '" title="' + E(f.name) + '"><input type="checkbox" data-fi="' + i + '" ' + (v ? "checked" : "") + "><i class=\"fa-solid fa-check\"></i></label>";
      if (f.radio) return '<label class="ck rd" style="' + st + '" title="' + E(f.name) + '"><input type="radio" name="pf-' + E(f.name) + '" data-fi="' + i + '" ' + (String(v) === String(f.exp) ? "checked" : "") + '><i class="fa-solid fa-circle"></i></label>';
      if (f.type === "Ch") return '<select data-fi="' + i + '" style="' + st + '" title="' + E(f.name) + '"><option value=""></option>' + f.opts.map(function (o) { return '<option value="' + E(o.v) + '" ' + (String(v) === String(o.v) || String(v) === String(o.t) ? "selected" : "") + ">" + E(o.t) + "</option>"; }).join("") + "</select>";
      return (f.multi ? '<textarea data-fi="' + i + '"' : '<input data-fi="' + i + '" value="' + E(v) + '"') + (f.max ? ' maxlength="' + f.max + '"' : "") + ' style="' + st + '" title="' + E(f.name) + '" placeholder="' + E(f.name) + '">' + (f.multi ? E(v) + "</textarea>" : "");
    }).join("");
    lay.querySelectorAll("[data-fi]").forEach(function (el) {
      var f = F[+el.dataset.fi];
      el.addEventListener("keydown", function (e) { e.stopPropagation(); if (e.key === "Tab") return; if (e.key === "Escape") el.blur(); });
      el.addEventListener("pointerdown", function (e) { e.stopPropagation(); });
      var on = function () { setF(p, f.name, f.check ? el.checked : f.radio ? (el.checked ? f.exp : "") : el.value); if (f.radio) lay.querySelectorAll('input[name="pf-' + CSS.escape(f.name) + '"]').forEach(function () { }); };
      el.addEventListener(f.check || f.radio || f.type === "Ch" ? "change" : "input", on);
    });
  }
  function formClear() { var p = edPage(); if (!p || !PE.form || !PE.form[p.d]) return; pushUndo(); delete PE.form[p.d]; formLayer(); toast("Isian formulir dikosongkan (kembali ke nilai asli)", "info"); }

  // ---------- potong (crop) & ubah ukuran halaman ----------
  function xformOp(o, s) {
    var X = function (v) { return s.tx + v * s.sc; }, Y = function (v) { return s.ty + v * s.sc; };
    if (o.pts) o.pts = o.pts.map(function (q) { return [X(q[0]), Y(q[1])]; });
    if (o.x1 != null) { o.x1 = X(o.x1); o.x2 = X(o.x2); o.y1 = Y(o.y1); o.y2 = Y(o.y2); }
    if (o.x != null) { o.x = X(o.x); o.y = Y(o.y); }
    if (o.w != null) o.w *= s.sc; if (o.h != null) o.h *= s.sc; if (o.lw != null) o.lw *= s.sc; if (o.size != null) o.size *= s.sc; if (o.minW) o.minW *= s.sc;
  }
  function xformLine(l, s, key) {
    var c = clone(l), X = function (v) { return s.tx + v * s.sc; }, Y = function (v) { return s.ty + v * s.sc; };
    c.x = X(l.x); c.top = Y(l.top); c.base = Y(l.base); c.w = l.w * s.sc; c.h = l.h * s.sc; c.size = l.size * s.sc; c.key = key + "#o" + l.key.split("#").pop();
    if (c.words) c.words.forEach(function (w) { w.x = X(w.x); w.top = Y(w.top); w.base = Y(w.base); w.w *= s.sc; w.h *= s.sc; });
    return c;
  }
  // rakit ulang halaman ke dokumen baru (tampilan sekarang → ukuran/area baru); editan & hasil OCR ikut dipindah
  async function remake(pages, specFn, label) {
    var L = await loadPdfLib(), out = await L.PDFDocument.create(), specs = [];
    for (var k = 0; k < pages.length; k++) {
      var p = pages[k], D = dims(p), sp0 = specFn(p, D); specs.push(sp0);
      var src = await getSrc(p.d, true), sp = src.getPage(p.i), cb = sp.getCropBox(), W = cb.width, H = cb.height, np = out.addPage([sp0.W, sp0.H]);
      if (hasContents(sp)) {
        var emb = await out.embedPage(sp, { left: cb.x, bottom: cb.y, right: cb.x + W, top: cb.y + H }), pos = { 0: [0, 0], 90: [0, W], 180: [W, H], 270: [H, 0] }[D.t], sc = sp0.sc, x0 = sp0.tx, y0 = sp0.H - sp0.ty - D.h * sc;
        np.drawPage(emb, { x: x0 + pos[0] * sc, y: y0 + pos[1] * sc, width: W * sc, height: H * sc, rotate: L.degrees(-D.t) });
      }
      busy(label + "… " + (k + 1) + "/" + pages.length, 10 + 85 * (k + 1) / pages.length);
      if (k % 4 === 3) await tick();
    }
    var bytes = new Uint8Array(await out.save()), d = PE.docs.length;
    PE.docs.push({ bytes: bytes, name: label + " · " + PE.base, hash: "rm" + d + ":" + bytes.length });
    pushUndo();
    pages.forEach(function (p, k) {
      var s = specs[k], ok = pkey(p), oc = OCR[ok];
      p.d = d; p.i = k; p.r0 = 0; p.rot = 0; p.w = s.W; p.h = s.H;
      p.ops.forEach(function (o) { xformOp(o, s); });
      if (oc) OCR[pkey(p)] = oc.map(function (l) { return xformLine(l, s, pkey(p)); });
    });
    ED.baseKey = null; ED.crop = null; THUMB = {}; stripReset(); render(); if (ED.on) { edStrip(); edLoad(); }
  }
  async function autoBox(p) {
    var D = dims(p), sc = Math.min(2, 900 / Math.max(D.w, D.h)), c = await renderBase(p, D.w * sc, 1), W = c.width, H = c.height, d = c.getContext("2d", { willReadFrequently: true }).getImageData(0, 0, W, H).data;
    var lum = function (x, y) { var i = (y * W + x) * 4; return 0.3 * d[i] + 0.59 * d[i + 1] + 0.11 * d[i + 2]; };
    var flat = function (get, len) { var a = [], i; for (i = 0; i < len; i += 2) a.push(get(i)); a.sort(function (u, v) { return u - v; }); var med = a[a.length >> 1], off = 0; for (i = 0; i < a.length; i++) if (Math.abs(a[i] - med) > 45) off++; return off / a.length < 0.004; };
    var t = 0, b = H - 1, l = 0, r = W - 1;
    while (t < b && flat(function (x) { return lum(x, t); }, W)) t++;
    while (b > t && flat(function (x) { return lum(x, b); }, W)) b--;
    while (l < r && flat(function (y) { return lum(l, y); }, H)) l++;
    while (r > l && flat(function (y) { return lum(r, y); }, H)) r--;
    c.width = c.height = 0;
    if (r - l < 20 || b - t < 20) return null;
    var pad = 8;
    return { x: Math.max(0, l / sc - pad), y: Math.max(0, t / sc - pad), w: Math.min(D.w, (r - l) / sc + pad * 2), h: Math.min(D.h, (b - t) / sc + pad * 2) };
  }
  async function cropApply(scope) {
    var p = edPage(), c = ED.crop; if (!p) return;
    var pages = scope === "all" ? PE.pages.slice() : [p], D0 = dims(p);
    if (scope === "auto" || scope === "autoAll") {
      pages = scope === "autoAll" ? PE.pages.slice() : [p]; var boxes = {};
      busy("Mendeteksi tepi kosong…", 5, "read");
      for (var i = 0; i < pages.length; i++) { boxes[pages[i].id] = await autoBox(pages[i]); busy("Mendeteksi tepi kosong… " + (i + 1) + "/" + pages.length, 5 + 40 * (i + 1) / pages.length, "read"); }
      pages = pages.filter(function (q) { var b = boxes[q.id], D = dims(q); return b && (b.w < D.w - 4 || b.h < D.h - 4); });
      if (!pages.length) { busy(null); return toast("Tidak ada tepi kosong yang bisa dipotong", "info"); }
      await remake(pages, function (q) { var b = boxes[q.id]; return { W: b.w, H: b.h, tx: -b.x, ty: -b.y, sc: 1 }; }, "Potong otomatis");
      busy(null); return toast(pages.length + " halaman dipotong otomatis — Ctrl+Z untuk membatalkan", "success");
    }
    if (!c || c.w < 10 || c.h < 10) return toast("Tarik kotak area yang ingin dipertahankan dulu", "error");
    var fx = c.x / D0.w, fy = c.y / D0.h, fw = c.w / D0.w, fh = c.h / D0.h;
    busy("Memotong halaman…", 5);
    try { await remake(pages, function (q, D) { return { W: fw * D.w, H: fh * D.h, tx: -fx * D.w, ty: -fy * D.h, sc: 1 }; }, "Potong"); } catch (e) { busy(null); return toast("Gagal: " + e.message, "error"); }
    busy(null); toast(pages.length + " halaman dipotong — Ctrl+Z untuk membatalkan", "success");
  }
  var SIZES = { A4: [595.28, 841.89, "A4 · 210×297 mm"], F4: [609.45, 935.43, "F4 / Folio · 215×330 mm"], Letter: [612, 792, "Letter · 216×279 mm"], Legal: [612, 1008, "Legal · 216×356 mm"], A5: [419.53, 595.28, "A5 · 148×210 mm"], A3: [841.89, 1190.55, "A3 · 297×420 mm"] };
  function sizeModal() {
    var p = edPage() || PE.pages[0], D = dims(p);
    var m = modal('<i class="fa-solid fa-up-right-and-down-left-from-center" style="color:#059669"></i> Ubah ukuran halaman',
      '<p class="pe-mp">Ukuran sekarang: <b>' + Math.round(D.w * 0.3528) + " × " + Math.round(D.h * 0.3528) + ' mm</b>. Isi halaman diskalakan pas & ditengahkan — tidak terpotong.</p>'
      + '<div class="pe-pn-f"><div class="g2"><div><label>Ukuran kertas</label><select id="sz-k">' + Object.keys(SIZES).map(function (k) { return '<option value="' + k + '">' + SIZES[k][2] + "</option>"; }).join("") + '</select></div><div><label>Orientasi</label><select id="sz-o"><option value="auto">Ikuti tiap halaman</option><option value="p">Potret</option><option value="l">Lanskap</option></select></div></div>'
      + '<div class="g2"><div><label>Margin (mm)</label><input type="number" id="sz-m" min="0" max="40" value="0"></div><div><label>Halaman</label><input id="sz-r" placeholder="Semua · atau mis. 1-3"></div></div></div>',
      '<button class="pe-b" data-c>Batal</button><button class="pe-b pri" data-ok><i class="fa-solid fa-check"></i>Ubah ukuran</button>', 560);
    m.querySelectorAll("input").forEach(function (x) { x.addEventListener("keydown", function (e) { e.stopPropagation(); }); });
    m.querySelector("[data-c]").onclick = function () { m.remove(); };
    m.querySelector("[data-ok]").onclick = async function () {
      var S = SIZES[m.querySelector("#sz-k").value], o = m.querySelector("#sz-o").value, mg = Math.max(0, +m.querySelector("#sz-m").value || 0) / 0.3528, pages = pickRange(m.querySelector("#sz-r").value); if (!pages) return;
      m.remove(); busy("Mengubah ukuran…", 5);
      try {
        await remake(pages, function (q, Dq) { var land = o === "l" || (o === "auto" && Dq.w > Dq.h), TW = land ? Math.max(S[0], S[1]) : Math.min(S[0], S[1]), TH = land ? Math.min(S[0], S[1]) : Math.max(S[0], S[1]), sc = Math.min((TW - 2 * mg) / Dq.w, (TH - 2 * mg) / Dq.h); return { W: TW, H: TH, sc: sc, tx: (TW - Dq.w * sc) / 2, ty: (TH - Dq.h * sc) / 2 }; }, "Ubah ukuran");
      } catch (e) { busy(null); return toast("Gagal: " + e.message, "error"); }
      busy(null); toast(pages.length + " halaman diubah ke " + S[2].split(" ·")[0] + " — Ctrl+Z untuk membatalkan", "success");
    };
  }

  // ---------- catatan & tautan ----------
  var NOTEC = ["#f59e0b", "#3b82f6", "#22c55e", "#ec4899", "#a855f7"];
  function popAt(o) { var mp = $("pe-mpop"), k = ED.k, pw = $("pe-ed-paper").offsetWidth, left = (o.x + o.w) * k + 10; if (left + mp.offsetWidth > pw - 4) left = Math.max(4, o.x * k - mp.offsetWidth - 10); mp.style.left = left + "px"; mp.style.top = Math.max(4, Math.min($("pe-ed-paper").offsetHeight - mp.offsetHeight - 4, o.y * k)) + "px"; }
  function notePop(o, fresh) {
    var mp = $("pe-mpop"); if (!mp) return;
    mp.innerHTML = '<div class="hd"><span class="dot" style="background:' + o.c + '"></span><b>Catatan</b><small>' + E(o.by || "") + '</small><button data-a="x" class="x"><i class="fa-solid fa-xmark"></i></button></div>'
      + '<textarea class="pe-nta" id="pe-nta" rows="4" placeholder="Tulis catatan / komentar untuk dokumen ini…">' + E(o.text || "") + "</textarea>"
      + '<div class="pe-ntc">' + NOTEC.map(function (c) { return '<button data-nc="' + c + '" class="' + (c === o.c ? "on" : "") + '" style="background:' + c + '"></button>'; }).join("") + '<span style="flex:1"></span><button class="pe-b red" data-a="del" style="height:28px"><i class="fa-regular fa-trash-can"></i>Hapus</button><button class="pe-b pri" data-a="ok" style="height:28px"><i class="fa-solid fa-check"></i>Simpan</button></div>';
    mp.classList.remove("hidden"); popAt(o);
    var ta = mp.querySelector("#pe-nta"); ta.onkeydown = function (e) { e.stopPropagation(); if (e.key === "Enter" && (e.ctrlKey || e.metaKey)) save(); if (e.key === "Escape") close(); };
    ta.onpointerdown = function (e) { e.stopPropagation(); };
    setTimeout(function () { ta.focus(); }, 30);
    var p = edPage(), before = JSON.stringify(o);
    var close = function () { hidePop(); if (fresh && !o.text) { p.ops.splice(p.ops.indexOf(o), 1); ED.sel = null; PE.undo.pop(); syncUndo(); } edDraw(); edProps(); renderSoon(); };
    var save = function () { var t = ta.value.trim(); if (!fresh && t !== o.text) pushUndo(); o.text = t; if (!t) { if (!fresh) p.ops.splice(p.ops.indexOf(o), 1); else close(); } fresh = false; hidePop(); edDraw(); edProps(); renderSoon(); };
    mp.querySelectorAll("[data-nc]").forEach(function (b) { b.onpointerdown = function (e) { e.stopPropagation(); }; b.onclick = function () { if (!fresh) pushUndo(); o.c = ED.st.nc = b.dataset.nc; mp.querySelectorAll("[data-nc]").forEach(function (x) { x.classList.toggle("on", x === b); }); mp.querySelector(".dot").style.background = o.c; edDraw(); }; });
    mp.querySelectorAll("[data-a]").forEach(function (b) { b.onpointerdown = function (e) { e.stopPropagation(); }; b.onclick = function (e) { e.stopPropagation(); var a = b.dataset.a; if (a === "x") close(); else if (a === "ok") save(); else if (a === "del") { if (fresh) { o.text = ""; close(); } else { pushUndo(); p.ops.splice(p.ops.indexOf(o), 1); ED.sel = null; hidePop(); edDraw(); edProps(); renderSoon(); } } }; });
    void before;
  }
  function linkPop(o, fresh) {
    var mp = $("pe-mpop"); if (!mp) return;
    var web = !o.page;
    mp.innerHTML = '<div class="hd"><span class="dot" style="background:#2563eb"></span><b>Tautan</b><button data-a="x" class="x"><i class="fa-solid fa-xmark"></i></button></div>'
      + '<div class="pe-fseg" style="margin:4px 0 8px"><button data-lt="web" class="' + (web ? "on" : "") + '"><i class="fa-solid fa-globe"></i>Situs web</button><button data-lt="pg" class="' + (web ? "" : "on") + '"><i class="fa-regular fa-file"></i>Halaman</button></div>'
      + '<input id="pe-lku" placeholder="https://…" value="' + E(o.url || "") + '" class="' + (web ? "" : "hidden") + '" style="width:100%">'
      + '<input id="pe-lkp" type="number" min="1" max="' + PE.pages.length + '" placeholder="Nomor halaman tujuan (1–' + PE.pages.length + ')" value="' + (o.page || "") + '" class="' + (web ? "hidden" : "") + '" style="width:100%">'
      + '<div class="pe-ntc" style="margin-top:8px"><span style="flex:1"></span><button class="pe-b red" data-a="del" style="height:28px"><i class="fa-regular fa-trash-can"></i>Hapus</button><button class="pe-b pri" data-a="ok" style="height:28px"><i class="fa-solid fa-check"></i>Simpan</button></div>';
    mp.classList.remove("hidden"); popAt(o);
    var u = mp.querySelector("#pe-lku"), pg = mp.querySelector("#pe-lkp"), p = edPage();
    [u, pg].forEach(function (x) { x.onkeydown = function (e) { e.stopPropagation(); if (e.key === "Enter") save(); }; x.onpointerdown = function (e) { e.stopPropagation(); }; });
    setTimeout(function () { (web ? u : pg).focus(); }, 30);
    mp.querySelectorAll("[data-lt]").forEach(function (b) { b.onpointerdown = function (e) { e.stopPropagation(); }; b.onclick = function () { web = b.dataset.lt === "web"; mp.querySelectorAll("[data-lt]").forEach(function (x) { x.classList.toggle("on", x === b); }); u.classList.toggle("hidden", !web); pg.classList.toggle("hidden", web); (web ? u : pg).focus(); }; });
    var drop = function () { var i = p.ops.indexOf(o); if (i >= 0) p.ops.splice(i, 1); ED.sel = null; };
    var save = function () {
      var url = u.value.trim(), n = parseInt(pg.value, 10);
      if (web) { if (!url) return toast("Isi alamat web", "error"); if (!/^(https?:|mailto:|tel:)/i.test(url)) url = (/@/.test(url) && !/\//.test(url) ? "mailto:" : "https://") + url; }
      else if (!(n >= 1 && n <= PE.pages.length)) return toast("Nomor halaman 1–" + PE.pages.length, "error");
      if (!fresh) pushUndo(); o.url = web ? url : ""; o.page = web ? 0 : n; fresh = false; hidePop(); edDraw(); edProps(); renderSoon(); toast("Tautan disimpan — aktif saat PDF dibuka", "success");
    };
    mp.querySelectorAll("[data-a]").forEach(function (b) { b.onpointerdown = function (e) { e.stopPropagation(); }; b.onclick = function (e) { e.stopPropagation(); var a = b.dataset.a; if (a === "ok") save(); else if (a === "x") { if (fresh) { drop(); PE.undo.pop(); syncUndo(); } hidePop(); edDraw(); edProps(); } else if (a === "del") { if (!fresh) pushUndo(); else { PE.undo.pop(); syncUndo(); } drop(); hidePop(); edDraw(); edProps(); renderSoon(); } }; });
  }
  function notesList() {
    var rows = []; PE.pages.forEach(function (p, i) { p.ops.forEach(function (o) { if (o.t === "note" || o.t === "link") rows.push({ p: p, i: i, o: o }); }); });
    var m = modal('<i class="fa-solid fa-comments" style="color:#f59e0b"></i> Daftar catatan &amp; tautan (' + rows.length + ")",
      rows.length ? '<div class="pe-nlist">' + rows.map(function (r, j) { var o = r.o; return '<button data-j="' + j + '"><span class="pg">Hal ' + (r.i + 1) + '</span>' + (o.t === "note" ? '<i class="fa-solid fa-note-sticky" style="color:' + o.c + '"></i><span class="tx"><b>' + E(o.by || "") + "</b>" + E(o.text || "(kosong)") + "</span>" : '<i class="fa-solid fa-link" style="color:#2563eb"></i><span class="tx">' + E(o.url || "ke halaman " + o.page) + "</span>") + "</button>"; }).join("") + "</div>" : '<div class="pe-lib-empty"><i class="fa-solid fa-note-sticky"></i><b>Belum ada catatan</b><small>Pilih alat Catatan lalu klik di halaman.</small></div>',
      '<button class="pe-b" data-c>Tutup</button>', 560);
    m.querySelector("[data-c]").onclick = function () { m.remove(); };
    m.querySelectorAll("[data-j]").forEach(function (b) { b.onclick = function () { var r = rows[+b.dataset.j]; m.remove(); if (r.p.id !== ED.id) edGoTo(r.p.id, 1); ED.tool = "sel"; ED.sel = r.o; edTools(); edProps(); edDraw(); setTimeout(function () { r.o.t === "note" ? notePop(r.o) : linkPop(r.o); }, 120); }; });
  }

  // ---------- kompres ----------
  function compModal() {
    var m = modal('<i class="fa-solid fa-file-zipper" style="color:#7c3aed"></i> Kompres PDF',
      '<p class="pe-mp">Halaman bergambar (hasil scan / foto) diperkecil resolusinya; halaman teks biasa tetap tajam. Teks tetap <b>bisa dicari & disalin</b>. Berlaku untuk Unduh, Submit, dan Simpan ke Drive.</p>'
      + radioRow("pe-cp", [["0", "Tanpa kompres", "kualitas asli"], ["1", "Seimbang (disarankan)", "150 dpi — tetap jelas untuk dibaca & dicetak"], ["2", "Maksimal", "110 dpi — paling kecil, cocok untuk kirim via chat / email"]], String(PE.comp || 0))
      + '<div class="pe-msum" id="pe-cpsum" style="margin-top:10px"><div><b>–</b><small>asli</small></div><div><b>–</b><small>seimbang</small></div><div><b>–</b><small>maksimal</small></div></div>',
      '<button class="pe-b" data-calc style="margin-right:auto"><i class="fa-solid fa-calculator"></i>Hitung ukuran</button><button class="pe-b" data-c>Batal</button><button class="pe-b pri" data-ok><i class="fa-solid fa-check"></i>Pakai</button>', 560);
    m.querySelector("[data-c]").onclick = function () { m.remove(); };
    m.querySelector("[data-calc]").onclick = async function () {
      var L = listNow(), box = m.querySelector("#pe-cpsum"), res = [];
      m.dataset.busy = 1;
      try { for (var c = 0; c <= 2; c++) { busy("Menghitung ukuran " + ["asli", "seimbang", "maksimal"][c] + "…", 10 + c * 30); res.push((await buildPdf(L, PE.base, null, { comp: c, noCmp: 1 })).length); } } catch (e) { toast(e.message, "error"); }
      busy(null); delete m.dataset.busy;
      if (res.length === 3) box.innerHTML = res.map(function (b, i) { var pct = i ? Math.round(100 - 100 * Math.min(b, res[0]) / res[0]) : 0; return "<div><b>" + MB(Math.min(b, res[0])) + "</b><small>" + ["asli", "seimbang", "maksimal"][i] + (i ? (pct > 0 ? " · −" + pct + "%" : " · tidak lebih kecil") : "") + "</small></div>"; }).join("");
    };
    m.querySelector("[data-ok]").onclick = function () { PE.comp = +rv(m, "pe-cp") || 0; m.remove(); render(); toast(PE.comp ? "Kompres " + COMP[PE.comp].t + " aktif untuk semua hasil" : "Kompres dimatikan", "success"); };
  }

  // ---------- password (qpdf) ----------
  var QW = null;
  function qpdfLib() {
    if (!QW) QW = (async function () {
      var base = "https://cdn.jsdelivr.net/npm/@neslinesli93/qpdf-wasm@0.3.0/dist/";
      var r1 = await fetch(base + "qpdf.js"), r2 = await fetch(base + "qpdf.wasm"); if (!r1.ok || !r2.ok) throw new Error("unduh gagal");
      var src = await r1.text(), factory = new Function("module", "exports", src + "\n;return Module;")({}, {});
      return { factory: factory, wasm: new Uint8Array(await r2.arrayBuffer()) };
    })().catch(function (e) { QW = null; throw new Error("Modul password gagal dimuat — periksa koneksi (" + (e && e.message) + ")"); });
    return QW;
  }
  async function qpdf(args, input) {
    var q = await qpdfLib(), err = [], inst = await q.factory({ wasmBinary: q.wasm, noInitialRun: true, locateFile: function (f) { return "https://cdn.jsdelivr.net/npm/@neslinesli93/qpdf-wasm@0.3.0/dist/" + f; }, instantiateWasm: function (imp, cb) { WebAssembly.instantiate(q.wasm, imp).then(function (r) { cb(r.instance, r.module); }); return {}; }, print: function () { }, printErr: function (t) { err.push(t); } });
    inst.FS.writeFile("/in.pdf", input);
    var code = 0; try { code = inst.callMain(args); } catch (e) { code = e && e.status != null ? e.status : 1; if (!err.length && e && e.message) err.push(e.message); }
    if (code !== 0 && code !== 3) { var msg = err.join(" "); var ex = new Error(/invalid password/i.test(msg) ? "Password salah" : (msg || "qpdf gagal (" + code + ")")); ex.pw = /invalid password/i.test(msg); ex.code = code; throw ex; }
    return inst.FS.readFile("/out.pdf");
  }
  var hasEncrypt = function (b) { var pat = [47, 69, 110, 99, 114, 121, 112, 116]; outer: for (var i = 0, n = b.length - 8; i < n; i++) { if (b[i] !== 47) continue; for (var j = 1; j < 8; j++) if (b[i + j] !== pat[j]) continue outer; return true; } return false; };
  function askPw(name, wrong) {
    return new Promise(function (ok) {
      var m = modal('<i class="fa-solid fa-lock" style="color:#d97706"></i> PDF dikunci password', '<p class="pe-mp">"' + E(name) + '" dilindungi password. Masukkan password untuk membukanya — kunci dilepas di perangkat ini saja.</p>' + (wrong ? '<p class="pe-mp" style="color:#e11d48;font-weight:700"><i class="fa-solid fa-triangle-exclamation"></i> Password salah, coba lagi.</p>' : "") + '<input type="password" id="pe-pwi" placeholder="Password PDF" style="width:100%;height:38px" autocomplete="off">',
        '<button class="pe-b" data-c>Lewati file ini</button><button class="pe-b pri" data-ok><i class="fa-solid fa-unlock"></i>Buka kunci</button>', 440);
      var i = m.querySelector("#pe-pwi"); setTimeout(function () { i.focus(); }, 40);
      var done = function (v) { m.remove(); ok(v); };
      i.onkeydown = function (e) { e.stopPropagation(); if (e.key === "Enter") done(i.value); };
      m.querySelector("[data-c]").onclick = function () { done(null); }; m.querySelector("[data-ok]").onclick = function () { done(i.value); };
      m.querySelector("[data-x]").onclick = function () { done(null); };
    });
  }
  // buka file berpassword / berenkripsi pemilik (izin) → salinan tanpa kunci
  async function unlockBytes(bytes, name) {
    var wrong = false;
    for (;;) {
      busy(null); var pw = await askPw(name, wrong); if (pw == null) return null;
      busy("Membuka kunci…", 40, "read");
      try { return await qpdf(["--password=" + pw, "--decrypt", "/in.pdf", "/out.pdf"], bytes); } catch (e) { if (e.pw || e.code === 2) { wrong = true; continue; } busy(null); throw e; }
    }
  }
  async function finalPdf(b, P0) {
    var P = P0 || PE.pw; if (!P) return b;
    var owner = P.owner || (P.user + "·" + Math.random().toString(36).slice(2, 10));
    return qpdf(["--encrypt", P.user || "", owner, "256", "--print=" + (P.print ? "full" : "none"), "--extract=" + (P.copy ? "y" : "n"), "--modify=" + (P.edit ? "all" : "none"), "--", "/in.pdf", "/out.pdf"], b);
  }
  function pwModal() {
    var P = PE.pw || { user: "", print: true, copy: false, edit: false };
    var tg = function (k, t, s) { return '<label class="pe-tog"><input type="checkbox" data-pk="' + k + '" ' + (P[k] ? "checked" : "") + '><span class="sw"></span><span><b>' + t + "</b><small>" + s + "</small></span></label>"; };
    var m = modal('<i class="fa-solid fa-lock" style="color:#d97706"></i> Kunci PDF dengan password',
      '<p class="pe-mp">Berlaku untuk file yang <b>diunduh</b> (AES-256). File yang dikirim ke sistem (Submit / Drive / Signing) tidak dikunci agar tetap bisa diproses.</p>'
      + '<div class="pe-pn-f"><label>Password untuk membuka</label><input type="password" id="pw-u" value="' + E(P.user) + '" placeholder="min. 4 karakter" autocomplete="new-password"><label>Ulangi password</label><input type="password" id="pw-u2" value="' + E(P.user) + '" autocomplete="new-password">'
      + tg("print", "Boleh dicetak", "penerima bisa mencetak") + tg("copy", "Boleh menyalin teks", "matikan agar isi tidak mudah disalin") + tg("edit", "Boleh diubah", "matikan agar tidak bisa diedit di aplikasi PDF") + "</div>",
      (PE.pw ? '<button class="pe-b red" data-off style="margin-right:auto"><i class="fa-solid fa-lock-open"></i>Matikan kunci</button>' : "") + '<button class="pe-b" data-c>Batal</button><button class="pe-b pri" data-ok><i class="fa-solid fa-lock"></i>Kunci unduhan</button>', 520);
    m.querySelectorAll("input").forEach(function (x) { x.addEventListener("keydown", function (e) { e.stopPropagation(); }); });
    m.querySelector("[data-c]").onclick = function () { m.remove(); };
    var off = m.querySelector("[data-off]"); if (off) off.onclick = function () { PE.pw = null; m.remove(); render(); toast("Kunci password dimatikan", "info"); };
    m.querySelector("[data-ok]").onclick = function () {
      var u = m.querySelector("#pw-u").value, u2 = m.querySelector("#pw-u2").value;
      if (u.length < 4) return toast("Password minimal 4 karakter", "error"); if (u !== u2) return toast("Ulangi password tidak sama", "error");
      var o = { user: u }; m.querySelectorAll("[data-pk]").forEach(function (c) { o[c.dataset.pk] = c.checked; });
      PE.pw = o; m.remove(); render(); qpdfLib().catch(function (e) { toast(e.message, "error"); }); toast("File yang diunduh akan dikunci password", "success");
    };
  }

  // ---------- konversi: gambar, Word, Excel ----------
  async function pageCanvas(p, dpi) { var D = dims(p), sc = Math.min(dpi / 72, 4000 / Math.max(D.w, D.h)), c = await renderBase(p, D.w * sc, 1); drawOps(c.getContext("2d"), p.ops, c.width / D.w); return c; }
  function imgModal() {
    var m = modal('<i class="fa-solid fa-file-image" style="color:#0891b2"></i> Unduh sebagai gambar',
      '<div class="pe-pn-f"><div class="g2"><div><label>Format</label><select id="im-f"><option value="jpg">JPG (lebih kecil)</option><option value="png">PNG (tajam, lossless)</option></select></div><div><label>Resolusi</label><select id="im-d"><option value="100">100 dpi · layar</option><option value="150" selected>150 dpi · standar</option><option value="200">200 dpi · tajam</option><option value="300">300 dpi · cetak</option></select></div></div><label>Halaman</label><input id="im-r" placeholder="Semua halaman · atau mis. 1-3, 5"></div><p class="pe-mp mute">Lebih dari 1 halaman → satu file ZIP. Semua editan ikut tergambar.</p>',
      '<button class="pe-b" data-c>Batal</button><button class="pe-b pri" data-ok><i class="fa-solid fa-download"></i>Unduh</button>', 500);
    m.querySelector("#im-r").onkeydown = function (e) { e.stopPropagation(); };
    m.querySelector("[data-c]").onclick = function () { m.remove(); };
    m.querySelector("[data-ok]").onclick = async function () {
      var fmt = m.querySelector("#im-f").value, dpi = +m.querySelector("#im-d").value, L = listNow(), r = parseRange(m.querySelector("#im-r").value, L.length); if (r.bad) return toast("Rentang \"" + r.bad + "\" tidak valid", "error");
      m.remove(); var files = [];
      try {
        for (var k = 0; k < r.idx.length; k++) {
          busy("Membuat gambar halaman " + (r.idx[k] + 1) + "…", 5 + 90 * k / r.idx.length);
          var c = await pageCanvas(L[r.idx[k]], dpi), b = fmt === "png" ? await canvasPng(c) : await canvasJpg(c, 0.9); c.width = c.height = 0;
          files.push({ name: safeName(PE.base) + " - hal " + (r.idx[k] + 1) + "." + fmt, bytes: b });
        }
        if (files.length === 1) saveBlob(files[0].bytes, files[0].name, fmt === "png" ? "image/png" : "image/jpeg");
        else { busy("Membuat ZIP…", 97); await loadJs("https://cdnjs.cloudflare.com/ajax/libs/jszip/3.10.1/jszip.min.js"); var z = new window.JSZip(); files.forEach(function (f) { z.file(f.name, f.bytes); }); saveBlob(await z.generateAsync({ type: "uint8array" }), safeName(PE.base) + " (" + files.length + " gambar).zip", "application/zip"); }
      } catch (e) { toast("Gagal: " + e.message, "error"); }
      busy(null);
    };
  }
  var X = function (t) { return String(t == null ? "" : t).replace(/[&<>"]/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]; }).replace(/[\u0000-\u0008\u000b\u000c\u000e-\u001f]/g, ""); };
  // baris teks halaman untuk ekspor: teks asli/OCR yang belum diganti + teks tambahan; yang disensor dibuang
  async function exportLines(p) {
    var ln = []; try { ln = await pageLines(p); } catch (e) { }
    var done = {}, er = p.ops.filter(function (o) { return o.t === "erase"; }); p.ops.forEach(function (o) { if (o.key) done[o.key] = 1; });
    var out = [];
    ln.forEach(function (l) { if (done[l.key]) return; var ws = wordsOf(l).filter(function (w) { var wb = { x: w.x, y: w.top, w: w.w, h: w.h }; return !er.some(function (e) { return ovl(e, wb) > wb.w * wb.h * 0.25; }); }); if (!ws.length) return; out.push({ str: ws.map(function (w) { return w.s; }).join(" "), x: ws[0].x, top: l.top, h: l.h, size: l.size, b: l.mf.b, i: l.mf.i, words: ws }); });
    p.ops.forEach(function (o) { if (o.t !== "text" || !o.text || o.grp === "wm") return; textLines(o).forEach(function (t, j) { if (!t.trim()) return; out.push({ str: t, x: o.x + PAD, top: o.y + PAD + j * o.size * LH, h: o.size * LH, size: o.size, b: o.b, i: o.i, al: o.al, w: o.w }); }); });
    out.sort(function (a, b) { return Math.abs(a.top - b.top) > Math.min(a.h, b.h) * 0.5 ? a.top - b.top : a.x - b.x; });
    return out;
  }
  function docxModal() {
    var m = modal('<i class="fa-solid fa-file-word" style="color:#2563eb"></i> Unduh sebagai Word (.docx)',
      radioRow("pe-dx", [["text", "Teks bisa diedit", "baris & paragraf jadi teks Word (ukuran, tebal, posisi dikira-kira). Halaman scan perlu OCR dulu."], ["img", "Tampilan persis seperti asli", "tiap halaman jadi gambar di Word — rapi tapi teks tidak bisa diedit"]], "text"),
      '<button class="pe-b" data-c>Batal</button><button class="pe-b pri" data-ok><i class="fa-solid fa-download"></i>Unduh .docx</button>', 520);
    m.querySelector("[data-c]").onclick = function () { m.remove(); };
    m.querySelector("[data-ok]").onclick = function () { var v = rv(m, "pe-dx"); m.remove(); exportDocx(v); };
  }
  async function exportDocx(mode, L0, ret) {
    var L = L0 || listNow(); if (!L.length) return;
    busy("Menyusun dokumen Word…", 3);
    try {
      await loadJs("https://cdnjs.cloudflare.com/ajax/libs/jszip/3.10.1/jszip.min.js");
      var z = new window.JSZip(), body = "", rels = [], D0 = dims(L[0]), emptyPages = 0;
      for (var k = 0; k < L.length; k++) {
        var p = L[k], D = dims(p);
        if (k) body += '<w:p><w:r><w:br w:type="page"/></w:r></w:p>';
        if (mode === "img") {
          var c = await pageCanvas(p, 150), b = await canvasJpg(c, 0.85), id = "rI" + (k + 1); c.width = c.height = 0;
          z.file("word/media/hal" + (k + 1) + ".jpeg", b); rels.push('<Relationship Id="' + id + '" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/image" Target="media/hal' + (k + 1) + '.jpeg"/>');
          var cx = Math.round(D0.w * 0.985 * 12700), cy = Math.round(D0.w * 0.985 * D.h / D.w * 12700);
          body += '<w:p><w:pPr><w:spacing w:before="0" w:after="0"/><w:jc w:val="center"/></w:pPr><w:r><w:drawing><wp:inline distT="0" distB="0" distL="0" distR="0"><wp:extent cx="' + cx + '" cy="' + cy + '"/><wp:docPr id="' + (k + 1) + '" name="Halaman ' + (k + 1) + '"/><a:graphic xmlns:a="http://schemas.openxmlformats.org/drawingml/2006/main"><a:graphicData uri="http://schemas.openxmlformats.org/drawingml/2006/picture"><pic:pic xmlns:pic="http://schemas.openxmlformats.org/drawingml/2006/picture"><pic:nvPicPr><pic:cNvPr id="' + (k + 1) + '" name="hal' + (k + 1) + '.jpeg"/><pic:cNvPicPr/></pic:nvPicPr><pic:blipFill><a:blip r:embed="' + id + '"/><a:stretch><a:fillRect/></a:stretch></pic:blipFill><pic:spPr><a:xfrm><a:off x="0" y="0"/><a:ext cx="' + cx + '" cy="' + cy + '"/></a:xfrm><a:prstGeom prst="rect"><a:avLst/></a:prstGeom></pic:spPr></pic:pic></a:graphicData></a:graphic></wp:inline></w:drawing></w:r></w:p>';
        } else {
          var ls = await exportLines(p); if (!ls.length) { emptyPages++; body += '<w:p><w:r><w:rPr><w:i/><w:color w:val="94A3B8"/></w:rPr><w:t xml:space="preserve">[Halaman ' + (k + 1) + ': tidak ada teks — halaman scan perlu OCR]</w:t></w:r></w:p>'; continue; }
          var left = Math.max(28, Math.min(90, Math.min.apply(null, ls.map(function (l) { return l.x; })))), prevB = 50;
          // gabung baris dengan top sama → satu paragraf dengan tab
          var rows = []; ls.forEach(function (l) { var r = rows[rows.length - 1]; if (r && Math.abs(r.top - l.top) < Math.min(r.h, l.h) * 0.5) r.parts.push(l); else rows.push({ top: l.top, h: l.h, parts: [l] }); });
          rows.forEach(function (r) {
            var f = r.parts[0], gap = Math.max(0, r.top - prevB), mid = (f.x + (r.parts[r.parts.length - 1].x + (r.parts[r.parts.length - 1].w || 0))) / 2, center = r.parts.length === 1 && f.x > left + 40 && Math.abs((f.x + f.str.length * f.size * 0.25) - D.w / 2) < D.w * 0.08;
            void mid;
            body += '<w:p><w:pPr><w:spacing w:before="' + Math.round(Math.min(gap, 60) * 20) + '" w:after="0" w:line="' + Math.round(Math.max(f.size * 1.15, 10) * 20) + '" w:lineRule="atLeast"/>' + (center ? '<w:jc w:val="center"/>' : '<w:ind w:left="' + Math.round(Math.max(0, f.x - left) * 20) + '"/>') + "</w:pPr>";
            r.parts.forEach(function (pt, j) { body += (j ? '<w:r><w:tab/></w:r>' : "") + '<w:r><w:rPr><w:rFonts w:ascii="Arial" w:hAnsi="Arial" w:cs="Arial"/>' + (pt.b ? "<w:b/>" : "") + (pt.i ? "<w:i/>" : "") + '<w:sz w:val="' + Math.max(12, Math.round(pt.size * 2)) + '"/></w:rPr><w:t xml:space="preserve">' + X(pt.str) + "</w:t></w:r>"; });
            body += "</w:p>"; prevB = r.top + r.h;
          });
        }
        busy("Menyusun dokumen Word… " + (k + 1) + "/" + L.length, 5 + 85 * (k + 1) / L.length);
      }
      var mg = mode === "img" ? 0 : 720, left2 = mode === "img" ? 0 : 1134;
      var doc = '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships" xmlns:wp="http://schemas.openxmlformats.org/drawingml/2006/wordprocessingDrawing"><w:body>' + body
        + '<w:sectPr><w:pgSz w:w="' + Math.round(D0.w * 20) + '" w:h="' + Math.round(D0.h * 20) + '"' + (D0.w > D0.h ? ' w:orient="landscape"' : "") + '/><w:pgMar w:top="' + mg + '" w:right="' + left2 + '" w:bottom="' + mg + '" w:left="' + left2 + '" w:header="0" w:footer="0" w:gutter="0"/></w:sectPr></w:body></w:document>';
      z.file("[Content_Types].xml", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/><Default Extension="xml" ContentType="application/xml"/><Default Extension="jpeg" ContentType="image/jpeg"/><Override PartName="/word/document.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.document.main+xml"/></Types>');
      z.file("_rels/.rels", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="word/document.xml"/></Relationships>');
      z.file("word/_rels/document.xml.rels", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">' + rels.join("") + "</Relationships>");
      z.file("word/document.xml", doc);
      var out = await z.generateAsync({ type: "uint8array", compression: "DEFLATE" });
      if (ret) { busy(null); return { bytes: out, empty: emptyPages }; }
      saveBlob(out, safeName(PE.base) + ".docx", "application/vnd.openxmlformats-officedocument.wordprocessingml.document");
      busy(null); toast("File Word diunduh" + (emptyPages ? " — " + emptyPages + " halaman tanpa teks (jalankan OCR untuk halaman scan)" : ""), emptyPages ? "info" : "success", 6000);
    } catch (e) { busy(null); if (ret) throw e; toast("Gagal: " + e.message, "error"); }
  }
  // sel tabel dari posisi teks: baris = garis dasar sama, kolom = jarak antar teks
  async function pageCells(p) {
    var items = [];
    try { await nativeLines(p); } catch (e) { }
    var k = pkey(p), done = {}, er = p.ops.filter(function (o) { return o.t === "erase"; }); p.ops.forEach(function (o) { if (o.key) done[o.key] = 1; });
    if (TXTI[k] && TXTI[k].length) items = TXTI[k].map(function (it) { return { x: it.x, base: it.base, w: it.w, size: it.size, str: it.str }; });
    else if (OCR[k]) OCR[k].forEach(function (l) { l.words.forEach(function (w) { items.push({ x: w.x, base: w.base, w: w.w, size: l.size, str: w.s }); }); });
    items = items.filter(function (it) { var b = { x: it.x, y: it.base - it.size, w: it.w, h: it.size }; return it.str.trim() && !er.some(function (e) { return ovl(e, b) > b.w * b.h * 0.25; }); });
    var rows = [];
    items.sort(function (a, b) { return Math.abs(a.base - b.base) > Math.min(a.size, b.size) * 0.4 ? a.base - b.base : a.x - b.x; }).forEach(function (it) { var r = rows[rows.length - 1]; if (r && Math.abs(r.base - it.base) < Math.min(r.size, it.size) * 0.45) r.it.push(it); else rows.push({ base: it.base, size: it.size, it: [it] }); });
    rows.forEach(function (r) { r.it.sort(function (a, b) { return a.x - b.x; }); var cells = []; r.it.forEach(function (it) { var c = cells[cells.length - 1]; if (c && it.x - (c.x + c.w) < Math.max(r.size * 0.9, 4)) { c.s += (it.x - (c.x + c.w) > r.size * 0.15 ? " " : "") + it.str.trim(); c.w = it.x + it.w - c.x; } else cells.push({ x: it.x, w: it.w, s: it.str.trim() }); }); r.cells = cells; });
    var xs = []; rows.forEach(function (r) { r.cells.forEach(function (c) { xs.push(c.x); }); }); xs.sort(function (a, b) { return a - b; });
    var anc = []; xs.forEach(function (x) { if (!anc.length || x - anc[anc.length - 1].last > 9) anc.push({ x: x, last: x, n: 1 }); else { anc[anc.length - 1].last = x; anc[anc.length - 1].n++; } });
    var col = function (x) { var best = 0, bd = 1e9; anc.forEach(function (a, i) { var d = Math.abs(a.x - x); if (d < bd) { bd = d; best = i; } }); return best; };
    return rows.map(function (r) { var out = []; r.cells.forEach(function (c) { var j = col(c.x); while (out[j] != null && j < anc.length + 20) j++; out[j] = c.s; }); return out; });
  }
  var numId = function (s) { var t = String(s).replace(/^Rp\.?\s*/i, "").trim(); if (/^-?\d{1,3}(\.\d{3})+(,\d+)?$/.test(t) || /^-?\d+(,\d+)?$/.test(t)) { var n = parseFloat(t.replace(/\./g, "").replace(",", ".")); if (isFinite(n) && t.replace(/\D/g, "").length < 16) return n; } return null; };
  var colName = function (i) { var s = ""; i++; while (i) { var m = (i - 1) % 26; s = String.fromCharCode(65 + m) + s; i = Math.floor((i - 1) / 26); } return s; };
  async function exportXlsx(L0, ret) {
    var L = (L0 && L0.length != null ? L0 : null) || listNow(); if (!L.length) return;
    busy("Menyusun Excel…", 3);
    try {
      await loadJs("https://cdnjs.cloudflare.com/ajax/libs/jszip/3.10.1/jszip.min.js");
      var z = new window.JSZip(), sheets = [], empty = 0;
      for (var k = 0; k < L.length; k++) {
        var rows = await pageCells(L[k]), wid = [];
        if (!rows.length) empty++;
        var sd = rows.map(function (r, ri) { return '<row r="' + (ri + 1) + '">' + r.map(function (v, ci) { if (v == null || v === "") return ""; wid[ci] = Math.max(wid[ci] || 6, Math.min(60, String(v).length + 2)); var ref = colName(ci) + (ri + 1), n = numId(v); return n != null ? '<c r="' + ref + '"><v>' + n + "</v></c>" : '<c r="' + ref + '" t="inlineStr"><is><t xml:space="preserve">' + X(v) + "</t></is></c>"; }).join("") + "</row>"; }).join("");
        var cols = wid.length ? "<cols>" + wid.map(function (w, i) { return '<col min="' + (i + 1) + '" max="' + (i + 1) + '" width="' + (w || 8) + '" customWidth="1"/>'; }).join("") + "</cols>" : "";
        z.file("xl/worksheets/sheet" + (k + 1) + ".xml", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">' + cols + "<sheetData>" + sd + "</sheetData></worksheet>");
        sheets.push(k + 1); busy("Menyusun Excel… " + (k + 1) + "/" + L.length, 5 + 85 * (k + 1) / L.length);
      }
      z.file("[Content_Types].xml", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/><Default Extension="xml" ContentType="application/xml"/><Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/><Override PartName="/xl/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/>' + sheets.map(function (n) { return '<Override PartName="/xl/worksheets/sheet' + n + '.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>'; }).join("") + "</Types>");
      z.file("_rels/.rels", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/></Relationships>');
      z.file("xl/workbook.xml", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"><sheets>' + sheets.map(function (n) { return '<sheet name="Hal ' + n + '" sheetId="' + n + '" r:id="rId' + n + '"/>'; }).join("") + "</sheets></workbook>");
      z.file("xl/_rels/workbook.xml.rels", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">' + sheets.map(function (n) { return '<Relationship Id="rId' + n + '" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet' + n + '.xml"/>'; }).join("") + '<Relationship Id="rIdS" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/></Relationships>');
      z.file("xl/styles.xml", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><styleSheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"><fonts count="1"><font><sz val="11"/><name val="Calibri"/></font></fonts><fills count="2"><fill><patternFill patternType="none"/></fill><fill><patternFill patternType="gray125"/></fill></fills><borders count="1"><border><left/><right/><top/><bottom/><diagonal/></border></borders><cellStyleXfs count="1"><xf numFmtId="0" fontId="0" fillId="0" borderId="0"/></cellStyleXfs><cellXfs count="1"><xf numFmtId="0" fontId="0" fillId="0" borderId="0" xfId="0"/></cellXfs></styleSheet>');
      var outx = await z.generateAsync({ type: "uint8array", compression: "DEFLATE" });
      if (ret) { busy(null); return { bytes: outx, empty: empty }; }
      saveBlob(outx, safeName(PE.base) + ".xlsx", "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet");
      busy(null); toast("File Excel diunduh — 1 sheet per halaman" + (empty ? " · " + empty + " halaman tanpa teks (jalankan OCR untuk scan)" : ""), empty ? "info" : "success", 6000);
    } catch (e) { busy(null); if (ret) throw e; toast("Gagal: " + e.message, "error"); }
  }

  // ---------- bandingkan 2 versi ----------
  function myers(a, b) {
    var n = a.length, m = b.length, max = n + m, v = { 1: 0 }, tr = [];
    for (var d = 0; d <= max; d++) {
      tr.push(Object.assign({}, v));
      for (var k = -d; k <= d; k += 2) {
        var x = (k === -d || (k !== d && v[k - 1] < v[k + 1])) ? v[k + 1] : v[k - 1] + 1, y = x - k;
        while (x < n && y < m && a[x] === b[y]) { x++; y++; }
        v[k] = x;
        if (x >= n && y >= m) {
          var ops = [], cx = n, cy = m;
          for (var dd = d; dd > 0; dd--) { var V = tr[dd], kk = cx - cy, pk = (kk === -dd || (kk !== dd && V[kk - 1] < V[kk + 1])) ? kk + 1 : kk - 1, px = V[pk], py = px - pk; while (cx > px && cy > py) { ops.push(["=", cx - 1, cy - 1]); cx--; cy--; } if (cx === px) ops.push(["+", -1, cy - 1]); else ops.push(["-", cx - 1, -1]); cx = px; cy = py; }
          while (cx > 0 && cy > 0) { ops.push(["=", cx - 1, cy - 1]); cx--; cy--; }
          return ops.reverse();
        }
      }
      if (d > 2500) return null;
    }
    return null;
  }
  async function cmpLoad(bytes) {
    var Lj = await loadPdfJs(), doc = await Lj.getDocument({ data: bytes.slice(0) }).promise, pages = [];
    for (var i = 1; i <= doc.numPages; i++) {
      var pg = await doc.getPage(i), vp = pg.getViewport({ scale: 1 }), tc = await pg.getTextContent(), ws = [];
      tc.items.forEach(function (it) { if (!it.str || !it.str.trim()) return; var tx = Lj.Util.transform(vp.transform, it.transform), sz = Math.hypot(tx[2], tx[3]), len = it.str.length || 1, re = /\S+/g, mm, rot = Math.abs(tx[1]) > sz * 0.05 || Math.abs(tx[2]) > sz * 0.05; if (sz < 2) return; while ((mm = re.exec(it.str))) ws.push({ s: mm[0], x: tx[4] + it.width * mm.index / len, w: Math.max(2, it.width * mm[0].length / len), y: tx[5] - sz * 0.85, h: sz * 1.1, rot: rot }); });
      ws.sort(function (a, b) { return Math.abs(a.y - b.y) > a.h * 0.4 ? a.y - b.y : a.x - b.x; });
      pages.push({ pg: pg, vp: vp, ws: ws });
    }
    return { doc: doc, pages: pages };
  }
  function compareOpen() {
    var A = null, B = null, R = null, cur = 0, vis = false;
    var m = modal('<i class="fa-solid fa-code-compare" style="color:#7c3aed"></i> Bandingkan 2 versi PDF',
      '<div class="pe-cmp-in"><div class="pe-cmp-slot" data-s="A"><b>Versi lama (A)</b><span class="nm">' + (PE.pages.length ? "Dokumen yang sedang dibuka · " + PE.pages.length + " hal" : "Belum dipilih") + '</span><label class="pe-b"><input type="file" accept="application/pdf,.pdf" class="hidden" data-f="A"><i class="fa-solid fa-folder-open"></i>Pilih PDF</label></div>'
      + '<i class="fa-solid fa-arrow-right-arrow-left pe-cmp-ar"></i><div class="pe-cmp-slot" data-s="B"><b>Versi baru (B)</b><span class="nm">Belum dipilih</span><label class="pe-b pri"><input type="file" accept="application/pdf,.pdf" class="hidden" data-f="B"><i class="fa-solid fa-folder-open"></i>Pilih PDF</label></div></div>'
      + '<div id="pe-cmp-r"></div>',
      '<button class="pe-b" data-c>Tutup</button><button class="pe-b pri" data-go><i class="fa-solid fa-code-compare"></i>Bandingkan</button>', 1180);
    m.classList.add("pe-cmp");
    var src = { A: PE.pages.length ? "cur" : null, B: null }, files = {};
    m.querySelector("[data-c]").onclick = function () { m.remove(); };
    m.querySelectorAll("[data-f]").forEach(function (inp) { inp.onchange = async function () { var f = inp.files[0]; inp.value = ""; if (!f) return; files[inp.dataset.f] = await readBuf(f); src[inp.dataset.f] = "file"; m.querySelector('[data-s="' + inp.dataset.f + '"] .nm').textContent = f.name + " · " + MB(f.size); }; });
    m.querySelector("[data-go]").onclick = async function () {
      if (!src.A || !src.B) return toast("Pilih kedua versi PDF dulu", "error");
      busy("Membaca kedua versi…", 10, "read");
      try {
        var ab = src.A === "cur" ? await buildPdf(PE.pages, PE.base, null, { raw: 1 }) : files.A;
        A = await cmpLoad(ab); busy("Membaca versi baru…", 40, "read"); B = await cmpLoad(files.B);
        busy("Membandingkan…", 70, "read");
        R = []; var n = Math.max(A.pages.length, B.pages.length), tot = 0;
        for (var i = 0; i < n; i++) {
          var pa = A.pages[i], pb = B.pages[i], r = { i: i, del: [], ins: [], ch: [] };
          if (!pa || !pb) { r.only = pa ? "A" : "B"; R.push(r); tot++; continue; }
          var ops = myers(pa.ws.map(function (w) { return w.s; }), pb.ws.map(function (w) { return w.s; }));
          if (!ops) { r.del = pa.ws.map(function (_, j) { return j; }); r.ins = pb.ws.map(function (_, j) { return j; }); r.ch.push({ a: "(seluruh halaman berubah)", b: "" }); }
          else { var run = null; ops.forEach(function (o) { if (o[0] === "=") { run = null; return; } if (!run) { run = { a: [], b: [] }; r.ch.push(run); } if (o[0] === "-") { r.del.push(o[1]); run.a.push(pa.ws[o[1]].s); } else { r.ins.push(o[2]); run.b.push(pb.ws[o[2]].s); } }); r.ch = r.ch.map(function (c) { return c.a.join ? { a: c.a.join(" "), b: c.b.join(" ") } : c; }); }
          tot += r.ch.length; R.push(r);
          if (i % 5 === 4) await tick();
        }
        busy(null); cur = Math.max(0, R.findIndex(function (r) { return r.ch.length || r.only; })); draw(tot);
      } catch (e) { busy(null); toast("Gagal: " + e.message, "error"); }
    };
    function draw(tot) {
      var box = m.querySelector("#pe-cmp-r"), np = R.filter(function (r) { return r.ch.length || r.only; }).length;
      box.innerHTML = '<div class="pe-cmp-sum">' + (tot ? '<b>' + tot + "</b> perubahan di <b>" + np + "</b> halaman" : '<b style="color:#059669"><i class="fa-solid fa-circle-check"></i> Teks kedua versi sama persis</b>') + (A.pages.length !== B.pages.length ? ' · <span style="color:#d97706">jumlah halaman beda: ' + A.pages.length + " vs " + B.pages.length + "</span>" : "") + '<label class="pe-tog sm"><input type="checkbox" id="pe-cmp-vis" ' + (vis ? "checked" : "") + '><span class="sw"></span><span><b>Sorot beda visual</b><small>gambar, stempel, tata letak</small></span></label></div>'
        + '<div class="pe-cmp-main"><div class="pe-cmp-pages">' + R.map(function (r) { return '<button data-pi="' + r.i + '" class="' + (r.i === cur ? "on" : "") + '">Hal ' + (r.i + 1) + (r.only ? '<em>' + (r.only === "A" ? "dihapus" : "baru") + "</em>" : r.ch.length ? "<em>" + r.ch.length + "</em>" : '<i class="fa-solid fa-check"></i>') + "</button>"; }).join("") + "</div>"
        + '<div class="pe-cmp-view"><div class="pe-cmp-col"><small>A · versi lama</small><canvas id="pe-cmp-a"></canvas></div><div class="pe-cmp-col"><small>B · versi baru</small><canvas id="pe-cmp-b"></canvas></div></div>'
        + '<div class="pe-cmp-list" id="pe-cmp-l"></div></div>';
      box.querySelectorAll("[data-pi]").forEach(function (b) { b.onclick = function () { cur = +b.dataset.pi; box.querySelectorAll("[data-pi]").forEach(function (x) { x.classList.toggle("on", x === b); }); page(); }; });
      box.querySelector("#pe-cmp-vis").onchange = function () { vis = this.checked; page(); };
      page();
    }
    async function rend(P, cv, w) { var vp = P.pg.getViewport({ scale: w / P.vp.width }), dpr = Math.min(2, devicePixelRatio || 1); cv.width = Math.round(vp.width * dpr); cv.height = Math.round(vp.height * dpr); cv.style.width = vp.width + "px"; var g = cv.getContext("2d"); g.fillStyle = "#fff"; g.fillRect(0, 0, cv.width, cv.height); await P.pg.render({ canvasContext: g, viewport: P.pg.getViewport({ scale: w / P.vp.width * dpr }) }).promise; return w / P.vp.width * dpr; }
    async function page() {
      var r = R[cur], ca = m.querySelector("#pe-cmp-a"), cb = m.querySelector("#pe-cmp-b"), w = Math.min(470, (m.querySelector(".pe-cmp-view").clientWidth - 30) / 2), pa = A.pages[cur], pb = B.pages[cur];
      var hl = function (cv, P, idx, col, s) { var g = cv.getContext("2d"); g.save(); g.fillStyle = col; idx.forEach(function (j) { var t = P.ws[j]; if (t.rot) return; g.fillRect(t.x * s - 1, t.y * s - 1, t.w * s + 2, t.h * s + 2); }); g.restore(); };
      if (pa) { var sa = await rend(pa, ca, w); hl(ca, pa, r.del, "rgba(225,29,72,.32)", sa); } else { ca.width = ca.height = 1; }
      if (pb) { var sb = await rend(pb, cb, w); hl(cb, pb, r.ins, "rgba(22,163,74,.32)", sb); } else { cb.width = cb.height = 1; }
      if (vis && pa && pb) {   // beda piksel → magenta
        var ga = ca.getContext("2d"), gb = cb.getContext("2d"), W = Math.min(ca.width, cb.width), H = Math.min(ca.height, cb.height), da = ga.getImageData(0, 0, W, H).data, db = gb.getImageData(0, 0, W, H), d2 = db.data, cnt = 0;
        for (var q = 0; q < d2.length; q += 4) { var la = 0.3 * da[q] + 0.59 * da[q + 1] + 0.11 * da[q + 2], lb = 0.3 * d2[q] + 0.59 * d2[q + 1] + 0.11 * d2[q + 2]; if (Math.abs(la - lb) > 70) { d2[q] = 236; d2[q + 1] = 72; d2[q + 2] = 153; cnt++; } }
        gb.putImageData(db, 0, 0); if (!cnt) toast("Tidak ada beda visual di halaman ini", "info");
      }
      var L = m.querySelector("#pe-cmp-l");
      L.innerHTML = r.only ? '<div class="it"><b>Halaman ' + (cur + 1) + (r.only === "A" ? " dihapus di versi baru" : " ditambahkan di versi baru") + "</b></div>" : r.ch.length ? r.ch.map(function (c) { return '<div class="it">' + (c.a ? '<del>' + E(c.a) + "</del>" : "") + (c.a && c.b ? '<i class="fa-solid fa-arrow-right"></i>' : "") + (c.b ? "<ins>" + E(c.b) + "</ins>" : "") + "</div>"; }).join("") : '<div class="it mute"><i class="fa-solid fa-check"></i> Teks halaman ini sama</div>';
    }
  }

  // ===================== Konversi File: PDF ⇄ Word / Excel / Gambar / Teks =====================
  var JSD = "https://cdn.jsdelivr.net/npm/";
  var CV = [
    { k: "pdf2docx", g: "from", t: "PDF → Word", s: "teks bisa diedit, atau tata letak persis", a: "pdf", b: "docx", acc: ".pdf,application/pdf" },
    { k: "pdf2xlsx", g: "from", t: "PDF → Excel", s: "tabel & angka jadi sel siap hitung", a: "pdf", b: "xlsx", acc: ".pdf,application/pdf" },
    { k: "pdf2img", g: "from", t: "PDF → JPG / PNG", s: "tiap halaman jadi gambar, 100–300 dpi", a: "pdf", b: "jpg", acc: ".pdf,application/pdf" },
    { k: "pdf2txt", g: "from", t: "PDF → Teks", s: "ambil semua teks (.txt)", a: "pdf", b: "txt", acc: ".pdf,application/pdf" },
    { k: "pdfocr", g: "from", t: "Scan → PDF bisa dicari", s: "OCR: teks scan bisa dicari & disalin", a: "scan", b: "pdf", acc: ".pdf,application/pdf,image/*", tag: "OCR" },
    { k: "pdfcomp", g: "from", t: "Perkecil PDF", s: "kompres tanpa kehilangan teks", a: "pdf", b: "zip", acc: ".pdf,application/pdf" },
    { k: "pdflock", g: "from", t: "Kunci PDF", s: "password AES-256 + izin cetak/salin", a: "pdf", b: "lock", acc: ".pdf,application/pdf" },
    { k: "pdfunlock", g: "from", t: "Buka kunci PDF", s: "lepas password (butuh password-nya)", a: "lock", b: "pdf", acc: ".pdf,application/pdf" },
    { k: "img2pdf", g: "to", t: "Gambar → PDF", s: "JPG, PNG, WebP, GIF, BMP — 1 file atau per gambar", a: "jpg", b: "pdf", acc: "image/*,.jpg,.jpeg,.png,.webp,.gif,.bmp" },
    { k: "docx2pdf", g: "to", t: "Word → PDF", s: ".docx dengan judul, tabel & gambar", a: "docx", b: "pdf", acc: ".docx,application/vnd.openxmlformats-officedocument.wordprocessingml.document" },
    { k: "xlsx2pdf", g: "to", t: "Excel → PDF", s: ".xlsx / .xls / .csv jadi tabel rapi", a: "xlsx", b: "pdf", acc: ".xlsx,.xls,.csv,text/csv" },
    { k: "txt2pdf", g: "to", t: "Teks → PDF", s: ".txt jadi dokumen A4", a: "txt", b: "pdf", acc: ".txt,text/plain" }
  ];
  var FT = { pdf: ["PDF", "#e11d48", "fa-file-pdf"], docx: ["DOCX", "#2563eb", "fa-file-word"], xlsx: ["XLSX", "#16a34a", "fa-file-excel"], jpg: ["JPG", "#d97706", "fa-file-image"], txt: ["TXT", "#475569", "fa-file-lines"], scan: ["SCAN", "#0891b2", "fa-glasses"], zip: ["KECIL", "#7c3aed", "fa-compress"], lock: ["KUNCI", "#b45309", "fa-lock"] };
  var isConv = function () { return PE.mode === "conv"; };
  PE.conv = PE.conv || [];
  function cvIcon(x) { var f = FT[x]; return '<span class="cv-f" style="--c:' + f[1] + '"><i class="fa-solid ' + f[2] + '"></i><b>' + f[0] + "</b></span>"; }
  function renderConv(grid) {
    var cur = PE.pages.length;
    grid.innerHTML = '<div class="pe-cv"><div class="pe-cv-hero"><div><span class="cv-kicker"><i class="fa-solid fa-bolt"></i>Diproses di perangkat ini · file tidak diunggah</span><h2>Konversi file</h2><p>PDF ⇄ Word, Excel, gambar, dan teks. Tarik file apa saja ke kotak unggah — jenisnya dikenali otomatis.</p>'
      + (cur ? '<div class="cv-cur"><i class="fa-solid fa-file-pdf"></i><span><b>' + E(PE.base) + "</b><small>" + cur + ' halaman sedang terbuka · semua editan ikut dikonversi</small></span></div>' : "") + "</div>"
      + '<label class="cv-drop" id="cv-drop"><input type="file" multiple class="hidden" id="cv-any"><i class="fa-solid fa-cloud-arrow-up"></i><b>Tarik &amp; lepas file</b><small>PDF · Word · Excel · CSV · JPG · PNG · TXT</small><span class="st-b pri"><i class="fa-solid fa-folder-open"></i>Pilih file</span></label></div>'
      + ["from", "to"].map(function (g) { return '<section><h4>' + (g === "from" ? '<i class="fa-solid fa-file-export"></i>Dari PDF' : '<i class="fa-solid fa-file-import"></i>Jadi PDF') + "</h4><div class=\"pe-cv-g\">" + CV.filter(function (c) { return c.g === g; }).map(function (c, i) { return '<button class="cv-tile" data-cv="' + c.k + '" style="--d:' + i * 35 + 'ms">' + (c.tag ? '<em class="cv-tag">' + c.tag + "</em>" : "") + '<span class="cv-pair">' + cvIcon(c.a) + '<i class="fa-solid fa-arrow-right-long cv-ar"></i>' + cvIcon(c.b) + "</span><b>" + c.t + "</b><small>" + c.s + "</small></button>"; }).join("") + "</div></section>"; }).join("") + "</div>";
    grid.querySelectorAll("[data-cv]").forEach(function (b) { b.onclick = function () { cvStart(b.dataset.cv); }; });
    var any = $("cv-any"), dz = $("cv-drop");
    any.onchange = function () { var f = Array.from(any.files || []); any.value = ""; if (f.length) cvAuto(f); };
    dz.ondragover = function (e) { e.preventDefault(); e.stopPropagation(); dz.classList.add("over"); }; dz.ondragleave = function () { dz.classList.remove("over"); };
    dz.ondrop = function (e) { e.preventDefault(); e.stopPropagation(); dz.classList.remove("over"); hideDz(); var f = Array.from(e.dataTransfer.files || []); if (f.length) cvAuto(f); };
  }
  function renderConvOut(box) {
    var L = PE.conv;
    box.innerHTML = '<div class="pe-files-h"><div style="display:flex;align-items:center;gap:6px"><b style="font-size:13px;font-weight:800;flex:1">Hasil konversi (' + L.length + ")</b>" + (L.length > 1 ? '<button class="pe-b" id="cv-zip" style="height:28px"><i class="fa-solid fa-file-zipper"></i>ZIP</button>' : "") + (L.length ? '<button class="pe-b" id="cv-clr" style="height:28px" title="Kosongkan daftar"><i class="fa-regular fa-trash-can"></i></button>' : "") + "</div></div>"
      + '<div class="pe-files-l">' + (L.length ? L.map(function (r, i) { var f = FT[r.ext === "png" ? "jpg" : r.ext === "zip" ? "zip" : r.ext] || FT.pdf; return '<div class="cv-out' + (i === 0 && r.fresh ? " fresh" : "") + '" style="--c:' + f[1] + '"><span class="ic"><i class="fa-solid ' + f[2] + '"></i></span><span class="tx"><b title="' + E(r.name) + '">' + E(r.name) + "</b><small>" + MB(r.bytes.length) + " · " + E(r.note || "") + '</small></span><span class="ac"><button class="pe-b" data-dl="' + i + '" style="height:28px"><i class="fa-solid fa-download"></i>Unduh</button>' + (r.ext === "pdf" ? '<button class="pe-b" data-ed="' + i + '" style="height:28px" title="Buka di Edit PDF"><i class="fa-solid fa-pen-to-square"></i></button>' : "") + "</span></div>"; }).join("") : '<div class="cv-empty"><i class="fa-solid fa-wand-magic-sparkles"></i><b>Belum ada hasil</b><small>Pilih jenis konversi di kiri. Hasil muncul di sini dan langsung terunduh.</small></div>') + "</div>";
    L.forEach(function (r) { r.fresh = false; });
    box.querySelectorAll("[data-dl]").forEach(function (b) { b.onclick = function () { var r = L[+b.dataset.dl]; saveBlob(r.bytes, r.name, r.mime); }; });
    box.querySelectorAll("[data-ed]").forEach(function (b) { b.onclick = async function () { var r = L[+b.dataset.ed]; busy("Membuka di editor…", 30, "read"); try { var pg = await addBytes(r.bytes, r.name); pushUndo(); PE.pages = PE.pages.concat(pg); if (PE.pages.length === pg.length) PE.base = safeName(r.name); busy(null); await switchMode("edit"); toast("\"" + r.name + "\" dibuka di Edit PDF", "success"); } catch (e) { busy(null); toast(e.message, "error"); } }; });
    var z = $("cv-zip"); if (z) z.onclick = async function () { busy("Membuat ZIP…", 50); await loadJs("https://cdnjs.cloudflare.com/ajax/libs/jszip/3.10.1/jszip.min.js"); var zz = new window.JSZip(), seen = {}; L.forEach(function (r) { var n = r.name, k = 1; while (seen[n]) n = r.name.replace(/(\.\w+)$/, " (" + (++k) + ")$1"); seen[n] = 1; zz.file(n, r.bytes); }); saveBlob(await zz.generateAsync({ type: "uint8array" }), "Hasil konversi (" + L.length + " file).zip", "application/zip"); busy(null); };
    var c = $("cv-clr"); if (c) c.onclick = function () { PE.conv = []; render(); };
  }
  function cvPush(name, bytes, mime, note) { var ext = (name.match(/\.(\w+)$/) || [, "pdf"])[1].toLowerCase(); PE.conv.unshift({ name: name, bytes: bytes, mime: mime, ext: ext, note: note, fresh: true, at: Date.now() }); PE.conv = PE.conv.slice(0, 40); saveBlob(bytes, name, mime); }
  // jenis file dikenali otomatis
  function cvAuto(files) {
    var ext = function (f) { return (f.name.match(/\.(\w+)$/) || [, ""])[1].toLowerCase(); }, all = function (re) { return files.every(function (f) { return re.test(ext(f)) || re.test(f.type); }); };
    if (all(/^(jpe?g|png|webp|gif|bmp)$|^image\//)) return cvRun("img2pdf", files);
    if (all(/^docx$/)) return cvRun("docx2pdf", files);
    if (all(/^(xlsx|xls|csv)$/)) return cvRun("xlsx2pdf", files);
    if (all(/^txt$|^text\/plain/)) return cvRun("txt2pdf", files);
    if (all(/^pdf$|pdf$/)) {
      var m = modal('<i class="fa-solid fa-right-left" style="color:#7c3aed"></i> Mau dikonversi ke apa?', '<p class="pe-mp">' + files.length + ' file PDF dipilih.</p><div class="pe-cv-g mini">' + CV.filter(function (c) { return c.g === "from"; }).map(function (c) { return '<button class="cv-tile" data-q="' + c.k + '"><span class="cv-pair">' + cvIcon(c.a) + '<i class="fa-solid fa-arrow-right-long cv-ar"></i>' + cvIcon(c.b) + "</span><b>" + c.t + "</b></button>"; }).join("") + "</div>", '<button class="pe-b" data-c>Batal</button>', 760);
      m.querySelector("[data-c]").onclick = function () { m.remove(); };
      m.querySelectorAll("[data-q]").forEach(function (b) { b.onclick = function () { m.remove(); cvRun(b.dataset.q, files); }; });
      return;
    }
    if (files.some(function (f) { return /^(doc|ppt|pptx|odt|rtf|pages|heic)$/.test(ext(f)); })) return toast("Format " + files.map(ext).filter(function (x, i, a) { return a.indexOf(x) === i; }).join(", ") + " belum didukung — simpan dulu sebagai .docx / .pdf / .jpg", "error", 7000);
    toast("Campuran jenis file — pilih jenis konversinya dari daftar", "info");
  }
  function cvStart(k) {
    var c = CV.filter(function (x) { return x.k === k; })[0], usesPdf = c.g === "from" && k !== "pdfunlock";
    if (usesPdf && PE.pages.length) {
      var m = modal('<i class="fa-solid fa-right-left" style="color:#7c3aed"></i> ' + c.t, '<p class="pe-mp">Konversi dokumen yang sedang terbuka, atau pilih file lain?</p>' + radioRow("cv-src", [["cur", "Dokumen yang sedang terbuka", E(PE.base) + " · " + PE.pages.length + " halaman · termasuk editan"], ["file", "Pilih file PDF lain", "bisa beberapa file sekaligus"]], "cur"), '<button class="pe-b" data-c>Batal</button><button class="pe-b pri" data-ok><i class="fa-solid fa-arrow-right"></i>Lanjut</button>', 520);
      m.querySelector("[data-c]").onclick = function () { m.remove(); };
      m.querySelector("[data-ok]").onclick = function () { var v = rv(m, "cv-src"); m.remove(); if (v === "cur") cvRun(k, null); else cvPick(c); };
      return;
    }
    cvPick(c);
  }
  function cvPick(c) { var i = document.createElement("input"); i.type = "file"; i.multiple = c.k !== "pdfunlock"; i.accept = c.acc; i.onchange = function () { var f = Array.from(i.files || []); if (f.length) cvRun(c.k, f); }; i.click(); }
  // pilihan per jenis konversi
  function cvOpts(k) {
    return new Promise(function (ok) {
      var body = "";
      if (k === "pdf2docx") body = radioRow("o-m", [["text", "Teks bisa diedit", "paragraf, ukuran & tebal huruf dipertahankan"], ["img", "Tata letak persis", "tiap halaman jadi gambar di Word"]], "text");
      else if (k === "pdf2img") body = '<div class="pe-pn-f"><div class="g2"><div><label>Format</label><select id="o-f"><option value="jpg">JPG</option><option value="png">PNG</option></select></div><div><label>Resolusi</label><select id="o-d"><option value="100">100 dpi</option><option value="150" selected>150 dpi</option><option value="200">200 dpi</option><option value="300">300 dpi</option></select></div></div></div>';
      else if (k === "pdfcomp") body = radioRow("o-c", [["1", "Seimbang", "150 dpi — tetap jelas"], ["2", "Maksimal", "110 dpi — paling kecil"]], "1");
      else if (k === "img2pdf") body = radioRow("o-j", [["one", "Gabung jadi 1 PDF", "urut sesuai nama file"], ["each", "1 PDF per gambar", ""]], "one") + '<div class="pe-pn-f" style="margin-top:8px"><label>Ukuran halaman</label><select id="o-s"><option value="fit">Ikuti ukuran gambar</option><option value="A4">A4 (gambar dipaskan)</option><option value="F4">F4 / Folio</option></select></div>';
      else if (k === "pdflock") body = '<div class="pe-pn-f"><label>Password</label><input type="password" id="o-p" autocomplete="new-password" placeholder="min. 4 karakter"><label>Ulangi</label><input type="password" id="o-p2" autocomplete="new-password"><label class="chk"><input type="checkbox" id="o-pr" checked> Boleh dicetak</label><label class="chk"><input type="checkbox" id="o-cp"> Boleh menyalin teks</label></div>';
      if (!body) return ok({});
      var c = CV.filter(function (x) { return x.k === k; })[0];
      var m = modal('<i class="fa-solid fa-sliders" style="color:#7c3aed"></i> ' + c.t, body, '<button class="pe-b" data-c>Batal</button><button class="pe-b pri" data-ok><i class="fa-solid fa-bolt"></i>Konversi</button>', 500);
      m.querySelectorAll("input").forEach(function (x) { x.addEventListener("keydown", function (e) { e.stopPropagation(); }); });
      m.querySelector("[data-c]").onclick = function () { m.remove(); ok(null); }; m.querySelector("[data-x]").onclick = function () { m.remove(); ok(null); };
      m.querySelector("[data-ok]").onclick = function () {
        var o = {};
        if (k === "pdf2docx") o.mode = rv(m, "o-m");
        if (k === "pdf2img") { o.fmt = m.querySelector("#o-f").value; o.dpi = +m.querySelector("#o-d").value; }
        if (k === "pdfcomp") o.lvl = +rv(m, "o-c");
        if (k === "img2pdf") { o.join = rv(m, "o-j"); o.size = m.querySelector("#o-s").value; }
        if (k === "pdflock") { var a = m.querySelector("#o-p").value, b = m.querySelector("#o-p2").value; if (a.length < 4) return toast("Password minimal 4 karakter", "error"); if (a !== b) return toast("Ulangi password tidak sama", "error"); o.pw = { user: a, print: m.querySelector("#o-pr").checked, copy: m.querySelector("#o-cp").checked, edit: false }; }
        m.remove(); ok(o);
      };
    });
  }
  var stem = function (n) { return safeName(String(n || "Dokumen").replace(/\.\w+$/, "")) || "Dokumen"; };
  async function cvRun(k, files) {
    var o = await cvOpts(k); if (!o) return;
    var jobs = files ? files : [null], t0 = Date.now(), made = 0;
    var c = CV.filter(function (x) { return x.k === k; })[0];
    busy(c.t + "…", 3, "read");
    try {
      if (k === "img2pdf") { await cvImages(files, o); made = 1; }
      else for (var i = 0; i < jobs.length; i++) {
        var f = jobs[i], nm = f ? stem(f.name) : stem(PE.base), tag = (jobs.length > 1 ? " (" + (i + 1) + "/" + jobs.length + ")" : "");
        busy(c.t + tag + "…", 5 + 85 * i / jobs.length, "read");
        if (c.g === "to") {
          var buf = await readBuf(f), pdf = k === "docx2pdf" ? await docxToPdf(buf, nm) : k === "xlsx2pdf" ? await sheetToPdf(buf, nm, f.name) : await txtToPdf(buf, nm);
          cvPush(nm + ".pdf", pdf, "application/pdf", c.t); made++; continue;
        }
        var pages;
        if (!f) pages = PE.pages.slice();
        else {
          var bytes = await readBuf(f);
          if (/^image\//.test(f.type) || /\.(jpe?g|png|webp|gif|bmp)$/i.test(f.name)) bytes = await imageToPdf(f);
          else if (k === "pdfunlock") { var ub = await unlockBytes(bytes, f.name); if (!ub) continue; cvPush(nm + " (tanpa password).pdf", ub, "application/pdf", "kunci dilepas"); made++; continue; }
          else { bytes = await prepBytes(bytes, f.name); if (!bytes) continue; }
          pages = await addBytes(bytes, f.name);
        }
        busy(c.t + tag + "…", 10 + 85 * (i + 0.4) / jobs.length, "read");
        if (k === "pdf2docx") { var r = await exportDocx(o.mode, pages, true); cvPush(nm + ".docx", r.bytes, "application/vnd.openxmlformats-officedocument.wordprocessingml.document", o.mode === "img" ? "tata letak persis" : "teks bisa diedit" + (r.empty ? " · " + r.empty + " hal tanpa teks" : "")); }
        else if (k === "pdf2xlsx") { var x = await exportXlsx(pages, true); cvPush(nm + ".xlsx", x.bytes, "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", pages.length + " sheet"); }
        else if (k === "pdf2txt") { var txt = []; for (var q = 0; q < pages.length; q++) { var ls = await exportLines(pages[q]); txt.push("=== Halaman " + (q + 1) + " ===\n" + (ls.length ? ls.map(function (l) { return l.str; }).join("\n") : "[tidak ada teks — halaman scan perlu OCR]")); } cvPush(nm + ".txt", new TextEncoder().encode(txt.join("\n\n")), "text/plain;charset=utf-8", pages.length + " halaman"); }
        else if (k === "pdf2img") {
          var imgs = []; for (var j = 0; j < pages.length; j++) { busy(c.t + tag + " · hal " + (j + 1) + "/" + pages.length, 10 + 85 * (i + j / pages.length) / jobs.length); var cv = await pageCanvas(pages[j], o.dpi), b = o.fmt === "png" ? await canvasPng(cv) : await canvasJpg(cv, 0.9); cv.width = cv.height = 0; imgs.push({ n: nm + " - hal " + (j + 1) + "." + o.fmt, b: b }); }
          if (imgs.length === 1) cvPush(imgs[0].n, imgs[0].b, o.fmt === "png" ? "image/png" : "image/jpeg", o.dpi + " dpi");
          else { await loadJs("https://cdnjs.cloudflare.com/ajax/libs/jszip/3.10.1/jszip.min.js"); var z = new window.JSZip(); imgs.forEach(function (m2) { z.file(m2.n, m2.b); }); cvPush(nm + " (" + imgs.length + " gambar).zip", await z.generateAsync({ type: "uint8array" }), "application/zip", imgs.length + " " + o.fmt.toUpperCase() + " · " + o.dpi + " dpi"); }
        }
        else if (k === "pdfocr") { var need = []; for (var w = 0; w < pages.length; w++) { var nl = []; try { nl = await nativeLines(pages[w]); } catch (e) { } if (!nl.length && !OCR[pkey(pages[w])]) need.push(pages[w]); } busy(null); if (need.length) await runOcr(need); busy(c.t + tag + " · menyusun…", 92); cvPush(nm + " (bisa dicari).pdf", await buildPdf(pages, nm, null, { raw: 1 }), "application/pdf", need.length ? need.length + " hal di-OCR" : "sudah punya teks"); }
        else if (k === "pdfcomp") { var a0 = await buildPdf(pages, nm, null, { raw: 1 }), a1 = await buildPdf(pages, nm, null, { comp: o.lvl }); var best = a1.length < a0.length ? a1 : a0; cvPush(nm + " (kecil).pdf", best, "application/pdf", MB(f ? f.size : a0.length) + " → " + MB(best.length)); }
        else if (k === "pdflock") { cvPush(nm + " (terkunci).pdf", await finalPdf(await buildPdf(pages, nm, null, { raw: 1 }), o.pw), "application/pdf", "AES-256"); }
        made++;
      }
    } catch (e) { busy(null); render(); return toast("Gagal: " + e.message, "error", 8000); }
    busy(null); render();
    if (made) toast(c.t + " selesai: " + made + " file dalam " + Math.max(1, Math.round((Date.now() - t0) / 1000)) + " detik — tersimpan di Hasil konversi", "success", 5000);
  }
  async function cvImages(files, o) {
    var L = await loadPdfLib(), col = new Intl.Collator("id", { numeric: true }), F = files.slice().sort(function (a, b) { return col.compare(a.name, b.name); });
    var mk = async function (list) {
      var out = await L.PDFDocument.create();
      for (var i = 0; i < list.length; i++) {
        busy("Gambar → PDF… " + (i + 1) + "/" + list.length, 5 + 90 * i / list.length);
        var src = await L.PDFDocument.load(await imageToPdf(list[i])), sp = src.getPage(0), W = sp.getWidth(), H = sp.getHeight();
        if (o.size === "fit") { var cp = await out.copyPages(src, [0]); out.addPage(cp[0]); }
        else { var S = SIZES[o.size], land = W > H, TW = land ? S[1] : S[0], TH = land ? S[0] : S[1], m = 20, sc = Math.min((TW - 2 * m) / W, (TH - 2 * m) / H), emb = await out.embedPage(sp), np = out.addPage([TW, TH]); np.drawPage(emb, { x: (TW - W * sc) / 2, y: (TH - H * sc) / 2, width: W * sc, height: H * sc }); }
      }
      return new Uint8Array(await out.save());
    };
    if (o.join === "one") cvPush((F.length > 1 ? stem(F[0].name) + " +" + (F.length - 1) : stem(F[0].name)) + ".pdf", await mk(F), "application/pdf", F.length + " gambar · 1 PDF");
    else for (var i = 0; i < F.length; i++) cvPush(stem(F[i].name) + ".pdf", await mk([F[i]]), "application/pdf", "dari gambar");
  }
  // Word (.docx) → HTML (mammoth) → PDF bervektor (jsPDF.html: teks tetap bisa dicari)
  async function docxToPdf(buf, nm) {
    await loadJs(JSD + "mammoth@1.8.0/mammoth.browser.min.js");
    var res = await window.mammoth.convertToHtml({ arrayBuffer: buf.buffer.slice(buf.byteOffset, buf.byteOffset + buf.byteLength) });
    await loadJs(JSD + "html2canvas@1.4.1/dist/html2canvas.min.js"); await loadJs(JSD + "jspdf@2.5.2/dist/jspdf.umd.min.js");
    var host = document.createElement("div"); host.className = "pe-docrender"; host.innerHTML = res.value || "<p></p>"; document.body.appendChild(host);
    try {
      var doc = new window.jspdf.jsPDF({ unit: "pt", format: "a4", compress: true });
      await new Promise(function (ok, no) { try { doc.html(host, { callback: function () { ok(); }, margin: [48, 48, 56, 48], autoPaging: "text", width: 499, windowWidth: 680 }); } catch (e) { no(e); } });
      var n = doc.getNumberOfPages(); for (var i = 1; i <= n; i++) { doc.setPage(i); doc.setFontSize(8); doc.setTextColor(148, 163, 184); doc.text(i + " / " + n, 595.28 / 2, 841.89 - 24, { align: "center" }); }
      return new Uint8Array(doc.output("arraybuffer"));
    } finally { host.remove(); }
  }
  // Excel / CSV → tabel PDF rapi (kolom otomatis, header berulang, lanskap bila lebar)
  async function sheetToPdf(buf, nm, fname) {
    await loadJs(JSD + "xlsx@0.18.5/dist/xlsx.full.min.js");
    var wb = /\.csv$/i.test(fname) ? window.XLSX.read(new TextDecoder().decode(buf), { type: "string" }) : window.XLSX.read(buf, { type: "array" });
    var L = await loadPdfLib(), out = await L.PDFDocument.create(), f = await out.embedFont(L.StandardFonts.Helvetica), fb = await out.embedFont(L.StandardFonts.HelveticaBold), total = 0;
    var safe = function (t) { return stdSafe(f, String(t == null ? "" : t).replace(/\s+/g, " "), true); };
    for (var si = 0; si < wb.SheetNames.length; si++) {
      var sn = wb.SheetNames[si], rows = window.XLSX.utils.sheet_to_json(wb.Sheets[sn], { header: 1, raw: false, defval: "", blankrows: false });
      rows = rows.filter(function (r) { return r.some(function (v) { return String(v).trim(); }); }); if (!rows.length) continue;
      var nc = Math.max.apply(null, rows.map(function (r) { var k = r.length; while (k && !String(r[k - 1]).trim()) k--; return k; })); if (!nc) continue;
      var fs = 9, pad = 4, wid = [];
      for (var c = 0; c < nc; c++) wid[c] = Math.min(220, Math.max(28, Math.max.apply(null, rows.slice(0, 400).map(function (r, ri) { return (ri ? f : fb).widthOfTextAtSize(safe(r[c]).slice(0, 60), fs); })) + pad * 2));
      var tw = wid.reduce(function (a, b) { return a + b; }, 0), land = tw > 595 - 60, PW = land ? 841.89 : 595.28, PH = land ? 595.28 : 841.89, avail = PW - 60, sc = Math.min(1, avail / tw);
      if (sc < 1) { wid = wid.map(function (w) { return w * sc; }); fs = Math.max(5.5, fs * Math.max(sc, 0.62)); }
      var rh = fs * 1.9, y = 0, pg = null, pn = 0, head = rows[0];
      var newPage = function () { pg = out.addPage([PW, PH]); pn++; y = PH - 36; pg.drawText(safe(nm + " · " + sn).slice(0, 110), { x: 30, y: y, size: 10, font: fb, color: L.rgb(0.06, 0.09, 0.16) }); pg.drawText("Hal " + pn, { x: PW - 60, y: 22, size: 7.5, font: f, color: L.rgb(0.58, 0.64, 0.72) }); y -= 18; };
      var drawRow = function (r, isHead, zebra) {
        var x = 30; pg.drawRectangle({ x: 30, y: y - rh + 3, width: wid.reduce(function (a, b) { return a + b; }, 0), height: rh, color: isHead ? L.rgb(0.93, 0.95, 0.98) : zebra ? L.rgb(0.985, 0.988, 0.995) : L.rgb(1, 1, 1), borderColor: L.rgb(0.86, 0.89, 0.93), borderWidth: 0.4 });
        for (var c2 = 0; c2 < nc; c2++) { var t = safe(r[c2]), ft = isHead ? fb : f, mx = wid[c2] - pad * 2; while (t && ft.widthOfTextAtSize(t, fs) > mx) t = t.slice(0, -2) + "…"; var num = !isHead && /^-?[\d.,]+%?$/.test(t); pg.drawText(t, { x: num ? x + wid[c2] - pad - ft.widthOfTextAtSize(t, fs) : x + pad, y: y - rh + 3 + (rh - fs) / 2 + 1, size: fs, font: ft, color: L.rgb(0.1, 0.12, 0.18) }); x += wid[c2]; }
        y -= rh;
      };
      newPage(); drawRow(head, true);
      for (var ri = 1; ri < rows.length; ri++) { if (y - rh < 40) { newPage(); drawRow(head, true); } drawRow(rows[ri], false, ri % 2 === 0); if (ri % 200 === 0) await tick(); }
      total++;
    }
    if (!total) throw new Error("Tidak ada data di file Excel");
    return new Uint8Array(await out.save());
  }
  async function txtToPdf(buf, nm) {
    var L = await loadPdfLib(), out = await L.PDFDocument.create(), f = await out.embedFont(L.StandardFonts.Helvetica), fs = 11, lh = 15.5, W = 595.28, H = 841.89, m = 56, pg = null, y = 0;
    var text = new TextDecoder("utf-8").decode(buf).replace(/\r\n?/g, "\n").replace(/\t/g, "    ");
    var np = function () { pg = out.addPage([W, H]); y = H - m; };
    np();
    text.split("\n").forEach(function (para) {
      var t = stdSafe(f, para, true), words = t.split(/(\s+)/), line = "";
      var flush = function () { if (y < m) np(); pg.drawText(line, { x: m, y: y, size: fs, font: f, color: L.rgb(0.1, 0.12, 0.18) }); y -= lh; line = ""; };
      if (!t.trim()) { y -= lh; if (y < m) np(); return; }
      words.forEach(function (w) { if (f.widthOfTextAtSize(line + w, fs) > W - 2 * m && line.trim()) { flush(); w = w.replace(/^\s+/, ""); } line += w; });
      if (line) flush();
    });
    return new Uint8Array(await out.save());
  }

  // ===================== buka / tutup =====================
  async function peOpen(opt) {
    opt = opt || {};
    if (!canPdf()) return toast("Akun Anda tidak memiliki akses Split & Edit PDF", "error");
    shell(); reset();
    PE.origin = { kind: opt.kind || "tab", id: opt.id || "" }; PE.lock = !!opt.lock; PE.mode = /^(edit|merge|conv)$/.test(opt.mode) ? opt.mode : "split";
    SEEN = new Set(); PE.open = true; $("pe").classList.remove("hidden"); document.documentElement.style.overflow = "hidden";
    $("pe-ttl").textContent = opt.title || MODE_T[PE.mode];
    render();
    if (opt.file) await addFiles([opt.file]);
    if (opt.files && opt.files.length) await addFiles(opt.files);
    if (opt.bytes) { busy("Membuka dokumen…", 40); try { var pages = await addBytes(opt.bytes, opt.name || "Dokumen.pdf"); PE.pages = pages; PE.base = safeName(opt.name) || "Dokumen"; } catch (e) { toast(e.message, "error"); } busy(null); render(); }
  }
  function reset() { PE.docs = []; PE.pages = []; PE.cuts = new Set(); PE.names = {}; PE.pairs = {}; PE.sel = new Set(); PE.undo = []; PE.redo = []; PE.pattern = ""; PE.base = "Dokumen"; PE.mf = false; JS = {}; LIB = {}; LIBF = {}; PE.blankDoc = null; PE.mfiles = []; PE.mopt = { marks: true, flatten: true, a4: false, blank: false, inter: false, interRev: true, outName: "" }; ED.baseKey = null; SAVED = { docs: -1, imgs: -1 }; Object.keys(IMGS).forEach(function (k) { try { URL.revokeObjectURL(IMGS[k].url); } catch (e) { } }); IMGS = {}; THUMB = {}; TXT = {}; TXTI = {}; OCR = {}; MARKS = {}; PE.form = {}; FORMF = {}; LIBX = {}; PE.comp = 0; PE.pw = null; PE.conv = []; }
  function peClose(force) {
    if (!force && PE.undo.length && PE.pages.length && !confirm("Tutup " + (isEdit() ? "Edit PDF" : "Split PDF") + "? Pekerjaan ini akan dibuang (yang sudah diunduh / dikirim tetap aman).")) return;
    if (ED.on) { edCommitText(); ED.on = false; var ed = $("pe-ed"); if (ed) ed.classList.add("hidden"); }
    closeMenus(); busy(null);
    $("pe").classList.add("hidden"); document.documentElement.style.overflow = ""; PE.open = false;
    clearDraft();
    try { JS && Object.keys(JS).forEach(function (k) { JS[k].then(function (d) { d.destroy(); }).catch(function () { }); }); } catch (e) { }
    reset();
  }
  if (/^(localhost|127\.0\.0\.1)$/.test(location.hostname)) window.__peT = { ptr: function () { return [PTR.size, !!ED.pinch, ED.tool]; }, render: render, lines: function () { return ED.lines; }, PE: PE, ED: ED, segs: segs, buildPdf: buildPdf, finalNames: finalNames, IMGS: function () { return IMGS; }, exportDocx: exportDocx, exportXlsx: exportXlsx, OCR: function () { return OCR; }, qpdf: qpdf, finalPdf: finalPdf, spStats: function () { return spStats(); }, cvRun: cvRun };
  window.peOpen = function (mode) { peOpen({ kind: "tab", mode: mode }); };
  window.__peOpenOpt = function (opt) { return peOpen(opt || {}); };
  window.peClose = peClose;

  // Rapikan PDF dari form Submit / langkah unggah Signing
  window.peRapikan = function (where) {
    var file = where === "sgw" ? (typeof SGW !== "undefined" && SGW.file) : (typeof UP !== "undefined" && UP.file);
    peOpen({ kind: where, mode: "edit", file: file || null, title: "Edit PDF" + (where === "sgw" ? " · Signing Document" : " · Submit PDF") });
  };
  // Split PDF dari Signing (khusus status Selesai)
  window.peFromSigning = async function (id) {
    var d = typeof sgDoc === "function" ? sgDoc(id) : null;
    if (!d) return toast("Dokumen tidak ditemukan", "error");
    if (d.status !== "selesai") return toast("Split PDF hanya untuk dokumen yang sudah Selesai ditandatangani", "error");
    if (!canPdf()) return toast("Akun Anda tidak memiliki akses Split & Edit PDF", "error");
    busy("Mengambil PDF final…", 20);
    try {
      var bytes = null; try { bytes = typeof SGC !== "undefined" ? await SGC.get("final_" + id) : null; } catch (e) { }
      if (!bytes) { var r = await callApi("sign.file", { id: id }, 18e4); bytes = b64ToBytes(r.pdf); try { SGC.put("final_" + id, bytes); } catch (e) { } }
      busy(null);
      await peOpen({ kind: "signing", mode: "split", id: id, lock: true, bytes: bytes, name: d.name, title: "Split PDF · Signing Document" });
      toast("Mode Split saja: isi dokumen bertanda tangan dikunci", "info", 5000);
    } catch (e) { busy(null); toast("Gagal mengambil PDF final: " + e.message, "error", 8000); }
  };

  // ===================== kaitan ke aplikasi =====================
  // tombol di PDF Tools punya animasi proses sendiri — jangan ikut ditandai "Memproses/Berhasil" oleh panggilan server latar belakang
  var appBusy = function () { try { return (0, eval)("typeof BUSY !== 'undefined' ? BUSY : null"); } catch (er) { return null; } };   // BUSY milik aplikasi (bukan overlay PDF Tools)
  document.addEventListener("click", function (e) { try { if (e.target.closest && e.target.closest("#pe, .pe-menu")) { var ab = appBusy(); if (ab && "lastBtn" in ab) ab.lastBtn = null; } } catch (er) { } }, true);
  function hook() {
    var ok = canPdf();
    var bar = $("gs-toolbar");
    if (bar && !$("docs-tab-pdf")) {   // satu tombol "PDF Tools" → Split / Gabung / Edit (toolbar tetap ringkas)
      var b = document.createElement("button"); b.id = "docs-tab-pdf"; b.title = "PDF Tools — Split, Gabung & Edit PDF";
      b.innerHTML = '<span class="gs-ic" style="--c:#7c3aed"><i class="fa-solid fa-file-pen"></i></span><span class="gs-tx"><b>PDF Tools</b><small>Konversi · Split · Gabung · Edit</small></span>';
      b.onclick = function (e) {
        e.stopPropagation();
        try { lsSet(uKey("seen_" + NEWV), Date.now()); b.classList.remove("st-isnew"); var nw = $("st-new"); if (nw) ntClose(nw); } catch (er) { }
        menu(b, [
          { ic: "fa-right-left", t: "Konversi File  ✦ BARU", s: "PDF ⇄ Word, Excel, JPG/PNG, teks, OCR", fn: function () { peOpen({ kind: "tab", mode: "conv" }); } },
          { ic: "fa-scissors", t: "Split PDF", s: "pecah satu PDF jadi banyak file bernama custom", fn: function () { peOpen({ kind: "tab", mode: "split" }); } },
          { ic: "fa-object-group", t: "Gabung PDF", s: "satukan beberapa PDF / gambar jadi satu file", fn: function () { peOpen({ kind: "tab", mode: "merge" }); } },
          { ic: "fa-pen-to-square", t: "Edit PDF", s: "edit teks, OCR scan, TTD & stempel, formulir, catatan", fn: function () { peOpen({ kind: "tab", mode: "edit" }); } },
          { ic: "fa-code-compare", t: "Bandingkan PDF", s: "cari perbedaan 2 versi dokumen", fn: function () { peOpen({ kind: "tab", mode: "edit" }).then(compareOpen); } },
          { ic: "fa-wand-magic-sparkles", t: "Apa yang baru?", s: "lihat daftar fitur terbaru", fn: function () { whatsNew(true); } }
        ]);
      };
      var up = $("docs-tab-upload"), nx = up ? up.nextSibling : null;
      bar.insertBefore(b, nx);
    }
    var tbp = $("docs-tab-pdf"); if (tbp) tbp.classList.toggle("hidden", !ok);
    var drop = $("up-drop");
    if (drop && !$("pe-up-btn")) {
      var r = document.createElement("button"); r.type = "button"; r.id = "pe-up-btn"; r.className = "btn btn-ghost w-full"; r.style.marginTop = "6px";
      r.innerHTML = '<i class="fa-solid fa-pen-to-square"></i>Edit PDF dulu (edit teks, susun, hapus area, tulis, gabung)';
      r.onclick = function () { window.peRapikan("submit"); };
      var fi = $("up-file") || drop; fi.parentNode.insertBefore(r, fi.nextSibling);
    }
    var ub = $("pe-up-btn"); if (ub) ub.classList.toggle("hidden", !ok);
    var sd = $("sgw-drop");
    if (sd && !$("pe-sgw-btn")) {
      var s = document.createElement("button"); s.type = "button"; s.id = "pe-sgw-btn"; s.className = "btn btn-ghost w-full";
      s.innerHTML = '<i class="fa-solid fa-pen-to-square"></i>Edit PDF dulu (edit teks, susun, hapus halaman, hapus area)';
      s.onclick = function () { window.peRapikan("sgw"); };
      sd.parentNode.insertBefore(s, sd.nextSibling);
    }
    var sb = $("pe-sgw-btn"); if (sb) sb.classList.toggle("hidden", !ok);
  }
  var ht = null;
  new MutationObserver(function () { clearTimeout(ht); ht = setTimeout(hook, 80); }).observe(document.body, { childList: true, subtree: true });
  hook();

  // ===================== notifikasi: fitur baru & SP bertahap (belum rilis / overdue) =====================
  var NEWV = "pdf-v18";
  var lsGet = function (k) { try { return localStorage.getItem(k); } catch (e) { return null; } }, lsSet = function (k, v) { try { localStorage.setItem(k, v); } catch (e) { } };
  var uKey = function (k) { return "starlite_" + k + "_" + (currentUser && currentUser.username || ""); };
  try { if (typeof PERMS !== "undefined" && !PERMS.some(function (p) { return p.key === "spnotif"; })) PERMS.push({ key: "spnotif", group: "Notifikasi", label: "Terima notifikasi SP (belum rilis & overdue)", icon: "fa-bell" }, { key: "spnotif_lock", group: "Notifikasi", label: "Notifikasi SP wajib — selalu tampil, tidak bisa ditunda", icon: "fa-bell-concierge" }); if (typeof DEFAULT_ROLE_PERMS !== "undefined") { DEFAULT_ROLE_PERMS.operator.spnotif = true; DEFAULT_ROLE_PERMS.operator.spnotif_lock = false; DEFAULT_ROLE_PERMS.viewer.spnotif = false; DEFAULT_ROLE_PERMS.viewer.spnotif_lock = false; } } catch (e) { }
  var NT = { newShown: false, shown: false, min: false };
  function ntHost() { var h = $("st-nt"); if (!h) { h = document.createElement("div"); h.id = "st-nt"; document.body.appendChild(h); } return h; }
  function ntClose(card, cb) { if (!card) return; card.classList.add("out"); setTimeout(function () { card.remove(); if (cb) cb(); }, 300); }
  var onMain = function () { var v = $("view-dashboard"); return !!v && !v.classList.contains("hidden") && !PE.open; };
  var bellEl = function () { return Array.from(document.querySelectorAll(".notif-bell:not(.undo-btn)")).filter(function (b) { return b.offsetParent; })[0] || null; };
  // ---------- hak menerima notifikasi (diatur di Manajemen User) ----------
  function ntPerm() {
    if (!currentUser) return { on: false, lock: false };
    var P = currentUser.perms || {}, d = (typeof DEFAULT_ROLE_PERMS !== "undefined" && DEFAULT_ROLE_PERMS[currentUser.role]) || {};
    var on = "spnotif" in P ? !!P.spnotif : currentUser.role === "owner" ? true : !!d.spnotif, lock = "spnotif_lock" in P ? !!P.spnotif_lock : !!d.spnotif_lock;
    var canSp = false; try { canSp = can("sp"); } catch (e) { }
    return { on: on && canSp, lock: on && canSp && lock };
  }
  // ---------- tahapan terstruktur ----------
  var STG = [
    { n: 0, k: "Pengingat", l: "Belum rilis", r: "tanpa tanggal", c: "#8b5cf6", sn: 240, ic: "fa-paper-plane" },
    { n: 1, k: "Teguran", l: "1–7 hari", r: "lewat tenggat", c: "#f59e0b", sn: 120, ic: "fa-hourglass-end" },
    { n: 2, k: "Peringatan", l: "8–14 hari", r: "lewat tenggat", c: "#f97316", sn: 60, ic: "fa-triangle-exclamation" },
    { n: 3, k: "Kritis", l: "15–30 hari", r: "lewat tenggat", c: "#ef4444", sn: 30, ic: "fa-fire" },
    { n: 4, k: "Eskalasi", l: "> 30 hari", r: "lewat tenggat", c: "#be123c", sn: 0, ic: "fa-hand-fist" }
  ];
  var stOf = function (od) { return od > 30 ? 4 : od > 14 ? 3 : od > 7 ? 2 : 1; };
  // konsep SP: status "Close" / "Final" = selesai → tidak dihitung. Yang dinotifikasi hanya:
  //  (a) SP belum punya Tanggal Rilis   (b) SP berstatus OVERDUE (jumlah hari diambil dari teks status, mis. "OVERDUE SP1 13 hari")
  var spDone = function (s) { return !!s.closed || /\b(clos(e|ed|ing)?|final)\b/i.test(String(s.overdue_raw || "") + " " + String(s.remark || "")); };
  var spIsOverdue = function (s) { return /overdue/i.test(String(s.overdue_raw || "")); };
  var spOdDays = function (s) { var m = String(s.overdue_raw || "").match(/(\d+)\s*hari/i); if (m) return +m[1]; var n = null; try { n = spDaysLeft(s); } catch (e) { } return n != null && n < 0 ? -n : 1; };
  function spItems() {
    var L = (typeof STATE !== "undefined" && STATE.sp) || [], out = [];
    L.forEach(function (s) {
      if (spDone(s)) return;
      if (emp(s.release_raw) && !s.release_ts) { out.push({ s: s, st: 0, od: 0 }); return; }
      if (spIsOverdue(s)) { var d = Math.max(1, spOdDays(s)); out.push({ s: s, st: stOf(d), od: d }); }
    });
    return out.sort(function (a, b) { return b.st - a.st || b.od - a.od; });
  }
  // perbaikan data SP: hari overdue dibaca dari teks status ("OVERDUE SP1 5 hari" = 5, bukan 15); Final = selesai; status ikut bisa dicari
  function spFix(s) {
    var m = String(s.overdue_raw || "").match(/(\d+)\s*hari/i); if (m && /overdue/i.test(s.overdue_raw)) s.overdue = +m[1];
    s.closed = spDone(s); s.__fx = 1;
    s.q = String(s.q || "") + " | " + String(s.overdue_raw || "").toLowerCase() + (emp(s.release_raw) ? " | belum rilis" : "") + (s.closed ? " | close closed final" : "");
    return s;
  }
  if (typeof buildSp === "function") { var origBS = buildSp; window.buildSp = buildSp = function () { var r = origBS.apply(this, arguments); try { (r || []).forEach(spFix); } catch (e) { } return r; }; }
  // pengaman data lokal: baris hasil "tambah" menggantikan entri lama di nomor baris yang sama (tidak dobel)
  // antrean Supabase: riwayat yang SUDAH selesai jangan diputar ulang saat aplikasi dibuka.
  // Dulu: setiap buka aplikasi, hasil "tambah baris" lama (mis. 047/SP1 di baris 49) dimasukkan lagi ke tampilan
  // walau barisnya sudah dihapus di spreadsheet → data hantu muncul & data asli di baris itu tertimpa.
  if (typeof qApplyRemote === "function") {
    var origQA = qApplyRemote;
    window.qApplyRemote = qApplyRemote = function (e, prev) {
      try {
        if (!prev && e && (e.status === "done" || e.status === "discarded")) {
          var dt = Date.parse(e.doneAt || e.at || "") || 0, ls = (typeof STATE !== "undefined" && STATE.lastSync) || 0;
          if (!dt || !ls || dt < ls - 60000) return;   // sudah termasuk di data spreadsheet yang dimuat
        }
      } catch (er) { }
      return origQA.apply(this, arguments);
    };
  }
  if (typeof recApplyRow === "function") { var origRAR = recApplyRow; window.recApplyRow = recApplyRow = function (sh, oldRow, newRow) { try { if (oldRow == null && newRow != null && STATE[sh] && STATE[sh].some(function (x) { return x.row === newRow; })) STATE[sh] = STATE[sh].filter(function (x) { return x.row !== newRow; }); } catch (e) { } return origRAR.apply(this, arguments); }; }
  // bila ada 2 data di baris yang sama (cache lama) → ambil ulang sheet tersebut dari spreadsheet
  var DUPAT = 0;
  function dupHeal() {
    try {
      if (Date.now() - DUPAT < 300000 || typeof STATE === "undefined" || typeof autoSyncGoogleSheets !== "function" || STATE.syncing) return;
      var bad = ["sp", "takeover", "spk", "perseroan"].filter(function (k) { var L = STATE[k]; if (!Array.isArray(L)) return false; var seen = {}; return L.some(function (x) { if (x.row == null) return false; if (seen[x.row]) return true; seen[x.row] = 1; return false; }); });
      if (!bad.length) return; DUPAT = Date.now(); console.warn("Data lokal dobel di", bad, "→ sinkron ulang"); autoSyncGoogleSheets({ keys: bad, silent: true });
    } catch (e) { }
  }
  var SPFIXED = null;
  function spFixAll() { try { if (typeof STATE === "undefined" || !STATE.sp || STATE.sp === SPFIXED) return; STATE.sp.forEach(function (s) { if (!s.__fx) { spFix(s); s.__fx = 1; } }); SPFIXED = STATE.sp; } catch (e) { } }
  function spStats() {
    spFixAll();
    var it = spItems(), cnt = [0, 0, 0, 0, 0]; it.forEach(function (x) { cnt[x.st]++; });
    var od = it.filter(function (x) { return x.st > 0; }), top = it.length ? it[0].st : -1;
    return { items: it, cnt: cnt, total: it.length, od: od.length, maxOd: od.length ? od[0].od : 0, stage: top, worst: od.length ? (od[0].od > 30 ? "31+" : od[0].od > 14 ? "15-30" : "0-14") : "" };
  }
  var MSG = {
    0: [["Ada SP yang belum dirilis", "Psst… ada yang tertinggal 👀"], function (S) { return "<b>" + S.cnt[0] + " SP</b> belum rilis. Segera TTD dok yang sudah dikirim di grup WA."; }],
    1: [["Ehem… ada SP yang telat", "Sekadar mengingatkan…"], function (S) { return "<b>" + S.od + " SP</b> lewat tenggat, terlama <b>" + S.maxOd + " hari</b>. Masih bisa dikejar — yuk tindak lanjuti sekarang."; }],
    2: [["Aku mulai kesal 😠", "Kok didiamkan terus? 😤"], function (S) { return "Sudah lebih dari seminggu! <b>" + S.od + " SP</b> lewat tenggat, terlama <b>" + S.maxOd + " hari</b>. Mitranya santai, aku yang deg-degan."; }],
    3: [["Ini sudah serius! 🔥", "Sabarku tinggal sedikit…"], function (S) { return "<b>" + S.od + " SP</b> lewat tenggat, ada yang <b>" + S.maxOd + " hari</b>. Segera naikkan ke SP berikutnya atau tutup yang sudah beres."; }],
    4: [["CUKUP! ✊ Aku mogok", "Revolusi notifikasi dimulai ✊"], function (S) { return "<b>" + S.od + " SP</b> terbengkalai, terlama <b>" + S.maxOd + " hari</b> lewat tenggat. Aku tidak akan diam sampai ini dibereskan!"; }]
  };
  function mascot(st) {
    var brow = st >= 2 ? '<path d="M15 19l6 3M33 19l-6 3" stroke="#0f172a" stroke-width="2.4" stroke-linecap="round"/>' : st === 1 ? '<path d="M15 21h6M27 21h6" stroke="#0f172a" stroke-width="2" stroke-linecap="round"/>' : '<path d="M15 20q3-2 6 0M27 20q3-2 6 0" stroke="#0f172a" stroke-width="2" fill="none" stroke-linecap="round"/>';
    var mouth = st >= 3 ? '<path d="M18 33q6-6 12 0" stroke="#0f172a" stroke-width="2.4" fill="none" stroke-linecap="round"/>' : st === 2 ? '<path d="M19 31h10" stroke="#0f172a" stroke-width="2.4" stroke-linecap="round"/>' : st === 1 ? '<path d="M19 31q5 1 10-1" stroke="#0f172a" stroke-width="2" fill="none" stroke-linecap="round"/>' : '<path d="M19 30q5 4 10 0" stroke="#0f172a" stroke-width="2" fill="none" stroke-linecap="round"/>';
    var extra = st >= 4 ? '<g class="st-sign"><rect x="33" y="-4" width="19" height="12" rx="2" fill="#fff" stroke="#0f172a" stroke-width="1.5"/><text x="42.5" y="5" text-anchor="middle" font-size="6.5" font-weight="900" fill="#be123c" font-family="Arial">SP!</text><path d="M42.5 8v9" stroke="#0f172a" stroke-width="1.6"/></g>' : st === 3 ? '<g class="st-steam"><path d="M8 6q-3-4 0-7M40 6q3-4 0-7" stroke="#ef4444" stroke-width="2" fill="none" stroke-linecap="round"/></g>' : st === 0 ? '<g class="st-zz"><text x="38" y="6" font-size="8" font-weight="900" fill="#8b5cf6" font-family="Arial">?</text></g>' : "";
    return '<svg viewBox="0 0 48 52" class="st-bell"><path d="M24 4c-9 0-14 7-14 15v9l-4 7h36l-4-7v-9c0-8-5-15-14-15z" fill="currentColor"/><circle cx="24" cy="42" r="5" fill="currentColor"/>' + brow + '<circle cx="18" cy="25" r="2.2" fill="#0f172a"/><circle cx="30" cy="25" r="2.2" fill="#0f172a"/>' + mouth + extra + "</svg>";
  }
  function groups(S, small) {
    var od = S.od, rl = S.cnt[0];
    return '<div class="st-grp' + (small ? " sm" : "") + '"><button data-g="od" style="--c:' + GRP.od.c + '"' + (od ? "" : " disabled") + '><i class="fa-solid ' + GRP.od.ic + '"></i><b>' + od + '</b><span>Overdue' + (od ? "<small>terlama " + S.maxOd + " hari</small>" : "") + '</span></button><button data-g="rl" style="--c:' + GRP.rl.c + '"' + (rl ? "" : " disabled") + '><i class="fa-solid ' + GRP.rl.ic + '"></i><b>' + rl + "</b><span>Belum rilis<small>Segera TTD dok di grup WA</small></span></button></div>";
  }
  function topList(S, n) {
    var od = S.items.filter(function (x) { return x.st; }), rl = S.items.filter(function (x) { return !x.st; }), a = od.slice(0, n), b = rl.slice(0, Math.max(1, n - a.length));
    var h = (a.length ? '<p class="st-gh" style="--c:' + GRP.od.c + '">Overdue · ' + od.length + "</p>" + a.map(itemRow).join("") : "") + (b.length ? '<p class="st-gh" style="--c:' + GRP.rl.c + '">Belum rilis · ' + rl.length + ' <em>— segera TTD dok di grup WA</em></p>' + b.map(itemRow).join("") : "");
    var rest = S.total - a.length - b.length; return h + (rest > 0 ? '<div class="st-more">+' + rest + " SP lainnya di lonceng</div>" : "");
  }
  function bindGroups(root, after) { root.querySelectorAll("[data-g]").forEach(function (b) { b.onclick = function () { if (after) after(); try { notifClose(); } catch (e) { } try { goSp({ q: b.dataset.g === "od" ? "overdue" : "belum rilis" }); } catch (e) { try { switchTab("sp"); } catch (er) { } } }; }); }
  function stepper(S, small) {
    return '<div class="st-steps' + (small ? " sm" : "") + '" style="--p:' + Math.max(0, S.stage) / 4 + '">' + '<i class="st-track"><b></b></i>' + STG.map(function (g) { var on = g.n === S.stage, done = g.n < S.stage; return '<div class="st-step' + (on ? " on" : done ? " done" : "") + (S.cnt[g.n] ? " has" : "") + '" style="--c:' + g.c + '"><span class="dot">' + (S.cnt[g.n] ? S.cnt[g.n] : '<i class="fa-solid fa-check"></i>') + "</span><b>" + g.k + "</b><small>" + g.l + "</small></div>"; }).join("") + "</div>";
  }
  function nagInfo() { var day = new Date().toDateString(), raw = (lsGet(uKey("sp_nag")) || "").split("|"); return { day: day, n: raw[0] === day ? +raw[1] || 0 : 0 }; }
  var GRP = { od: { k: "Overdue", c: "#e11d48", ic: "fa-hourglass-end" }, rl: { k: "Belum rilis", c: "#8b5cf6", ic: "fa-paper-plane" } };
  // saran tindak lanjut: belum rilis → rilis SP level itu; overdue SP1 → SP-2; SP2 → SP-3; SP3 → eskalasi
  function fuOf(s, st) { var lv = +s.level || (s.sp3 ? 3 : s.sp2 ? 2 : 1); if (!st) return { j: "SP-" + lv, t: "TTD SP-" + lv }; return lv >= 3 ? { j: "Lainnya", t: "Eskalasi" } : { j: "SP-" + (lv + 1), t: "Ajukan SP-" + (lv + 1) }; }
  function reqOf(s) {   // request SP yang masih terbuka untuk SP ini
    try { if (typeof REQ === "undefined" || !REQ.items) return null; var po = String(s.po || "").split(/[,;\s]+/)[0], lt = s.sp3 || s.sp2 || s.sp1 || "";
      return REQ.items.filter(function (r) { return !r.parent && r.status !== "selesai" && /^SP-|^Lainnya/.test(r.jenis || "") && ((lt && r.text.indexOf(lt) >= 0) || (po && s.mitra && r.text.indexOf(po) >= 0 && r.text.toUpperCase().indexOf(String(s.mitra).toUpperCase()) >= 0)); }).pop() || null; } catch (e) { return null; }
  }
  function itemRow(x) {
    var s = x.s, lt = ""; try { lt = spLetter(s); } catch (e) { lt = s.sp1 || ""; } var g = x.st ? GRP.od : GRP.rl, fu = fuOf(s, x.st), rq = reqOf(s);
    var rs = rq && typeof REQ_ST !== "undefined" && REQ_ST[rq.status] ? REQ_ST[rq.status][0] : "";
    return '<div class="st-it" style="--c:' + g.c + '"><button class="st-itm" data-sid="' + E(s.id) + '"><span class="ic"><i class="fa-solid ' + g.ic + '"></i></span><span class="tx"><b>' + E(s.mitra || "-") + "</b><small>" + E(lt || "-") + (s.site ? " · " + E(s.site) : "") + (s.region ? " · " + E(s.region) : "") + '</small></span><span class="chip">' + (x.st ? "overdue " + x.od + " hari" : "belum rilis") + "</span></button>"
      + (rq ? '<button class="st-fu done" data-fu="' + E(s.id) + '" data-st="' + x.st + '" title="Sudah ada request — klik untuk membuka"><i class="fa-solid fa-comments"></i>' + E(rq.jenis) + " · " + E(rs || rq.status) + "</button>"
        : '<button class="st-fu" data-fu="' + E(s.id) + '" data-st="' + x.st + '" title="Buat request tindak lanjut"><i class="fa-solid fa-share-from-square"></i>' + E(fu.t) + "</button>") + "</div>";
  }
  function bindItems(root) { root.querySelectorAll("[data-fu]").forEach(function (b) { b.onclick = function (ev) { ev.stopPropagation(); spFollow(b.dataset.fu, +b.dataset.st, b); }; }); root.querySelectorAll("[data-sid]").forEach(function (b) { b.onclick = function () { var c = $("st-call"); if (c) ntClose(c); try { notifClose(); } catch (e) { } try { notifOpen(b.dataset.sid); } catch (e) { try { openRecord(b.dataset.sid); } catch (er) { } } }; }); }
  // ---------- tindak lanjut → Request (SP-2 / SP-3 / rilis / eskalasi) ----------
  async function spFollow(sid, st, btn) {
    var s = (STATE.sp || []).filter(function (x) { return x.id === sid; })[0]; if (!s) return;
    var old = $("st-fu-pop"); if (old) { var same = old.dataset.sid === sid; old.remove(); if (same) return; }
    try { if (typeof REQ !== "undefined" && !REQ.loaded && typeof reqLoad === "function") await reqLoad(); } catch (e) { }
    var rq = reqOf(s);
    if (rq) { try { notifClose(); } catch (e) { } var c0 = $("st-call"); c0 && ntClose(c0); try { REQ.filter = "open"; reqOpenPane(); } catch (e) { } setTimeout(function () { var el = document.querySelector('[data-req-id="' + rq.id + '"]') || document.querySelector("#req-list"); el && el.scrollIntoView({ block: "center", behavior: "smooth" }); }, 600); return; }
    var fu = fuOf(s, st), lt = ""; try { lt = spLetter(s); } catch (e) { lt = s.sp3 || s.sp2 || s.sp1 || ""; }
    var x = spItems().filter(function (y) { return y.s === s; })[0] || { st: st, od: 0 };
    var txt = (fu.j === "Lainnya" ? "Eskalasi SP-3 (sudah lewat tenggat)" : st ? "Mohon diterbitkan " + fu.j + " (lanjutan)" : "Segera TTD " + fu.j + " (dok sudah di grup WA)") + "\n"
      + "No SP: " + (lt || "-") + "\nMitra: " + (s.mitra || "-") + "\nSite: " + (s.site || "-") + (s.region ? " · " + s.region : "") + "\nPO: " + (s.po || "-")
      + (st ? "\nStatus: overdue " + x.od + " hari" : "\nStatus: belum rilis") + (s.pic ? "\nPIC: " + s.pic : "");
    var J = []; try { REQ_JENIS.forEach(function (g) { g[1].forEach(function (j) { J.push(j); }); }); } catch (e) { J = ["SP-1", "SP-2", "SP-3", "Lainnya"]; }
    var pop = document.createElement("div"); pop.id = "st-fu-pop"; pop.className = "st-fu-pop"; pop.dataset.sid = sid;
    pop.innerHTML = '<div class="st-fu-h"><b><i class="fa-solid fa-share-from-square"></i>Tindak lanjut SP</b><button class="x" data-x title="Tutup"><i class="fa-solid fa-xmark"></i></button></div>'
      + '<div class="st-fu-opts">' + ["SP-2", "SP-3", "SP-1", "Lainnya"].filter(function (j, i, a) { return J.indexOf(j) >= 0; }).map(function (j) { var lab = j === "Lainnya" ? "Eskalasi / lainnya" : (st || j !== fu.j ? "Ajukan " : "TTD ") + j; return '<button type="button" data-j="' + j + '" class="' + (j === fu.j ? "on" : "") + '">' + lab + (j === fu.j ? " <em>disarankan</em>" : "") + "</button>"; }).join("") + "</div>"
      + '<textarea rows="7" class="field w-full" id="st-fu-t"></textarea>'
      + '<div class="st-fu-f"><small>Masuk ke <b>Request</b> sebagai jenis <b id="st-fu-j">' + E(fu.j) + '</b></small><button class="st-b pri" data-send><i class="fa-solid fa-paper-plane"></i>Kirim request</button></div>';
    document.body.appendChild(pop);
    var ta = pop.querySelector("#st-fu-t"); ta.value = txt; var J0 = fu.j;
    pop.querySelectorAll("[data-j]").forEach(function (b) { b.onclick = function () { pop.querySelectorAll("[data-j]").forEach(function (y) { y.classList.toggle("on", y === b); }); var j = b.dataset.j; ta.value = ta.value.replace(/^.*\n/, (j === "Lainnya" ? "Eskalasi SP (perlu keputusan lanjutan)" : st || j !== fuOf(s, 0).j ? "Mohon diterbitkan " + j + (st ? " (lanjutan)" : "") : "Segera TTD " + j + " (dok sudah di grup WA)") + "\n"); J0 = j; pop.querySelector("#st-fu-j").textContent = j; }; });
    var r = btn.getBoundingClientRect(), w = Math.min(360, innerWidth - 16);
    pop.style.width = w + "px"; pop.style.left = Math.max(8, Math.min(innerWidth - w - 8, r.right - w)) + "px";
    var top = r.bottom + 6; pop.style.top = top + "px"; var h = pop.offsetHeight; if (top + h > innerHeight - 8) pop.style.top = Math.max(8, r.top - h - 6) + "px";
    var close = function () { pop.remove(); document.removeEventListener("mousedown", out, true); document.removeEventListener("keydown", esc2); };
    var out = function (e) { if (!pop.contains(e.target) && e.target !== btn && !btn.contains(e.target)) close(); };
    var esc2 = function (e) { if (e.key === "Escape") close(); };
    setTimeout(function () { document.addEventListener("mousedown", out, true); document.addEventListener("keydown", esc2); }, 0);
    pop.onclick = function (e) { e.stopPropagation(); };
    pop.querySelector("[data-x]").onclick = close;
    pop.querySelector("[data-send]").onclick = async function () {
      var t = ta.value.trim(); if (!t) return ta.focus();
      var b = this; b.disabled = true; b.innerHTML = '<i class="fa-solid fa-circle-notch fa-spin"></i>Mengirim…';
      try {
        var res = await callApi("req.add", { parent: "", jenis: J0, text: t }, 60000);
        try { if (res && res.item) { REQ.items.push(res.item); REQ.rev = res.rev || REQ.rev; } if (typeof reqBadge === "function") reqBadge(); } catch (e) { }
        close(); toast("Request " + J0 + " terkirim — lihat di menu Request", "success", 5000);
        try { if (typeof NOTIF !== "undefined" && NOTIF.open) notifPanel(); } catch (e) { }
        var c = $("st-call"); if (c) { c.querySelectorAll('[data-fu="' + sid + '"]').forEach(function (y) { y.classList.add("done"); y.innerHTML = '<i class="fa-solid fa-comments"></i>' + E(J0) + " · Baru"; }); }
      } catch (e) { b.disabled = false; b.innerHTML = '<i class="fa-solid fa-paper-plane"></i>Kirim request'; toast("Gagal mengirim request: " + e.message, "error", 7000); }
    };
    setTimeout(function () { ta.focus(); ta.setSelectionRange(0, ta.value.indexOf("\n")); ta.scrollTop = 0; }, 30);
  }
  window.spFollow = spFollow;
  function goFix(S) { try { goSp({ q: S.stage >= 1 ? "overdue" : "belum rilis" }); } catch (e) { try { switchTab("sp"); } catch (er) { } } }
  // ---------- callout utama: menempel ke ikon lonceng di layar utama ----------
  function spCallout(force) {
    var P = ntPerm(); if (!P.on || $("st-call") || $("ton-call")) return;
    var S = spStats(); if (S.stage < 0) return;
    var nag = nagInfo(), snooze = +lsGet(uKey("sp_snooze")) || 0, snSt = +lsGet(uKey("sp_snooze_st"));
    if (!force && !P.lock && Date.now() < snooze && !(S.stage > snSt)) return;   // tunda berlaku sampai tahap naik
    var g = STG[S.stage], M = MSG[S.stage], title = M[0][nag.n % 2], bell = bellEl();
    var c = document.createElement("div"); c.id = "st-call"; c.className = "st-call st" + S.stage; c.style.setProperty("--c", g.c);
    var snoozeBtn = P.lock ? '<button class="st-b" data-min><i class="fa-solid fa-down-left-and-up-right-to-center"></i>Kecilkan</button>' : g.sn ? '<button class="st-b" data-sn>' + (nag.n ? "Tunda lagi " : "Ingatkan ") + (g.sn >= 60 ? g.sn / 60 + " jam lagi" : g.sn + " menit lagi") + "</button>" : '<button class="st-b" data-min><i class="fa-solid fa-down-left-and-up-right-to-center"></i>Kecilkan ke lonceng</button>';
    c.innerHTML = '<i class="st-arrow"></i><div class="st-aura"></div>'
      + '<div class="st-hd"><span class="st-av">' + mascot(S.stage) + '</span><div class="st-hd-t"><span class="st-tag"><i class="fa-solid fa-bell"></i>Notifikasi SP</span>' + (P.lock ? '<span class="st-tag lock"><i class="fa-solid fa-lock"></i>Wajib</span>' : "") + "<b>" + title + "</b><small>" + S.total + " SP perlu tindakan · " + S.cnt[0] + " belum rilis · " + S.od + " overdue</small></div>" + (P.lock ? "" : '<button class="x" data-x title="Tutup"><i class="fa-solid fa-xmark"></i></button>') + "</div>"
      + groups(S)
      + '<p class="st-msg">' + M[1](S) + (nag.n === 1 ? '<span class="st-nag">Tadi sudah kamu tunda. Aku ingat, lho.</span>' : nag.n >= 2 ? '<span class="st-nag">Sudah ' + nag.n + "× ditunda hari ini. Aku mulai curiga kamu menghindar 🙃</span>" : "") + "</p>"
      + '<div class="st-list">' + topList(S, 4) + "</div>"
      + '<div class="st-ft">' + snoozeBtn + '<button class="st-b pri" data-go><i class="fa-solid fa-list-check"></i>Bereskan sekarang</button></div>';
    ntHost().appendChild(c); place(c, bell); NT.shown = true;
    bindItems(c); bindGroups(c, function () { ntClose(c); });
    var toBell = function () { var b = bellEl(); if (b) { var r = b.getBoundingClientRect(), cr = c.getBoundingClientRect(); c.style.setProperty("--tx", (r.left + r.width / 2 - cr.left - cr.width / 2) + "px"); c.style.setProperty("--ty", (r.top + r.height / 2 - cr.top - 40) + "px"); c.classList.add("tobell"); setTimeout(function () { c.remove(); b.classList.remove("st-catch"); void b.offsetWidth; b.classList.add("st-catch"); }, 520); } else ntClose(c); };
    var sn = c.querySelector("[data-sn]"); if (sn) sn.onclick = function () { lsSet(uKey("sp_snooze"), Date.now() + g.sn * 60000); lsSet(uKey("sp_snooze_st"), S.stage); lsSet(uKey("sp_nag"), nag.day + "|" + (nag.n + 1)); toBell(); };
    var mn = c.querySelector("[data-min]"); if (mn) mn.onclick = function () { lsSet(uKey("sp_nag"), nag.day + "|" + (nag.n + 1)); toBell(); };
    var xx = c.querySelector("[data-x]"); if (xx) xx.onclick = function () { if (!g.sn) return toBell(); lsSet(uKey("sp_snooze"), Date.now() + g.sn * 60000); lsSet(uKey("sp_snooze_st"), S.stage); toBell(); };
    c.querySelector("[data-go]").onclick = function () { lsSet(uKey("sp_nag"), nag.day + "|0"); ntClose(c); goFix(S); };
  }
  function place(c, bell) {
    if (!bell) { c.classList.add("dock"); return; }
    if (!c.offsetWidth) { c.dataset.np = "1"; return; }   // sedang tertutup modal → posisikan saat terlihat lagi
    delete c.dataset.np;
    var r = bell.getBoundingClientRect();
    if (innerWidth < 640) { c.style.width = (innerWidth - 20) + "px"; c.style.maxHeight = (innerHeight - r.bottom - 90) + "px"; c.classList.add("mob"); }
    var w = c.offsetWidth, left = Math.max(10, Math.min(innerWidth - w - 10, r.right - w + 14));
    c.style.position = "fixed"; c.style.top = (r.bottom + 14) + "px"; c.style.left = left + "px";
    c.querySelector(".st-arrow").style.left = Math.max(18, Math.min(w - 30, r.left + r.width / 2 - left - 8)) + "px";
  }
  addEventListener("resize", function () { ["st-call", "ton-call"].forEach(function (i) { var c = $(i); if (c && !c.classList.contains("dock")) place(c, bellEl()); }); });
  setInterval(function () { ["st-call", "ton-call"].forEach(function (i) { var c = $(i); if (c && c.dataset.np && c.offsetWidth) place(c, bellEl()); }); }, 700);
  // ---------- panel lonceng: tahapan + daftar per tahap ----------
  function ntPanel() {
    var e = $("notif-panel"); if (!e) { e = document.createElement("div"); e.id = "notif-panel"; e.onclick = function (ev) { ev.stopPropagation(); }; document.body.appendChild(e); }
    var S = spStats(), P = ntPerm(), rd = new Set(); try { rd = notifRead(); } catch (er) { }
    var mk = function (L, g) { return L.length ? '<div class="st-pg" style="--c:' + g.c + '"><p><i class="fa-solid ' + g.ic + '"></i>' + g.k + (g === GRP.rl ? ' <em>— segera TTD dok di grup WA</em>' : '') + "<span>" + L.length + "</span></p>" + L.slice(0, 40).map(function (x) { return itemRow(x).replace('class="st-it"', 'class="st-it' + (rd.has(notifKey(x.s)) ? "" : " unread") + '"'); }).join("") + (L.length > 40 ? '<div class="st-more">+' + (L.length - 40) + " lainnya</div>" : "") + "</div>" : ""; };
    var grp = mk(S.items.filter(function (x) { return x.st; }), GRP.od) + mk(S.items.filter(function (x) { return !x.st; }), GRP.rl);
    e.className = "st-panel";
    e.innerHTML = '<div class="st-ph"><b><i class="fa-solid fa-bell"></i> Notifikasi SP</b>' + (P.lock ? '<span class="st-tag lock"><i class="fa-solid fa-lock"></i>Wajib</span>' : "") + '<button class="x" onclick="notifClose()"><i class="fa-solid fa-xmark"></i></button></div>'
      + (S.total ? groups(S, true) + '<div class="st-pl">' + grp + "</div>" : '<div class="st-empty"><i class="fa-solid fa-circle-check"></i><b>Semua SP aman</b><small>Tidak ada SP yang belum rilis atau overdue.</small></div>')
      + '<div class="st-pf"><button onclick="notifClose(); goSp({})">Buka Monitoring SP</button>' + (S.total ? '<button data-sum>Lihat ringkasan</button>' : "") + (currentUser && currentUser.role === "owner" ? '<button data-set><i class="fa-solid fa-sliders"></i>Atur penerima</button>' : "") + "</div>";
    bindItems(e); bindGroups(e);
    try { if (typeof REQ !== "undefined" && !REQ.loaded && !REQ.loading && typeof reqLoad === "function") reqLoad().then(function () { if (typeof NOTIF !== "undefined" && NOTIF.open) notifPanel(); }); } catch (er) { }
    var sm = e.querySelector("[data-sum]"); if (sm) sm.onclick = function () { try { notifClose(); } catch (er) { } spCallout(true); };
    var st = e.querySelector("[data-set]"); if (st) st.onclick = function () { try { notifClose(); switchTab("users"); } catch (er) { } setTimeout(function () { var c = $("st-umn"); if (c) c.scrollIntoView({ behavior: "smooth", block: "start" }); }, 400); };
    var b = bellEl(); if (b) { var r = b.getBoundingClientRect(), w = Math.min(420, innerWidth - 16); e.style.width = w + "px"; e.style.top = r.bottom + 8 + "px"; e.style.left = Math.max(8, Math.min(innerWidth - w - 8, r.right - w)) + "px"; }
  }
  if (typeof notifCompute === "function") { window.notifCompute = notifCompute = function () { try { spFixAll(); NOTIF.items = spItems().map(function (x) { return { s: x.s, n: x.st ? -x.od : "rilis" }; }); } catch (e) { } }; }
  if (typeof notifPanel === "function") { window.notifPanel = notifPanel = ntPanel; }
  if (typeof notifRender === "function") {
    var origNR = notifRender;
    window.notifRender = notifRender = function () {
      var r = origNR.apply(this, arguments);
      try { var S = spStats(), P = ntPerm(); document.querySelectorAll(".notif-bell:not(.undo-btn)").forEach(function (b) { if (!P.on) { b.classList.remove("st-ring"); return; } b.classList.toggle("st-ring", S.stage >= 0); b.style.setProperty("--c", S.stage >= 0 ? STG[S.stage].c : ""); b.dataset.stage = S.stage; b.title = S.stage >= 0 ? "Notifikasi SP · " + S.od + " overdue · " + S.cnt[0] + " belum rilis" : "Notifikasi SP"; }); } catch (e) { }
      return r;
    };
  }
  // ---------- fitur baru (sekali per akun per versi) ----------
  function whatsNew(force) {
    if (!currentUser || !canPdf() || $("st-new")) return;
    if (!force && lsGet(uKey("seen_" + NEWV))) return;
    var F = [["fa-right-left", "Konversi File", "PDF ⇄ Word, Excel, JPG, teks", 1], ["fa-glasses", "OCR scan", "teks scan bisa dicari & diedit"], ["fa-user-secret", "Sensor data", "email, NIK, No. HP otomatis"], ["fa-signature", "Tanda tangan", "gambar, ketik, atau foto"], ["fa-object-group", "Split · Gabung · Edit", "saling tersambung"], ["fa-rectangle-list", "Isi formulir", "langsung di PDF"], ["fa-code-compare", "Bandingkan versi", "lihat kata yang berubah"], ["fa-file-zipper", "Kompres & password", "file kecil & terkunci"]];
    var c = document.createElement("div"); c.id = "st-new"; c.className = "st-nt st-new";
    c.innerHTML = '<div class="st-new-hd"><span class="st-spark"><i class="fa-solid fa-wand-magic-sparkles"></i></span><div><small>Baru di STARLITE VM</small><b>PDF Tools + Konversi File</b></div><button class="x" data-x title="Tutup"><i class="fa-solid fa-xmark"></i></button></div>'
      + '<div class="st-new-g">' + F.map(function (f, i) { return '<div class="' + (f[3] ? "hot" : "") + '" style="--d:' + (i * 45) + 'ms"><i class="fa-solid ' + f[0] + '"></i><span><b>' + f[1] + (f[3] ? " <em>BARU</em>" : "") + "</b><small>" + f[2] + "</small></span></div>"; }).join("") + "</div>"
      + '<div class="st-new-ft"><button class="st-b" data-cv><i class="fa-solid fa-right-left"></i>Konversi file</button><button class="st-b pri" data-go><i class="fa-solid fa-file-pen"></i>Buka PDF Tools</button></div>';
    ntHost().appendChild(c);
    var seen = function () { lsSet(uKey("seen_" + NEWV), Date.now()); var b = $("docs-tab-pdf"); if (b) b.classList.remove("st-isnew"); };
    c.querySelector("[data-x]").onclick = function () { seen(); ntClose(c); };
    c.querySelector("[data-cv]").onclick = function () { seen(); ntClose(c); peOpen({ kind: "tab", mode: "conv" }); };
    c.querySelector("[data-go]").onclick = function () { seen(); ntClose(c); try { switchTab("docs"); } catch (e) { } setTimeout(function () { var b = $("docs-tab-pdf"); if (b) b.click(); }, 250); };
  }
  // ---------- Manajemen User: siapa menerima notifikasi SP & siapa wajib ----------
  function umDefault(role, k) { if (role === "owner") return k === "spnotif"; var rp = (typeof UM !== "undefined" && UM.rolePerms && UM.rolePerms[role]) || {}; if (k in rp) return !!rp[k]; var d = (typeof DEFAULT_ROLE_PERMS !== "undefined" && DEFAULT_ROLE_PERMS[role]) || {}; return !!d[k]; }
  function umEff(u, k) { var px = u.px || {}; return k in px ? !!px[k] : umDefault(u.role, k); }
  function umNotifCard() {
    if (typeof UM === "undefined" || !UM.users || !currentUser || currentUser.role !== "owner") return;
    var pane = $("um-pane-accounts"); if (!pane) return;
    var box = $("st-umn"); if (!box) { box = document.createElement("div"); box.id = "st-umn"; box.className = "st-umn"; pane.appendChild(box); }
    var L = UM.users.slice().sort(function (a, b) { return ["owner", "operator", "viewer"].indexOf(a.role) - ["owner", "operator", "viewer"].indexOf(b.role) || String(a.name).localeCompare(b.name, "id"); });
    var nOn = L.filter(function (u) { return u.active !== false && umEff(u, "spnotif"); }).length, nLock = L.filter(function (u) { return u.active !== false && umEff(u, "spnotif") && umEff(u, "spnotif_lock"); }).length;
    var RL = { owner: ["Akun Utama", "#0891b2"], operator: ["Operator", "#4f46e5"], viewer: ["Viewer", "#64748b"] };
    box.innerHTML = '<div class="st-umh"><span class="st-umi"><i class="fa-solid fa-bell"></i></span><div><b>Notifikasi SP</b><small>Atur akun mana yang menerima pengingat SP <b>belum rilis</b> &amp; <b>overdue</b>, dan mana yang <b>wajib</b> (selalu tampil saat membuka aplikasi, tidak bisa ditunda).</small></div><div class="st-ums"><span><b>' + nOn + "</b> menerima</span><span><b>" + nLock + "</b> wajib</span></div></div>"
      + '<div class="st-umflow"><span style="--c:' + GRP.od.c + '"><i class="fa-solid ' + GRP.od.ic + '"></i><b>Overdue</b>SP lewat tenggat<small>tindak lanjut: ajukan SP berikutnya</small></span><span style="--c:' + GRP.rl.c + '"><i class="fa-solid ' + GRP.rl.ic + '"></i><b>Belum rilis</b>SP tanpa tanggal rilis<small>segera TTD dok di grup WA</small></span></div>'
      + '<div class="st-umt"><div class="st-umr hd"><span>Akun</span><span>Terima</span><span>Wajib</span></div>' + L.map(function (u) {
        var on = umEff(u, "spnotif"), lk = umEff(u, "spnotif_lock"), cust = u.px && ("spnotif" in u.px || "spnotif_lock" in u.px), r = RL[u.role] || [u.role, "#64748b"];
        return '<div class="st-umr' + (u.active === false ? " off" : "") + '"><span class="who"><i class="av" style="--c:' + r[1] + '">' + E(String(u.name || "?").trim().split(/\s+/).map(function (w) { return w[0]; }).slice(0, 2).join("").toUpperCase()) + "</i><span><b>" + E(u.name) + '</b><small>@' + E(u.username) + ' · <em style="color:' + r[1] + '">' + r[0] + "</em>" + (cust ? " · diatur khusus" : " · ikut bawaan") + (u.active === false ? " · nonaktif" : "") + '</small></span></span><label class="st-sw"><input type="checkbox" data-u="' + u.id + '" data-k="spnotif" ' + (on ? "checked" : "") + '><i></i></label><label class="st-sw lk"><input type="checkbox" data-u="' + u.id + '" data-k="spnotif_lock" ' + (lk ? "checked" : "") + (on ? "" : " disabled") + "><i></i></label></div>";
      }).join("") + "</div>"
      + '<div class="st-umf"><button class="st-b" data-all><i class="fa-solid fa-check-double"></i>Semua aktif menerima</button><button class="st-b" data-reset><i class="fa-solid fa-rotate-left"></i>Kembali ke bawaan</button><button class="st-b" data-prev><i class="fa-solid fa-eye"></i>Pratinjau notifikasi</button></div>';
    var save = function (u, patch, msg) { var px = Object.assign({}, u.px || {}, patch); Object.keys(patch).forEach(function (k) { if (patch[k] === null) delete px[k]; }); return umCall("users.update", { id: u.id, px: px }, msg); };
    box.querySelectorAll("[data-u]").forEach(function (cb) { cb.onchange = function () { var u = UM.users.filter(function (x) { return x.id === cb.dataset.u; })[0]; if (!u) return; var p = {}; p[cb.dataset.k] = cb.checked; if (cb.dataset.k === "spnotif" && !cb.checked) p.spnotif_lock = false; save(u, p, "Notifikasi SP untuk " + u.name + (cb.dataset.k === "spnotif" ? (cb.checked ? " diaktifkan" : " dimatikan") : (cb.checked ? " dibuat wajib" : " tidak wajib lagi"))); }; });
    box.querySelector("[data-all]").onclick = async function () { for (var i = 0; i < L.length; i++) if (L[i].active !== false && !umEff(L[i], "spnotif")) await save(L[i], { spnotif: true }); toast("Semua akun aktif menerima notifikasi SP", "success"); };
    box.querySelector("[data-reset]").onclick = async function () { if (!confirm("Kembalikan pengaturan notifikasi SP semua akun ke bawaan jenis akun?")) return; for (var i = 0; i < L.length; i++) if (L[i].px && ("spnotif" in L[i].px || "spnotif_lock" in L[i].px)) await save(L[i], { spnotif: null, spnotif_lock: null }); toast("Pengaturan notifikasi SP kembali ke bawaan", "success"); };
    box.querySelector("[data-prev]").onclick = function () { try { switchTab("dashboard"); } catch (e) { } setTimeout(function () { spCallout(true); }, 400); };
  }
  if (typeof renderAccounts === "function") { var origRA = renderAccounts; window.renderAccounts = renderAccounts = function () { var r = origRA.apply(this, arguments); try { umNotifCard(); } catch (e) { console.warn(e); } return r; }; }
  function ntTick() {
    dupHeal();
    try {
      if (!currentUser || typeof STATE === "undefined" || !STATE.sp) return;
      var b = $("docs-tab-pdf"); if (b && canPdf() && !lsGet(uKey("seen_" + NEWV))) b.classList.add("st-isnew");
      if (!STATE.sp.length) return;
      if (!onMain()) return;   // hanya di layar utama
      if (!NT.shown) { NT.shown = true; setTimeout(function () { if (onMain()) { if (!(window.__tonShow && window.__tonShow(function () { if (onMain()) spCallout(); }))) spCallout(); } setTimeout(function () { if (onMain() && !$("st-call") && !$("ton-call")) whatsNew(); else if (!$("st-new")) NT.newLater = 1; }, 1200); }, 2600); }
      else if (NT.newLater && !$("st-call") && !$("ton-call")) { NT.newLater = 0; whatsNew(); }
    } catch (e) { }
  }
  setInterval(ntTick, 4000); setTimeout(ntTick, 2000);
  window.__NT = { host: ntHost, close: ntClose, onMain: onMain, bell: bellEl, place: place, uKey: uKey, lsGet: lsGet, lsSet: lsSet, sp: function () { spCallout(); } };
  window.stWhatsNew = function () { whatsNew(true); }; window.stSpRebel = window.stSpCallout = function () { spCallout(true); };
  // menu ⋯ Signing: tambah "Split PDF" untuk dokumen Selesai
  if (typeof sgMenu === "function") {
    var origMenu = sgMenu;
    window.sgMenu = sgMenu = function (ev, id) {
      var rect = ev && ev.currentTarget ? ev.currentTarget.getBoundingClientRect() : null;
      var r = origMenu.apply(this, arguments);
      try {
        var d = sgDoc(id), m = $("sgr-menu");
        if (m && d && d.status === "selesai" && canPdf()) {
          var b = document.createElement("button"); b.innerHTML = '<i class="fa-solid fa-scissors"></i>Split PDF (pecah dokumen final)';
          b.onclick = function () { sgMenuClose(); window.peFromSigning(id); };
          m.insertBefore(b, m.children[1] || null);
          if (d.splitFolderUrl) { var f = document.createElement("button"); f.innerHTML = '<i class="fa-solid fa-folder-open"></i>Buka folder hasil split'; f.onclick = function () { sgMenuClose(); window.open(d.splitFolderUrl, "_blank", "noopener"); }; m.insertBefore(f, b.nextSibling); }
          if (rect) { var l = m.offsetWidth, c = m.offsetHeight; m.style.left = Math.max(8, Math.min(innerWidth - l - 8, rect.right - l)) + "px"; m.style.top = (rect.bottom + c + 8 > innerHeight ? Math.max(8, rect.top - c - 4) : rect.bottom + 4) + "px"; }
        }
      } catch (e) { }
      return r;
    };
  }
  // rincian Signing: daftar file hasil split
  if (typeof sgRowDetail === "function") {
    var origDet = sgRowDetail;
    window.sgRowDetail = sgRowDetail = function (d) {
      var h = origDet.apply(this, arguments);
      try {
        if (d && d.splits && d.splits.length) {
          var add = '<div class="sgr-auto" style="display:block"><i class="fa-solid fa-scissors"></i> Hasil split (' + d.splits.length + ' file)' + (d.splitFolderUrl ? ' · <a href="' + E(d.splitFolderUrl) + '" target="_blank" rel="noopener" class="underline font-bold">folder</a>' : "") + ":<br>" + d.splits.map(function (s) { return '<a href="' + E(s.url) + '" target="_blank" rel="noopener" class="underline">' + E(s.name) + "</a>"; }).join(" · ") + "</div>";
          h = h.replace(/<\/div>\s*$/, add + "</div>");
        }
      } catch (e) { }
      return h;
    };
  }
})();

/* ===== v19 · Form Monitoring SP terhubung Tracker All Starlite ===== */
(function () {
  if (typeof openRecModal !== "function") return;
  var LS = "sp_link_mitra";
  var lsGet = function () { try { return localStorage.getItem(LS) || "before"; } catch (e) { return "before"; } };
  var lsSet = function (v) { try { localStorage.setItem(LS, v); } catch (e) { } };
  var X = function (s) { return typeof esc === "function" ? esc(s) : String(s == null ? "" : s); };
  var cl = function (s) { return String(s == null ? "" : s).replace(/\s+/g, " ").trim(); };
  var emp = function (s) { return typeof isEmpty === "function" ? isEmpty(s) : !cl(s); };
  var bare = function (n) { return cl(n).replace(/^(PT|CV|UD|PD|KOPERASI|KSU)\.?\s+/i, "").replace(/,?\s*(PT|TBK)\.?$/i, "").trim(); };
  var nk = function (n) { return bare(n).toUpperCase(); };
  var poList = function (s) { var m = String(s || "").toUpperCase().match(/PO\.\d{4}\.\d{2}\.\d{3,6}/g) || []; return m.filter(function (x, i) { return m.indexOf(x) === i; }); };
  var PL = {};   // tulisan nama PIC yang benar (bukan huruf besar semua)
  var picFix = function (p) {
    p = cl(p); if (!p || p !== p.toUpperCase()) return p;
    var k = p.toUpperCase(); if (PL[k]) return PL[k];
    return p.toLowerCase().replace(/(^|[\s.\-'])([a-z])/g, function (a, b, c) { return b + c.toUpperCase(); });
  };
  var IDX = { key: "", m: null };
  function index() {
    if ((typeof TRK === "undefined" || !TRK.rows || !TRK.rows.length) && typeof trkLoadCache === "function") { try { trkLoadCache(); } catch (e) { } }
    var tr = (typeof TRK !== "undefined" && TRK.rows) || [], to = STATE.takeover || [];
    var key = tr.length + ":" + (typeof TRK !== "undefined" && TRK.at) + ":" + to.length + ":" + STATE.lastSync;
    if (IDX.key === key && IDX.m) return IDX.m;
    var m = new Map();
    [].concat(STATE.sp || [], to).forEach(function (r) { var p = cl(r.pic); if (p && p !== p.toUpperCase()) PL[p.toUpperCase()] = p; });
    var put = function (r, src) {
      var po = cl(r.po).toUpperCase(); if (!po) return;
      var o = m.get(po) || { po: po, src: [] };
      ["before", "after", "stasiun", "region", "pic", "status"].forEach(function (k) { if (emp(o[k]) && !emp(r[k])) o[k] = cl(r[k]); });
      if (src === "to" && !emp(r.status_to)) o.to = cl(r.status_to);
      o.src.indexOf(src) < 0 && o.src.push(src); m.set(po, o);
    };
    tr.forEach(function (r) { put(r, "trk"); });   // sumber utama: Tracker All Starlite (semua PO SP ada di sini)
    to.forEach(function (r) { put(r, "to"); });    // Data Mitra Takeover hanya melengkapi yang kosong
    IDX = { key: key, m: m }; return m;
  }
  // HR / Sales / Email dari SP sebelumnya untuk mitra yang sama + Info Perseroan
  function mitraExtra(name) {
    var k = nk(name), o = {}; if (!k) return o;
    (STATE.sp || []).slice().sort(function (a, b) { return b.row - a.row; }).forEach(function (s) {
      if (nk(s.mitra) !== k) return;
      if (!o.hr && !emp(s.hr)) o.hr = s.hr; if (!o.sales && !emp(s.sales)) o.sales = s.sales; if (!o.email && !emp(s.email)) o.email = s.email;
    });
    if (!o.email) (STATE.perseroan || []).some(function (p) { if ((nk(p.nama) === k || nk(p.short) === k) && !emp(p.email)) { o.email = p.email; return true; } });
    return o;
  }
  function look(poStr) {
    var m = index(), pos = poList(poStr), hit = [], miss = [];
    pos.forEach(function (p) { var r = m.get(p); r ? hit.push(r) : miss.push(p); });
    return { pos: pos, hit: hit, miss: miss };
  }
  var F = function (c) { return document.querySelector('#rec-body [data-c="' + c + '"]'); };
  var L = { mode: "before", site: "auto", res: null };
  function setVal(c, v, force) {
    var el = F(c); if (!el || el.disabled) return false;
    v = cl(v); var cur = cl(el.value);
    if (!v && !(cur && el.dataset.auto === "1")) return false;   // kosong → hanya bersihkan isian otomatis lama
    if (!force && cur && el.dataset.auto !== "1") return false;
    if (cur === v) { el.dataset.auto = "1"; return false; }
    el.value = v; el.dataset.auto = "1"; el.classList.add("spl-auto");
    typeof recDirty === "function" && recDirty(); return true;   // tanpa memicu popup saran
  }
  function uniq(a) { var o = []; a.forEach(function (x) { x = cl(x); x && o.indexOf(x) < 0 && o.push(x); }); return o; }
  function apply(force) {
    var el = F(3); if (!el) return;
    var R = L.res = look(el.value), h = R.hit, n = 0;
    if (h.length) {
      var f = h[0], mitraFull = L.mode === "after" ? (f.after || f.before) : (f.before || f.after), mitra = bare(mitraFull);
      if (setVal(4, mitra, force || L.forceMitra)) n++; L.forceMitra = false;
      if (L.site === "auto" && setVal(5, uniq(h.map(function (x) { return x.stasiun; })).join(", "), force || L.forceSite)) n++; L.forceSite = false;
      if (setVal(6, f.region, force)) n++;
      if (setVal(7, picFix(f.pic), force)) n++;
      var ex = mitraExtra(mitra);
      if (setVal(8, ex.hr, force)) n++; if (setVal(9, ex.sales, force)) n++; if (setVal(14, ex.email, force)) n++;
    }
    render(); return n;
  }
  function render() {
    var box = document.getElementById("spl-box"); if (!box) return;
    var R = L.res || { pos: [], hit: [], miss: [] }, f = R.hit[0];
    var st;
    if (!R.pos.length) st = '<span class="spl-st"><i class="fa-solid fa-keyboard"></i>Ketik / tempel No PO — Mitra, Stasiun, Region, PIC, HR, Sales & Email terisi otomatis.</span>';
    else if (!R.hit.length) st = '<span class="spl-st warn"><i class="fa-solid fa-circle-exclamation"></i>PO <b>' + X(R.miss.join(", ")) + '</b> belum ada di Tracker All Starlite — cek penulisan PO, atau isi manual.</span>';
    else st = '<span class="spl-st ok"><i class="fa-solid fa-circle-check"></i><b>' + R.hit.length + "/" + R.pos.length + ' PO</b> ditemukan' + (f.status ? ' · status Tracker <b>' + X(f.status) + "</b>" : "") + (f.to ? " · Takeover <b>" + X(f.to) + "</b>" : "") + (R.miss.length ? ' · <span class="spl-miss">tidak ketemu: ' + X(R.miss.join(", ")) + "</span>" : "") + "</span>";
    var seg = function (k, lbl, name) { return '<button type="button" class="spl-opt' + (L.mode === k ? " on" : "") + '" data-m="' + k + '"' + (f && !name ? " disabled" : "") + '><small>' + lbl + "</small><b>" + X(f ? (bare(name) || "—") : lbl) + "</b></button>"; };
    var siteT = f ? uniq(R.hit.map(function (x) { return x.stasiun; })).join(", ") : "";
    box.innerHTML = '<div class="spl-hd"><span class="spl-ic"><i class="fa-solid fa-link"></i></span><div><b>Terhubung Tracker All Starlite</b>' + st + "</div>" +
      (f ? '<button type="button" class="spl-re" data-a="all" title="Timpa semua kolom dari Tracker (kecuali Dasar SP & Tanggal Rilis)"><i class="fa-solid fa-arrows-rotate"></i>Timpa semua</button>' : "") + "</div>" +
      '<div class="spl-row"><div class="spl-g"><label>Mitra yang dicantumkan</label><div class="spl-seg">' + seg("before", "Mitra Before", f && f.before) + seg("after", "Mitra After", f && f.after) + "</div></div>" +
      '<div class="spl-g"><label>Stasiun / Site</label><div class="spl-seg"><button type="button" class="spl-opt' + (L.site === "auto" ? " on" : "") + '" data-s="auto"><small>Ikuti Tracker</small><b>' + X(siteT || "otomatis") + '</b></button><button type="button" class="spl-opt' + (L.site === "manual" ? " on" : "") + '" data-s="manual"><small>Manual</small><b>Ketik sendiri</b></button></div></div></div>';
  }
  function mark() {
    [10, 11].forEach(function (c) {
      var el = F(c), w = el && el.closest(".rec-field"); if (!w || w.querySelector(".spl-man")) return;
      var lb = w.querySelector("label"); lb && lb.insertAdjacentHTML("beforeend", '<span class="spl-man" title="Tidak diambil dari Tracker">isi manual</span>');
    });
    var s = F(5), sw = s && s.closest(".rec-field");
    if (s) s.addEventListener("input", function (e) { if (e.isTrusted && L.site === "auto") { L.site = "manual"; s.dataset.auto = "0"; render(); } });
    [4, 6, 7, 8, 9, 14].forEach(function (c) { var el = F(c); el && el.addEventListener("input", function (e) { if (e.isTrusted) { el.dataset.auto = "0"; el.classList.remove("spl-auto"); } }); });
  }
  var LOADING = null;
  function ensureTrk() {   // Tracker belum dimuat di perangkat ini → ambil otomatis, lalu isi ulang form
    if ((typeof TRK !== "undefined" && TRK.rows && TRK.rows.length) || LOADING || typeof trkFetch !== "function") return;
    var bx = document.getElementById("spl-box"); bx && bx.insertAdjacentHTML("beforeend", '<p class="spl-st" id="spl-load"><i class="fa-solid fa-circle-notch fa-spin"></i>Memuat Tracker All Starlite…</p>');
    LOADING = Promise.resolve().then(function () { return trkFetch(); }).catch(function () { }).then(function () {
      LOADING = null; IDX.key = ""; var l = document.getElementById("spl-load"); l && l.remove();
      if (document.getElementById("spl-box")) apply(false);
    });
  }
  function init() {
    var body = document.getElementById("rec-body"), po = F(3);
    if (!body || !po || document.getElementById("spl-box")) return;
    L = { mode: lsGet(), site: "auto", res: null };
    var box = document.createElement("div"); box.id = "spl-box"; box.className = "spl-box md:col-span-2";
    var grid = po.closest(".rec-field") && po.closest(".rec-field").parentNode;
    (grid || body).insertBefore(box, (grid || body).firstChild);
    // daftar PO dari Tracker untuk saran ketik
    if (!po.getAttribute("list")) {
      var dl = document.createElement("datalist"); dl.id = "spl-dl";
      var m = index(), h = ""; m.forEach(function (v, k) { h += '<option value="' + X(k) + '">' + X(bare(v.before) + " · " + (v.stasiun || "")) + "</option>"; });
      dl.innerHTML = h; body.appendChild(dl); po.setAttribute("list", "spl-dl");
    }
    if (REC.mode === "edit") {   // data lama tidak ditimpa — hanya baca pilihan yang cocok
      var R = L.res = look(po.value), f = R.hit[0];
      if (f) {
        var mi = nk(F(4) && F(4).value);
        if (mi && nk(f.after) === mi && nk(f.before) !== mi) L.mode = "after"; else if (mi && nk(f.before) === mi) L.mode = "before";
        var sv = cl(F(5) && F(5).value), st = uniq(R.hit.map(function (x) { return x.stasiun; })).join(", ");
        if (sv && sv.toUpperCase() !== st.toUpperCase()) L.site = "manual";
      }
      render();
    } else apply(false);
    var t; po.addEventListener("input", function () { clearTimeout(t); t = setTimeout(function () { apply(false); }, 220); });
    box.addEventListener("click", function (e) {
      var b = e.target.closest("button"); if (!b || b.disabled) return;
      if (b.dataset.m) { L.mode = b.dataset.m; lsSet(L.mode); L.forceMitra = true; apply(false); }
      else if (b.dataset.s) { L.site = b.dataset.s; if (L.site === "auto") L.forceSite = true; else { var s = F(5); s && (s.dataset.auto = "0", s.classList.remove("spl-auto"), s.focus()); } apply(false); }
      else if (b.dataset.a === "all") { var n = apply(true); showToast(n ? n + " kolom diperbarui dari Tracker" : "Semua kolom sudah sesuai Tracker", "success"); }
    });
    mark(); ensureTrk();
  }
  var orig = openRecModal;
  window.openRecModal = openRecModal = function () {
    var r = orig.apply(this, arguments);
    try { if (REC.sheet === "sp" && (REC.mode === "add" || REC.mode === "edit")) init(); } catch (e) { console.warn("spLink", e); }
    return r;
  };
  if (location.hostname === "localhost") window.__spLink = { look: look, index: index, bare: bare, mitraExtra: mitraExtra };
})();

/* ===== v19 · Notifikasi Takeover (ditentukan Akun Utama: PO, pesan, penerima) ===== */
(function () {
  var N = window.__NT; if (!N) return;
  var $ = function (i) { return document.getElementById(i); };
  var E = function (t) { return String(t == null ? "" : t).replace(/[&<>"']/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]; }); };
  var toast = function (m, t, ms) { try { showToast(m, t || "info", ms); } catch (e) { } };
  var srv = function () { try { return typeof isServerMode === "function" && isServerMode(); } catch (e) { return false; } };
  var isOwner = function () { return !!currentUser && currentUser.role === "owner"; };
  var emp = function (v) { return typeof isEmpty === "function" ? isEmpty(v) : !String(v || "").trim(); };
  var TON = { items: [], rev: "", at: 0, busy: false, user: "" };
  var CK = function () { return N.uKey("ton_cache"); };
  function loadCache() {
    var u = currentUser && currentUser.username || ""; if (TON.user === u) return; TON.user = u; TON.items = []; TON.rev = ""; TON.at = 0;
    try { var c = JSON.parse(N.lsGet(CK()) || "null"); if (c && Array.isArray(c.items)) { TON.items = c.items; TON.rev = c.rev || ""; } } catch (e) { }
  }
  function saveCache() { N.lsSet(CK(), JSON.stringify({ items: TON.items, rev: TON.rev })); }
  var mine = function () { loadCache(); return TON.items.filter(function (x) { return x.mine && x.on; }); };
  var unread = function () { return mine().filter(function (x) { return !x.read; }); };
  var SS = "ton_later";   // "nanti saja" berlaku sampai aplikasi dibuka lagi
  var later = function () { try { return JSON.parse(sessionStorage.getItem(SS) || "{}"); } catch (e) { return {}; } };
  var setLater = function (ids) { var o = later(); ids.forEach(function (i) { o[i] = 1; }); try { sessionStorage.setItem(SS, JSON.stringify(o)); } catch (e) { } };
  var pending = function () { var l = later(); return mine().filter(function (x) { return (x.w || !x.read) && !l[x.id]; }); };
  function toOf(po) { po = String(po || "").toUpperCase(); return (STATE.takeover || []).filter(function (t) { return String(t.po || "").toUpperCase() === po; })[0] || null; }
  function missAtt(t) { var M = [["att_ba", "BA"], ["att_spk", "SPK"], ["att_bap", "BAP"], ["att_bastm", "BASTM"]]; return M.filter(function (m) { return emp(t[m[0]]); }).map(function (m) { return m[1]; }); }
  function stTxt(t) { return emp(t.status_to) ? "Status kosong" : t.status_to; }
  function stCls(t) { var s = String(t.status_to || "").toUpperCase(); return !s.trim() ? "e" : /HOLD/.test(s) ? "h" : /FINAL/.test(s) ? "f" : "o"; }
  function openPo(po) { var t = toOf(po); if (!t) return toast("PO " + po + " tidak ada di Data Mitra Takeover", "info"); try { notifClose(); } catch (e) { } var c = $("ton-call"); c && N.close(c); try { openRecord(t.id); } catch (e) { } }
  window.tonOpenPo = openPo;
  function poRow(po) {
    var t = toOf(po);
    if (!t) return '<button type="button" class="ton-po" data-po="' + E(po) + '"><b>' + E(po) + '</b><small>tidak ditemukan di Data Takeover</small></button>';
    var ma = missAtt(t);
    return '<button type="button" class="ton-po" data-po="' + E(po) + '"><b>' + E(po) + (t.stasiun ? " · " + E(t.stasiun) : "") + '</b><small>' + E((t.before || "-") + " → " + (t.after || "-")) + (ma.length ? ' · <em>lampiran belum: ' + E(ma.join(", ")) + "</em>" : "") + '</small><i class="ton-st ' + stCls(t) + '">' + E(stTxt(t)) + "</i></button>";
  }
  function bindPo(root) { root.querySelectorAll("[data-po]").forEach(function (b) { b.onclick = function (e) { e.stopPropagation(); openPo(b.dataset.po); }; }); }
  async function markRead(ids, read) {
    var ok = 0;
    for (var i = 0; i < ids.length; i++) {
      var x = TON.items.filter(function (y) { return y.id === ids[i]; })[0]; if (x) x.read = read !== false;
      try { var r = await callApi("ton.read", { id: ids[i], read: read !== false }, 30000); if (r && r.item) { replaceItem(r.item); ok++; } } catch (e) { }
    }
    saveCache(); changed(true); return ok;
  }
  function replaceItem(it) { var i = TON.items.findIndex(function (y) { return y.id === it.id; }); if (i >= 0) TON.items[i] = Object.assign({}, TON.items[i], it); else TON.items.unshift(it); }
  async function fetchTon(force) {
    if (!currentUser || !srv() || TON.busy) return; loadCache();
    if (!force && Date.now() - TON.at < 150000) return;
    TON.busy = true;
    try {
      var r = await callApi("ton.list", { rev: force ? "" : TON.rev }, 30000); TON.at = Date.now();
      if (r && !r.same && Array.isArray(r.items)) { TON.items = r.items; TON.rev = r.rev || ""; saveCache(); changed(false); }
    } catch (e) { } finally { TON.busy = false; }
  }
  window.tonRefresh = function () { return fetchTon(true); };
  function changed(quiet) {
    try { notifRender(); } catch (e) { }
    try { if (typeof NOTIF !== "undefined" && NOTIF.open) notifPanel(); } catch (e) { }
    try { umCard(); } catch (e) { }
    if (!quiet && N.onMain() && !$("st-call") && !$("ton-call") && !$("st-new") && N.__started) tonShow(null);
  }
  // ---------- pop-up di layar utama (menempel ke lonceng) ----------
  function tonShow(after) {
    if (!currentUser || $("ton-call")) return false;
    var P = pending(); if (!P.length) return false;
    var w = P.some(function (x) { return x.w; });
    var c = document.createElement("div"); c.id = "ton-call"; c.className = "st-call ton-call"; c.style.setProperty("--c", "#0d9488");
    var list = P.slice(0, 3).map(function (x) {
      return '<div class="ton-it"><div class="ton-ih"><b>' + E(x.t) + "</b>" + (x.w ? '<span class="st-tag lock"><i class="fa-solid fa-lock"></i>Wajib</span>' : "") + "</div>" + (x.m ? '<p>' + E(x.m) + "</p>" : "") + '<div class="ton-pos">' + x.pos.slice(0, 4).map(poRow).join("") + (x.pos.length > 4 ? '<div class="st-more">+' + (x.pos.length - 4) + " PO lainnya — buka lonceng</div>" : "") + "</div></div>";
    }).join("") + (P.length > 3 ? '<div class="st-more">+' + (P.length - 3) + " notifikasi lainnya di lonceng</div>" : "");
    c.innerHTML = '<i class="st-arrow"></i><div class="st-hd"><span class="st-av ton-av"><i class="fa-solid fa-handshake-angle"></i></span><div class="st-hd-t"><span class="st-tag"><i class="fa-solid fa-bullhorn"></i>Notifikasi Takeover</span><b>' + (P.length === 1 ? E(P[0].t) : P.length + " hal takeover perlu perhatian") + "</b><small>dari " + E(P[0].by || "Akun Utama") + " · " + P.reduce(function (n, x) { return n + x.pos.length; }, 0) + " PO</small></div>" + (w ? "" : '<button class="x" data-x title="Nanti saja"><i class="fa-solid fa-xmark"></i></button>') + "</div>"
      + '<div class="ton-list">' + list + "</div>"
      + '<div class="st-ft"><button class="st-b" data-later>' + (w ? '<i class="fa-solid fa-down-left-and-up-right-to-center"></i>Kecilkan' : "Nanti saja") + '</button><button class="st-b pri" data-read><i class="fa-solid fa-check"></i>Sudah dibaca</button></div>';
    N.host().appendChild(c); N.place(c, N.bell()); bindPo(c);
    var done = function () { N.close(c, function () { if (after) after(); }); };
    var lt = function () { setLater(P.map(function (x) { return x.id; })); done(); };
    c.querySelector("[data-later]").onclick = lt; var xx = c.querySelector("[data-x]"); if (xx) xx.onclick = lt;
    c.querySelector("[data-read]").onclick = function () { var ids = P.map(function (x) { return x.id; }); setLater(ids); markRead(ids.filter(function (i) { return P.some(function (x) { return x.id === i && !x.read; }); }), true); done(); };
    return true;
  }
  window.__tonShow = function (after) { N.__started = true; loadCache(); var r = tonShow(after); fetchTon(false); return r; };
  // ---------- lonceng: badge + bagian Takeover di panel ----------
  if (typeof notifRender === "function") {
    var oNR = notifRender;
    window.notifRender = notifRender = function () {
      var r = oNR.apply(this, arguments);
      try {
        if (!currentUser) return r;
        var my = mine(), u = unread().length;
        document.querySelectorAll("[data-notif-slot]").forEach(function (sl) {
          if (!sl.querySelector(".notif-bell") && my.length) sl.innerHTML = '<button onclick="notifToggle(event)" class="notif-bell" title="Notifikasi Takeover"><i class="fa-solid fa-bell"></i></button>';
          var b = sl.querySelector(".notif-bell"); if (!b) return;
          var bd = b.querySelector(".notif-badge"), base = bd ? +(bd.dataset.sp || bd.textContent.replace(/\D/g, "")) || 0 : 0;
          if (u) { b.classList.add("has", "ton-has"); if (!bd) { bd = document.createElement("span"); bd.className = "notif-badge"; b.appendChild(bd); } bd.dataset.sp = base; var t = base + u; bd.textContent = t > 99 ? "99+" : t; }
          else b.classList.remove("ton-has");
        });
      } catch (e) { }
      return r;
    };
  }
  var canSp = function () { try { return can("sp"); } catch (e) { return false; } };
  function panelSec() {
    var my = mine(); if (!my.length) return "";
    return '<div class="ton-sec"><p class="ton-sh"><i class="fa-solid fa-handshake-angle"></i>Takeover<span>' + my.length + "</span>" + (unread().length ? '<button data-allread>Tandai semua dibaca</button>' : "") + "</p>" + my.map(function (x) {
      return '<div class="ton-pi' + (x.read ? "" : " unread") + '"><div class="ton-ih"><b>' + E(x.t) + "</b>" + (x.w ? '<span class="st-tag lock"><i class="fa-solid fa-lock"></i>Wajib</span>' : "") + '<button class="ton-rd" data-rd="' + E(x.id) + '" data-v="' + (x.read ? 0 : 1) + '" title="' + (x.read ? "Tandai belum dibaca" : "Tandai sudah dibaca") + '"><i class="fa-' + (x.read ? "regular fa-envelope-open" : "solid fa-envelope") + '"></i></button></div>' + (x.m ? "<p>" + E(x.m) + "</p>" : "") + '<div class="ton-pos">' + x.pos.slice(0, 12).map(poRow).join("") + (x.pos.length > 12 ? '<div class="st-more">+' + (x.pos.length - 12) + " PO lainnya</div>" : "") + "</div><small class=\"ton-meta\">" + E(x.by || "") + " · " + E(fmtD(x.up || x.at)) + "</small></div>";
    }).join("") + "</div>";
  }
  function fmtD(s) { try { return new Date(s).toLocaleString("id-ID", { day: "2-digit", month: "short", hour: "2-digit", minute: "2-digit" }); } catch (e) { return s || ""; } }
  if (typeof notifPanel === "function") {
    var oNP = notifPanel;
    window.notifPanel = notifPanel = function () {
      var r = oNP.apply(this, arguments);
      try {
        var e = $("notif-panel"); if (!e) return r;
        var h = panelSec();
        if (!canSp()) {   // akun tanpa akses SP: panel hanya berisi takeover
          e.className = "st-panel"; e.innerHTML = '<div class="st-ph"><b><i class="fa-solid fa-bell"></i> Notifikasi</b><button class="x" onclick="notifClose()"><i class="fa-solid fa-xmark"></i></button></div>' + (h || '<div class="st-empty"><i class="fa-solid fa-circle-check"></i><b>Tidak ada notifikasi</b></div>');
          var b = N.bell(); if (b) { var q = b.getBoundingClientRect(), w = Math.min(420, innerWidth - 16); e.style.width = w + "px"; e.style.top = q.bottom + 8 + "px"; e.style.left = Math.max(8, Math.min(innerWidth - w - 8, q.right - w)) + "px"; }
        } else if (h) { var ph = e.querySelector(".st-ph"); if (ph) { ph.insertAdjacentHTML("afterend", h); var hb = ph.querySelector("b"); hb && (hb.innerHTML = '<i class="fa-solid fa-bell"></i> Notifikasi'); } else e.insertAdjacentHTML("afterbegin", h); }
        bindPo(e);
        e.querySelectorAll("[data-rd]").forEach(function (b) { b.onclick = function (ev) { ev.stopPropagation(); markRead([b.dataset.rd], b.dataset.v === "1"); }; });
        var ar = e.querySelector("[data-allread]"); if (ar) ar.onclick = function (ev) { ev.stopPropagation(); markRead(unread().map(function (x) { return x.id; }), true); };
      } catch (er) { console.warn("ton panel", er); }
      return r;
    };
  }
  // ---------- Manajemen User: kartu Notifikasi Takeover ----------
  function users() { return (typeof UM !== "undefined" && UM.users) || []; }
  function uName(id) { var u = users().filter(function (x) { return x.id === id; })[0]; return u ? u.name : "(akun dihapus)"; }
  function recipients(x) { return (x.to || []).indexOf("*") >= 0 ? users().filter(function (u) { return u.active !== false; }).map(function (u) { return u.id; }) : (x.to || []); }
  function umCard() {
    if (!isOwner() || typeof UM === "undefined" || !UM.users) return;
    var pane = $("um-pane-accounts"); if (!pane) return;
    var box = $("ton-um"); if (!box) { box = document.createElement("div"); box.id = "ton-um"; box.className = "st-umn ton-um"; var sp = $("st-umn"); sp && sp.parentNode === pane ? sp.after(box) : pane.appendChild(box); }
    loadCache();
    var L = TON.items;
    box.innerHTML = '<div class="st-umh"><span class="st-umi" style="background:#0d9488"><i class="fa-solid fa-handshake-angle"></i></span><div><b>Notifikasi Takeover</b><small>Anda yang memilih <b>PO takeover</b> mana yang ditampilkan, isi pesannya, dan <b>akun penerima</b>. Notifikasi <b>wajib</b> selalu muncul tiap aplikasi dibuka sampai Anda menonaktifkan atau menghapusnya.</small></div><div class="st-ums"><span><b>' + L.filter(function (x) { return x.on; }).length + "</b> aktif</span><span><b>" + L.length + '</b> total</span></div></div>'
      + (L.length ? '<div class="ton-ul">' + L.map(function (x) {
        var rc = recipients(x), rd = rc.filter(function (i) { return (x.reads || {})[i]; });
        return '<div class="ton-ur' + (x.on ? "" : " off") + '"><div class="ton-ut"><b>' + E(x.t) + "</b><small>" + x.pos.length + " PO · " + ((x.to || []).indexOf("*") >= 0 ? "Semua akun" : rc.length + " akun") + ' · <span title="' + E(rc.map(function (i) { return uName(i) + ((x.reads || {})[i] ? " ✓ dibaca " + fmtD(x.reads[i]) : " — belum dibaca"); }).join("\n")) + '"><i class="fa-solid fa-check-double"></i> ' + rd.length + "/" + rc.length + " sudah baca</span> · " + E(fmtD(x.up || x.at)) + '</small><div class="ton-uc">' + x.pos.slice(0, 6).map(function (p) { return '<span>' + E(p) + "</span>"; }).join("") + (x.pos.length > 6 ? "<span>+" + (x.pos.length - 6) + "</span>" : "") + "</div></div>"
          + '<label class="st-sw" title="Aktif"><input type="checkbox" data-on="' + E(x.id) + '" ' + (x.on ? "checked" : "") + '><i></i><small>Aktif</small></label><label class="st-sw" title="Wajib"><input type="checkbox" data-w="' + E(x.id) + '" ' + (x.w ? "checked" : "") + '><i></i><small>Wajib</small></label>'
          + '<div class="ton-ua"><button class="st-b" data-ed="' + E(x.id) + '"><i class="fa-solid fa-pen"></i>Ubah</button><button class="st-b dng" data-del="' + E(x.id) + '"><i class="fa-solid fa-trash-can"></i></button></div></div>';
      }).join("") + "</div>" : '<div class="ton-empty"><i class="fa-regular fa-bell"></i>Belum ada notifikasi takeover. Buat satu untuk mengingatkan tim soal PO tertentu.</div>')
      + '<div class="st-umf"><button class="st-b pri" data-new><i class="fa-solid fa-plus"></i>Buat notifikasi takeover</button><button class="st-b" data-rf><i class="fa-solid fa-rotate"></i>Muat ulang</button></div>';
    box.querySelector("[data-new]").onclick = function () { editor(null); };
    box.querySelector("[data-rf]").onclick = function () { fetchTon(true).then(function () { toast("Notifikasi takeover dimuat ulang", "success"); }); };
    box.querySelectorAll("[data-ed]").forEach(function (b) { b.onclick = function () { editor(TON.items.filter(function (x) { return x.id === b.dataset.ed; })[0]); }; });
    box.querySelectorAll("[data-del]").forEach(function (b) { b.onclick = async function () { var x = TON.items.filter(function (y) { return y.id === b.dataset.del; })[0]; if (!x || !confirm('Hapus notifikasi "' + x.t + '"? Penerima tidak akan melihatnya lagi.')) return; try { await callApi("ton.delete", { id: x.id }, 30000); TON.items = TON.items.filter(function (y) { return y.id !== x.id; }); saveCache(); changed(true); toast("Notifikasi takeover dihapus", "success"); } catch (e) { toast(e.message, "error", 7000); } }; });
    var quick = function (attr, key) { box.querySelectorAll("[" + attr + "]").forEach(function (cb) { cb.onchange = async function () { var x = TON.items.filter(function (y) { return y.id === cb.getAttribute(attr); })[0]; if (!x) return; var it = { id: x.id, t: x.t, m: x.m, pos: x.pos, to: x.to, w: x.w, on: x.on }; it[key] = cb.checked; cb.disabled = true; try { var r = await callApi("ton.save", { item: it }, 30000); replaceItem(r.item); saveCache(); changed(true); toast(key === "on" ? (cb.checked ? "Notifikasi diaktifkan" : "Notifikasi dinonaktifkan") : (cb.checked ? "Notifikasi dibuat wajib" : "Notifikasi tidak wajib lagi"), "success"); } catch (e) { cb.checked = !cb.checked; toast(e.message, "error", 7000); } cb.disabled = false; }; }); };
    quick("data-on", "on"); quick("data-w", "w");
    if (!TON.at) fetchTon(true);
  }
  if (typeof renderAccounts === "function") { var oRA = renderAccounts; window.renderAccounts = renderAccounts = function () { var r = oRA.apply(this, arguments); try { umCard(); } catch (e) { console.warn(e); } return r; }; }
  // ---------- editor: pilih PO, pesan, penerima ----------
  var FL = [["all", "Semua"], ["empty", "Status kosong"], ["hold", "HOLD"], ["att", "Lampiran belum lengkap"], ["nofinal", "Belum FINAL"], ["sel", "Terpilih"]];
  function editor(x) {
    var old = $("ton-ov"); old && old.remove();
    var D = { id: x && x.id || "", t: x && x.t || "", m: x && x.m || "", pos: (x && x.pos || []).slice(), to: (x && x.to || []).slice(), w: !!(x && x.w), on: x ? x.on : true, f: "all", q: "" };
    var ov = document.createElement("div"); ov.id = "ton-ov"; ov.className = "ton-ov";
    ov.innerHTML = '<div class="ton-card" role="dialog" aria-modal="true" aria-labelledby="ton-h"><div class="ton-hd"><span class="st-umi" style="background:#0d9488"><i class="fa-solid fa-handshake-angle"></i></span><div><b id="ton-h">' + (x ? "Ubah" : "Buat") + ' notifikasi takeover</b><small>Muncul di layar utama &amp; lonceng akun yang Anda pilih</small></div><button class="x" data-x title="Tutup"><i class="fa-solid fa-xmark"></i></button></div>'
      + '<div class="ton-bd"><div class="ton-col"><label class="ton-l">Judul<input id="ton-t" class="field w-full" maxlength="120" placeholder="mis. Lengkapi BAP & BASTM takeover Jatim"></label><label class="ton-l">Pesan<textarea id="ton-m" class="field w-full" rows="3" maxlength="1200" placeholder="Apa yang perlu dilakukan penerima?"></textarea></label>'
      + '<div class="ton-l">Penerima<div class="ton-to" id="ton-to"></div></div><label class="ton-wj"><input type="checkbox" id="ton-w"><span><b>Wajib</b><small>Selalu muncul setiap aplikasi dibuka, hanya bisa dikecilkan.</small></span></label>' + (x ? '<label class="ton-wj"><input type="checkbox" id="ton-un"><span><b>Tampilkan ulang ke semua penerima</b><small>Status "sudah dibaca" dihapus.</small></span></label>' : "") + "</div>"
      + '<div class="ton-col"><div class="ton-l">PO takeover <span id="ton-cnt"></span></div><input id="ton-q" class="field w-full" placeholder="Cari PO, stasiun, mitra, region, PIC…"><div class="ton-fl" id="ton-fl"></div><div class="ton-res" id="ton-res"></div><div class="ton-selbar"><button type="button" class="st-b" data-pickall>Pilih semua yang tampil</button><button type="button" class="st-b" data-clear>Kosongkan pilihan</button></div></div></div>'
      + '<p class="ton-err hidden" id="ton-err"></p><div class="ton-ft"><button class="st-b" data-x>Batal</button><button class="st-b pri" id="ton-save"><i class="fa-solid fa-paper-plane"></i>' + (x ? "Simpan perubahan" : "Kirim notifikasi") + "</button></div></div>";
    document.body.appendChild(ov);
    var q = function (s) { return ov.querySelector(s); };
    q("#ton-t").value = D.t; q("#ton-m").value = D.m; q("#ton-w").checked = D.w;
    var close = function () { ov.remove(); document.removeEventListener("keydown", esc); };
    var esc = function (e) { if (e.key === "Escape") close(); }; document.addEventListener("keydown", esc);
    ov.querySelectorAll("[data-x]").forEach(function (b) { b.onclick = close; }); ov.onclick = function (e) { if (e.target === ov) close(); };
    var U = users().filter(function (u) { return u.active !== false || D.to.indexOf(u.id) >= 0; }).sort(function (a, b) { return ["owner", "operator", "viewer"].indexOf(a.role) - ["owner", "operator", "viewer"].indexOf(b.role) || String(a.name).localeCompare(b.name, "id"); });
    function drawTo() {
      var all = D.to.indexOf("*") >= 0;
      q("#ton-to").innerHTML = '<label class="ton-u all"><input type="checkbox" data-uid="*" ' + (all ? "checked" : "") + '><b>Semua akun</b><small>termasuk akun yang dibuat nanti</small></label>' + U.map(function (u) { return '<label class="ton-u' + (all ? " dim" : "") + '"><input type="checkbox" data-uid="' + E(u.id) + '" ' + (all || D.to.indexOf(u.id) >= 0 ? "checked" : "") + (all ? " disabled" : "") + "><b>" + E(u.name) + "</b><small>@" + E(u.username) + " · " + E({ owner: "Akun Utama", operator: "Operator", viewer: "Viewer" }[u.role] || u.role) + (u.active === false ? " · nonaktif" : "") + "</small></label>"; }).join("");
      q("#ton-to").querySelectorAll("[data-uid]").forEach(function (cb) { cb.onchange = function () { var id = cb.dataset.uid; if (id === "*") D.to = cb.checked ? ["*"] : []; else { D.to = D.to.filter(function (i) { return i !== id && i !== "*"; }); if (cb.checked) D.to.push(id); } drawTo(); }; });
    }
    var TOs = (STATE.takeover || []).filter(function (t) { return !emp(t.po); });
    function match(t) {
      var s = String(t.status_to || "").toUpperCase();
      if (D.f === "empty" && !emp(t.status_to)) return false; if (D.f === "hold" && !/HOLD/.test(s)) return false;
      if (D.f === "att" && !missAtt(t).length) return false; if (D.f === "nofinal" && /FINAL/.test(s)) return false;
      if (D.f === "sel" && D.pos.indexOf(String(t.po).toUpperCase()) < 0) return false;
      if (D.q) { var h = [t.po, t.stasiun, t.before, t.after, t.region, t.pic, t.status_to, t.bap_no].join(" ").toLowerCase(); if (D.q.split(/\s+/).some(function (w) { return h.indexOf(w) < 0; })) return false; }
      return true;
    }
    var shown = [];
    function drawRes() {
      var cnt = {}; FL.forEach(function (f) { var o = D.f; D.f = f[0]; var qq = D.q; D.q = ""; cnt[f[0]] = TOs.filter(match).length; D.f = o; D.q = qq; });
      q("#ton-fl").innerHTML = FL.map(function (f) { return '<button type="button" class="ton-chip' + (D.f === f[0] ? " on" : "") + '" data-f="' + f[0] + '">' + f[1] + " <i>" + (f[0] === "sel" ? D.pos.length : cnt[f[0]]) + "</i></button>"; }).join("");
      q("#ton-fl").querySelectorAll("[data-f]").forEach(function (b) { b.onclick = function () { D.f = b.dataset.f; drawRes(); }; });
      shown = TOs.filter(match); var extra = D.f === "sel" ? D.pos.filter(function (p) { return !toOf(p); }) : [];
      q("#ton-res").innerHTML = (shown.length || extra.length ? shown.slice(0, 150).map(function (t) {
        var po = String(t.po).toUpperCase(), on = D.pos.indexOf(po) >= 0, ma = missAtt(t);
        return '<label class="ton-r' + (on ? " on" : "") + '"><input type="checkbox" data-p="' + E(po) + '" ' + (on ? "checked" : "") + '><span><b>' + E(po) + (t.stasiun ? " · " + E(t.stasiun) : "") + "</b><small>" + E((t.before || "-") + " → " + (t.after || "-")) + " · " + E(t.region || "-") + (ma.length ? ' · <em>belum: ' + E(ma.join(", ")) + "</em>" : "") + '</small></span><i class="ton-st ' + stCls(t) + '">' + E(stTxt(t)) + "</i></label>";
      }).join("") + extra.map(function (p) { return '<label class="ton-r on"><input type="checkbox" data-p="' + E(p) + '" checked><span><b>' + E(p) + "</b><small>tidak ada lagi di Data Takeover</small></span></label>"; }).join("") + (shown.length > 150 ? '<div class="st-more">+' + (shown.length - 150) + " PO lagi — persempit pencarian</div>" : "") : '<div class="ton-empty">Tidak ada PO yang cocok.</div>');
      q("#ton-res").querySelectorAll("[data-p]").forEach(function (cb) { cb.onchange = function () { var p = cb.dataset.p; D.pos = D.pos.filter(function (x) { return x !== p; }); if (cb.checked) D.pos.push(p); cb.closest(".ton-r").classList.toggle("on", cb.checked); cntTxt(); }; });
      cntTxt();
    }
    function cntTxt() { q("#ton-cnt").innerHTML = "<b>" + D.pos.length + "</b> dipilih"; var b = q('[data-f="sel"] i'); if (b) b.textContent = D.pos.length; }
    var tq; q("#ton-q").oninput = function () { clearTimeout(tq); var v = this.value; tq = setTimeout(function () { D.q = v.trim().toLowerCase(); drawRes(); }, 150); };
    q("[data-pickall]").onclick = function () { shown.slice(0, 150).forEach(function (t) { var p = String(t.po).toUpperCase(); if (D.pos.indexOf(p) < 0) D.pos.push(p); }); drawRes(); };
    q("[data-clear]").onclick = function () { D.pos = []; drawRes(); };
    var err = function (m) { var e = q("#ton-err"); e.textContent = m; e.classList.remove("hidden"); };
    q("#ton-save").onclick = async function () {
      var it = { id: D.id, t: q("#ton-t").value.trim(), m: q("#ton-m").value.trim(), pos: D.pos, to: D.to, w: q("#ton-w").checked, on: D.on, unread: !!(q("#ton-un") && q("#ton-un").checked) };
      if (!it.t) return err("Isi judul notifikasi."); if (!it.pos.length) return err("Pilih minimal satu PO takeover."); if (!it.to.length) return err("Pilih minimal satu akun penerima.");
      var b = this; b.disabled = true; b.innerHTML = '<i class="fa-solid fa-circle-notch fa-spin"></i>Menyimpan…';
      try { var r = await callApi("ton.save", { item: it }, 45000); replaceItem(r.item); TON.rev = ""; saveCache(); close(); changed(true); toast(D.id ? "Notifikasi takeover diperbarui" : "Notifikasi takeover terkirim ke " + (it.to[0] === "*" ? "semua akun" : it.to.length + " akun"), "success"); fetchTon(true); }
      catch (e) { b.disabled = false; b.innerHTML = '<i class="fa-solid fa-paper-plane"></i>' + (D.id ? "Simpan perubahan" : "Kirim notifikasi"); err(e.message); }
    };
    drawTo(); drawRes(); setTimeout(function () { q("#ton-t").focus(); }, 50);
  }
  window.tonEditor = editor;
  setInterval(function () { if (currentUser && document.visibilityState === "visible") fetchTon(false); }, 60000);
  setTimeout(function () { fetchTon(true); }, 3500);
  if (location.hostname === "localhost") window.__ton = { TON: TON, fetchTon: fetchTon, tonShow: tonShow, umCard: umCard, editor: editor, markRead: markRead };
})();

/* ===== v21 · Migrasi IKR (khusus Akun Utama) — verifikasi pengajuan dari sheet "Migrasi IKR" ===== */
(function () {
  var $ = function (i) { return document.getElementById(i); };
  var E = function (t) { return String(t == null ? "" : t).replace(/[&<>"']/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]; }); };
  var toast = function (m, t, ms) { try { showToast(m, t || "info", ms); } catch (e) { } };
  var isOwner = function () { return !!currentUser && currentUser.role === "owner"; };
  var srv = function () { try { return typeof isServerMode === "function" && isServerMode(); } catch (e) { return false; } };
  var nk = function (s) { return String(s || "").toUpperCase().replace(/\s+/g, ""); };
  var nm = function (s) { return String(s || "").toUpperCase().replace(/\b(PT|CV|TBK|STASIUN|ST)\b\.?/g, " ").replace(/[^A-Z0-9]+/g, " ").trim(); };
  var lev = function (a, b) { if (a === b) return 0; var m = a.length, n = b.length, d = []; for (var i = 0; i <= m; i++) { d[i] = [i]; } for (var j = 1; j <= n; j++) d[0][j] = j; for (i = 1; i <= m; i++) for (j = 1; j <= n; j++) d[i][j] = Math.min(d[i - 1][j] + 1, d[i][j - 1] + 1, d[i - 1][j - 1] + (a.charAt(i - 1) === b.charAt(j - 1) ? 0 : 1)); return d[m][n]; };
  var near1 = function (a, b) {   // toleran: spasi, PT/CV, salah ketik kecil (ALLIGATOR ~ ALIGATOR, OPTIK ~ OPTIC)
    a = nm(a); b = nm(b); if (!a || !b) return false;
    var ac = a.replace(/ /g, ""), bc = b.replace(/ /g, "");
    if (ac === bc || ac.indexOf(bc) >= 0 || bc.indexOf(ac) >= 0) return true;
    if (a.split(" ").sort().join(" ") === b.split(" ").sort().join(" ")) return true;   // urutan kata beda (KOPEGTEL)
    var L = Math.max(ac.length, bc.length); return L >= 6 && lev(ac, bc) / L <= 0.15;
  };
  var near = function (cand, val) { return String(cand || "").split(/[,;\/]+/).some(function (c) { return near1(c, val); }); };
  var PORTAL = "https://partner.starliteindonesia.com";
  var MIG = { rows: [], chk: {}, settings: { to: "", cc: "" }, loaded: false, loading: null, f: "wait", jenis: "", q: "", at: 0 };
  window.MIG = MIG;
  var VERIF_BAD = /^(Revisi|Tidak Sesuai|Done tidak sesuai)/i;
  function stOf(r) {
    if (/^done$/i.test(r.it)) return "done";
    if (/cancel/i.test(r.it)) return "cancel";
    if (/^(Done Verifikasi|Done Email IT)$/i.test(r.verif)) return "done";   // sudah diverifikasi / sudah dikirim ke IT = selesai
    if (/^Revisi/i.test(r.verif)) return "rev";
    if (VERIF_BAD.test(r.verif)) return "bad";   // Tidak Sesuai / Done tidak sesuai prosedure
    return "wait";
  }
  var ST = { wait: ["Menunggu verifikasi", "#d97706", "fa-hourglass-half"], rev: ["Revisi", "#ea580c", "fa-rotate-left"], bad: ["Tidak sesuai", "#e11d48", "fa-circle-xmark"], done: ["Selesai", "#059669", "fa-circle-check"], cancel: ["Batal (IT)", "#64748b", "fa-ban"] };
  function parseTs(s) { var m = String(s || "").match(/(\d{1,2})\/(\d{1,2})\/(\d{4})(?:\s+(\d{1,2}):(\d{2}))?/); return m ? new Date(+m[3], +m[2] - 1, +m[1], +(m[4] || 0), +(m[5] || 0)).getTime() : 0; }
  function ago(ts) { if (!ts) return ""; var d = Math.floor((Date.now() - ts) / 864e5); return d <= 0 ? "hari ini" : d + " hari"; }
  function chkOf(r) { return MIG.chk[r.ck] || {}; }
  function rowKey(r) { return r.ts + "|" + nk(r.noSpk); }
  // ---------- data ----------
  async function load(force) {
    if (!isOwner() || !srv() || MIG.off) return;
    if (MIG.loading) return MIG.loading;
    if (!force && MIG.loaded && Date.now() - MIG.at < 120000) return;
    MIG.loading = (async function () {
      try {
        var r = await callApi("mig.list", {}, 60000);
        MIG.rows = (r.rows || []).map(function (x) { x.tsMs = parseTs(x.ts); return x; });
        MIG.chk = r.chk || {}; MIG.settings = r.settings || MIG.settings; MIG.hasKey = !!r.formKey;
        MIG.loaded = true; MIG.at = Date.now(); MIG.err = "";
      } catch (e) {
        MIG.err = e.message; MIG.loaded = true; MIG.at = Date.now();   // berhenti memuat, tampilkan pesan sekali (tidak berulang)
        if (/tidak dikenal|unknown action/i.test(e.message)) MIG.off = true;   // Code.gs di server belum versi Migrasi IKR
      }
      finally { MIG.loading = null; badge(); if (isOpen()) render(); }
    })();
    return MIG.loading;
  }
  async function keyOf(r) { return r.ck; }
  async function keyAll() { for (var i = 0; i < MIG.rows.length; i++) await keyOf(MIG.rows[i]); }
  // ---------- pencocokan dengan Data Mitra Takeover & Tracker ----------
  var spkKey = function (s) { var k = nk(s); return /\d/.test(k) ? k : ""; };   // "-" / kosong bukan nomor SPK
  // nomor urut SPK + tahun: "1547/PRJ/STARLITE/IX/2026", "1547 SPK TAKE OVER … .pdf", "1547/PRJ/STARLITE,'D0'2026" → 1547 (+2026)
  var spkNum = function (s) { var m = String(s || "").match(/^\s*0*(\d{1,5})(?=\D|$)/); if (!m) return null; var y = String(s).match(/20\d\d(?!.*20\d\d)/); return { n: m[1], y: y ? y[0] : "" }; };
  var poOf = function (s) { return (String(s || "").toUpperCase().match(/PO\.[A-Z0-9.]+/g) || []).map(function (p) { return p.replace(/\.+$/, ""); }); };
  function matchBy(list, field, r) {
    var k = spkKey(r.noSpk); if (!k) return { rows: [], how: "" };
    var ex = list.filter(function (x) { return nk(x[field]) === k; }); if (ex.length) return { rows: ex, how: "" };
    var a = spkNum(r.noSpk);
    if (a) { var nu = list.filter(function (x) { var b = spkNum(x[field]); return b && b.n === a.n && (!a.y || !b.y || a.y === b.y); }); if (nu.length) return { rows: nu, how: "nomor" }; }
    var ps = poOf(r.noSpk);   // mitra mengisi No PO di kolom No SPK
    if (ps.length) { var pp = list.filter(function (x) { var q = poOf(x.po); return ps.some(function (p) { return q.indexOf(p) >= 0; }); }); if (pp.length) return { rows: pp, how: "po" }; }
    return { rows: [], how: "" };
  }
  function toRows(r) { return matchBy(STATE.takeover || [], "att_spk", r).rows; }
  function spkRows(r) { return matchBy(STATE.spk || [], "no_spk", r).rows; }
  // Tracker All Starlite: PO dari SPK / Data Mitra Takeover + baris yang stasiunnya sama DAN mitranya = mitra lama / pengganti
  function trkHp(pos, r) {
    var rows = (typeof TRK !== "undefined" && TRK.rows) || [], set = {}, seen = {}, hit = [], byPo = 0, byNm = 0; pos.forEach(function (p) { set[nk(p)] = 1; });
    rows.forEach(function (x) {
      var k = nk(x.po), a = !!set[k], b = !!(r && x.stasiun && near1(x.stasiun, r.stasiun) && (near1(x.after, r.baru) || near1(x.after, r.lama) || near1(x.before, r.lama)));
      if (!(a || b) || (k && seen[k])) return; if (k) seen[k] = 1; hit.push(x); if (a) byPo++; else byNm++;
    });
    return { n: hit.length, hp: hit.reduce(function (a, x) { return a + (+String(x.hp).replace(/[^\d]/g, "") || 0); }, 0), pos: hit.map(function (x) { return x.po + " (" + (+String(x.hp).replace(/[^\d]/g, "") || 0) + ")"; }), byPo: byPo, byNm: byNm };
  }
  // SPK lain yang cocok dengan stasiun + mitra pengganti pengajuan (saran bila No SPK salah / kosong)
  function suggestSpk(r, exclude) {
    var out = [], add = function (no, st, lama, baru) { var n = spkNum(no); if (!n) return; var lbl = /\/PRJ\//i.test(no) ? String(no).trim() : n.n; if (exclude && spkNum(exclude) && spkNum(exclude).n === n.n) return; if (out.some(function (o) { return spkNum(o.no).n === n.n; })) return; out.push({ no: lbl, txt: (lama || "-") + " → " + baru + " · " + st }); };
    (STATE.spk || []).forEach(function (x) { if (near(x.stasiun, r.stasiun) && near(x.mitra, r.baru)) add(x.no_spk, x.stasiun, x.prev, x.mitra); });
    (STATE.takeover || []).forEach(function (t) { if (near(t.stasiun, r.stasiun) && near(t.after, r.baru)) add(t.att_spk, t.stasiun, t.before, t.after); });
    out.sort(function (a, b) { return (/,/.test(a.txt) ? 1 : 0) - (/,/.test(b.txt) ? 1 : 0); });
    return out.slice(0, 3);
  }
  function holderOf(r) {   // SPK lain di stasiun yang sama dengan mitra pengganti = Mitra Lama pengajuan
    var a = (STATE.spk || []).filter(function (x) { return near(x.stasiun, r.stasiun) && near(x.mitra, r.lama); }).map(function (x) { return String(x.no_spk).trim(); });
    (STATE.takeover || []).forEach(function (t) { if (near(t.stasiun, r.stasiun) && near(t.after, r.lama) && spkNum(t.att_spk)) a.push(/\/PRJ\//i.test(t.att_spk) ? String(t.att_spk).trim() : spkNum(t.att_spk).n); });
    var own = spkNum(r.noSpk); a = a.filter(function (x, i) { return x && a.indexOf(x) === i && !(own && spkNum(x) && spkNum(x).n === own.n); }); return a.slice(0, 3).join(", ");
  }
  function autoChecks(r) {
    var mT = matchBy(STATE.takeover || [], "att_spk", r), mK = matchBy(STATE.spk || [], "no_spk", r), T = mT.rows, K = mK.rows, out = [];
    // sumber 1: Data Mitra Takeover (kolom Q = No SPK) · sumber 2: All SPK (TRACKER SPK VM)
    var src = T.length && K.length ? "Data Mitra Takeover & All SPK" : T.length ? "Data Mitra Takeover" : K.length ? "All SPK" : "";
    var how = mK.how || mT.how;
    var pos = []; T.concat(K).forEach(function (x) { poOf(x.po).forEach(function (p) { if (pos.indexOf(p) < 0) pos.push(p); }); });
    var sug = function () { var s = suggestSpk(r, src ? r.noSpk : ""); return s.length ? " · SPK yang cocok dengan stasiun & mitra ini: " + s.map(function (x) { return x.no + " (" + x.txt + ")"; }).join("; ") : ""; };
    if (src) out.push({ ok: how === "po" ? false : true, t: how === "po" ? "Kolom No SPK berisi nomor PO, bukan nomor SPK" : "No SPK ditemukan di " + src, d: (how === "nomor" ? "dicocokkan dari nomor urut (penulisan berbeda) · " : "") + (pos.length ? pos.length + " PO: " + pos.join(", ") : "tanpa nomor PO") + (how === "po" ? sug() : "") });
    else out.push({ ok: false, t: r.noSpk && spkKey(r.noSpk) ? "No SPK tidak ditemukan di Data Mitra Takeover maupun All SPK" : "No SPK tidak diisi", d: (r.noSpk || "(kosong)") + sug() });
    if (src) {
      var uniq = function (a) { return a.filter(function (c, i) { return a.indexOf(c) === i; }); };
      var lamaC = uniq(T.map(function (t) { return t.before; }).concat(K.map(function (x) { return x.prev; })).filter(function (x) { return x && x !== "-"; }));
      var baruC = uniq(T.map(function (t) { return t.after; }).concat(K.map(function (x) { return x.mitra; })).filter(Boolean));
      var stC = uniq(T.map(function (t) { return t.stasiun; }).concat(K.map(function (x) { return x.stasiun; })).filter(Boolean));
      var hit = function (cands, val) { return cands.some(function (c) { return near(c, val); }); };
      var chk = function (label, val, cands) { if (!cands.length) return { ok: null, t: label, d: val + " (pembanding tidak ada di data)" }; var ok = hit(cands, val); return { ok: ok, t: label, d: val + (ok ? "" : " ≠ di SPK: " + cands.join(" / ")) }; };
      var cL = chk("Mitra Lama", r.lama, lamaC), cB = chk("Mitra Pengganti", r.baru, baruC), cS = chk("Stasiun", r.stasiun, stC);
      if (cL.ok === false && cB.ok === false && hit(baruC, r.lama) && hit(lamaC, r.baru)) { out.push({ ok: false, t: "Mitra Lama & Mitra Pengganti tertukar", d: "Pengajuan: " + r.lama + " → " + r.baru + " · di SPK: " + lamaC.join(" / ") + " → " + baruC.join(" / ") }); }
      else {
        // Mitra Lama tak sama dengan "mitra sebelum" di SPK ini, tapi tercatat sebagai pemegang stasiun ini di SPK lain (rantai takeover)
        if (near1(r.lama, r.baru)) { cL.ok = false; cL.t = "Mitra Lama sama dengan Mitra Pengganti"; cL.d = r.lama + " → " + r.baru + (lamaC.length ? " · di SPK mitra lama: " + lamaC.join(" / ") : ""); }
        else if (cL.ok === false) { var hold = holderOf(r); if (hold) { cL.ok = null; cL.t = "Mitra Lama (perlu dicek)"; cL.d = r.lama + " tercatat memegang stasiun ini di SPK " + hold + " · di SPK pengajuan tertulis: " + lamaC.join(" / "); } }
        out.push(cL); out.push(cB);
      }
      if (cS.ok === false) cS.d += sug();
      out.push(cS);
    }
    var h = trkHp(pos, r);
    out.push({ ok: null, t: "HP Actual (Tracker All Starlite, opsional)", d: h.n ? h.hp.toLocaleString("id-ID") + " HP dari " + h.n + " PO" + (h.n > 1 ? " (dijumlahkan)" : "") + ": " + h.pos.join(", ") + " · cocok " + [h.byPo ? h.byPo + " dari No SPK/Takeover" : "", h.byNm ? h.byNm + " dari nama mitra & stasiun" : ""].filter(Boolean).join(", ") : "Tidak ada PO di Tracker untuk stasiun " + r.stasiun + " dengan mitra lama / pengganti ini" });
    out.push({ ok: /^https?:/i.test(r.ba), t: "BA Pemindahan Akun & capture dashboard", d: r.ba ? "terlampir" : "tidak ada" });
    out.push({ ok: /^https?:/i.test(r.kml), t: "File KML stasiun tujuan", d: r.kml ? "terlampir" : "tidak ada" });
    out.push({ ok: /^https?:/i.test(r.spk), t: "File SPK", d: r.spk ? "terlampir" : "tidak ada" });
    return { list: out, T: T, K: K };
  }
  function hcStart() { return "2025-01-01"; }   // HC dihitung dari 1 Januari 2025 sampai hari ini
  var today = function () { var d = new Date(); return new Date(d.getTime() - d.getTimezoneOffset() * 6e4).toISOString().slice(0, 10); };
  // ---------- email ke IT ----------
  function mails(s) { return (String(s || "").match(/[^\s<>";,]+@[^\s<>";,]+/g) || []).filter(function (x, i, a) { return a.indexOf(x) === i; }); }
  // nama resmi mitra dari Info Perseroan (kolom B); bila tidak ketemu, pakai yang diisi mitra
  function offName(x) {
    var P = (STATE.perseroan || []), k = nm(x).replace(/ /g, ""), i;
    if (!k) return x;
    for (i = 0; i < P.length; i++) if (nm(P[i].nama).replace(/ /g, "") === k || nm(P[i].short).replace(/ /g, "") === k) return P[i].nama || x;
    for (i = 0; i < P.length; i++) if (near1(P[i].nama, x)) return P[i].nama;
    return x;
  }
  function itSubject(r) { return "PERPINDAHAN AKUN - " + offName(r.baru) + " - " + r.stasiun; }
  function itBody(r) {
    return "Yth. Team IT\n\nBerikut permintaan perpindahan Akun:\n\nMitra Lama          : " + offName(r.lama) + "\nMitra Baru          : " + offName(r.baru) + "\nNama Stasiun        : " + r.stasiun + "\nNo SPK              : " + r.noSpk + (r.spk ? " (" + r.spk + ")" : "")
      + "\n\nSebagai pemenuhan syarat administrasi, bersama email ini kami lampirkan dokumen-dokumen pendukung sebagai berikut:\n\n1. Berita Acara Pemindahan Akun IKR: Terlampir" + (r.ba ? " (" + r.ba + ")" : "")
      + "\n2. File KML stasiun yang dituju: " + (r.kml || "-") + "\n3. Akun email penampung: " + (r.sales || "-") + "\n4. Akun email Lead IKR mitra lama: " + (r.ikrLama || "-") + "\n5. Akun email Lead IKR mitra baru: " + (r.ikrBaru || "-")
      + "\n\nMohon untuk segera di proses perpindahan akun.\n\nBest Regards\nVendor Management";
  }
  // buka di tab browser bernama (dipakai ulang tiap klik) — tanpa jendela pop-up berukuran khusus (pop-up layar penuh tampil hitam di sebagian laptop)
  function side(url, name) {
    var win = null; try { win = window.open(url, name); } catch (e) { }
    if (!win) { window.open(url, "_blank", "noopener"); return; }
    try { win.opener = null; win.focus(); } catch (e) { }
  }
  function outlookUrl(r) {
    var q = "to=" + encodeURIComponent(mails(MIG.settings.to).join(";")) + "&cc=" + encodeURIComponent(mails(MIG.settings.cc).join(";")) + "&subject=" + encodeURIComponent(itSubject(r)) + "&body=" + encodeURIComponent(itBody(r));
    var from = String(MIG.settings.from || "vendormanagement@pmosurge.co.id").trim();
    return "https://outlook.office.com/mail/deeplink/compose?" + q + (from ? "&login_hint=" + encodeURIComponent(from) : "");
  }
  function waUrl(r, text) { var n = String(r.wa || "").replace(/\D/g, "").replace(/^0/, "62"); return "https://wa.me/" + n + "?text=" + encodeURIComponent(text); }
  // ---------- tampilan ----------
  function isOpen() { var v = $("view-migrasi"); return v && !v.classList.contains("hidden"); }
  function ensureUi() {
    if (!isOwner()) { var n0 = $("nav-migrasi"); n0 && n0.classList.add("hidden"); return; }
    var nt = $("nav-takeover");
    if (nt && !$("nav-migrasi")) {
      var b = document.createElement("button"); b.id = "nav-migrasi"; b.title = "Migrasi IKR"; b.className = nt.className; b.setAttribute("onclick", "switchTab('migrasi')");
      b.innerHTML = '<div class="flex items-center gap-3"><i class="fa-solid fa-people-arrows text-sm shrink-0 group-hover:scale-110 transition-transform"></i><span class="sidebar-text">Migrasi IKR</span></div><span id="sidebar-migrasi-badge" class="sidebar-text text-[10px] font-mono px-2 py-0.5 rounded-full bg-amber-500/15 text-amber-700 dark:text-amber-300 hidden">0</span>';
      nt.after(b);
    }
    var n = $("nav-migrasi"); n && n.classList.remove("hidden");
    var th = document.querySelector('#desk-top .tb-actions [onclick^="toggleTheme"]');
    if (th && !$("mig-tb")) {
      var tb = document.createElement("div"); tb.id = "mig-tb"; tb.className = "mig-tb hidden";
      tb.innerHTML = '<button class="tb-btn" data-t="reload" title="Muat ulang pengajuan"><i class="fa-solid fa-rotate"></i></button><button class="tb-btn" data-t="form" title="Link form mitra"><i class="fa-solid fa-link"></i></button><button class="tb-btn" data-t="set" title="Penerima email IT"><i class="fa-solid fa-envelope"></i></button>';
      th.before(tb);
      tb.querySelector('[data-t="reload"]').onclick = reloadNow; tb.querySelector('[data-t="form"]').onclick = function () { formLink(); }; tb.querySelector('[data-t="set"]').onclick = function () { settings(); };
    }
    var vt = $("view-takeover");
    if (vt && !$("view-migrasi")) { var v = document.createElement("section"); v.id = "view-migrasi"; v.className = "tab-view hidden space-y-5"; vt.after(v); }
  }
  function reloadNow() { MIG.off = false; MIG.err = ""; MIG.loaded = false; render(); load(true).then(function () { if (!MIG.err) toast("Pengajuan Migrasi IKR dimuat ulang", "success"); }); }
  function badge() { var b = $("sidebar-migrasi-badge"); if (!b) return; var n = MIG.rows.filter(function (r) { return stOf(r) === "wait"; }).length; b.textContent = n; b.classList.toggle("hidden", !n); }
  function filtered() {
    var q = String(MIG.q || "").trim().toLowerCase().replace(/\s+/g, " ");
    return MIG.rows.filter(function (r) {
      if (MIG.f !== "all" && stOf(r) !== MIG.f) return false;
      if (MIG.jenis && r.tujuan !== MIG.jenis) return false;
      if (q && [r.lama, r.baru, r.stasiun, r.noSpk, r.nama, r.email, r.sales, r.ikrBaru].join(" ").toLowerCase().indexOf(q) < 0) return false;
      return true;
    }).sort(function (a, b) { return b.tsMs - a.tsMs; });
  }
  function chip(k) { var s = ST[k]; return '<span class="mig-chip" style="--c:' + s[1] + '"><i class="fa-solid ' + s[2] + '"></i>' + s[0] + "</span>"; }
  function render() {
    var v = $("view-migrasi"); if (!v) return;
    var cnt = { wait: 0, rev: 0, bad: 0, done: 0, cancel: 0 }; MIG.rows.forEach(function (r) { cnt[stOf(r)]++; });
    var L = filtered();
    var card = function (k) { var s = ST[k]; return '<button class="mig-card' + (MIG.f === k ? " on" : "") + '" data-f="' + k + '" style="--c:' + s[1] + '"><i class="fa-solid ' + s[2] + '"></i><b>' + cnt[k] + "</b><span>" + s[0] + "</span></button>"; };
    v.innerHTML = '<div class="glass-panel rounded-2xl p-4 mig-head"><div><h2>Migrasi IKR</h2><p>Verifikasi pengajuan perpindahan akun IKR dan Create Stasiun · data dari sheet <b>Migrasi IKR</b>' + (MIG.at ? " · dimuat " + new Date(MIG.at).toLocaleTimeString("id-ID", { hour: "2-digit", minute: "2-digit" }) : "") + "</p></div>"
      + '<div class="mig-acts"><button class="btn btn-ghost" data-a="reload" title="Muat ulang"><i class="fa-solid fa-rotate"></i><span>Muat ulang</span></button><button class="btn btn-ghost" data-a="form"><i class="fa-solid fa-link"></i><span>Link form mitra</span></button><button class="btn btn-ghost" data-a="set"><i class="fa-solid fa-envelope"></i><span>Penerima email IT</span></button></div></div>'
      + (MIG.off ? '<div class="mig-off"><i class="fa-solid fa-plug-circle-xmark"></i><div><b>Server belum mendukung Migrasi IKR</b><p>Code.gs di Apps Script masih versi lama. Fitur ini aktif setelah Code.gs terbaru dipasang dan deployment diperbarui.</p></div></div>'
        : MIG.err ? '<div class="mig-err"><i class="fa-solid fa-triangle-exclamation"></i>Gagal memuat pengajuan: ' + E(MIG.err) + ' · klik Muat ulang untuk mencoba lagi</div>' : "")
      + (MIG.off ? "" : '<div class="mig-cards">' + ["wait", "rev", "bad", "done"].map(card).join("") + '<button class="mig-card' + (MIG.f === "all" ? " on" : "") + '" data-f="all" style="--c:#475569"><i class="fa-solid fa-layer-group"></i><b>' + MIG.rows.length + "</b><span>Semua</span></button></div>"
      + '<div class="glass-panel rounded-2xl p-4 space-y-3"><div class="flex flex-wrap gap-2"><div class="relative flex-1 min-w-[220px]"><i class="fa-solid fa-magnifying-glass absolute left-3 top-1/2 -translate-y-1/2 text-slate-400 text-xs"></i><input id="mig-q" class="field w-full pl-9" placeholder="Cari mitra, stasiun, No SPK, pengaju, email…" value="' + E(MIG.q) + '"></div><select id="mig-jenis" class="field"><option value="">Semua jenis</option><option' + (MIG.jenis === "Migrasi Akun IKR" ? " selected" : "") + '>Migrasi Akun IKR</option><option' + (MIG.jenis === "Create Stasiun (Stasiun Take Over)" ? " selected" : "") + ">Create Stasiun (Stasiun Take Over)</option></select></div>"
      + (!MIG.loaded ? '<div class="mig-empty"><i class="fa-solid fa-circle-notch fa-spin"></i>Memuat pengajuan…</div>' : L.length ? '<div class="mig-list">' + L.map(function (r) {
        var k = stOf(r), em = chkOf(r).emailAt ? Date.parse(chkOf(r).emailAt) : 0, late = k === "it" && em && Date.now() - em > 7 * 864e5;
        return '<button class="mig-row" data-row="' + r.row + '"><span class="mig-d">' + E(r.ts.split(" ")[0]) + "<small>" + ago(r.tsMs) + '</small></span><span class="mig-m"><b>' + E(r.baru || "-") + " · " + E(r.stasiun || "-") + "</b><small>dari " + E(r.lama || "-") + " · " + E(r.noSpk || "tanpa No SPK") + " · " + (/create/i.test(r.tujuan) ? "Create Stasiun" : "Migrasi Akun") + "</small></span>" + chip(k) + (late ? '<span class="mig-late" title="Status IT masih kosong > 7 hari setelah email">IT > 7 hari</span>' : "") + "</button>";
      }).join("") + "</div>" : '<div class="mig-empty"><i class="fa-regular fa-folder-open"></i>Tidak ada pengajuan pada filter ini.</div>') + "</div>");
    if (MIG.off) { v.querySelector('[data-a="reload"]').onclick = reloadNow; v.querySelector('[data-a="form"]').onclick = formLink; v.querySelector('[data-a="set"]').onclick = settings; return; }
    v.querySelectorAll("[data-f]").forEach(function (b) { b.onclick = function () { MIG.f = b.dataset.f; render(); }; });
    v.querySelectorAll("[data-row]").forEach(function (b) { b.onclick = function () { openDetail(+b.dataset.row); }; });
    var t; $("mig-q").oninput = function () {
      clearTimeout(t); var x = this; MIG.q = x.value;   // spasi tetap (tidak di-trim saat mengetik)
      t = setTimeout(function () { var pos = x.selectionStart, end = x.selectionEnd; render(); var y = $("mig-q"); y.value = MIG.q; y.focus(); try { y.setSelectionRange(pos, end); } catch (e) { } }, 250);
    };
    $("mig-jenis").onchange = function () { MIG.jenis = this.value; render(); };
    v.querySelector('[data-a="reload"]').onclick = reloadNow;
    v.querySelector('[data-a="form"]').onclick = formLink;
    v.querySelector('[data-a="set"]').onclick = settings;
  }
  // ---------- modal ----------
  function modal(html, cls) {
    var old = $("mig-ov"); old && old.remove();
    var ov = document.createElement("div"); ov.id = "mig-ov"; ov.className = "mig-ov"; ov.innerHTML = '<div class="mig-card-m ' + (cls || "") + '" role="dialog" aria-modal="true">' + html + "</div>";
    document.body.appendChild(ov);
    var close = function () { ov.remove(); document.removeEventListener("keydown", esc); };
    var esc = function (e) { if (e.key === "Escape") close(); }; document.addEventListener("keydown", esc);
    ov.onclick = function (e) { if (e.target === ov) close(); };
    ov.querySelectorAll("[data-x]").forEach(function (b) { b.onclick = close; });
    return { el: ov, close: close };
  }
  async function openDetail(rowNo) {
    var r = MIG.rows.filter(function (x) { return x.row === rowNo; })[0]; if (!r) return;
    await keyOf(r);
    var A = autoChecks(r), T = A.T, K = A.K, c = chkOf(r), it = c.items || {}, k = stOf(r);
    var st = hcStart(r, T, K), en = today();
    var lnk = function (u, t) { return u ? '<a href="' + E(u) + '" target="_blank" rel="noopener" class="mig-lnk"><i class="fa-solid fa-arrow-up-right-from-square"></i>' + t + "</a>" : '<span class="mig-none">' + t + " — tidak ada</span>"; };
    var CK = [["hc", "HC sama persis dengan menu Pelanggan Aktif di portal (capture dashboard)"], ["ikr", "Akun Lead IKR mitra pengganti ada & aktif"], ["sales", "Akun Sales penampung ada & aktif"], ["dok", "BA, KML, dan SPK lengkap dan benar"]];
    var M = modal('<div class="mig-mh"><div><small>' + E(r.tujuan) + " · diajukan " + E(r.ts) + "</small><h3>" + E(r.baru) + " · " + E(r.stasiun) + "</h3><p>dari <b>" + E(r.lama) + "</b> · No SPK <b>" + E(r.noSpk || "-") + "</b></p></div>" + chip(k) + '<button class="mig-ed" data-edit title="Ubah data pengajuan"><i class="fa-solid fa-pen"></i><span>Ubah data</span></button><button class="x" data-x title="Tutup"><i class="fa-solid fa-xmark"></i></button></div>'
      + '<div class="mig-mb"><div class="mig-col">'
      + '<section><h4>Pengaju</h4><p><b>' + E(r.nama) + "</b> · " + E(r.jabatan) + "<br>" + E(r.email) + (r.wa ? ' · <a class="mig-lnk" target="_blank" rel="noopener" href="' + E(waUrl(r, "")) + '"><i class="fa-brands fa-whatsapp"></i>' + E(r.wa) + "</a>" : "") + "</p></section>"
      + '<section><h4>Akun</h4><dl class="mig-dl"><dt>Sales penampung</dt><dd>' + E(r.sales || "-") + "</dd><dt>Lead IKR mitra lama</dt><dd>" + E(r.ikrLama || "-") + "</dd><dt>Lead IKR mitra pengganti</dt><dd>" + E(r.ikrBaru || "-") + "</dd></dl></section>"
      + '<section><h4>Dokumen</h4><div class="mig-docs">' + lnk(r.ba, "BA & capture dashboard") + lnk(r.kml, "File KML") + lnk(r.spk, "SPK") + "</div>"
      + '<div class="mig-batools"><button class="st-b" data-ba="edit"' + (r.ba ? "" : " disabled") + '><i class="fa-solid fa-pen-to-square"></i>Edit BA (PDF)</button><button class="st-b" data-ba="add"><i class="fa-solid fa-file-circle-plus"></i>Tambah file / capture ke BA</button></div></section>'
      + '<section><h4>Cek otomatis</h4><ul class="mig-auto">' + A.list.map(function (x) { return '<li class="' + (x.ok === true ? "ok" : x.ok === false ? "bad" : "info") + '"><i class="fa-solid ' + (x.ok === true ? "fa-circle-check" : x.ok === false ? "fa-circle-xmark" : "fa-circle-info") + '"></i><span><b>' + E(x.t) + "</b><small>" + E(x.d) + "</small></span></li>"; }).join("") + "</ul></section>"
      + (c.h && c.h.length ? '<section><h4>Riwayat</h4><ul class="mig-hist">' + c.h.slice().reverse().map(function (h) { return "<li><b>" + E(h.act) + "</b> · " + E(h.by) + " · " + E(new Date(h.at).toLocaleString("id-ID", { day: "2-digit", month: "short", hour: "2-digit", minute: "2-digit" })) + (h.note ? "<br><small>" + E(h.note) + "</small>" : "") + "</li>"; }).join("") + "</ul></section>" : "")
      + '</div><div class="mig-col">'
      + '<section><h4>Cek di portal</h4><div class="mig-range"><label>Dari<input type="date" id="mig-d1" class="field" value="' + st + '"></label><label>Sampai<input type="date" id="mig-d2" class="field" value="' + en + '"></label></div>'
      + '<div class="mig-portal"><button class="st-b" data-p="hc"><i class="fa-solid fa-users"></i>Cek HC · Pelanggan Aktif</button><button class="st-b" data-p="ikr"><i class="fa-solid fa-screwdriver-wrench"></i>Cek Lead IKR</button><button class="st-b" data-p="sales"><i class="fa-solid fa-user-tie"></i>Cek Lead Sales</button></div><p class="mig-note">Portal terbuka di tab browser tersendiri (tab yang sama dipakai ulang) dengan login portal Anda — cukup login sekali, aplikasi ini tetap terbuka di tab-nya. Untuk Lead IKR / Sales, email akunnya otomatis disalin — tempel di kolom cari portal.</p></section>'
      + '<section><h4>Checklist verifikator</h4><div class="mig-ck">' + CK.map(function (x) { return '<label><input type="checkbox" data-ck="' + x[0] + '"' + (it[x[0]] === true ? " checked" : "") + "><span>" + x[1] + "</span></label>"; }).join("") + '</div><label class="mig-hc">HC di portal (opsional)<input id="mig-hcv" class="field" inputmode="numeric" placeholder="mis. 53" value="' + E(c.hc || "") + '"></label></section>'
      + '<section><h4>Keputusan</h4><textarea id="mig-rem" class="field w-full" rows="3" placeholder="Catatan untuk mitra (wajib bila Revisi / Tidak Sesuai)">' + E(r.remark || "") + '</textarea><div class="mig-dec"><button class="st-b dng" data-d="Tidak Sesuai"><i class="fa-solid fa-ban"></i>Tidak Sesuai</button><button class="st-b warn" data-d="Revisi"><i class="fa-solid fa-rotate-left"></i>Revisi</button><button class="st-b pri" data-d="lolos"><i class="fa-solid fa-circle-check"></i>Lolos → Kirim ke IT</button></div><p class="mig-st">Status Verifikasi (kolom R): <b>' + E(r.verif || "—") + "</b> · Status IT (kolom S): <b>" + E(r.it || "—") + "</b></p></section>"
      + "</div></div>", "lg");
    var el = M.el, q = function (s) { return el.querySelector(s); };
    var items = function () { var o = {}; el.querySelectorAll("[data-ck]").forEach(function (cb) { o[cb.dataset.ck] = cb.checked; }); return o; };
    el.querySelectorAll("[data-p]").forEach(function (b) {
      b.onclick = function () {
        var p = b.dataset.p, url;
        if (p === "hc") url = PORTAL + "/admin/customer-overview/active?date_start=" + q("#mig-d1").value + "&date_end=" + q("#mig-d2").value;
        else { url = PORTAL + (p === "ikr" ? "/admin/ikr-management" : "/admin/sales-management"); var em = p === "ikr" ? r.ikrBaru : r.sales; if (em) { try { var pr = navigator.clipboard && navigator.clipboard.writeText(em); if (pr && pr.then) pr.then(function () { toast("Email " + em + " disalin — tempel di kolom cari portal", "info", 5000); }, function () { toast("Email akun: " + em, "info", 8000); }); } catch (e) { toast("Email akun: " + em, "info", 8000); } } }
        side(url, "starlite-portal");
      };
    });
    el.querySelector("[data-edit]").onclick = function () { editData(r); };
    el.querySelectorAll("[data-ba]").forEach(function (b) { b.onclick = function () { if (b.dataset.ba === "edit") baEdit(r, []); else baAdd(r); }; });
    var save = async function (verif, remark, extra) {
      var res = await callApi("mig.save", Object.assign({ row: r.row, ts: r.ts, noSpk: r.noSpk, verif: verif, remark: remark, chk: items(), hc: q("#mig-hcv").value.trim() }, extra || {}), 60000);
      if (res.item) { Object.assign(r, res.item); }
      if (res.chk) { MIG.chk[res.chk.key] = res.chk.value; r.ck = res.chk.key; }
      badge(); if (isOpen()) render();
      return res;
    };
    el.querySelectorAll("[data-ck]").forEach(function (cb) { cb.onchange = function () { save(undefined, undefined).catch(function (e) { toast(e.message, "error", 7000); }); }; });
    el.querySelectorAll("[data-d]").forEach(function (b) {
      b.onclick = async function () {
        var d = b.dataset.d, its = items(), miss = CK.filter(function (x) { return !its[x[0]]; });
        if (d === "lolos") {
          if (miss.length) return toast("Belum semua checklist dicentang: " + miss.map(function (x) { return x[1]; }).join("; "), "error", 7000);
          return emailIt(r, T, function () { M.close(); });
        }
        var rem = q("#mig-rem").value.trim();
        if (!rem) { rem = "Mohon diperbaiki: " + (miss.length ? miss.map(function (x) { return x[1]; }).join("; ") : "-"); q("#mig-rem").value = rem; return toast("Catatan terisi otomatis dari checklist — periksa lalu klik lagi", "info", 5000); }
        b.disabled = true;
        try {
          await save(d, rem, { note: rem.slice(0, 200) });
          toast("Status Verifikasi: " + d, "success");
          var link = await formUrl();
          var msg = "Yth. " + (r.nama || "Bapak/Ibu") + ",\n\nPengajuan " + r.tujuan + " " + r.baru + " – " + r.stasiun + " (No SPK " + r.noSpk + ") berstatus " + d.toUpperCase() + ".\nCatatan: " + rem + "\n\nMohon perbaiki dan ajukan ulang melalui link berikut:\n" + (link || "(link form pengajuan)") + "\n\nVendor Management";
          M.close(); revisiShare(r, msg);
        } catch (e) { b.disabled = false; toast(e.message, "error", 7000); }
      };
    });
  }
  // ---------- BA: edit di Edit PDF, tambah file / capture ----------
  var b64ToFile = function (x) { var bin = atob(x.b64), u = new Uint8Array(bin.length); for (var i = 0; i < bin.length; i++) u[i] = bin.charCodeAt(i); var nm = x.name || "BA.pdf"; return new File([u], nm, { type: x.mime || (/\.pdf$/i.test(nm) ? "application/pdf" : "application/octet-stream") }); };
  async function baFiles(r) {
    if (!r.ba) return [];
    var res = await callApi("mig.bafile", { row: r.row, ts: r.ts, noSpk: r.noSpk }, 120000);
    return (res.files || []).map(b64ToFile);
  }
  async function baEdit(r, extra) {
    if (typeof window.peOpen !== "function") return toast("Fitur Edit PDF tidak tersedia di akun ini", "error");
    toast("Mengambil BA dari Drive…", "info", 3000);
    try {
      var files = (await baFiles(r)).concat(extra || []);
      if (!files.length) return toast("Tidak ada BA / file untuk dibuka", "error");
      var ov = $("mig-ov"); ov && ov.remove();
      MIG.baRow = r.row;
      window.__peOpenOpt({ kind: "mig", id: String(r.row), mode: "edit", files: files, title: "Edit BA · " + r.baru + " · " + r.stasiun });
    } catch (e) { toast("Gagal membuka BA: " + e.message, "error", 8000); }
  }
  window.__migBaSave = async function (file, rowId) {
    var r = MIG.rows.filter(function (x) { return String(x.row) === String(rowId); })[0]; if (!r) return toast("Pengajuan tidak ditemukan — klik Muat ulang", "error");
    try {
      var buf = new Uint8Array(await file.arrayBuffer()), bin = "", CH = 0x8000;
      for (var i = 0; i < buf.length; i += CH) bin += String.fromCharCode.apply(null, buf.subarray(i, i + CH));
      var res = await callApi("mig.ba", { row: r.row, ts: r.ts, noSpk: r.noSpk, fileBase64: btoa(bin) }, 180000);
      if (res.item) Object.assign(r, res.item); if (res.chk) { MIG.chk[res.chk.key] = res.chk.value; r.ck = res.chk.key; }
      toast("BA baru tersimpan di Drive & kolom M · BA lama tetap tersimpan", "success", 6000);
      try { switchTab("migrasi"); } catch (e) { } openDetail(r.row);
    } catch (e) { toast("Gagal menyimpan BA: " + e.message, "error", 9000); try { switchTab("migrasi"); } catch (er) { } openDetail(r.row); }
  };
  async function grabScreen() {
    if (!navigator.mediaDevices || !navigator.mediaDevices.getDisplayMedia) throw new Error("Browser ini tidak mendukung capture layar — pakai Win+Shift+S lalu tempel (Ctrl+V)");
    var st = await navigator.mediaDevices.getDisplayMedia({ video: { displaySurface: "window" }, audio: false });
    try {
      var v = document.createElement("video"); v.muted = true; v.srcObject = st; await v.play(); await new Promise(function (r) { setTimeout(r, 400); });
      var c = document.createElement("canvas"); c.width = v.videoWidth; c.height = v.videoHeight; c.getContext("2d").drawImage(v, 0, 0);
      var blob = await new Promise(function (r) { c.toBlob(r, "image/png"); });
      return new File([blob], "Capture " + new Date().toLocaleString("id-ID").replace(/[\/:]/g, ".") + ".png", { type: "image/png" });
    } finally { st.getTracks().forEach(function (t) { t.stop(); }); }
  }
  function baAdd(r) {
    var L = [];
    var M = modal('<div class="mig-mh"><div><small>' + E(r.baru) + " · " + E(r.stasiun) + '</small><h3>Tambah file / capture ke BA</h3><p>File & capture ditambahkan sebagai halaman setelah BA, lalu dibuka di Edit PDF untuk dirapikan sebelum disimpan.</p></div><button class="x" data-x><i class="fa-solid fa-xmark"></i></button></div>'
      + '<div class="mig-pad"><div class="mig-drop" id="mig-drop" tabindex="0"><i class="fa-solid fa-cloud-arrow-up"></i><b>Seret file ke sini, atau tempel capture (Ctrl+V)</b><small>PDF, JPG, PNG</small><div class="mig-dec"><label class="st-b"><input type="file" id="mig-addf" class="hidden" multiple accept="application/pdf,.pdf,image/png,image/jpeg,.jpg,.jpeg,.png"><i class="fa-solid fa-folder-open"></i>Pilih file</label><button class="st-b" data-g><i class="fa-solid fa-camera"></i>Capture layar (mis. dashboard portal)</button></div></div>'
      + '<ul class="mig-addl" id="mig-addl"></ul><div class="mig-dec"><button class="st-b" data-x>Batal</button><button class="st-b pri" data-go disabled><i class="fa-solid fa-pen-to-square"></i>Gabungkan ke BA &amp; buka Edit PDF</button></div></div>', "md");
    var el = M.el, list = el.querySelector("#mig-addl"), go = el.querySelector("[data-go]");
    var draw = function () {
      list.innerHTML = L.map(function (f, i) { return '<li><i class="fa-solid ' + (/pdf/.test(f.type) ? "fa-file-pdf" : "fa-image") + '"></i><span>' + E(f.name) + "<small>" + Math.max(1, Math.round(f.size / 1024)) + ' KB</small></span><button class="mig-cpb" data-rm="' + i + '" title="Hapus"><i class="fa-solid fa-xmark"></i></button></li>'; }).join("");
      list.querySelectorAll("[data-rm]").forEach(function (b) { b.onclick = function () { L.splice(+b.dataset.rm, 1); draw(); }; });
      go.disabled = !L.length;
    };
    var add = function (fs) { Array.from(fs || []).forEach(function (f) { if (/pdf|image\/(png|jpe?g)/i.test(f.type) || /\.(pdf|png|jpe?g)$/i.test(f.name)) L.push(f); else toast('"' + f.name + '" dilewati — hanya PDF / JPG / PNG', "error", 5000); }); draw(); };
    el.querySelector("#mig-addf").onchange = function () { add(this.files); this.value = ""; };
    var dz = el.querySelector("#mig-drop");
    dz.ondragover = function (e) { e.preventDefault(); dz.classList.add("on"); }; dz.ondragleave = function () { dz.classList.remove("on"); };
    dz.ondrop = function (e) { e.preventDefault(); dz.classList.remove("on"); add(e.dataTransfer.files); };
    var paste = function (e) { if (!document.body.contains(el)) return document.removeEventListener("paste", paste); var fs = Array.from((e.clipboardData || {}).items || []).filter(function (it) { return it.kind === "file"; }).map(function (it) { var f = it.getAsFile(); return f && /^image\//.test(f.type) && f.name === "image.png" ? new File([f], "Capture " + (L.length + 1) + ".png", { type: f.type }) : f; }).filter(Boolean); if (fs.length) { e.preventDefault(); add(fs); toast(fs.length + " capture ditempel", "success"); } };
    document.addEventListener("paste", paste); dz.focus();
    el.querySelector("[data-g]").onclick = async function () { try { add([await grabScreen()]); } catch (e) { if (e && e.name !== "NotAllowedError") toast(e.message, "error", 7000); } };
    go.onclick = function () { document.removeEventListener("paste", paste); go.disabled = true; go.innerHTML = '<i class="fa-solid fa-circle-notch fa-spin"></i>Membuka…'; baEdit(r, L.slice()); };
  }
  // ---------- ubah data pengajuan (akun Sales / Lead IKR, No SPK, mitra, stasiun, dll.) ----------
  var EF = [["noSpk", "No SPK", "text", 1], ["tujuan", "Tujuan", "sel", 1], ["lama", "Mitra lama", "mitra", 1], ["baru", "Mitra pengganti", "mitra", 1], ["stasiun", "Stasiun", "text", 1],
            ["sales", "Akun email Sales penampung", "email", 1], ["ikrBaru", "Akun email Lead IKR mitra pengganti", "email", 1], ["ikrLama", "Akun email Lead IKR mitra lama", "email", 0],
            ["nama", "Nama pengaju", "text", 1], ["jabatan", "Jabatan", "text", 0], ["wa", "No WhatsApp", "text", 0], ["email", "Email pengaju", "email", 1], ["kml", "Link file KML", "url", 0], ["spk", "Link file SPK", "url", 0]];
  function editData(r) {
    var names = ((STATE.perseroan || []).map(function (x) { return x.nama; }).filter(Boolean)).filter(function (x, i, a) { return a.indexOf(x) === i; }).sort();
    var fld = function (f) {
      var v = E(r[f[0]] || ""), req = f[3] ? ' <i class="rq">*</i>' : "";
      var inp = f[2] === "sel" ? '<select class="field w-full" data-k="tujuan"><option' + (r.tujuan === "Migrasi Akun IKR" ? " selected" : "") + '>Migrasi Akun IKR</option><option' + (/create/i.test(r.tujuan) ? " selected" : "") + ">Create Stasiun (Stasiun Take Over)</option></select>"
        : '<input class="field w-full" data-k="' + f[0] + '" value="' + v + '"' + (f[2] === "email" ? ' type="email"' : "") + (f[2] === "mitra" ? ' list="mig-dlm"' : "") + (f[2] === "url" ? ' placeholder="https://drive.google.com/…"' : "") + ">";
      return '<label class="mig-ef' + (/kml|spk|sales|ikr|stasiun/.test(f[0]) ? " w2" : "") + '"><span>' + f[1] + req + "</span>" + inp + "</label>";
    };
    var M = modal('<div class="mig-mh"><div><small>Pengajuan ' + E(r.ts) + '</small><h3>Ubah data pengajuan</h3><p>Perubahan langsung tersimpan di sheet Migrasi IKR dan tercatat di riwayat.</p></div><button class="x" data-x><i class="fa-solid fa-xmark"></i></button></div>'
      + '<div class="mig-pad"><datalist id="mig-dlm">' + names.map(function (n) { return '<option value="' + E(n) + '">'; }).join("") + '</datalist><div class="mig-efg">' + EF.map(fld).join("") + '</div><p class="mig-note" id="mig-efn"></p>'
      + '<div class="mig-dec"><button class="st-b" data-x>Batal</button><button class="st-b pri" data-s><i class="fa-solid fa-floppy-disk"></i>Simpan perubahan</button></div></div>', "md");
    var el = M.el, note = el.querySelector("#mig-efn");
    var changes = function () { var o = {}; el.querySelectorAll("[data-k]").forEach(function (i) { var v = i.value.trim(); if (v !== String(r[i.dataset.k] || "").trim()) o[i.dataset.k] = v; }); return o; };
    var upd = function () { var n = Object.keys(changes()).length; note.textContent = n ? n + " kolom diubah" : ""; el.querySelectorAll("[data-k]").forEach(function (i) { i.classList.toggle("mig-chg", i.value.trim() !== String(r[i.dataset.k] || "").trim()); }); };
    el.addEventListener("input", upd); el.addEventListener("change", upd);
    el.querySelector("[data-s]").onclick = async function () {
      var ch = changes(); if (!Object.keys(ch).length) return toast("Belum ada yang diubah", "info");
      var b = this; b.disabled = true; b.innerHTML = '<i class="fa-solid fa-circle-notch fa-spin"></i>Menyimpan…';
      try {
        var res = await callApi("mig.edit", { row: r.row, ts: r.ts, noSpk: r.noSpk, changes: ch }, 60000);
        if (res.oldKey && res.oldKey !== res.chk.key) delete MIG.chk[res.oldKey];
        Object.assign(r, res.item); MIG.chk[res.chk.key] = res.chk.value; r.ck = res.chk.key;
        M.close(); toast("Data pengajuan diperbarui", "success"); badge(); if (isOpen()) render(); openDetail(r.row);
      } catch (e) { b.disabled = false; b.innerHTML = '<i class="fa-solid fa-floppy-disk"></i>Simpan perubahan'; toast(e.message, "error", 7000); }
    };
  }
  function revisiShare(r, msg) {
    var M = modal('<div class="mig-mh"><div><h3>Kabari mitra</h3><p>Status tersimpan di kolom R, catatan di kolom Q.</p></div><button class="x" data-x><i class="fa-solid fa-xmark"></i></button></div><div class="mig-pad"><textarea class="field w-full mig-pre mig-big" rows="12" id="mig-msg">' + E(msg) + '</textarea><div class="mig-dec"><button class="st-b" data-c><i class="fa-solid fa-copy"></i>Salin pesan</button>' + (r.wa ? '<button class="st-b pri" data-w><i class="fa-brands fa-whatsapp"></i>Kirim WA ke ' + E(r.wa) + "</button>" : "") + "</div></div>", "md");
    var t = function () { return M.el.querySelector("#mig-msg").value; };
    M.el.querySelector("[data-c]").onclick = function () { copyText(t(), "Pesan disalin"); };
    var w = M.el.querySelector("[data-w]"); if (w) w.onclick = function () { window.open(waUrl(r, t()), "_blank", "noopener"); };
  }
  function emailIt(r, T, done) {
    var body = itBody(r), subj = itSubject(r);
    var isCreate = /create/i.test(r.tujuan), fin = isCreate ? "Done Verifikasi" : "Done Email IT";
    var M = modal('<div class="mig-mh"><div><small>Lolos verifikasi · status akhir: ' + fin + '</small><h3>Kirim ke Team IT</h3><p>Salin teks atau buka di Outlook Web, kirim, lalu tandai sudah dikirim.</p></div><button class="x" data-x><i class="fa-solid fa-xmark"></i></button></div>'
      + '<div class="mig-pad"><dl class="mig-dl wide mig-cp"><dt>To</dt><dd><span>' + E(MIG.settings.to) + '</span><button class="mig-cpb" data-cp="to" title="Salin To"><i class="fa-solid fa-copy"></i></button></dd><dt>Cc</dt><dd><span>' + E(MIG.settings.cc) + '</span><button class="mig-cpb" data-cp="cc" title="Salin Cc"><i class="fa-solid fa-copy"></i></button></dd><dt>Subjek</dt><dd><b>' + E(subj) + '</b><button class="mig-cpb" data-cp="subj" title="Salin subjek"><i class="fa-solid fa-copy"></i></button></dd></dl><textarea class="field w-full mig-pre mig-big" rows="22" id="mig-body">' + E(body) + "</textarea>"
      + '<p class="mig-note"><i class="fa-solid fa-paperclip"></i> Lampirkan file BA dari Drive bila perlu: <a class="mig-lnk" target="_blank" rel="noopener" href="' + E(r.ba) + '">buka BA</a></p>'
      + (T.length ? '<label class="mig-upd"><input type="checkbox" id="mig-updto" checked><span>Perbarui Data Mitra Takeover: <b>' + T.length + " PO</b> (" + E(T.map(function (t) { return t.po; }).join(", ")) + ") — kolom M jadi <b>" + fin + "</b>" + (isCreate ? "" : ", kolom X tanggal hari ini (bila kosong)") + "</span></label>" : "")
      + '<div class="mig-dec"><button class="st-b" data-c><i class="fa-solid fa-copy"></i>Salin teks</button><button class="st-b" data-o><i class="fa-solid fa-envelope-open-text"></i>Buka di Outlook Web</button><button class="st-b pri" data-s><i class="fa-solid fa-check-double"></i>Tandai sudah dikirim ke IT</button></div></div>', "xl");
    var el = M.el, txt = function () { return el.querySelector("#mig-body").value; };
    el.querySelector("[data-c]").onclick = function () { copyText(txt(), "Teks email disalin"); };
    el.querySelectorAll("[data-cp]").forEach(function (b) { b.onclick = function () { var k = b.dataset.cp; copyText(k === "subj" ? subj : mails(MIG.settings[k]).join("; "), (k === "subj" ? "Subjek" : k === "to" ? "To" : "Cc") + " disalin"); }; });
    el.querySelector("[data-o]").onclick = function () { var u = outlookUrl(Object.assign({}, r)); if (txt() !== body) u = u.replace(/&body=[^&]*/, "&body=" + encodeURIComponent(txt())); side(u, "starlite-outlook"); };
    el.querySelector("[data-s]").onclick = async function () {
      var b = this; b.disabled = true; b.innerHTML = '<i class="fa-solid fa-circle-notch fa-spin"></i>Menyimpan…';
      try {
        var upd = el.querySelector("#mig-updto");
        var res = await callApi("mig.save", { row: r.row, ts: r.ts, noSpk: r.noSpk, verif: fin, updTakeover: upd ? upd.checked : false, toRows: T.map(function (t) { return t.row; }), note: "Email ke IT: " + subj }, 60000);
        if (res.item) Object.assign(r, res.item); if (res.chk) { MIG.chk[res.chk.key] = res.chk.value; r.ck = res.chk.key; }
        M.close(); if (done) done(); badge(); if (isOpen()) render();
        toast("Status VM: " + fin + (res.takeoverRows && res.takeoverRows.length ? " · Data Takeover " + res.takeoverRows.length + " PO diperbarui" : ""), "success", 6000);
        try { if (res.takeoverRows && res.takeoverRows.length && typeof autoSyncGoogleSheets === "function") autoSyncGoogleSheets({ keys: ["takeover"], silent: true }); } catch (e) { }
      } catch (e) { b.disabled = false; b.innerHTML = '<i class="fa-solid fa-check-double"></i>Tandai sudah dikirim ke IT'; toast(e.message, "error", 8000); }
    };
  }
  async function formUrl() {   // link form pengajuan mitra (dengan kunci) — untuk pesan pengajuan ulang
    try { if (!MIG.formKey) { var r = await callApi("mig.formkey", {}, 30000); MIG.formKey = r.key; } return location.origin + location.pathname.replace(/[^\/]*$/, "") + "migrasi.html?k=" + MIG.formKey; } catch (e) { return ""; }
  }
  async function formLink() {
    try {
      var r = await callApi("mig.formkey", {}, 30000);
      var base = location.origin + location.pathname.replace(/[^\/]*$/, "");
      var url = base + "migrasi.html?k=" + r.key;
      var M = modal('<div class="mig-mh"><div><h3>Link form pengajuan mitra</h3><p>Bagikan lewat WA. Mitra mengisi tanpa login; pengajuan masuk ke sheet Migrasi IKR.</p></div><button class="x" data-x><i class="fa-solid fa-xmark"></i></button></div><div class="mig-pad"><input class="field w-full" readonly value="' + E(url) + '" id="mig-url"><div class="mig-dec"><button class="st-b" data-o><i class="fa-solid fa-arrow-up-right-from-square"></i>Buka</button><button class="st-b pri" data-c><i class="fa-solid fa-copy"></i>Salin link</button></div></div>', "sm");
      M.el.querySelector("[data-c]").onclick = function () { copyText(M.el.querySelector("#mig-url").value, "Link form disalin"); };
      M.el.querySelector("[data-o]").onclick = function () { window.open(M.el.querySelector("#mig-url").value, "_blank", "noopener"); };
    } catch (e) { toast(e.message, "error", 7000); }
  }
  function settings() {
    var M = modal('<div class="mig-mh"><div><h3>Penerima email ke Team IT</h3><p>Dipakai di tombol Salin teks dan Buka di Outlook Web.</p></div><button class="x" data-x><i class="fa-solid fa-xmark"></i></button></div><div class="mig-pad"><label class="mig-l">Akun Outlook pengirim<input id="mig-from" class="field w-full" value="' + E(MIG.settings.from || "vendormanagement@pmosurge.co.id") + '"></label><label class="mig-l">To<textarea id="mig-to" class="field w-full" rows="2">' + E(MIG.settings.to) + '</textarea></label><label class="mig-l">Cc<textarea id="mig-cc" class="field w-full" rows="5">' + E(MIG.settings.cc) + '</textarea></label><div class="mig-dec"><button class="st-b" data-x>Batal</button><button class="st-b pri" data-s><i class="fa-solid fa-floppy-disk"></i>Simpan</button></div></div>', "sm");
    M.el.querySelector("[data-s]").onclick = async function () { try { var r = await callApi("mig.settings", { save: { from: M.el.querySelector("#mig-from").value, to: M.el.querySelector("#mig-to").value, cc: M.el.querySelector("#mig-cc").value } }, 30000); MIG.settings = r.settings; M.close(); toast("Penerima email IT disimpan", "success"); } catch (e) { toast(e.message, "error", 7000); } };
  }
  // ---------- kait ke aplikasi ----------
  if (typeof switchTab === "function") { var oST = switchTab; window.switchTab = switchTab = function (t) { ensureUi(); var r = oST.apply(this, arguments); try { var tb = $("mig-tb"); tb && tb.classList.toggle("hidden", t !== "migrasi"); } catch (e) { } try { if (t === "migrasi" && isOwner()) { render(); load(false); } } catch (e) { console.warn("mig", e); } return r; }; }
  if (typeof applyPermissions === "function") { var oAP = applyPermissions; window.applyPermissions = applyPermissions = function () { var r = oAP.apply(this, arguments); try { ensureUi(); } catch (e) { } return r; }; }
  // detail PO di Data Mitra Takeover: status migrasi PO itu
  if (typeof renderTakeoverDetail === "function") {
    var oRT = renderTakeoverDetail;
    window.renderTakeoverDetail = renderTakeoverDetail = function (t) {
      var r = oRT.apply(this, arguments);
      try {
        if (isOwner() && MIG.loaded && t && t.att_spk) {
          var m = MIG.rows.filter(function (x) { return nk(x.noSpk) === nk(t.att_spk); }).sort(function (a, b) { return b.tsMs - a.tsMs; })[0];
          var body = $("detail-modal-body");
          if (m && body) { body.insertAdjacentHTML("afterbegin", '<button class="mig-to-banner" data-mrow="' + m.row + '"><i class="fa-solid fa-people-arrows"></i><span>Migrasi IKR · diajukan ' + E(m.ts.split(" ")[0]) + "</span>" + chip(stOf(m)) + "</button>"); body.querySelector("[data-mrow]").onclick = function () { try { closeDetailModal(); } catch (e) { } switchTab("migrasi"); setTimeout(function () { openDetail(m.row); }, 300); }; }
        }
      } catch (e) { }
      return r;
    };
  }
  // lonceng: bagian Migrasi IKR untuk Akun Utama
  if (typeof notifPanel === "function") {
    var oNP = notifPanel;
    window.notifPanel = notifPanel = function () {
      var r = oNP.apply(this, arguments);
      try {
        if (!isOwner() || !MIG.loaded) return r;
        var w = MIG.rows.filter(function (x) { return stOf(x) === "wait"; }).length, late = MIG.rows.filter(function (x) { var c = chkOf(x); return stOf(x) === "it" && c.emailAt && Date.now() - Date.parse(c.emailAt) > 7 * 864e5; }).length;
        if (!w && !late) return r;
        var e = $("notif-panel"), ph = e && e.querySelector(".st-ph"); if (!ph) return r;
        ph.insertAdjacentHTML("afterend", '<button class="mig-np" id="mig-np"><i class="fa-solid fa-people-arrows"></i><span><b>Migrasi IKR</b><small>' + (w ? w + " pengajuan menunggu verifikasi" : "") + (w && late ? " · " : "") + (late ? late + " Pending IT > 7 hari" : "") + '</small></span><i class="fa-solid fa-chevron-right"></i></button>');
        $("mig-np").onclick = function (ev) { ev.stopPropagation(); try { notifClose(); } catch (er) { } switchTab("migrasi"); };
      } catch (er) { }
      return r;
    };
  }
  try { if (typeof BUSY_SKIP !== "undefined" && BUSY_SKIP instanceof RegExp) { var bsT = RegExp.prototype.test; BUSY_SKIP.test = function (a) { return /^(mig\.(list|check|formkey|settings)|ton\.list|sign\.sbtoken)$/.test(a) || bsT.call(BUSY_SKIP, a); }; } } catch (e) { }
  setInterval(function () { if (isOwner() && srv() && document.visibilityState === "visible") { ensureUi(); load(false); } }, 300000);
  setTimeout(function () { if (isOwner() && srv()) { ensureUi(); load(false); } }, 5000);
  if (location.hostname === "localhost") window.__mig = { MIG: MIG, load: load, render: render, openDetail: openDetail, autoChecks: autoChecks, itBody: itBody, itSubject: itSubject, outlookUrl: outlookUrl, keyOf: keyOf, ensureUi: ensureUi, stOf: stOf };
})();

/* ===== v22 · Keandalan: link lampiran Data Mitra Takeover, draf Edit Data, kolom Tracker All Starlite ===== */
(function () {
  "use strict";
  var wait = function (ms) { return new Promise(function (r) { setTimeout(r, ms); }); };
  var toast = function (m, t, ms) { try { showToast(m, t || "info", ms); } catch (e) { } };
  var keyOf = function (t) { return String(t.po || "").toUpperCase().trim() + "|" + String(t.bap_no || "").toUpperCase().trim(); };

  // ---------- 1) link lampiran (kolom P–T): chip, hyperlink, link di teks ----------
  // Sebelumnya: satu kegagalan 400 mematikan pembacaan chip untuk seluruh sesi, satu paket gagal = semua link hilang,
  // dan link lama ditempel per NOMOR BARIS (salah tempel bila baris bergeser). Sekarang: per paket, diulang, dan dicocokkan per PO.
  var MASK = ["sheets(data(startRow,rowData(values(formattedValue,hyperlink,textFormatRuns(startIndex,format(link(uri))),chipRuns(startIndex,chip(richLinkProperties(uri)))))))",
              "sheets(data(startRow,rowData(values(formattedValue,hyperlink,textFormatRuns(startIndex,format(link(uri)))))))"];
  // semua link dalam satu sel (BASTM kolom T bisa berisi beberapa lampiran: take over ke mitra A, lalu mitra B, …)
  function cellLinks(v) {
    if (!v) return [];
    var txt = String(v.formattedValue || ""), runs = [];
    (v.textFormatRuns || []).forEach(function (r) { runs.push({ i: r.startIndex || 0, u: r.format && r.format.link && r.format.link.uri || "" }); });
    (v.chipRuns || []).forEach(function (r) { var u = r.chip && r.chip.richLinkProperties && r.chip.richLinkProperties.uri; if (u) runs.push({ i: r.startIndex || 0, u: u, chip: 1 }); });
    runs.sort(function (a, b) { return a.i - b.i; });
    var out = [];
    runs.forEach(function (r, k) {
      var end = k + 1 < runs.length ? runs[k + 1].i : txt.length;
      if (!r.u) return;
      var t = txt.slice(r.i, end).replace(/\s+/g, " ").trim(), last = out[out.length - 1];
      if (last && last.u === r.u) last.t = (last.t + " " + t).trim(); else out.push({ t: t, u: r.u });
    });
    if (!out.length && v.hyperlink) out.push({ t: txt.trim(), u: v.hyperlink });
    return out;
  }
  function cellLink(v) {
    if (!v) return "";
    var u = ""; try { u = extractLink(v); } catch (e) { }
    if (u) return u;
    var f = String(v.formattedValue || "").trim();
    return /^https?:\/\/\S+$/i.test(f) ? f : "";
  }
  if (typeof fetchLinks === "function" && typeof apiGet === "function") {
    window.fetchLinks = fetchLinks = async function (title, last, prog) {
      var C = CONFIG.LINK_COLS, size = Math.min(CONFIG.LINK_CHUNK_ROWS || 2000, 1500), chunks = [], out = new Map();
      for (var a = 2; a <= last; a += size) chunks.push([a, Math.min(a + size - 1, last)]);
      out.failed = [];
      await runPool(chunks.map(function (ch) {
        return async function () {
          var res = null;
          for (var i = 0; i < 4 && !res; i++) {
            for (var m = 0; m < MASK.length && !res; m++) {
              try { res = await apiGet("", [["ranges", qSheet(title) + "!" + C.from + ch[0] + ":" + C.to + ch[1]], ["includeGridData", "true"], ["fields", MASK[m]]]); }
              catch (e) { if (e && e.status !== 400) break; }
            }
            if (!res) await wait(1200 * (i + 1));
          }
          if (!res) { out.failed.push(ch); if (prog) prog(); return; }
          var d = res.sheets && res.sheets[0] && res.sheets[0].data && res.sheets[0].data[0], st = (d && d.startRow != null ? d.startRow : ch[0] - 1) + 1;
          ((d && d.rowData) || []).forEach(function (rd, i) {
            var vals = rd.values || [], L = vals.map(cellLink);
            var multi = cellLinks(vals[4]);   // kolom T (BASTM)
            if (multi.length > 1) { L[4] = multi[multi.length - 1].u; L[5] = JSON.stringify(multi); }   // dibuka default = lampiran terbaru
            if (L.some(Boolean)) out.set(st + i, L);
          });
          if (prog) prog();
        };
      }), CONFIG.CONCURRENCY || 3);
      return out;
    };
  }
  var LK = { tries: 0, timer: 0, last: null };
  function prevLinks() { var m = new Map(); (STATE.takeover || []).forEach(function (t) { if (t.links && t.links.some(Boolean)) m.set(keyOf(t), t.links); }); return m; }
  function afterLinks() {
    try { renderTakeoverPage(); } catch (e) { } try { applyDocFilters(false); } catch (e) { } try { renderDashboard(); } catch (e) { } try { updateSyncLabels(); } catch (e) { } try { saveSnapshot(); } catch (e) { }
    resolveNames();
  }
  if (typeof loadLinksInBackground === "function") {
    window.loadLinksInBackground = loadLinksInBackground = async function (title, last) {
      LK.last = [title, last]; clearTimeout(LK.timer);
      var prev = prevLinks(), n = null;
      try {
        var tot = Math.ceil(Math.max(1, last - 1) / 1500), k = 0;
        n = await fetchLinks(title, last, function () { k++; if (tot > 2) try { setProgress("Memuat link lampiran… (" + k + "/" + tot + ")", k / tot * 100); } catch (e) { } });
      } catch (e) { console.warn("link lampiran:", e && e.message); }
      try { setProgress(null); } catch (e) { }
      var failed = n ? n.failed : [[2, last]];
      var inFail = function (row) { return failed.some(function (r) { return row >= r[0] && row <= r[1]; }); };
      (STATE.takeover || []).forEach(function (t) { t.links = n && !inFail(t.row) ? (n.get(t.row) || null) : (prev.get(keyOf(t)) || null); });
      STATE.linksLoaded = !failed.length;
      afterLinks();
      if (failed.length) {
        LK.tries++;
        if (LK.tries <= 4) { LK.timer = setTimeout(function () { loadLinksInBackground(title, last); }, 20000 * LK.tries); }
        if (LK.tries === 1) toast("Sebagian link lampiran belum terbaca — dicoba ulang otomatis (data lampiran sebelumnya tetap dipakai)", "info", 7000);
      } else LK.tries = 0;
    };
  }
  // sinkron penuh: link lama ditempel ulang per PO, bukan per nomor baris (baris bisa bergeser karena tambah / hapus baris)
  if (typeof autoSyncGoogleSheets === "function") {
    var oSync = autoSyncGoogleSheets;
    window.autoSyncGoogleSheets = autoSyncGoogleSheets = async function () {
      var prev = prevLinks(), rowKey = new Map((STATE.takeover || []).map(function (t) { return [t.row, keyOf(t)]; }));
      try { return await oSync.apply(this, arguments); }
      finally {
        try {
          var fixed = 0;
          (STATE.takeover || []).forEach(function (t) { if (rowKey.has(t.row) && rowKey.get(t.row) === keyOf(t)) return; var l = prev.get(keyOf(t)) || null; if (t.links !== l) { t.links = l; fixed++; } });
          if (fixed) { try { renderTakeoverPage(); applyDocFilters(false); } catch (e) { } }
        } catch (e) { }
      }
    };
  }
  // kembali ke aplikasi: link yang belum terbaca dicoba lagi
  document.addEventListener("visibilitychange", function () { if (!document.hidden && LK.last && STATE.linksLoaded === false && !STATE.syncing) { clearTimeout(LK.timer); loadLinksInBackground(LK.last[0], LK.last[1]); } });

  // teks nama file tanpa link (chip tidak terbaca / ditulis manual) → dicari di Drive lewat server, hasil disimpan
  var NM_KEY = "att_name_links_v1", NM = {};
  try { NM = JSON.parse(localStorage.getItem(NM_KEY) || "{}"); } catch (e) { NM = {}; }
  var fileish = function (s) { s = String(s || "").trim(); return s.length > 6 && !/^https?:/i.test(s) && (/\.(pdf|jpe?g|png|docx?)$/i.test(s) || /^(BA|BAP|BAST|BASTM|SPK)[\s_.-]/i.test(s)); };
  var sameName = function (a, b) { var n = function (x) { return String(x || "").toLowerCase().replace(/\.pdf$/, "").replace(/\s+/g, " ").trim(); }; return n(a) === n(b); };
  var DOCC = [[15, "att_ba"], [16, "att_spk"], [18, "att_bap"], [19, "att_bastm"]], RES = { busy: false };
  function applyNames() {
    var hit = 0;
    (STATE.takeover || []).forEach(function (t) {
      DOCC.forEach(function (d) {
        var txt = String(t[d[1]] || "").trim(), i = d[0] - CONFIG.LINK_COLS.startIndex;
        if (!txt || (t.links && t.links[i])) return;
        var u = NM[txt.toLowerCase()]; if (!u || !u.url) return;
        t.links = t.links ? t.links.slice() : []; t.links[i] = u.url; hit++;
      });
    });
    return hit;
  }
  async function resolveNames() {
    var applied = applyNames();
    if (RES.busy || typeof isServerMode !== "function" || !isServerMode() || !currentUser) { if (applied) try { applyDocFilters(false); } catch (e) { } return; }
    var want = [], seen = {}, now = Date.now();
    (STATE.takeover || []).forEach(function (t) {
      if (t.st === "cancel") return;
      DOCC.forEach(function (d) {
        var txt = String(t[d[1]] || "").trim(), i = d[0] - CONFIG.LINK_COLS.startIndex, k = txt.toLowerCase();
        if (!fileish(txt) || (t.links && t.links[i]) || seen[k]) return;
        var c = NM[k]; if (c && (c.url || now - c.at < 864e5)) return;   // "tidak ketemu" dicoba lagi besok
        seen[k] = 1; want.push(txt);
      });
    });
    if (!want.length) { if (applied) try { applyDocFilters(false); } catch (e) { } return; }
    RES.busy = true;
    try {
      for (var i = 0; i < Math.min(want.length, 25); i++) {
        var nm = want[i];
        try { var r = await callApi("att.find", { name: nm }, 45000); NM[nm.toLowerCase()] = sameName(r.name, nm) ? { url: r.url, at: now } : { url: "", at: now }; }
        catch (e) { NM[nm.toLowerCase()] = { url: "", at: now }; }
      }
      try { localStorage.setItem(NM_KEY, JSON.stringify(NM)); } catch (e) { }
      if (applyNames() || applied) { try { renderTakeoverPage(); applyDocFilters(false); renderDashboard(); } catch (e) { } }
    } finally { RES.busy = false; }
  }
  try { if (typeof BUSY_SKIP !== "undefined" && BUSY_SKIP instanceof RegExp) { var bt = BUSY_SKIP.test; BUSY_SKIP.test = function (a) { return a === "att.find" || bt.call(BUSY_SKIP, a); }; } } catch (e) { }
  setTimeout(function () { try { if (STATE.linksLoaded) resolveNames(); } catch (e) { } }, 15000);

  // ---------- 2) draf Edit / Tambah Data: tidak hilang saat pindah aplikasi / klik di luar jendela ----------
  var DK = "rec_draft_v1", DAY = 3 * 864e5;
  var getD = function () { try { var d = JSON.parse(localStorage.getItem(DK) || "null"); return d && Date.now() - d.at < DAY ? d : null; } catch (e) { return null; } };
  var putD = function (d) { if (!d) clearTimeout(saveT); try { if (d) localStorage.setItem(DK, JSON.stringify(d)); else localStorage.removeItem(DK); } catch (e) { } };
  var sameRec = function (d) { return d && typeof REC !== "undefined" && d.sheet === REC.sheet && d.mode === REC.mode && String(d.id || "") === String(REC.id || ""); };
  var dirtyNow = function () { try { return Object.keys(recChanges()).length > 0; } catch (e) { return false; } };
  var saveT = 0;
  function saveDraft() {
    if (typeof REC === "undefined" || !REC.sheet) return;
    var mm = document.getElementById("rec-modal"); if (!mm || mm.classList.contains("hidden")) return;   // form sudah ditutup → jangan simpan lagi
    var vals = {}, n = 0;
    document.querySelectorAll("#rec-body [data-c]").forEach(function (el) { var v = el.value; if (String(v).trim() !== String(el.dataset.orig || "").trim()) { vals[el.dataset.c] = v; n++; } });
    if (!n) { var d0 = getD(); if (sameRec(d0)) putD(null); return; }
    var lbl = ""; try { var it = REC.id && STATE.idx.byId.get(REC.id); lbl = it ? recLabel(REC.sheet, it) : ""; } catch (e) { }
    putD({ sheet: REC.sheet, mode: REC.mode, id: REC.id || "", label: lbl, vals: vals, at: Date.now() });
  }
  document.addEventListener("input", function (e) { if (e.target && e.target.closest && e.target.closest("#rec-body") && e.target.dataset.c != null) { clearTimeout(saveT); saveT = setTimeout(saveDraft, 300); } }, true);
  document.addEventListener("change", function (e) { if (e.target && e.target.closest && e.target.closest("#rec-body") && e.target.dataset.c != null) { clearTimeout(saveT); saveT = setTimeout(saveDraft, 100); } }, true);
  window.addEventListener("pagehide", saveDraft); document.addEventListener("visibilitychange", function () { if (document.hidden) saveDraft(); });
  // pulihkan saat form yang sama dibuka lagi
  var restored = "";
  // dicek SEKALI per form yang baru dirender (bukan tiap ketikan) — supaya isian yang sedang diketik tidak ditimpa
  function tryRestore() {
    var body = document.getElementById("rec-body"); if (!body || body.dataset.draftChecked) return;
    var els = body.querySelectorAll("[data-c]"); if (!els.length) return;
    body.dataset.draftChecked = "1";
    var d = getD(); if (!sameRec(d)) return;
    var n = 0; els.forEach(function (el) { var v = d.vals[el.dataset.c]; if (v != null && el.value !== v && !el.disabled) { el.value = v; n++; } });
    if (!n) return;
    try { recDirty(); } catch (e) { }
    var body = document.getElementById("rec-body"), old = document.getElementById("rec-draftbar"); old && old.remove();
    var bar = document.createElement("div"); bar.id = "rec-draftbar"; bar.className = "rec-draftbar";
    bar.innerHTML = '<i class="fa-solid fa-clock-rotate-left"></i><span><b>' + n + " isian yang belum disimpan dipulihkan</b><small>dari " + new Date(d.at).toLocaleString("id-ID", { day: "2-digit", month: "short", hour: "2-digit", minute: "2-digit" }) + ' — periksa lalu klik Simpan</small></span><button type="button">Buang</button>';
    bar.querySelector("button").onclick = function () { putD(null); restored = ""; bar.remove(); var id = REC.id, sh = REC.sheet, md = REC.mode; try { REC.busy = false; recGuardClose._inner = true; closeRecModal(); } catch (e) { } finally { recGuardClose._inner = false; } setTimeout(function () { try { md === "add" ? openRecAdd(sh) : openRecEdit(id); } catch (e) { } }, 50); };
    body.parentNode.insertBefore(bar, body);
  }
  var recM = document.getElementById("rec-modal");
  var recC = document.getElementById("rec-card");
  if (recC && window.MutationObserver) new MutationObserver(function () { if (!recM.classList.contains("hidden")) setTimeout(tryRestore, 30); }).observe(recC, { childList: true });
  // klik di luar jendela / tombol tutup: jangan buang isian tanpa konfirmasi
  if (recM) recM.setAttribute("onclick", "if(event.target===this && !REC.busy){ if(typeof recGuardClose==='function'){ recGuardClose(true); } else closeRecModal(); }");
  window.recGuardClose = function (backdrop) {
    if (!dirtyNow()) { putD(null); return closeRecModal(); }
    saveDraft();
    if (backdrop) { var c = document.getElementById("rec-card"); if (c) { c.classList.remove("rec-shake"); void c.offsetWidth; c.classList.add("rec-shake"); } return toast("Ada isian yang belum disimpan — klik Simpan, atau tombol Tutup untuk keluar", "info", 4500); }
    if (confirm("Ada isian yang belum disimpan.\nOK = buang perubahan & tutup · Batal = kembali ke form")) { putD(null); restored = ""; closeRecModal(); }
  };
  if (typeof closeRecModal === "function") {
    var oClose = closeRecModal;
    window.closeRecModal = closeRecModal = function () {
      // dipanggil dari tombol Tutup / Batal di form (bukan saat proses simpan) → minta konfirmasi bila ada perubahan
      if (!REC.busy && !SAVING && !recGuardClose._inner && dirtyNow()) { recGuardClose._inner = true; try { return recGuardClose(false); } finally { recGuardClose._inner = false; } }
      return oClose.apply(this, arguments);
    };
  }
  var SAVING = false;
  ["saveRecEdit", "saveRecAdd"].forEach(function (fn) {
    if (typeof window[fn] !== "function") return;
    var o = window[fn];
    window[fn] = async function () {
      var r; SAVING = true;
      try { r = await o.apply(this, arguments); } finally { SAVING = false; }
      try { var m = document.getElementById("rec-modal"), err = document.getElementById("rec-err"); if (m && (m.classList.contains("hidden") || (err && err.classList.contains("hidden") && !dirtyNow()))) { putD(null); restored = ""; } } catch (e) { }
      return r;
    };
  });
  // setelah aplikasi dibuka ulang: tawarkan lanjutkan draf
  function offerDraft() {
    var d = getD(); if (!d || !currentUser || document.getElementById("rec-draftoffer")) return;
    var m = document.getElementById("rec-modal"); if (m && !m.classList.contains("hidden")) return;
    var b = document.createElement("div"); b.id = "rec-draftoffer"; b.className = "rec-draftoffer";
    b.innerHTML = '<i class="fa-solid fa-pen-to-square"></i><span><b>Edit yang belum disimpan</b><small>' + (d.mode === "add" ? "Tambah data · " : "") + (d.label || d.sheet) + " · " + Object.keys(d.vals).length + ' kolom</small></span><button data-go type="button">Lanjutkan</button><button data-x type="button" title="Buang">✕</button>';
    b.querySelector("[data-go]").onclick = function () { b.remove(); try { d.mode === "add" ? openRecAdd(d.sheet) : openRecEdit(d.id); } catch (e) { toast("Data untuk draf ini tidak ditemukan", "error"); } };
    b.querySelector("[data-x]").onclick = function () { if (confirm("Buang isian edit yang belum disimpan?")) { putD(null); b.remove(); } };
    document.body.appendChild(b);
  }
  setTimeout(function loop() { try { if (STATE.takeover && STATE.takeover.length) return offerDraft(); } catch (e) { } setTimeout(loop, 3000); }, 4000);

  // ---------- 3) Tracker All Starlite: kolom dibaca dari JUDUL kolom (sheet sering berubah susunan) ----------
  // Coresite = kolom BK "PIC Coorsite", Admin IJE = kolom BL "PMO ADM"; HP = "Home Pass"
  if (typeof TRK !== "undefined" && typeof trkSlim === "function") {
    try { if (/^trk_cache_v[345]$/.test(TRK.key)) { ["trk_cache_v3", "trk_cache_v4", "trk_cache_v5"].forEach(function (k) { localStorage.removeItem(k); }); TRK.key = "trk_cache_v6"; } } catch (e) { }
    try { TRK_COLS.pic = "BK"; TRK_COLS.admin = "BL"; TRK_COLS.hp = "AZ"; } catch (e) { }
    var MAP = [["before", /^mitra history$/, "A"], ["after", /^mitra update$/, "B"], ["item", /^hp po$/, "H"], ["region", /^regional$/, "I"], ["stasiun", /^stasiun$/, "J"], ["po", /^no\s*po\s*pembangunan$/, "L"],
               ["status", /^status$/, "R"], ["don", /^(donasi|nominal donasi|donation|nilai donasi)$/, "AC"], ["hp", /^home\s*pass$/, "AZ"], ["pic", /^pic\s*coo?re?site$/, "BK"], ["admin", /^(pmo\s*adm(in)?|admin\s*ije)$/, "BL"]];
    // pengambilan per bagian kolom (lebih cepat dari CSV penuh): kolom ditentukan dari judul, bukan huruf tetap
    var colL = function (i) { var t = ""; i++; while (i > 0) { var m = (i - 1) % 26; t = String.fromCharCode(65 + m) + t; i = Math.floor((i - 1) / 26); } return t; };
    if (typeof trkFetchParts === "function" && typeof trkGetText === "function") {
      window.trkFetchParts = trkFetchParts = async function () {
        var t0 = Date.now(), got = 0, need = 0;
        var tick = setInterval(function () { try { trkTick(t0, "Mengambil data Tracker… " + got + "/" + (need || "?") + " bagian", 0, 5 + (need ? got / need * 90 : 3)); } catch (e) { } }, 400);
        try {
          var top = trkParseCsv(await trkGetText(TRK.url + "&range=" + encodeURIComponent("A1:ZZ8")));
          var h = top.findIndex(function (r) { return r.some(function (x) { return /^no\s*po\s*pembangunan$/i.test(String(x).trim()); }); });
          if (h < 0) throw new Error("Judul kolom Tracker tidak ditemukan");
          var H = top[h].map(function (x) { return String(x || "").replace(/\s+/g, " ").trim().toLowerCase(); }), ix = {};
          MAP.forEach(function (m) { var i = H.findIndex(function (x) { return m[1].test(x); }); ix[m[0]] = i >= 0 ? i : m[2] ? trkLetter(m[2]) : -1; });
          TRK.colsUsed = ix;
          var keys = MAP.map(function (m) { return m[0]; }).filter(function (k) { return ix[k] >= 0; });
          var cols = keys.map(function (k) { return ix[k]; }).filter(function (c, i, a) { return a.indexOf(c) === i; }).sort(function (a, b) { return a - b; });
          var groups = []; cols.forEach(function (c) { var g = groups[groups.length - 1]; if (g && c - g[1] <= 3) g[1] = c; else groups.push([c, c]); });
          need = groups.length;
          var parts = await Promise.all(groups.map(function (g) { return trkGetText(TRK.url + "&range=" + encodeURIComponent(colL(g[0]) + ":" + colL(g[1]))).then(function (t) { got++; return trkParseCsv(t); }); }));
          var at = function (r, c) { for (var i = 0; i < groups.length; i++) if (c >= groups[i][0] && c <= groups[i][1]) { var row = parts[i][r] || []; return row[c - groups[i][0]]; } return ""; };
          var n = Math.max.apply(null, parts.map(function (p) { return p.length; })), sx = function (v) { return String(v == null ? "" : v).replace(/\s+/g, " ").trim(); }, out = [];
          var g = function (r, k) { return ix[k] < 0 ? "" : at(r, ix[k]); };
          for (var r = h + 1; r < n; r++) {
            var st = sx(g(r, "stasiun")), po = sx(g(r, "po")); if (!st && !po) continue;
            out.push([sx(g(r, "before")), sx(g(r, "after")), sx(g(r, "item")), sx(g(r, "region")), st, po, sx(g(r, "status")), parseNumber(g(r, "don")), parseNumber(g(r, "hp")), sx(g(r, "pic")), sx(g(r, "admin"))]);
          }
          if (!out.length) throw new Error("Tracker kosong");
          return trkStore(out);
        } finally { clearInterval(tick); }
      };
    }
    window.trkSlim = trkSlim = function (rows) {
      var h = rows.findIndex(function (r, i) { return i < 8 && r.some(function (x) { return /^no\s*po\s*pembangunan$/i.test(String(x).trim()); }); }); if (h < 0) h = 2;
      var H = (rows[h] || []).map(function (x) { return String(x || "").replace(/\s+/g, " ").trim().toLowerCase(); }), ix = {};
      MAP.forEach(function (m) { var i = H.findIndex(function (x) { return m[1].test(x); }); ix[m[0]] = i >= 0 ? i : m[2] ? trkLetter(m[2]) : -1; });
      TRK.colsUsed = ix;
      var s = function (v) { return String(v == null ? "" : v).replace(/\s+/g, " ").trim(); }, g = function (r, k) { return ix[k] < 0 ? "" : r[ix[k]]; }, out = [];
      for (var i = h + 1; i < rows.length; i++) {
        var r = rows[i]; if (!r) continue;
        var st = s(g(r, "stasiun")), po = s(g(r, "po")); if (!st && !po) continue;
        out.push([s(g(r, "before")), s(g(r, "after")), s(g(r, "item")), s(g(r, "region")), st, po, s(g(r, "status")), parseNumber(g(r, "don")), parseNumber(g(r, "hp")), s(g(r, "pic")), s(g(r, "admin"))]);
      }
      return out;
    };
  }
})();

/* ===== v23 · BASTM (kolom T) berisi riwayat beberapa lampiran dalam satu kolom — tampil per bagian (mitra A, mitra B, …) ===== */
(function () {
  "use strict";
  var E = function (t) { return String(t == null ? "" : t).replace(/[&<>"']/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]; }); };
  function bastmList(t) {
    if (!t) return [];
    var L = t.links || [], list = [];
    try { if (L[5]) list = JSON.parse(L[5]) || []; } catch (e) { list = []; }
    if (!list.length && L[4]) list = [{ t: String(t.att_bastm || "BASTM").split("\n")[0], u: L[4] }];
    if (L[4] && list.length && !list.some(function (x) { return x.u === L[4]; })) list.push({ t: "Lampiran baru", u: L[4] });   // baru diunggah, sebelum link dimuat ulang
    return list;
  }
  window.bastmList = bastmList;
  function label(x, i) {
    var m = String(x.t || "").match(/ - ((?:PT|CV|PD|KOPERASI|UD)\.?\s[^-]+?)\s*-\s*(\d{2}-\d{2}-\d{4})/i);
    if (m) return { a: m[1].trim(), b: m[2].replace(/-/g, "/") };
    return { a: x.t || "Lampiran " + (i + 1), b: "" };
  }
  function open(u, ttl) { try { if (typeof sdPreviewUrl === "function") return sdPreviewUrl(u, ttl, "Kolom T"); } catch (e) { } window.open(u, "_blank", "noopener"); }
  window.bastmOpen = function (id, i) { var t = STATE.idx.byId.get(id), l = bastmList(t)[i]; if (l) open(l.u, "BASTM · bagian " + (i + 1) + " · " + label(l, i).a); };
  // tanda jumlah bagian di chip dokumen (tabel Status Dokumen, kartu, dll.)
  if (typeof docChip === "function") {
    var oChip = docChip;
    window.docChip = docChip = function (e, t) {
      var h = oChip.apply(this, arguments);
      try { if (t === "BASTM") { var n = bastmList(e).length; if (n > 1) h += '<span class="bst-n" title="' + n + ' lampiran BASTM (riwayat take over)">' + n + " bagian</span>"; } } catch (er) { }
      return h;
    };
  }
  // detail PO: daftar bagian BASTM di bawah kartu dokumen
  if (typeof renderTakeoverDetail === "function") {
    var oRT = renderTakeoverDetail;
    window.renderTakeoverDetail = renderTakeoverDetail = function (t) {
      var r = oRT.apply(this, arguments);
      try {
        var list = bastmList(t), body = document.getElementById("detail-modal-body");
        if (list.length > 1 && body && !body.querySelector(".bst-box")) {
          var lab = [].filter.call(body.querySelectorAll("span"), function (s) { return s.textContent.trim() === "BASTM"; })[0];
          var grid = lab && lab.closest(".grid");
          var html = '<div class="bst-box"><div class="bst-h"><i class="fa-solid fa-layer-group"></i><b>BASTM · ' + list.length + ' bagian</b><small>riwayat take over, tersimpan dalam satu kolom T</small></div><ol class="bst-l">'
            + list.map(function (x, i) { var lb = label(x, i); return '<li><button type="button" onclick="bastmOpen(\'' + t.id + "'," + i + ')"><span class="n">' + (i + 1) + '</span><span class="tx"><b>' + E(lb.a) + "</b>" + (lb.b ? "<small>" + E(lb.b) + "</small>" : "") + "</span>" + (i === list.length - 1 ? '<span class="nw">terbaru</span>' : "") + '<i class="fa-solid fa-arrow-up-right-from-square"></i></button></li>'; }).join("") + "</ol></div>";
          if (grid) grid.insertAdjacentHTML("afterend", html); else body.insertAdjacentHTML("beforeend", html);
          var card = lab && lab.closest(".rounded-lg"); if (card && !card.querySelector(".bst-n")) card.insertAdjacentHTML("beforeend", '<span class="bst-n">' + list.length + " bagian</span>");
        }
      } catch (e) { }
      return r;
    };
  }
})();

/* ===== v24: PO Close tidak dihitung "belum selesai" ===== */
(function () {
  if (typeof computeStatus !== "function" || typeof STATUS === "undefined") return;
  var RX = /\bpo\s*-?\s*clos|\bclosed?\b/i;
  var isClose = function (v) { return !!v && RX.test(String(v)); };
  window.isPoClose = isClose;
  if (!STATUS.close) {
    STATUS.close = { label: "PO Close", color: "#0ea5e9", icon: "fa-lock", badge: "bg-sky-500/15 text-sky-700 dark:text-sky-300 border-sky-500/40", dot: "bg-sky-500", desc: "PO sudah Close — tidak dihitung belum selesai" };
    var ci = STATUS_ORDER.indexOf("cancel");
    STATUS_ORDER.splice(ci < 0 ? STATUS_ORDER.length : ci, 0, "close");
  }
  var base = computeStatus;
  window.computeStatus = computeStatus = function (k, l, m, j) {
    if (isCancel(j) || isCancel(k) || isCancel(l) || isCancel(m)) return "cancel";
    if (isClose(j) || isClose(k) || isClose(l) || isClose(m)) return "close";
    return base(k, l, m, j);
  };
  var agg = aggregate;
  window.aggregate = aggregate = function (rows) {
    var t = agg(rows);
    try { t.close = (rows || []).filter(function (e) { return e.st === "close"; }).length; } catch (e) { t.close = 0; }
    return t;
  };
  if (typeof renderPicTable === "function") {
    var pic = renderPicTable;
    window.renderPicTable = renderPicTable = function (rows) {
      return pic((rows || []).map(function (e) { return e.st === "close" ? Object.assign({}, e, { st: "selesai" }) : e; }));
    };
  }
  function addOpt() {
    var s = document.getElementById("takeover-status-filter");
    if (s && !s.querySelector('option[value="close"]')) {
      var o = document.createElement("option"); o.value = "close"; o.textContent = "PO Close";
      var c = s.querySelector('option[value="cancel"]'); s.insertBefore(o, c || null);
    }
  }
  function recompute() {
    try {
      var ch = false;
      (STATE.takeover || []).forEach(function (e) { var st = computeStatus(e.k, e.l, e.m, e.status_to); if (st !== e.st) { e.st = st; ch = true; } });
      if (ch && typeof refreshAll === "function") refreshAll();
    } catch (e) { }
  }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", function () { addOpt(); recompute(); }); else { addOpt(); recompute(); }
})();

