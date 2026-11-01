
/* ===================== STARLITE v25 · Signing v2 + tabel tanpa pager =====================
   F1 Penanda tangan: kotak Paraf / Stempel / Tanggal / Isian / Centang · "Tanda tangani semua" atau "Pilih kotak"
      · simpan sementara (lanjut di HP mana pun) · daftar kotak & lompat halaman · zoom · pratinjau sebelum kirim
   F3 Semua tabel tanpa pager: data langsung tampil semua, digambar bertahap (ringan di HP)
   F4 PIN: ingat perangkat 90 hari · 5x salah → kunci 1 menit · reset PIN oleh pengirim + kirim WhatsApp
      · lupa PIN lewat kode email (opsional, bila email terdaftar)
   Butuh: supabase_signing_v2.sql (Supabase) & Kode.gs v12 (Apps Script, untuk kode email). */
(function () {
"use strict";
if (typeof sgRenderPdf !== 'function' || typeof SGP === 'undefined') return;
const $id = x => document.getElementById(x);
const E = s => (typeof esc === 'function' ? esc(s) : String(s == null ? '' : s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c])));
const toast = (m, t, ms) => { try { showToast(m, t || 'info', ms); } catch (e) { } };
const MM = 72 / 25.4;                       // 1 mm dalam point PDF
const PARAF_MM = { w: 22, h: 12 }, GAP_MM = 2;
const KINDS = {
    sign: { label: 'Tanda tangan', short: 'TTD', ic: 'fa-signature', mm: null, req: true },
    paraf: { label: 'Paraf', short: 'Paraf', ic: 'fa-pen-fancy', mm: [22, 12], req: false },
    date: { label: 'Tanggal', short: 'Tanggal', ic: 'fa-calendar-day', mm: [42, 6.5], req: false },
    text: { label: 'Isian teks', short: 'Isian', ic: 'fa-i-cursor', mm: [60, 7], req: true },
    check: { label: 'Centang', short: 'Centang', ic: 'fa-square-check', mm: [6, 6], req: false }
};
const TEXT_KINDS = { nama: 'Nama', jabatan: 'Jabatan', bebas: 'Isian bebas' };
const ftype = f => (f && KINDS[f.type]) ? f.type : 'sign';
const freq = f => f.req === undefined ? KINDS[ftype(f)].req : !!f.req;
const BULAN = ['Januari', 'Februari', 'Maret', 'April', 'Mei', 'Juni', 'Juli', 'Agustus', 'September', 'Oktober', 'November', 'Desember'];
const tglPanjang = iso => { const d = iso ? new Date(iso) : new Date(); return d.getDate() + ' ' + BULAN[d.getMonth()] + ' ' + d.getFullYear(); };
const b64png = s => String(s || '').replace(/^data:image\/png;base64,/, '');
const dataPng = s => !s ? '' : /^data:/.test(s) ? s : 'data:image/png;base64,' + s;
const extOf = (sigs, sid) => (sigs && sigs.__ext && sigs.__ext[sid]) || null;
// paraf milik penanda tangan (opsional, dipasang oleh penanda tangan sendiri) → kotak semu per halaman
function parafExtra(doc, sigs) {
    const out = [];
    for (const g of (doc && doc.signers) || []) {
        const ext = extOf(sigs, g.id); if (!ext || !ext.paraf || !ext.parafPos || g.status !== 'selesai') continue;
        for (const [pg, r] of Object.entries(ext.parafPos)) if (r && +pg > 0) out.push({ id: 'pf:' + g.id + ':' + pg, signer: g.id, page: +pg, x: +r.x, y: +r.y, w: +r.w, h: +r.h, type: 'paraf', pseudo: true });
    }
    return out;
}
function drawParafExtra(layer, n, doc, sigs) {
    layer.querySelectorAll('.sgv-pfx').forEach(e => e.remove());
    parafExtra(doc, sigs).filter(f => f.page === n).forEach(f => {
        const el = document.createElement('div'), ext = extOf(sigs, f.signer) || {};
        el.className = 'sg-field sgv t-paraf signed sgv-par sgv-pfx';
        Object.assign(el.style, { left: f.x * 100 + '%', top: f.y * 100 + '%', width: f.w * 100 + '%', height: f.h * 100 + '%' });
        el.innerHTML = `<img src="${dataPng(ext.paraf)}" alt="paraf">`; layer.appendChild(el);
    });
}
const sbHas = () => typeof sbOn === 'function' && sbOn();
window.SGV2 = { parafExtra, drawParafExtra, KINDS, ftype, freq, MM, PARAF_MM, GAP_MM, TEXT_KINDS, tglPanjang, extOf, dataPng, b64png, E, toast, $id };

/* =====================================================================
   PDF FINAL — semua jenis kotak. Urutan: teks dokumen → stempel → coretan TTD.
   ===================================================================== */
const STAMP_OPACITY = 0.85;
function stampRect(bx, by, bw, bh, pos) {     // stempel di atas kotak TTD (koordinat PDF, y dari bawah)
    const s = Math.min(bh * 1.05, bw * 0.62);
    const x = pos === 'r' ? bx + bw - s - bw * 0.02 : pos === 'c' ? bx + (bw - s) / 2 : bx + bw * 0.02;
    return { x, y: by + (bh - s) / 2, w: s, h: s };
}
function fitImg(img, x, y, w, h) { const r = Math.min(w / img.width, h / img.height), iw = img.width * r, ih = img.height * r; return { x: x + (w - iw) / 2, y: y + (h - ih) / 2, width: iw, height: ih }; }
sgStamp = async function (bytes, doc, signatures) {
    const L = await loadPdfLib();
    const pdf = await L.PDFDocument.load(bytes, { ignoreEncryption: true });
    const font = await pdf.embedFont(L.StandardFonts.Helvetica), bold = await pdf.embedFont(L.StandardFonts.HelveticaBold);
    const sigs = signatures || {}, cache = new Map();
    const emb = async b64 => { const k = b64png(b64); if (!k) return null; if (cache.has(k)) return cache.get(k); let im = null; try { im = await pdf.embedPng(b64ToBytes(k)); } catch (e) { } cache.set(k, im); return im; };
    const pages = pdf.getPages(), byId = Object.fromEntries((doc.signers || []).map(g => [g.id, g]));
    const ink = L.rgb(0.04, 0.12, 0.36), grey = L.rgb(0.35, 0.4, 0.5);
    const fitText = (t, f, w, h, max) => { let size = Math.min(max || 11, h * 0.78); while (size > 4 && f.widthOfTextAtSize(t, size) > w - 2) size -= 0.25; return size; };
    // 1) stempel lebih dulu (di bawah coretan) · 2) gambar & teks
    const later = [];
    for (const f of (doc.fields || []).concat(parafExtra(doc, sigs))) {
        const pg = pages[f.page - 1], g = byId[f.signer]; if (!pg || !g) continue;
        const main = sigs[f.signer], ext = extOf(sigs, f.signer) || {}, t = ftype(f);
        if (!main && !ext.v) continue;                                  // belum tanda tangan
        if (!f.pseudo && ext.filled && ['sign', 'paraf', 'stamp'].includes(t) && !ext.filled.includes(f.id)) continue;   // kotak opsional yang dikosongkan
        const { width: W, height: H } = pg.getSize();
        const bx = f.x * W, bw = f.w * W, bh = f.h * H, by = H - (f.y + f.h) * H;
        if (t === 'sign') {
            const off = (ext.stampOff || []).includes(f.id);
            if (ext.stamp && ext.stamp.img && !off) { const st = await emb(ext.stamp.img); if (st) { const r = stampRect(bx, by, bw, bh, (ext.stampPos || {})[f.id] || 'l'); pg.drawImage(st, Object.assign(fitImg(st, r.x, r.y, r.w, r.h), { opacity: STAMP_OPACITY })); } }
            later.push(async () => {
                const img = await emb(main); if (!img) return;
                const cap = Math.min(7, Math.max(4, bh * 0.12)), ah = bh - cap * 1.6;
                pg.drawImage(img, fitImg(img, bx, by + cap * 1.5, bw, ah));
                const txt = sgAscii('Ditandatangani ' + sgTime(g.signedAt || new Date().toISOString()));
                let size = cap; while (size > 3 && font.widthOfTextAtSize(txt, size) > bw) size -= 0.3;
                pg.drawText(txt, { x: bx + (bw - font.widthOfTextAtSize(txt, size)) / 2, y: by + 1, size, font, color: grey });
            });
        } else if (t === 'stamp') {
            if (ext.stamp && ext.stamp.img) { const st = await emb(ext.stamp.img); if (st) pg.drawImage(st, Object.assign(fitImg(st, bx, by, bw, bh), { opacity: 0.92 })); }
        } else if (t === 'paraf') {
            later.push(async () => { const img = await emb(ext.paraf || main); if (img) pg.drawImage(img, fitImg(img, bx + 0.5, by + 0.5, bw - 1, bh - 1)); });
        } else if (t === 'date') {
            const txt = sgAscii(tglPanjang(g.signedAt)), size = fitText(txt, font, bw, bh, 11);
            pg.drawText(txt, { x: bx + 1, y: by + (bh - size) / 2 + size * 0.18, size, font, color: ink });
        } else if (t === 'text') {
            const v = String((ext.vals || {})[f.id] || '').trim(); if (!v) continue;
            const txt = sgAscii(v), size = fitText(txt, font, bw, bh, 11);
            pg.drawText(txt, { x: bx + 1, y: by + (bh - size) / 2 + size * 0.18, size, font, color: ink });
        } else if (t === 'check') {
            const on = String((ext.vals || {})[f.id] || '') === 'true', s = Math.min(bw, bh);
            const x0 = bx + (bw - s) / 2, y0 = by + (bh - s) / 2;
            pg.drawRectangle({ x: x0, y: y0, width: s, height: s, borderColor: ink, borderWidth: Math.max(0.5, s * 0.07) });
            if (on) { const lw = Math.max(0.8, s * 0.13); pg.drawLine({ start: { x: x0 + s * 0.18, y: y0 + s * 0.52 }, end: { x: x0 + s * 0.42, y: y0 + s * 0.24 }, thickness: lw, color: ink }); pg.drawLine({ start: { x: x0 + s * 0.42, y: y0 + s * 0.24 }, end: { x: x0 + s * 0.84, y: y0 + s * 0.8 }, thickness: lw, color: ink }); }
        }
    }
    for (const fn of later) await fn();
    pdf.setTitle(doc.name); pdf.setProducer('STARLITE VM · Signing Document');
    void bold;
    return new Uint8Array(await pdf.save());
};

/* =====================================================================
   TAMPILAN KOTAK YANG SUDAH DIISI (penanda tangan lain / pengirim / pratinjau)
   ===================================================================== */
function signedHtml(f, g, sigs) {
    const t = ftype(f), main = sigs[f.signer], ext = extOf(sigs, f.signer) || {};
    if (ext.filled && ['sign', 'paraf', 'stamp'].includes(t) && !ext.filled.includes(f.id)) return { cls: 'sgv-empty', html: '' };
    if (t === 'sign') {
        const st = ext.stamp && ext.stamp.img && !(ext.stampOff || []).includes(f.id) ? `<img class="sgv-stp pos-${E((ext.stampPos || {})[f.id] || 'l')}" src="${dataPng(ext.stamp.img)}" alt="">` : '';
        return { cls: 'signed', html: `${st}<img class="sgv-sig" src="${dataPng(main)}" alt=""><em class="sg-when">${E(sgTime(g.signedAt))}</em>` };
    }
    if (t === 'paraf') return { cls: 'signed sgv-par', html: `<img src="${dataPng(ext.paraf || main)}" alt="">` };
    if (t === 'stamp') return { cls: 'signed sgv-stamp', html: ext.stamp ? `<img src="${dataPng(ext.stamp.img)}" alt="">` : '' };
    if (t === 'date') return { cls: 'signed sgv-txt', html: `<span>${E(tglPanjang(g.signedAt))}</span>` };
    if (t === 'text') return { cls: 'signed sgv-txt', html: `<span>${E((ext.vals || {})[f.id] || '')}</span>` };
    if (t === 'check') return { cls: 'signed sgv-chk', html: String((ext.vals || {})[f.id]) === 'true' ? '<i class="fa-solid fa-check"></i>' : '' };
    return { cls: 'signed', html: '' };
}
function pendingHtml(f, g) {
    const k = KINDS[ftype(f)];
    return `<span class="sgv-oth"><i class="fa-solid ${k.ic}"></i>${ftype(f) === 'sign' ? '' : E(k.short) + ' · '}${E(g.name || '')}</span>`;
}
window.SGV2.signedHtml = signedHtml; window.SGV2.pendingHtml = pendingHtml;

// pengirim: "Lihat dokumen" menampilkan semua jenis kotak
sgOwnerView = async function (id) {
    const d = sgDoc(id); if (!d) return;
    const m = document.createElement('div'); m.id = 'sg-ov'; m.className = 'fixed inset-0 z-[90] flex items-center justify-center p-2 md:p-6 bg-cyberDark/70 backdrop-blur-sm';
    m.onclick = e => { if (e.target === m) m.remove(); };
    m.innerHTML = `<div class="sd-pv"><div class="flex items-center gap-3 px-4 py-3 border-b border-slate-200/70 dark:border-slate-800"><i class="fa-solid fa-file-signature text-rose-500"></i><div class="min-w-0 flex-1"><p class="text-[13px] font-extrabold text-slate-900 dark:text-white truncate">${E(d.name)}</p><p id="sg-ov-sub" class="text-[10.5px] text-slate-500">Memuat…</p></div>
        <button id="sg-ov-dl" class="btn btn-primary !py-2" disabled><i class="fa-solid fa-download"></i><span class="hidden md:inline">Unduh</span></button><button onclick="$('sg-ov').remove()" class="icon-btn"><i class="fa-solid fa-xmark"></i></button></div>
        <div id="sg-ov-pages" class="sg-pages flex-1 overflow-y-auto p-3"></div></div>`;
    document.body.appendChild(m);
    try {
        const cached = await SGC.get('orig_' + id);
        const [f, b] = await Promise.all([cached ? null : callApi('sign.file', { id, which: 'original' }, 120000), callApi('sign.bundle', { id, partial: true, withPdf: false }, 60000)]);
        const bytes = cached || b64ToBytes(f.pdf), doc = b.doc, sigs = b.signatures || {};
        if (!cached) SGC.put('orig_' + id, bytes);
        const n = doc.signers.filter(g => g.status === 'selesai').length;
        const part = doc.signers.filter(g => g.status !== 'selesai' && g.draft).map(g => `${g.name} sebagian ${g.draft.n}/${g.draft.total}`);
        $id('sg-ov-sub').textContent = `${n}/${doc.signers.length} sudah tanda tangan${part.length ? ' · ' + part.join(' · ') : ''} — isian yang sudah masuk ditampilkan`;
        const byId = Object.fromEntries(doc.signers.map(g => [g.id, g]));
        await sgRenderPdf($id('sg-ov-pages'), bytes, 860, (pg, p) => { drawParafExtra(pg.layer, p, doc, sigs); doc.fields.filter(x => x.page === p).forEach(x => {
            const g = byId[x.signer] || {}, el = document.createElement('div');
            Object.assign(el.style, { left: x.x * 100 + '%', top: x.y * 100 + '%', width: x.w * 100 + '%', height: x.h * 100 + '%' });
            if (g.status === 'selesai' && (sigs[x.signer] || extOf(sigs, x.signer))) { const o = signedHtml(x, g, sigs); el.className = 'sg-field sgv t-' + ftype(x) + ' ' + o.cls; el.innerHTML = o.html; }
            else { el.className = 'sg-field other sgv t-' + ftype(x); el.innerHTML = pendingHtml(x, g); }
            pg.layer.appendChild(el);
        }); });
        const dl = $id('sg-ov-dl'); dl.disabled = false;
        dl.onclick = async () => { try { sgSaveBlob(await sgStamp(bytes, doc, sigs), d.name + (n === doc.signers.length ? ' - TTD Lengkap.pdf' : ` - TTD ${n} dari ${doc.signers.length}.pdf`)); } catch (e) { toast(e.message, 'error'); } };
    } catch (e) { $id('sg-ov-pages').innerHTML = `<p class="p-6 text-center text-rose-600 text-[12px]">${E(e.message)}</p>`; }
};

/* =====================================================================
   F3 · SEMUA TABEL TANPA PAGER — semua data tampil, digambar bertahap
   ===================================================================== */
const PG_TOTAL = {
    'takeover-pager': () => (STATE.takeover || []).length, 'perseroan-pager': () => (STATE.perseroan || []).length, 'sp-pager': () => (STATE.sp || []).length,
    'spk-pager': () => (STATE.spk || []).length, 'pc-pager': () => (STATE.pocancel || []).length,
    'trk-pager': () => (typeof TRK !== 'undefined' && TRK.rows ? TRK.rows.length : 0),
    'rn-pager': () => { try { return (STATE[RN.tab] || []).length; } catch (e) { return 0; } }
};
const PG = new Map();            // elId → { total, filterKey }
const idle = fn => (window.requestIdleCallback ? requestIdleCallback(fn, { timeout: 350 }) : setTimeout(fn, 60));
function quietRender(fn) {        // render ulang tanpa memindah posisi scroll
    const y = scrollY, siv = Element.prototype.scrollIntoView;
    Element.prototype.scrollIntoView = function () { };
    try { fn(); } finally { Element.prototype.scrollIntoView = siv; }
    if (Math.abs(scrollY - y) > 2) window.scrollTo({ top: y, behavior: 'instant' });
}
// TABEL BESAR: semua baris "ada" (tinggi scroll penuh), tapi yang digambar hanya sekitar layar (±60 baris).
// Penyebab macet sebelumnya: tiap sel kolom pertama "menempel" (sticky) = 1 lapisan grafis per baris → ratusan lapisan.
const TB_OF = { 'takeover-pager': 'takeover-table-body', 'perseroan-pager': 'perseroan-table-body', 'sp-pager': 'sp-table-body', 'spk-pager': 'spk-table-body', 'pc-pager': 'pc-table-body', 'trk-pager': 'trk-body', 'rn-pager': 'rn-table-body', 'doc-pager': 'doc-table-body' };
const IH = Object.getOwnPropertyDescriptor(Element.prototype, 'innerHTML');
const VW_MIN = 150, VW_PAD = 900, VW_EXTRA = 20;
const VW = new Set();
function vwInstall(tb) {
    if (!tb || tb.__vw || !IH) return;
    const S = tb.__vw = { on: false, rows: [], h: null, avg: 64, a: 0, b: 0 };
    Object.defineProperty(tb, 'innerHTML', {
        configurable: true, get() { return IH.get.call(this); },
        set(v) {
            v = String(v);
            const rows = v.length < 20000 ? null : v.split(/(?<=<\/tr>)/i).filter(r => r.trim());
            if (!rows || rows.length <= VW_MIN) { S.on = false; VW.delete(tb); return IH.set.call(this, v); }
            S.on = true; S.rows = rows; S.h = new Float64Array(rows.length); S.a = 0; S.b = Math.min(rows.length, 60);
            VW.add(tb); try { const t = tb.closest('.data-scroll') || tb.closest('table'); t.style.overflowAnchor = 'none'; tb.closest('table').style.overflowAnchor = 'none'; tb.style.overflowAnchor = 'none'; } catch (e) { } paint(); requestAnimationFrame(() => vwUpdate(tb));
        }
    });
    const block = () => getComputedStyle(tb).display === 'block';
    const cols = () => { const t = tb.closest('table'); return t && t.tHead && t.tHead.rows[0] ? t.tHead.rows[0].cells.length : 1; };
    const spacer = px => { px = Math.round(px); if (px <= 0) return ''; return block() ? `<tr class="vw-sp" aria-hidden="true" style="display:block;height:${px}px"></tr>` : `<tr class="vw-sp" aria-hidden="true"><td colspan="${cols()}" style="height:${px}px;padding:0;border:0"></td></tr>`; };
    S.H = i => S.h[i] || S.avg;
    S.sum = (a, b) => { let t = 0; for (let i = a; i < b; i++) t += S.H(i); return t; };
    function paint() {
        IH.set.call(tb, spacer(S.sum(0, S.a)) + S.rows.slice(S.a, S.b).join('') + spacer(S.sum(S.b, S.rows.length)));
        const trs = [...tb.children].filter(x => !x.classList.contains('vw-sp'));
        let tot = 0;
        trs.forEach((tr, k) => { const r = tr.getBoundingClientRect(), nx = trs[k + 1]; const h = nx ? nx.getBoundingClientRect().top - r.top : r.height; if (h > 0) { S.h[S.a + k] = h; tot += h; } });
        if (trs.length) S.avg = tot / trs.length || S.avg;
        try { if (typeof labelCards === 'function' && tb.id) labelCards(tb.id); } catch (e) { }
    }
    S.paint = paint;
}
function vwUpdate(tb) {
    const S = tb.__vw; if (!S || !S.on || !tb.isConnected || !tb.offsetParent) return;
    const n = S.rows.length, r = tb.getBoundingClientRect();
    const top = -r.top - VW_PAD, bot = -r.top + innerHeight + VW_PAD;
    let acc = 0, i0 = 0; while (i0 < n && acc + S.H(i0) < top) { acc += S.H(i0); i0++; }
    let i1 = i0; while (i1 < n && acc < bot) { acc += S.H(i1); i1++; }
    if (i0 >= S.a && i1 <= S.b) return;
    // jangkar: baris yang sedang terlihat paling atas → posisinya dijaga setelah digambar ulang
    let anchor = -1, aTop = 0;
    const rowsNow = [...tb.children].filter(x => !x.classList.contains('vw-sp'));
    for (let k = 0; k < rowsNow.length; k++) { const t = rowsNow[k].getBoundingClientRect().top; if (t >= 0 && t < innerHeight) { anchor = S.a + k; aTop = t; break; } }
    S.a = Math.max(0, i0 - VW_EXTRA); S.b = Math.min(n, Math.max(i1 + VW_EXTRA, S.a + 40));
    S.paint();
    if (anchor >= S.a && anchor < S.b) {
        const el = [...tb.children].filter(x => !x.classList.contains('vw-sp'))[anchor - S.a];
        if (el) { const d = el.getBoundingClientRect().top - aTop; if (Math.abs(d) > 1) window.scrollBy(0, d); }
    }
}
let vwRaf = 0;
const vwKick = () => { if (vwRaf) return; vwRaf = requestAnimationFrame(() => { vwRaf = 0; VW.forEach(vwUpdate); }); };
addEventListener('scroll', vwKick, { passive: true }); addEventListener('resize', vwKick);
window.SGV2.vwStats = () => [...VW].map(tb => ({ id: tb.id, rows: tb.__vw.rows.length, drawn: tb.__vw.b - tb.__vw.a, a: tb.__vw.a, b: tb.__vw.b }));
const chunkBody = vwInstall;
renderPager = function (elId, vs, total, onChange) {
    try { chunkBody($id(TB_OF[elId])); } catch (e) { }
    const el = $id(elId); if (!el) return;
    const st = PG.get(elId) || {}, all = (PG_TOTAL[elId] || (() => 0))();
    vs.page = 1;
    const shown = Math.min(total, vs.size);
    if (shown < total) {                        // sisa baris: langsung menyusul (tanpa tombol / halaman)
        if (!st.busy) { st.busy = true; PG.set(elId, st); idle(() => { st.busy = false; vs.size = 1e9; quietRender(onChange); }); }
    }
    // ganti filter / pencarian → kembali ke baris pertama tabel
    if (st.total !== undefined && st.total !== total) {
        const panel = el.closest('.glass-panel') || el.parentElement, top = panel ? panel.getBoundingClientRect().top : 0;
        const lim = parseInt(getComputedStyle(document.documentElement).getPropertyValue('--vm-top')) || 70;
        if (panel && top < lim - 4) window.scrollTo({ top: scrollY + top - lim - 8, behavior: 'instant' });
    }
    st.total = total; PG.set(elId, st);
    const filtered = all && total !== all;
    el.innerHTML = `<div class="vm-allrows"><i class="fa-solid fa-table-list"></i>${filtered ? `<b>${fmtInt(total)}</b> dari ${fmtInt(all)} data <span>(difilter)</span>` : `<b>${fmtInt(total)}</b> data`}${shown < total ? `<em><i class="fa-solid fa-circle-notch fa-spin"></i>menampilkan semua…</em>` : ''}</div>`;
};
// tabel yang sudah tampil sebelum addon ini jalan → langsung tampil semua
setTimeout(() => {
    try { [typeof VS_TO !== 'undefined' && VS_TO, typeof VS_PS !== 'undefined' && VS_PS, typeof VS_SP !== 'undefined' && VS_SP, typeof VS_SPK !== 'undefined' && VS_SPK, typeof VS_PC !== 'undefined' && VS_PC, typeof VS_DOC !== 'undefined' && VS_DOC].forEach(v => { if (v) v.size = 1e9; }); } catch (e) { }
    try { Object.values(TB_OF).forEach(id => chunkBody($id(id))); } catch (e) { }
    try { if (typeof renderTakeoverPage === 'function' && STATE.takeover && STATE.takeover.length) quietRender(renderTakeoverPage); } catch (e) { }
}, 0);

/* =====================================================================
   F1 · HALAMAN PENANDA TANGAN — semua jenis kotak, sebagian / semua, simpan sementara
   ===================================================================== */
const SGV = { id: '', sig: null, paraf: null, stamp: null, filled: new Set(), vals: {}, stampOff: new Set(), stampPos: {}, mode: 'all', dirty: false, stamps: null, zoom: 1, savedAt: '', remember: false, timer: 0, parafOn: false, parafPos: {} };
window.SGV2.state = SGV;
const curDoc = () => SGP.data && SGP.data.doc;
const curMe = () => SGP.data && SGP.data.me;
const myFields = () => { const d = curDoc(), me = curMe(); return d && me ? d.fields.filter(f => f.signer === me.id) : []; };
const fieldById = id => (curDoc() ? curDoc().fields.find(f => f.id === id) : null);
const isDone = f => { const t = ftype(f); if (t === 'sign' || t === 'paraf') return SGV.filled.has(f.id); if (t === 'stamp') return SGV.filled.has(f.id) && !!SGV.stamp; if (t === 'text') return !!String(SGV.vals[f.id] || '').trim(); if (t === 'check') return SGV.vals[f.id] === 'true'; return true; };
function progress() {
    const L = myFields().filter(f => ftype(f) !== 'date');
    return { n: L.filter(isDone).length, total: L.length, left: L.filter(f => freq(f) && !isDone(f)) };
}
const active = () => { const r = SGP.data, me = curMe(); return !!(r && me && !r.isFinal && me.status !== 'selesai' && SGV.id === r.doc.id); };
function textDefault(f) { const me = curMe() || {}; return f.kind === 'nama' ? me.name || '' : f.kind === 'jabatan' ? me.jabatan || '' : ''; }

function prepare(r) {
    if (!r || !r.doc || !r.me) return;
    if (SGV.id === r.doc.id && SGV.signer === r.me.id) return;
    Object.assign(SGV, { id: r.doc.id, signer: r.me.id, sig: null, paraf: null, stamp: null, filled: new Set(), vals: {}, stampOff: new Set(), stampPos: {}, mode: 'pick', dirty: false, savedAt: '', resumed: null, parafOn: false, parafPos: {} });
    const mine = r.doc.fields.filter(f => f.signer === r.me.id);
    mine.forEach(f => { if (ftype(f) === 'text') SGV.vals[f.id] = textDefault(f); if (ftype(f) === 'check') SGV.vals[f.id] = 'false'; });
    const dr = r.draft;
    if (dr && typeof dr === 'object') {
        const ids = new Set(mine.map(f => f.id));
        SGV.sig = dr.sig || null; SGV.paraf = dr.paraf || null;
        if (dr.parafOn && dr.paraf && dr.parafPos && typeof dr.parafPos === 'object') { SGV.parafOn = true; SGV.parafPos = dr.parafPos; }
        (dr.filled || []).forEach(id => ids.has(id) && SGV.filled.add(id));
        Object.entries(dr.vals || {}).forEach(([k, v]) => { if (ids.has(k)) SGV.vals[k] = String(v); });
        (dr.stampOff || []).forEach(id => SGV.stampOff.add(id));
        SGV.stampPos = dr.stampPos || {}; SGV.mode = 'pick';
        SGV.resumed = { n: dr.n, total: dr.total };
        if (SGV.sig) { SGP.sig = SGV.sig; SGP.lastSig = SGP.lastSig || SGV.sig; }
    }
}

/* ---------- kotak milik saya ---------- */
function asDiv(el) {
    if (el.tagName !== 'BUTTON') return el;
    const d = document.createElement('div'); d.style.cssText = el.style.cssText; d.dataset.fid = el.dataset.fid; el.replaceWith(d); return d;
}
function stampOverlay(f) {
    if (!SGV.stamp || !SGV.stamp.img || SGV.stampOff.has(f.id)) return '';
    return `<img class="sgv-stp pos-${E(SGV.stampPos[f.id] || 'l')}" src="${dataPng(SGV.stamp.img)}" alt="">`;
}
function paintOwn(el, f) {
    const t = ftype(f), k = KINDS[t], me = curMe() || {}, req = freq(f);
    el.onclick = null;
    if (t === 'sign') {
        const on = SGV.filled.has(f.id) && SGV.sig;
        el.className = 'sg-field own sgv t-sign' + (on ? ' filled' : '');
        el.innerHTML = on ? `${stampOverlay(f)}<img class="sgv-sig" src="${SGV.sig}" alt="tanda tangan"><em>ubah</em>`
            : `<span class="sg-own"><i class="fa-solid fa-signature"></i><b>${E(me.name || '')}</b><small>${SGV.mode === 'pick' ? 'Ketuk untuk tanda tangan di kotak ini' : 'Ketuk untuk tanda tangan'}</small></span>`;
        el.onclick = ev => { ev.stopPropagation(); tap(f.id, el); };
        return el;
    }
    el = asDiv(el);
    el.className = 'sg-field own2 sgv t-' + t + (isDone(f) ? ' filled' : '') + (req ? ' req' : '');
    if (t === 'paraf') {
        el.innerHTML = SGV.filled.has(f.id) && SGV.paraf ? `<img src="${SGV.paraf}" alt="paraf">` : `<span class="sgv-lbl"><i class="fa-solid ${k.ic}"></i>Paraf</span>`;
        el.onclick = ev => { ev.stopPropagation(); tap(f.id, el); };
    } else if (t === 'date') {
        el.innerHTML = `<span class="sgv-auto" title="Terisi otomatis tanggal saat Anda tanda tangan">${E(tglPanjang())}</span>`;
    } else if (t === 'text') {
        el.innerHTML = `<input class="sgv-in" value="${E(SGV.vals[f.id] || '')}" placeholder="${E(f.label || TEXT_KINDS[f.kind] || 'Isi di sini')}${req ? ' *' : ''}" aria-label="${E(f.label || 'Isian')}">`;
        const inp = el.querySelector('input');
        inp.onclick = ev => ev.stopPropagation();
        inp.oninput = () => { SGV.vals[f.id] = inp.value; el.classList.toggle('filled', isDone(f)); changed(true); };
        const fit = () => { inp.style.fontSize = Math.max(6, Math.min(15, el.clientHeight * 0.62)) + 'px'; };
        requestAnimationFrame(fit);
    } else if (t === 'check') {
        const on = SGV.vals[f.id] === 'true';
        el.innerHTML = `<button type="button" class="sgv-cb ${on ? 'on' : ''}" title="${E(f.label || 'Centang')}">${on ? '<i class="fa-solid fa-check"></i>' : ''}</button>${f.label ? `<span class="sgv-cbl">${E(f.label)}</span>` : ''}`;
        el.querySelector('button').onclick = ev => { ev.stopPropagation(); SGV.vals[f.id] = on ? 'false' : 'true'; paintOwn(el, f); changed(); };
    }
    return el;
}
function decorate(pg, n) {
    const r = SGP.data; if (!r || !r.doc || r.isFinal) return;
    const d = r.doc, me = r.me, sigs = SGP.sigs || {}, byId = Object.fromEntries(d.signers.map(g => [g.id, g]));
    d.fields.filter(f => f.page === n).forEach(f => {
        let el = pg.layer.querySelector(`[data-fid="${CSS.escape(f.id)}"]`); if (!el) return;
        const g = byId[f.signer] || {}, t = ftype(f), own = f.signer === me.id;
        if (g.status === 'selesai' && (sigs[f.signer] || extOf(sigs, f.signer))) {
            const o = signedHtml(f, g, sigs); el = asDiv(el); el.className = 'sg-field sgv t-' + t + ' ' + o.cls; el.innerHTML = o.html; el.onclick = null; return;
        }
        if (own && active()) { paintOwn(el, f); return; }
        if (!own) { el = asDiv(el); el.className = 'sg-field other sgv t-' + t; el.innerHTML = pendingHtml(f, g); }
    });
    drawParafExtra(pg.layer, n, d, sigs); paintMyParaf(pg.layer, n);
}
function repaint() {
    if (!active()) return;
    myFields().forEach(f => { const el = document.querySelector(`#sg-pages [data-fid="${CSS.escape(f.id)}"]`); if (el && !(ftype(f) === 'text' && el.contains(document.activeElement))) paintOwn(el, f); });
    bar();
}
function changed(soft) {
    SGV.dirty = true;
    if (!soft) repaint(); else bar();
    clearTimeout(SGV.timer); SGV.timer = setTimeout(() => saveDraft(true), 8000);
}
(function hookRender() {
    const baseRP = sgRenderPdf;
    sgRenderPdf = function (container, bytes, maxW, onPage) {
        if (container && container.id === 'sg-pages' && SGP.data && SGP.data.doc && typeof onPage === 'function') {
            const o = onPage; onPage = function (pg, n) { const out = o.apply(this, arguments); try { decorate(pg, n); } catch (e) { console.warn('sgv', e); } return out; };
        }
        return baseRP.call(this, container, bytes, maxW, onPage);
    };
    const baseRender = sgPublicRender;
    sgPublicRender = async function () {
        try { prepare(SGP.data); } catch (e) { console.warn(e); }
        const out = await baseRender.apply(this, arguments);
        try { afterRender(); } catch (e) { console.warn('sgv', e); }
        return out;
    };
})();

/* ---------- isi kotak ---------- */
async function padTitled(name, title, ok) {
    const p = sgPad(name);
    setTimeout(() => { const m = [...document.querySelectorAll('.proc-card')].pop(); if (!m) return; const h = m.querySelector('h3'); if (h) h.innerHTML = `<i class="fa-solid fa-pen-fancy text-cyan-600 mr-1.5"></i>${E(title)}`; const b = m.querySelector('[data-ok]'); if (b) b.innerHTML = `<i class="fa-solid fa-check"></i>${E(ok)}`; }, 0);
    return p;
}
async function ensureSig(force) {
    if (SGV.sig && !force) return true;
    const me = curMe() || {};
    let img = !force && ((typeof SGS !== 'undefined' && SGS.sig) || SGP.lastSig);
    if (img) toast('Tanda tangan tersimpan dipakai — ketuk kotak yang sudah terisi untuk menggantinya', 'info', 5000);
    else img = await sgPad(me.name);
    if (!img) return false;
    SGV.sig = img; SGP.sig = img; SGP.lastSig = img; return true;
}
async function ensureParaf(force) {
    if (SGV.paraf && !force) return true;
    const me = curMe() || {};
    const img = (!force && SGP.lastParaf) || await padTitled(me.name, 'Buat Paraf', 'Pakai Paraf');
    if (!img) return false;
    SGV.paraf = img; SGP.lastParaf = img; return true;
}
async function tap(fid, el) {
    if (!active()) return;
    const f = fieldById(fid); if (!f) return;
    const t = ftype(f);
    if (SGV.filled.has(fid)) return boxMenu(f, el);
    if (t === 'sign' && !(await ensureSig())) return;
    if (t === 'paraf' && !(await ensureParaf())) return;
    if (SGV.mode === 'all') myFields().filter(x => ftype(x) === t).forEach(x => SGV.filled.add(x.id)); else SGV.filled.add(fid);
    changed();
    if (SGV.mode === 'all') { const n = myFields().filter(x => ftype(x) === t).length; if (n > 1) toast(`${n} kotak ${KINDS[t].label.toLowerCase()} terisi sekaligus. Mau satu per satu? Pilih "Pilih kotak".`, 'success', 4500); }
}
async function signAll() {
    if (!active()) return;
    const L = myFields(), has = t => L.some(f => ftype(f) === t && (freq(f) || t !== 'stamp'));
    if (has('sign') && !(await ensureSig())) return;
    const parOk = L.some(f => ftype(f) === 'paraf') ? await ensureParaf() : false;   // paraf opsional: dilewati bila dibatalkan
    L.forEach(f => { const t = ftype(f); if (t === 'sign' || (t === 'paraf' && parOk)) SGV.filled.add(f.id); });
    changed();
    const p = progress();
    if (p.left.length) { toast('Lengkapi isian yang ditandai merah', 'info', 5000); jumpTo(p.left[0]); }
    else { toast('Semua kotak terisi — periksa lalu klik Kirim', 'success'); const go = $id('sg-go'); if (go) go.scrollIntoView({ behavior: 'smooth', block: 'center' }); }
}
function setMode(m) { SGV.mode = m; tools(); repaint(); if (m === 'pick') toast('Ketuk kotak satu per satu. Kotak yang sudah terisi bisa diketuk lagi untuk dikosongkan / diganti.', 'info', 5000); }
function closeMenu() { const x = $id('sgv-menu'); if (x) x.remove(); }
function boxMenu(f, el) {
    closeMenu();
    const t = ftype(f), items = [];
    items.push(['fa-eraser', 'Kosongkan kotak ini', () => { SGV.filled.delete(f.id); changed(); }]);
    if (t === 'sign') {
        items.push(['fa-pen', 'Ganti tanda tangan (semua kotak)', async () => { if (await ensureSig(true)) changed(); }]);
    } else if (t === 'paraf') items.push(['fa-pen-fancy', 'Ganti paraf (semua kotak)', async () => { if (await ensureParaf(true)) changed(); }]);
    const m = document.createElement('div'); m.id = 'sgv-menu'; m.dataset.at = Date.now();
    m.innerHTML = items.map(([ic, l], i) => `<button data-i="${i}"><i class="fa-solid ${ic}"></i>${E(l)}</button>`).join('');
    document.body.appendChild(m);
    m.querySelectorAll('[data-i]').forEach(b => b.onclick = ev => { ev.stopPropagation(); closeMenu(); items[+b.dataset.i][2](); });
    const r = el.getBoundingClientRect(), w = m.offsetWidth, h = m.offsetHeight;
    m.style.left = Math.max(8, Math.min(innerWidth - w - 8, r.left)) + 'px';
    m.style.top = (r.bottom + h + 8 > innerHeight ? Math.max(8, r.top - h - 6) : r.bottom + 6) + 'px';
    setTimeout(() => document.addEventListener('click', closeMenu, { once: true }), 0);
}
addEventListener('scroll', () => { const x = $id('sgv-menu'); if (x && Date.now() - (+x.dataset.at || 0) > 450) closeMenu(); }, { passive: true });


/* ---------- paraf opsional (hanya dari penanda tangan) ---------- */
let PFPAGES = null;      // { bytes, pages:[{w,h,page,vp}] }
async function pfPages() {
    if (PFPAGES && PFPAGES.bytes === SGP.bytes) return PFPAGES.pages;
    const doc = await (await loadPdfJs()).getDocument({ data: SGP.bytes.slice(0) }).promise, pages = [];
    for (let i = 1; i <= doc.numPages; i++) { const pg = await doc.getPage(i), vp = pg.getViewport({ scale: 1 }); pages.push({ w: vp.width, h: vp.height, page: pg, vp }); }
    PFPAGES = { bytes: SGP.bytes, pages }; return pages;
}
async function pfText(s) {
    const out = [];
    try {
        const tc = await s.page.getTextContent();
        tc.items.filter(it => it.str && it.str.trim()).forEach(it => {
            const t = it.transform, h = Math.abs(it.height || t[3] || 8), w = it.width || 0;
            const r = s.vp.convertToViewportRectangle([t[4], t[5] - h * 0.25, t[4] + w, t[5] + h]);
            out.push({ x0: Math.min(r[0], r[2]) / s.w, x1: Math.max(r[0], r[2]) / s.w, y0: Math.min(r[1], r[3]) / s.h, y1: Math.max(r[1], r[3]) / s.h });
        });
    } catch (e) { }
    return out;
}
// paraf hanya di halaman yang tidak punya kotak tanda tangan; di pinggir, tidak menutupi tulisan
async function calcParafPos() {
    const d = curDoc(), S = await pfPages(), res = {}, sigs = SGP.sigs || {}, others = parafExtra(d, sigs);
    const ov = (a, b, pad) => !(a.x1 + pad < b.x0 || b.x1 + pad < a.x0 || a.y1 + pad < b.y0 || b.y1 + pad < a.y0);
    for (let p = 1; p <= S.length; p++) {
        if (d.fields.some(f => f.page === p && ftype(f) === 'sign')) continue;
        const s = S[p - 1], w = Math.min(0.95, PARAF_MM.w * MM / s.w), h = Math.min(0.95, PARAF_MM.h * MM / s.h);
        const mx = 10 * MM / s.w, my = 8 * MM / s.h, step = 14 * MM / s.h, pad = 1.2 * MM / s.w;
        const c = [];
        for (let k = 0; k < 5; k++) c.push([1 - mx - w, 1 - my - h - k * step]);
        c.push([mx, 1 - my - h], [(1 - w) / 2, 1 - my - h], [1 - mx - w, my], [mx, my]);
        const txt = await pfText(s);
        const obs = txt.concat(d.fields.concat(others).filter(f => f.page === p).map(f => ({ x0: f.x, y0: f.y, x1: f.x + f.w, y1: f.y + f.h })));
        let pick = c.find(([x, y]) => x >= 0 && y >= 0 && x + w <= 1 && y + h <= 1 && !obs.some(b => ov({ x0: x, y0: y, x1: x + w, y1: y + h }, b, pad)));
        if (!pick) pick = c[0];
        res[p] = { x: +pick[0].toFixed(4), y: +pick[1].toFixed(4), w: +w.toFixed(4), h: +h.toFixed(4) };
    }
    return res;
}
function paintMyParaf(layer, n) {
    layer.querySelectorAll('.sgv-mine').forEach(e => e.remove());
    if (!active() || !SGV.parafOn || !SGV.paraf || !SGV.parafPos[n]) return;
    const r = SGV.parafPos[n], el = document.createElement('div');
    el.className = 'sg-field own2 sgv t-paraf filled sgv-mine';
    Object.assign(el.style, { left: r.x * 100 + '%', top: r.y * 100 + '%', width: r.w * 100 + '%', height: r.h * 100 + '%' });
    el.innerHTML = `<img src="${SGV.paraf}" alt="paraf">`;
    el.onclick = ev => { ev.stopPropagation(); parafMenu(el); };
    layer.appendChild(el);
}
function paintAllParaf() { document.querySelectorAll('#sg-pages .sg-page').forEach(pg => paintMyParaf(pg.querySelector('.sg-layer'), +pg.dataset.page)); }
function parafMenu(el) {
    closeMenu();
    const items = [['fa-eraser', 'Hapus paraf', () => setParaf(false)], ['fa-pen-fancy', 'Ganti paraf', async () => { if (await ensureParaf(true)) { changed(); paintAllParaf(); } }]];
    const m = document.createElement('div'); m.id = 'sgv-menu'; m.dataset.at = Date.now();
    m.innerHTML = items.map(([ic, l], i) => `<button data-i="${i}"><i class="fa-solid ${ic}"></i>${E(l)}</button>`).join('');
    document.body.appendChild(m);
    m.querySelectorAll('[data-i]').forEach(b => b.onclick = ev => { ev.stopPropagation(); closeMenu(); items[+b.dataset.i][2](); });
    const r = el.getBoundingClientRect(), w = m.offsetWidth, h = m.offsetHeight;
    m.style.left = Math.max(8, Math.min(innerWidth - w - 8, r.left)) + 'px';
    m.style.top = (r.bottom + h + 8 > innerHeight ? Math.max(8, r.top - h - 6) : r.bottom + 6) + 'px';
    setTimeout(() => document.addEventListener('click', closeMenu, { once: true }), 0);
}
async function setParaf(on) {
    if (!active()) return;
    if (!on) { SGV.parafOn = false; SGV.parafPos = {}; changed(); paintAllParaf(); tools(); return; }
    if (!(await ensureParaf())) return;
    let pos = {};
    try { pos = await calcParafPos(); } catch (e) { console.warn(e); }
    const n = Object.keys(pos).length;
    if (!n) return toast('Semua halaman sudah ada kotak tanda tangan — tidak perlu paraf', 'info', 5000);
    SGV.parafOn = true; SGV.parafPos = pos; changed(); paintAllParaf(); tools();
    toast(`Paraf dipasang di ${n} halaman (hanya halaman tanpa tanda tangan). Ketuk paraf untuk menghapus.`, 'success', 6000);
}

/* ---------- alat & bar bawah ---------- */
function tools() {
    const card = document.querySelector('.sg-main .sg-card'); if (!card) return;
    let t = card.querySelector('.sgv-tools');
    if (!active()) { if (t) t.remove(); return; }
    const L = myFields(), p = progress();
    const hasPar = L.some(f => ftype(f) === 'paraf');
    const parBtn = hasPar ? '' : (SGV.parafOn ? `<button type="button" data-a="pfoff" class="btn btn-ghost"><i class="fa-solid fa-xmark"></i>Hapus paraf</button>` : `<button type="button" data-a="pfon" class="btn btn-ghost"><i class="fa-solid fa-pen-fancy"></i>Tambah paraf <small>(opsional)</small></button>`);
    const html = `${SGV.resumed ? `<div class="sgv-resume"><i class="fa-solid fa-clock-rotate-left"></i>Melanjutkan isian yang tersimpan (${SGV.resumed.n}/${SGV.resumed.total} kotak).</div>` : ''}
        <div class="sgv-simple"><p><i class="fa-solid fa-hand-pointer"></i>Ketuk kotak berwarna di dokumen untuk <b>tanda tangan</b>${hasPar ? ' dan <b>paraf</b> <small>(paraf boleh dilewati)</small>' : ''}.</p>
        ${p.total > 1 && p.n < p.total ? `<button type="button" data-a="all" class="btn btn-primary"><i class="fa-solid fa-bolt"></i>Tanda tangani semua</button>` : ''}${parBtn}</div>`;
    if (!t) { t = document.createElement('div'); t.className = 'sgv-tools'; const ban = card.querySelector('.sg-banner'); (ban || card.lastElementChild).insertAdjacentElement('afterend', t); }
    if (t.dataset.h === html) return;
    t.dataset.h = html; t.innerHTML = html;
    const po = t.querySelector('[data-a="pfon"]'); if (po) po.onclick = () => setParaf(true);
    const pf = t.querySelector('[data-a="pfoff"]'); if (pf) pf.onclick = () => setParaf(false);
    const all = t.querySelector('[data-a="all"]'); if (all) all.onclick = async () => { await signAll(); tools(); };
}
function applyZoom() { const p = $id('sg-pages'); if (!p) return; p.style.zoom = SGV.zoom === 1 ? '' : SGV.zoom; p.classList.toggle('sgv-zoomed', SGV.zoom > 1); }
function bar() {
    const txt = $id('sg-bar-txt'), go = $id('sg-go'); if (!txt || !go || !active()) return;
    const p = progress();
    txt.innerHTML = !p.left.length ? `<i class="fa-solid fa-circle-check text-emerald-600"></i> ${p.n < p.total ? 'Siap dikirim · paraf boleh dilewati' : 'Semua kotak terisi — siap dikirim'}` : `${p.n} / ${p.total} kotak terisi · <b class="text-rose-600">${p.left.length} wajib lagi</b>`;
    go.disabled = !!p.left.length;
    let sv = $id('sgv-save');
    if (p.n && p.left.length) {
        if (!sv) { go.insertAdjacentHTML('beforebegin', `<button id="sgv-save" type="button" class="btn btn-ghost" title="Simpan isian, lanjutkan nanti dari HP mana pun"><i class="fa-solid fa-floppy-disk"></i><span>Simpan sementara</span></button>`); sv = $id('sgv-save'); sv.onclick = () => saveDraft(false); }
    } else if (sv) sv.remove();
    jump();
    tools();
}
function jumpTo(f) {
    const el = document.querySelector(`#sg-pages [data-fid="${CSS.escape(f.id)}"]`); if (!el) return;
    el.scrollIntoView({ behavior: 'smooth', block: 'center' }); el.classList.add('sg-flash'); setTimeout(() => el.classList.remove('sg-flash'), 1300);
    const inp = el.querySelector('input'); if (inp) setTimeout(() => inp.focus({ preventScroll: true }), 450);
}
function jump() {
    let b = $id('sg-jump');
    const p = progress();
    if (!active() || !p.left.length) { if (b) b.remove(); return; }
    if (!b) { b = document.createElement('button'); b.id = 'sg-jump'; document.body.appendChild(b); }
    b.onclick = () => { const y = scrollY + innerHeight / 2; const els = p.left.map(f => [f, document.querySelector(`#sg-pages [data-fid="${CSS.escape(f.id)}"]`)]).filter(x => x[1]); const nx = els.find(([, el]) => el.getBoundingClientRect().top + scrollY > y + 10) || els[0]; if (nx) jumpTo(nx[0]); };
    b.innerHTML = `<i class="fa-solid fa-forward"></i>Kotak berikutnya <b>${p.left.length}</b>`;
}
sgJumpRender = function () { if (active()) return jump(); const b = $id('sg-jump'); if (b) b.remove(); };
sgJumpNext = function () { const b = $id('sg-jump'); if (b) b.click(); };
function boxList() {
    const L = myFields().slice().sort((a, b) => a.page - b.page || a.y - b.y);
    const m = document.createElement('div'); m.id = 'sgv-list'; m.className = 'fixed inset-0 z-[96] flex items-end sm:items-center justify-center p-0 sm:p-4 bg-cyberDark/60 backdrop-blur-sm';
    m.onclick = e => { if (e.target === m) m.remove(); };
    m.innerHTML = `<div class="proc-card sgv-card"><div class="flex items-center gap-2 mb-2"><h3 class="text-base font-extrabold text-slate-900 dark:text-white flex-1"><i class="fa-solid fa-list-check text-cyan-600 mr-1.5"></i>Kotak Anda</h3><button onclick="$('sgv-list').remove()" class="icon-btn"><i class="fa-solid fa-xmark"></i></button></div>
        <div class="sgv-bl">${L.map(f => { const t = ftype(f), ok = isDone(f); return `<button data-f="${E(f.id)}" class="${ok ? 'ok' : freq(f) ? 'need' : ''}"><i class="fa-solid ${KINDS[t].ic}"></i><span class="min-w-0 flex-1"><b>${E(f.label || KINDS[t].label)}</b><small>Halaman ${f.page}${freq(f) ? '' : ' · opsional'}${t === 'date' ? ' · otomatis' : ''}</small></span><em>${ok ? '<i class="fa-solid fa-circle-check"></i>terisi' : freq(f) ? 'belum' : '—'}</em></button>`; }).join('')}</div></div>`;
    document.body.appendChild(m);
    m.querySelectorAll('[data-f]').forEach(b => b.onclick = () => { m.remove(); jumpTo(fieldById(b.dataset.f)); });
}
function afterRender() {
    applyZoom();
    if (!active()) { const t = document.querySelector('.sgv-tools'); if (t) t.remove(); jump(); return; }
    tools(); bar();
    // tombol bawaan "Pakai TTD tersimpan" → isi semua kotak tanda tangan
}

/* ---------- simpan sementara ---------- */
function payload() {
    return {
        sig: SGV.sig || null, paraf: SGV.paraf || null,
        parafOn: !!(SGV.parafOn && SGV.paraf), parafPos: SGV.parafOn && SGV.paraf ? SGV.parafPos : {},
        filled: [...SGV.filled], vals: SGV.vals, stampOff: [...SGV.stampOff], stampPos: SGV.stampPos, mode: SGV.mode
    };
}
async function saveDraft(quiet) {
    clearTimeout(SGV.timer);
    if (!active() || !SGV.dirty && quiet) return;
    const p = progress(); if (!p.n && quiet) return;
    const b = $id('sgv-save'); if (b && !quiet) { b.disabled = true; b.innerHTML = '<i class="fa-solid fa-circle-notch fa-spin"></i><span>Menyimpan…</span>'; }
    try {
        const r = await sbRpc('sg_draft_save', { p_t: SGP.t, p_signer: SGP.signer, p_pin: SGP.pin, p_data: payload() }, 30000);
        SGV.dirty = false; SGV.savedAt = r.at;
        if (!quiet) toast(`Tersimpan sementara (${r.n}/${r.total} kotak). Buka link yang sama kapan saja untuk melanjutkan.`, 'success', 6000);
    } catch (e) { if (!quiet) toast('Belum tersimpan: ' + e.message, 'error', 7000); }
    finally { const b2 = $id('sgv-save'); if (b2) { b2.disabled = false; b2.innerHTML = '<i class="fa-solid fa-floppy-disk"></i><span>Simpan sementara</span>'; } }
}
document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'hidden' && SGV.dirty && active()) saveDraft(true); });
window.SGV2.saveDraft = saveDraft;

// TTD tersimpan dipakai → semua kotak tanda tangan terisi
(function hookSavedSigUse() {
    if (typeof sgSigUse !== 'function') return;
    const base = sgSigUse;
    sgSigUse = function () {
        const r = base.apply(this, arguments);
        if (active() && SGP.sig) { SGV.sig = SGP.sig; myFields().filter(f => ftype(f) === 'sign').forEach(f => SGV.filled.add(f.id)); changed(); }
        return r;
    };
})();

/* ---------- konfirmasi & kirim ---------- */
sgPublicConfirm = function () {
    if (!active()) return;
    const p = progress();
    if (p.left.length) { toast(`Masih ada ${p.left.length} kotak wajib yang belum diisi`, 'error'); return jumpTo(p.left[0]); }
    SGP.sig = SGV.sig;
    const d = curDoc(), me = curMe(), L = myFields();
    const prev = [SGV.sig && L.some(f => ftype(f) === 'sign' && SGV.filled.has(f.id)) ? ['Tanda tangan', SGV.sig] : null, SGV.paraf && (SGV.parafOn || L.some(f => ftype(f) === 'paraf' && SGV.filled.has(f.id))) ? ['Paraf', SGV.paraf] : null].filter(Boolean);
    const m = document.createElement('div'); m.id = 'sg-confirm'; m.className = 'fixed inset-0 z-[95] flex items-center justify-center p-4 bg-cyberDark/60 backdrop-blur-sm';
    m.innerHTML = `<div class="proc-card" style="max-width:460px">
        <h3 class="text-base font-extrabold text-slate-900 dark:text-white"><i class="fa-solid fa-shield-halved text-cyan-600 mr-1.5"></i>Konfirmasi Tanda Tangan</h3>
        <div class="sgv-prev">${prev.map(([l, src]) => `<div><img src="${src}" alt=""><small>${E(l)}</small></div>`).join('')}</div>
        <p class="text-[11.5px] text-slate-500 mt-2">${p.total} kotak · ${L.filter(f => ftype(f) === 'date').length ? 'tanggal terisi otomatis ' + E(tglPanjang()) + ' · ' : ''}isian siap dikirim</p>
        <label class="flex items-start gap-2 mt-3 text-[12px] text-slate-600 dark:text-slate-300 cursor-pointer"><input id="sg-agree" type="checkbox" class="mt-0.5 w-4 h-4 accent-indigo-600"><span>Saya <b>${E(me.name)}</b> sudah membaca dokumen <b>${E(d.name)}</b> dan menyetujui untuk menandatanganinya secara elektronik.</span></label>
        <p id="sg-err" class="hidden mt-2 p-2 rounded-lg bg-rose-500/10 text-[11px] font-semibold text-rose-600"></p>
        <div class="flex flex-wrap gap-2 mt-4"><button onclick="$('sg-confirm').remove()" class="btn btn-ghost flex-1">Batal</button><button id="sgv-pv" class="btn btn-ghost flex-1"><i class="fa-solid fa-eye"></i>Pratinjau PDF</button><button id="sg-send" onclick="sgPublicSend()" class="btn btn-primary flex-1"><i class="fa-solid fa-paper-plane"></i>Tanda Tangani</button></div></div>`;
    document.body.appendChild(m);
    $id('sgv-pv').onclick = preview;
};
async function preview() {
    const b = $id('sgv-pv'); if (b) { b.disabled = true; b.innerHTML = '<i class="fa-solid fa-circle-notch fa-spin"></i>Menyusun…'; }
    const w = window.open('', '_blank');
    try {
        const d = JSON.parse(JSON.stringify(curDoc())), me = curMe(), now = new Date().toISOString();
        d.signers.forEach(g => { if (g.id === me.id) { g.status = 'selesai'; g.signedAt = now; } });
        const sigs = Object.assign({}, SGP.sigs || {}); sigs.__ext = Object.assign({}, (SGP.sigs || {}).__ext || {});
        const pl = payload();
        sigs[me.id] = b64png(SGV.sig || SGV.paraf || ''); sigs.__ext[me.id] = { v: 2, paraf: b64png(SGV.paraf || ''), parafPos: pl.parafPos, filled: pl.filled, vals: pl.vals, stampOff: pl.stampOff, stampPos: pl.stampPos };
        const out = await sgStamp(SGP.bytes, d, sigs);
        const url = URL.createObjectURL(new Blob([out], { type: 'application/pdf' }));
        if (w) w.location = url; else sgSaveBlob(out, d.name + ' - pratinjau.pdf');
        setTimeout(() => URL.revokeObjectURL(url), 120000);
    } catch (e) { if (w) w.close(); toast('Pratinjau gagal: ' + e.message, 'error'); }
    finally { if (b) { b.disabled = false; b.innerHTML = '<i class="fa-solid fa-eye"></i>Pratinjau PDF'; } }
}
(function hookSubmit() {
    const base = callApi;
    callApi = function (action, data) {
        if (action === 'sign.submit' && data && typeof sbTok === 'function' && sbTok(data.t) && SGV.id && SGV.id === sgDocId() && curMe() && SGV.signer === data.signer) {
            return sbRpc('sg_submit2', { p_t: data.t, p_signer: data.signer, p_pin: data.pin, p_data: payload() }, 60000).then(r => { SGV.dirty = false; clearTimeout(SGV.timer); return r; });
        }
        return base.apply(this, arguments);
    };
})();
// tanda tangani semua (Dokumen Saya): dokumen yang punya paraf / isian wajib harus dibuka
(function hookSignAll() {
    if (typeof sgSignAll !== 'function') return;
    const base = sgSignAll;
    sgSignAll = async function () {
        const ib = SGP.inbox; if (!ib || !ib.pending) return base.apply(this, arguments);
        const all = ib.pending, skip = all.filter(x => x.needOpen);
        ib.pending = all.filter(x => !x.needOpen);
        try { if (!ib.pending.length && skip.length) { toast(`${skip.length} dokumen punya paraf / isian — buka satu per satu untuk melengkapinya`, 'info', 7000); return; } return await base.apply(this, arguments); }
        finally { ib.pending = all; if (skip.length && ib.pending.length > skip.length) toast(`${skip.length} dokumen dengan paraf / isian tidak ikut — buka dokumennya untuk melengkapi`, 'info', 7000); }
    };
})();

/* =====================================================================
   F4 · PIN — ingat perangkat 90 hari, kunci 1 menit, lupa PIN (email opsional)
   ===================================================================== */
const VM_WA = '628984623040';       // Vendor Management (development)
function vmWaUrl(ctx) {
    let title = ''; try { const d = SGP.data && SGP.data.doc; title = (d && (d.title || d.name)) || ''; } catch (e) { }
    const msg = `Halo Tim Vendor Management, saya ${ctx && ctx.name || '(nama penanda tangan)'} lupa PIN tanda tangan${title ? ' untuk dokumen "' + title + '"' : ''}. Mohon dibantu reset PIN. Terima kasih.`;
    return `https://wa.me/${VM_WA}?text=${encodeURIComponent(msg)}`;
}
// PIN WAJIB setiap kali membuka link: tidak ada login tersimpan / perangkat yang diingat
SGA.get = () => null; SGA.set = () => { };
sgMeGet = () => null;
try { Object.keys(localStorage).filter(k => /^sgauth_/.test(k) || k === SGME.key).forEach(k => localStorage.removeItem(k)); } catch (e) { }
let PINCTX = null;
const isTok = p => /^dv:/.test(String(p || ''));
const isPin = p => /^\d{4}$/.test(String(p || ''));
function devLabel() {
    const u = navigator.userAgent;
    const b = /Edg\//.test(u) ? 'Edge' : /OPR\//.test(u) ? 'Opera' : /SamsungBrowser/.test(u) ? 'Samsung Internet' : /CriOS|Chrome\//.test(u) ? 'Chrome' : /FxiOS|Firefox\//.test(u) ? 'Firefox' : /Safari\//.test(u) ? 'Safari' : 'Browser';
    const o = /iPhone/.test(u) ? 'iPhone' : /iPad/.test(u) ? 'iPad' : /Android/.test(u) ? 'Android' : /Windows/.test(u) ? 'Windows' : /Mac OS X/.test(u) ? 'Mac' : /Linux/.test(u) ? 'Linux' : '';
    return b + (o ? ' · ' + o : '');
}
const UPG = new Map();
function upgrade(t, signer, pin) {
    if (!isPin(pin) || !SGV.remember || !t) return Promise.resolve(null);
    const k = t + '|' + (signer || '') + '|' + pin;
    if (UPG.has(k)) return UPG.get(k);
    const p = sbRpc('sg_dev_new', { p_t: t, p_signer: signer || null, p_pin: pin, p_label: devLabel() }, 20000).then(r => {
        const tok = r && r.tok; if (!tok) return null;
        if (SGP.pin === pin) SGP.pin = tok;
        if (SGP.me && SGP.me.pin === pin) { SGP.me.pin = tok; meWrite(SGP.me.name, tok); }
        try { const id = sgDocId(), a = SGA.get(id); if (a && a.pin === pin) SGA_SET(id, { signer: a.signer, pin: tok }); } catch (e) { }
        return tok;
    }).catch(() => null);
    UPG.set(k, p); return p;
}
const SGA_SET = SGA.set.bind(SGA);
SGA.set = function (docId, v) {
    if (!SGV.remember) return;                         // "jangan ingat perangkat ini"
    SGA_SET(docId, v);
    if (v && isPin(v.pin) && typeof sbTok === 'function' && sbTok(SGP.t)) upgrade(SGP.t, v.signer, v.pin);
};
function meWrite(name, pin) { try { localStorage.setItem(SGME.key, JSON.stringify({ key: sgNkey(name), name, pin, exp: Date.now() + (isTok(pin) ? 90 * 864e5 : 12 * 3600e3) })); } catch (e) { } }
sgMeSet = function (name, pin) {
    if (!SGV.remember) return;
    meWrite(name, pin);
    if (isPin(pin)) setTimeout(() => {
        const t = SGP.home || SGP.homeT || SGP.t, signer = SGP.home ? null : (SGP.homeSigner || SGP.signer);
        upgrade(t, signer, pin);
    }, 0);
};
(function hookLogout() {
    if (typeof sgMeLogout !== 'function') return;
    const base = sgMeLogout;
    sgMeLogout = function () {
        const c = typeof sgCred === 'function' ? sgCred() : null;
        if (c && isTok(c.p_pin)) { sbRpc('sg_dev_list', Object.assign({ p_revoke: 'this' }, c), 8000).catch(() => { }).finally(() => base.apply(this, arguments)); return; }
        return base.apply(this, arguments);
    };
})();

// layar PIN: centang "ingat perangkat", "Lupa PIN?", hitung mundur saat terkunci
function pinExtras(ctx) {
    const go = $id('sg-pgo'); if (!go || go.parentNode.querySelector('.sgv-rem')) return;
    PINCTX = ctx;
    const old = [...go.parentNode.querySelectorAll('p')].find(p => /Lupa PIN/.test(p.textContent));
    const html = `<button type="button" class="sgv-forgot"><i class="fa-solid fa-circle-question"></i>Lupa PIN?</button>`;
    if (old) old.outerHTML = html; else if (!ctx.create) go.insertAdjacentHTML('afterend', html);
    const fb = go.parentNode.querySelector('.sgv-forgot'); if (fb) fb.onclick = () => forgot(ctx);
    countdown();
}
function countdown() {
    const e = $id('sg-perr'), go = $id('sg-pgo'); if (!e || !go) return;
    const m = /dalam (\d+) detik/.exec(e.textContent || ''); if (!m) return;
    let n = +m[1]; go.disabled = true; clearInterval(countdown.t);
    if (!document.querySelector('.sgv-vmwa')) { let nm = ''; try { nm = (PINCTX && PINCTX.name) || SGP.data.me.name || ''; } catch (x) { } e.insertAdjacentHTML('afterend', `<a class="sgv-vmwa big" target="_blank" rel="noopener" href="${vmWaUrl({ name: nm })}"><i class="fa-brands fa-whatsapp"></i><span><b>Hubungi Vendor Management</b><small>Salah PIN 5 kali — minta bantuan reset lewat WhatsApp</small></span></a>`); }
    const tick = () => {
        if (!document.body.contains(go)) return clearInterval(countdown.t);
        if (n <= 0) { clearInterval(countdown.t); go.disabled = false; e.textContent = 'Silakan masukkan PIN lagi'; e.classList.remove('hidden'); return; }
        e.textContent = `Terlalu banyak salah PIN. Coba lagi dalam ${n} detik.`; n--;
    };
    tick(); countdown.t = setInterval(tick, 1000);
}
(function hookPinScreens() {
    const baseStep = sgPublicPinStep;
    sgPublicPinStep = function (r) {
        const out = baseStep.apply(this, arguments);
        try { pinExtras({ t: SGP.t, signer: r.me && r.me.id, name: r.me && r.me.name, mail: r.me && r.me.mail, createdBy: r.doc && r.doc.createdBy, create: !!r.pinCreate, devExpired: !!r.devExpired, person: false }); } catch (e) { }
        return out;
    };
    if (typeof sgPersonPin === 'function') {
        const basePP = sgPersonPin;
        sgPersonPin = function (p) {
            const out = basePP.apply(this, arguments);
            try { pinExtras({ t: SGP.t, signer: null, name: p.name, mail: p.mail, createdBy: '', create: !p.hasPin, person: true }); } catch (e) { }
            return out;
        };
    }
    const wrapGo = name => { if (typeof window[name] !== 'function') return; const b = window[name]; window[name] = async function () { const r = await b.apply(this, arguments); countdown(); return r; }; };
    // sgPinGo / sgPersonGo dipanggil dari onclick (nama global) → bungkus di window
    const bp = sgPinGo; sgPinGo = async function () { const r = await bp.apply(this, arguments); countdown(); return r; };
    if (typeof sgPersonGo === 'function') { const bq = sgPersonGo; sgPersonGo = async function () { const r = await bq.apply(this, arguments); countdown(); return r; }; }
    void wrapGo;
    // halaman galat (mis. terkunci saat membuka link) → hitung mundur di tombol "Coba lagi"
    if (typeof sgPublicError === 'function') {
        const be = sgPublicError;
        sgPublicError = function (msg) {
            const out = be.apply(this, arguments);
            const m = /dalam (\d+) detik/.exec(String(msg || ''));
            if (m) { const btn = document.querySelector('.sg-main .sg-card button'); let n = +m[1]; if (btn && !document.querySelector('.sgv-vmwa')) btn.insertAdjacentHTML('afterend', `<a class="sgv-vmwa big" target="_blank" rel="noopener" href="${vmWaUrl({})}"><i class="fa-brands fa-whatsapp"></i><span><b>Hubungi Vendor Management</b><small>Salah PIN 5 kali — minta bantuan reset lewat WhatsApp</small></span></a>`); if (btn) { btn.disabled = true; const t = setInterval(() => { if (--n <= 0 || !document.body.contains(btn)) { clearInterval(t); btn.disabled = false; btn.innerHTML = '<i class="fa-solid fa-rotate"></i>Coba lagi'; return; } btn.innerHTML = `<i class="fa-solid fa-hourglass-half"></i>Coba lagi dalam ${n} detik`; }, 1000); } }
            return out;
        };
    }
})();
async function forgot(ctx) {
    let mail = ctx.mail;
    if (mail === undefined) {          // ambil info email (tersamar) dari server
        try { const r = ctx.person ? await sbRpc('sg_inbox', { p_t: ctx.t }, 20000) : await sbRpc('sg_auth', { p_t: ctx.t, p_signer: ctx.signer }, 20000); mail = (r.me && r.me.mail) || ''; } catch (e) { mail = ''; }
        ctx.mail = mail;
    }
    const m = document.createElement('div'); m.id = 'sgv-fp'; m.className = 'fixed inset-0 z-[96] flex items-end sm:items-center justify-center p-0 sm:p-4 bg-cyberDark/60 backdrop-blur-sm';
    m.onclick = e => { if (e.target === m) m.remove(); };
    const who = ctx.createdBy ? String(ctx.createdBy).replace(/\s*\(.*\)$/, '') : 'pengirim dokumen';
    m.innerHTML = `<div class="proc-card sgv-card"><div class="flex items-center gap-2"><h3 class="text-base font-extrabold text-slate-900 dark:text-white flex-1"><i class="fa-solid fa-key text-amber-500 mr-1.5"></i>Lupa PIN</h3><button onclick="$('sgv-fp').remove()" class="icon-btn"><i class="fa-solid fa-xmark"></i></button></div>
        ${mail ? `<div class="sgv-fp-box"><p class="text-[12px] text-slate-600 dark:text-slate-300">Kirim kode ke email terdaftar <b>${E(mail)}</b>, lalu buat PIN baru.</p>
            <button id="sgv-fp-send" class="btn btn-primary w-full mt-2"><i class="fa-solid fa-envelope"></i>Kirim kode ke email</button>
            <div id="sgv-fp-step" class="hidden mt-3 space-y-2"><input id="sgv-fp-code" class="field w-full text-center tracking-[.4em]" inputmode="numeric" maxlength="6" placeholder="Kode 6 angka dari email" autocomplete="one-time-code">
                <input id="sgv-fp-p1" type="password" class="field w-full text-center tracking-[.4em]" inputmode="numeric" maxlength="4" placeholder="PIN baru (4 angka)" autocomplete="new-password">
                <input id="sgv-fp-p2" type="password" class="field w-full text-center tracking-[.4em]" inputmode="numeric" maxlength="4" placeholder="Ulangi PIN baru" autocomplete="new-password">
                <button id="sgv-fp-go" class="btn btn-primary w-full"><i class="fa-solid fa-check"></i>Simpan PIN baru</button></div>
            <p id="sgv-fp-msg" class="hidden mt-2 p-2 rounded-lg text-[11.5px] font-semibold"></p></div>
            <p class="text-[11px] text-slate-400 text-center my-2">atau</p>` : ''}
        <div class="sgv-fp-box"><p class="text-[12px] text-slate-600 dark:text-slate-300"><i class="fa-brands fa-whatsapp text-emerald-600 mr-1"></i>Minta <b>${E(who)}</b> mereset PIN Anda. Setelah direset, buka link ini lagi lalu buat PIN baru.</p>
            ${mail ? '' : '<p class="text-[11px] text-slate-400 mt-1">Ingin bisa reset sendiri lain kali? Minta pengirim mendaftarkan email Anda di daftar penanda tangan.</p>'}</div></div>`;
    document.body.appendChild(m);
    if (!mail) return;
    const msg = (t, ok) => { const e = $id('sgv-fp-msg'); e.className = 'mt-2 p-2 rounded-lg text-[11.5px] font-semibold ' + (ok ? 'bg-emerald-500/10 text-emerald-700' : 'bg-rose-500/10 text-rose-600'); e.textContent = t; };
    $id('sgv-fp-send').onclick = async () => {
        const b = $id('sgv-fp-send'); b.disabled = true; b.innerHTML = '<i class="fa-solid fa-circle-notch fa-spin"></i>Mengirim…';
        try { const r = await callApi('sign.pinmail', { t: ctx.t, signer: ctx.signer || '' }, 60000); msg(`Kode dikirim ke ${r.mask || mail}. Cek kotak masuk / spam (berlaku 10 menit).`, true); $id('sgv-fp-step').classList.remove('hidden'); $id('sgv-fp-code').focus(); b.innerHTML = '<i class="fa-solid fa-rotate"></i>Kirim ulang kode'; setTimeout(() => { b.disabled = false; }, 60000); }
        catch (e) { msg(/tidak dikenal/i.test(e.message) ? 'Fitur kode email belum aktif di server — hubungi pengirim dokumen' : e.message); b.disabled = false; b.innerHTML = '<i class="fa-solid fa-envelope"></i>Kirim kode ke email'; }
    };
    $id('sgv-fp-go').onclick = async () => {
        const code = $id('sgv-fp-code').value.trim(), p1 = $id('sgv-fp-p1').value.trim(), p2 = $id('sgv-fp-p2').value.trim();
        if (!/^\d{6}$/.test(code)) return msg('Masukkan kode 6 angka dari email');
        if (!/^\d{4}$/.test(p1)) return msg('PIN baru harus 4 angka');
        if (p1 !== p2) return msg('Ulangi PIN tidak sama');
        const b = $id('sgv-fp-go'); b.disabled = true;
        try {
            await sbRpc('sg_pin_otp_reset', { p_t: ctx.t, p_signer: ctx.signer || null, p_code: code, p_new_pin: p1 }, 30000);
            m.remove(); toast('PIN baru tersimpan', 'success');
            try { SGA.clear(sgDocId()); sgMeClear(); } catch (e) { }
            const i = $id('sg-pin'); if (i) { i.value = p1; const i2 = $id('sg-pin2'); if (i2) i2.value = p1; }
            if (ctx.person) sgPersonGo(false); else sgPinGo(false);
        } catch (e) { msg(e.message); b.disabled = false; }
    };
}
window.SGV2.forgot = forgot;

// perangkat yang diingat (penanda tangan)
async function devices() {
    const c = typeof sgCred === 'function' ? sgCred() : null; if (!c) return;
    const m = document.createElement('div'); m.id = 'sgv-dev'; m.className = 'fixed inset-0 z-[96] flex items-end sm:items-center justify-center p-0 sm:p-4 bg-cyberDark/60 backdrop-blur-sm';
    m.onclick = e => { if (e.target === m) m.remove(); };
    document.body.appendChild(m);
    const draw = (L, err) => {
        m.innerHTML = `<div class="proc-card sgv-card"><div class="flex items-center gap-2"><h3 class="text-base font-extrabold text-slate-900 dark:text-white flex-1"><i class="fa-solid fa-mobile-screen text-cyan-600 mr-1.5"></i>Perangkat yang diingat</h3><button onclick="$('sgv-dev').remove()" class="icon-btn"><i class="fa-solid fa-xmark"></i></button></div>
            <p class="text-[11px] text-slate-500 mt-1">Perangkat di bawah bisa membuka dokumen Anda tanpa PIN selama 90 hari sejak diingat.</p>
            ${err ? `<p class="mt-2 p-2 rounded-lg bg-rose-500/10 text-rose-600 text-[11.5px] font-semibold">${E(err)}</p>` : ''}
            <div class="sgv-bl mt-2">${L ? (L.length ? L.map(d => `<div class="sgv-dv ${d.current ? 'cur' : ''}"><i class="fa-solid ${/iPhone|Android/.test(d.label) ? 'fa-mobile-screen' : 'fa-laptop'}"></i><span class="min-w-0 flex-1"><b>${E(d.label || 'Perangkat')}${d.current ? ' · perangkat ini' : ''}</b><small>Terakhir dipakai ${E(sgTime(d.lastUsed))} · berlaku s/d ${E(sgTime(d.exp))}</small></span><button data-r="${E(d.id)}" class="btn btn-ghost !py-1 text-rose-600">Keluarkan</button></div>`).join('') : '<p class="text-center text-[12px] text-slate-400 py-5">Belum ada perangkat yang diingat</p>') : '<p class="text-center text-[12px] text-slate-400 py-5"><i class="fa-solid fa-circle-notch fa-spin mr-1"></i>Memuat…</p>'}</div>
            ${L && L.length ? '<button data-all class="btn btn-ghost w-full mt-3 text-rose-600"><i class="fa-solid fa-right-from-bracket"></i>Keluarkan semua perangkat</button>' : ''}</div>`;
        m.querySelectorAll('[data-r]').forEach(b => b.onclick = () => act(b.dataset.r, (L.find(x => x.id === b.dataset.r) || {}).current));
        const all = m.querySelector('[data-all]'); if (all) all.onclick = () => { if (confirm('Keluarkan semua perangkat? Semua HP / laptop perlu PIN lagi.')) act('all', true); };
    };
    const act = async (which, mine) => {
        try { const r = await sbRpc('sg_dev_list', Object.assign({}, c, { p_revoke: which }), 20000); if (mine) { try { SGA.clear(sgDocId()); sgMeClear(); } catch (e) { } toast('Perangkat ini dikeluarkan — buka lagi dengan PIN', 'success'); setTimeout(() => location.reload(), 900); return; } draw(r.devices); }
        catch (e) { draw([], e.message); }
    };
    draw(null);
    try { const r = await sbRpc('sg_dev_list', c, 20000); draw(r.devices); } catch (e) { draw([], e.message); }
}
window.SGV2.devices = devices;
function devButton() {
    const card = document.querySelector('.sg-main .sg-card'); if (!card || card.querySelector('.sgv-devbtn')) return;
    const c = typeof sgCred === 'function' ? sgCred() : null; if (!c || !isTok(c.p_pin)) return;
    const host = card.querySelector('.flex.items-start') || card;
    const anchor = host.querySelector('button.icon-btn');
    const html = `<button type="button" onclick="SGV2.devices()" class="icon-btn shrink-0 sgv-devbtn" title="Perangkat yang diingat"><i class="fa-solid fa-mobile-screen"></i></button>`;
    if (anchor) anchor.insertAdjacentHTML('beforebegin', html); else host.insertAdjacentHTML('beforeend', html);
}
(function hookDevBtn() {
    const br = sgPublicRender; sgPublicRender = async function () { const out = await br.apply(this, arguments); try { devButton(); } catch (e) { } return out; };
    if (typeof sgInboxRender === 'function') { const bi = sgInboxRender; sgInboxRender = function () { const out = bi.apply(this, arguments); try { devButton(); } catch (e) { } return out; }; }
})();

/* =====================================================================
   PEMBUAT DOKUMEN · langkah 3 — jenis kotak + paraf otomatis
   ===================================================================== */
SGW.ftype = SGW.ftype || 'sign';
const PG_SIZE = new Map();                 // bytes → [{w,h}] ukuran halaman (pt)
async function pageSizes() {
    if (!SGW.bytes) return [];
    if (PG_SIZE.has(SGW.bytes)) return PG_SIZE.get(SGW.bytes);
    let doc = null;
    try { doc = await (PDF_DOCS.get(SGW.bytes) || (await loadPdfJs()).getDocument({ data: SGW.bytes.slice(0) }).promise); } catch (e) { return []; }
    const out = [];
    for (let i = 1; i <= doc.numPages; i++) { const p = await doc.getPage(i), v = p.getViewport({ scale: 1 }); out.push({ w: v.width, h: v.height, page: p, vp: v }); }
    PG_SIZE.set(SGW.bytes, out); return out;
}
const mmFrac = (s, mmW, mmH) => ({ w: Math.min(0.95, mmW * MM / s.w), h: Math.min(0.95, mmH * MM / s.h) });
const hasSignOn = (page, fields) => (fields || SGW.fields).some(f => f.page === page && ftype(f) === 'sign');
const signerOf = id => SGW.signers.find(g => g.id === id) || {};
const parafOn = g => g.paraf !== false;
const parafMax = s => mmFrac(s, PARAF_MM.w, PARAF_MM.h);

// kotak teks di halaman (pt → pecahan 0..1) untuk mencari area kosong
const TXT = new WeakMap();
async function textBoxes(pi) {
    const s = pi; if (TXT.has(s.page)) return TXT.get(s.page);
    let boxes = [];
    try {
        const tc = await s.page.getTextContent();
        boxes = tc.items.filter(it => it.str && it.str.trim()).map(it => {
            const t = it.transform, h = Math.abs(it.height || t[3] || 8), w = it.width || 0;
            const r = s.vp.convertToViewportRectangle([t[4], t[5] - h * 0.25, t[4] + w, t[5] + h]);
            const x0 = Math.min(r[0], r[2]) / s.w, x1 = Math.max(r[0], r[2]) / s.w, y0 = Math.min(r[1], r[3]) / s.h, y1 = Math.max(r[1], r[3]) / s.h;
            return { x0, y0, x1, y1 };
        });
    } catch (e) { }
    TXT.set(s.page, boxes); return boxes;
}
const overlap = (a, b, pad) => !(a.x1 + pad < b.x0 || b.x1 + pad < a.x0 || a.y1 + pad < b.y0 || b.y1 + pad < a.y0);
// cari posisi strip paraf (lebar n kotak) yang tidak menutupi teks
async function stripSpot(page, n, pref) {
    const S = await pageSizes(), s = S[page - 1]; if (!s) return null;
    const one = parafMax(s), gap = GAP_MM * MM / s.w, W = n * one.w + (n - 1) * gap, H = one.h;
    const mx = 10 * MM / s.w, my = 8 * MM / s.h, step = 14 * MM / s.h;
    const cands = [];
    if (pref) cands.push([pref.x, pref.y]);
    for (let k = 0; k < 5; k++) cands.push([1 - mx - W, 1 - my - H - k * step]);           // kanan bawah, naik
    cands.push([mx, 1 - my - H], [(1 - W) / 2, 1 - my - H], [1 - mx - W, my], [mx, my]);   // kiri bawah, tengah bawah, kanan atas, kiri atas
    const txt = await textBoxes(s), other = SGW.fields.filter(f => f.page === page && ftype(f) !== 'paraf').map(f => ({ x0: f.x, y0: f.y, x1: f.x + f.w, y1: f.y + f.h }));
    const pad = 1.2 * MM / s.w;
    for (const [x, y] of cands) {
        if (x < 0 || y < 0 || x + W > 1 || y + H > 1) continue;
        const r = { x0: x, y0: y, x1: x + W, y1: y + H };
        if (!txt.some(b => overlap(r, b, pad)) && !other.some(b => overlap(r, b, pad))) return { x, y, one, gap, ok: true };
    }
    const [x, y] = cands[pref ? 1 : 0]; return { x, y, one, gap, ok: false };
}
sgAddField = async function (e, page) {
    if (e.target !== e.currentTarget) return;
    const r = e.currentTarget.getBoundingClientRect(), t = SGW.ftype || 'sign', k = KINDS[t];
    const S = await pageSizes(), s = S[page - 1];
    let w = 0.24, h = 0.075;
    if (k.mm && s) { const z = mmFrac(s, k.mm[0], k.mm[1]); w = z.w; h = z.h; }
    const x = Math.max(0, Math.min(1 - w, (e.clientX - r.left) / r.width - w / 2)), y = Math.max(0, Math.min(1 - h, (e.clientY - r.top) / r.height - h / 2));
    const f = { id: 'f' + sgNewId(), signer: SGW.active, page, x, y, w, h };
    if (t !== 'sign') f.type = t;
    if (t === 'text') { f.kind = SGW.tkind || 'jabatan'; f.label = TEXT_KINDS[f.kind]; f.req = true; }
    if (t === 'check') { f.label = 'Setuju'; f.req = false; }
    SGW.fields.push(f);
    sgDrawFields(); sgRenderWho(); sideRefresh();
};
// kotak di halaman: warna penanda tangan + ikon jenis; geser & ubah ukuran (paraf maks 22×12 mm)
sgDrawFields = function () {
    if (SGW.tplFields && SGW.pages && SGW.count) {          // posisi dari template
        const n = SGW.count;
        SGW.fields = SGW.tplFields.filter(f => SGW.signers[f.si]).map(f => Object.assign({ id: 'f' + sgNewId(), signer: SGW.signers[f.si].id, page: Math.min(n, f.page), x: f.x, y: f.y, w: f.w, h: f.h },
            f.type ? { type: f.type } : {}, f.req !== undefined ? { req: f.req } : {}, f.label ? { label: f.label } : {}, f.kind ? { kind: f.kind } : {}));
        SGW.tplFields = null;
        setTimeout(() => { try { sgRenderWho(); sideRefresh(); } catch (e) { } }, 0);
    }
    if (!SGW.pages) return;
    SGW.pages.forEach(pg => pg.layer.innerHTML = '');
    const S = PG_SIZE.get(SGW.bytes) || [];
    SGW.fields.forEach(f => {
        const pg = SGW.pages[f.page - 1], g = SGW.signers.find(s => s.id === f.signer); if (!pg || !g) return;
        const t = ftype(f), k = KINDS[t];
        const el = document.createElement('div'); el.className = 'sg-field edit sgv-e t-' + t; el.style.setProperty('--c', g.color);
        Object.assign(el.style, { left: f.x * 100 + '%', top: f.y * 100 + '%', width: f.w * 100 + '%', height: f.h * 100 + '%' });
        el.innerHTML = `<span><i class="fa-solid ${k.ic}"></i> ${t === 'sign' ? E(g.name) : E(f.label || k.short) + (t === 'paraf' ? '' : ' · ' + E(g.name.split(' ')[0]))}${freq(f) ? '' : ' <small>(opsional)</small>'}</span><button class="sg-del" title="Hapus"><i class="fa-solid fa-xmark"></i></button>${['text', 'check', 'date'].includes(t) ? `<button class="sgv-opt" title="Pengaturan kotak"><i class="fa-solid fa-gear"></i></button>` : ''}<i class="sg-rs"></i>`;
        el.querySelector('.sg-del').onclick = ev => { ev.stopPropagation(); SGW.fields = SGW.fields.filter(x => x !== f); sgDrawFields(); sgRenderWho(); sideRefresh(); };
        const ob = el.querySelector('.sgv-opt'); if (ob) ob.onclick = ev => { ev.stopPropagation(); fieldOpts(f); };
        const drag = (ev, resize) => {
            ev.preventDefault(); ev.stopPropagation();
            const lr = pg.layer.getBoundingClientRect(), sx = ev.clientX, sy = ev.clientY, o = { ...f };
            const mx = t === 'paraf' && S[f.page - 1] ? parafMax(S[f.page - 1]) : { w: 1, h: 1 };
            const mv = e2 => {
                const dx = (e2.clientX - sx) / lr.width, dy = (e2.clientY - sy) / lr.height;
                if (resize) { f.w = Math.max(0.02, Math.min(1 - f.x, mx.w, o.w + dx)); f.h = Math.max(0.012, Math.min(1 - f.y, mx.h, o.h + dy)); }
                else { f.x = Math.max(0, Math.min(1 - f.w, o.x + dx)); f.y = Math.max(0, Math.min(1 - f.h, o.y + dy)); }
                Object.assign(el.style, { left: f.x * 100 + '%', top: f.y * 100 + '%', width: f.w * 100 + '%', height: f.h * 100 + '%' });
            };
            const up = () => {
                window.removeEventListener('pointermove', mv); window.removeEventListener('pointerup', up);
                if (t === 'paraf' && !resize && f.grp === 'strip' && (Math.abs(f.x - o.x) > 0.005 || Math.abs(f.y - o.y) > 0.005)) {   // strip bergerak bersama
                    const dx = f.x - o.x, dy = f.y - o.y;
                    SGW.fields.filter(x => x !== f && x.page === f.page && ftype(x) === 'paraf' && x.grp === 'strip').forEach(x => { x.x = Math.max(0, Math.min(1 - x.w, x.x + dx)); x.y = Math.max(0, Math.min(1 - x.h, x.y + dy)); });
                    SGW.lastParafPage = f.page; sgDrawFields(); sideRefresh();
                }
            };
            window.addEventListener('pointermove', mv); window.addEventListener('pointerup', up);
        };
        el.addEventListener('pointerdown', ev => { if (ev.target.closest('.sg-del,.sgv-opt')) return; drag(ev, !!ev.target.closest('.sg-rs')); });
        pg.layer.appendChild(el);
    });
};
function fieldOpts(f) {
    const t = ftype(f);
    const m = document.createElement('div'); m.id = 'sgv-fo'; m.className = 'fixed inset-0 flex items-center justify-center p-4 bg-cyberDark/60 backdrop-blur-sm';
    m.onclick = e => { if (e.target === m) m.remove(); };
    m.innerHTML = `<div class="proc-card" style="max-width:380px;width:100%"><h3 class="text-base font-extrabold text-slate-900 dark:text-white"><i class="fa-solid ${KINDS[t].ic} text-cyan-600 mr-1.5"></i>${E(KINDS[t].label)}</h3>
        ${t === 'text' ? `<label class="ulabel mt-3">Isi dengan</label><select id="sgv-fo-k" class="field w-full">${Object.entries(TEXT_KINDS).map(([k, l]) => `<option value="${k}" ${f.kind === k ? 'selected' : ''}>${l}${k === 'bebas' ? '' : ' (terisi otomatis, bisa diubah)'}</option>`).join('')}</select>` : ''}
        ${t === 'text' || t === 'check' ? `<label class="ulabel mt-3">Label</label><input id="sgv-fo-l" class="field w-full" value="${E(f.label || '')}" placeholder="${t === 'check' ? 'mis. Setuju / Mengetahui' : 'mis. Jabatan'}">` : ''}
        ${t !== 'date' ? `<label class="flex items-center gap-2 mt-3 text-[12px] font-semibold"><input id="sgv-fo-r" type="checkbox" class="w-4 h-4 accent-indigo-600" ${freq(f) ? 'checked' : ''}>Wajib diisi</label>` : '<p class="text-[11.5px] text-slate-500 mt-2">Terisi otomatis dengan tanggal saat penanda tangan menandatangani (format: 23 Oktober 2026).</p>'}
        <div class="flex gap-2 mt-4"><button onclick="$('sgv-fo').remove()" class="btn btn-ghost flex-1">Batal</button><button id="sgv-fo-ok" class="btn btn-primary flex-1">Simpan</button></div></div>`;
    document.body.appendChild(m);
    $id('sgv-fo-ok').onclick = () => {
        const k = $id('sgv-fo-k'), l = $id('sgv-fo-l'), r = $id('sgv-fo-r');
        if (k) { const prevDef = TEXT_KINDS[f.kind]; f.kind = k.value; if (!l || !l.value.trim() || l.value.trim() === prevDef) f.label = TEXT_KINDS[f.kind]; }
        if (l && l.value.trim()) f.label = l.value.trim().slice(0, 60);
        if (r) f.req = r.checked;
        m.remove(); sgDrawFields();
    };
}
// panel samping langkah 3
function sideHtml() { SGW.ftype = 'sign'; return '<div class="sgv-side"></div>'; }
function sideRefresh() {
    const side = document.querySelector('.sg-place-side'); if (!side || SGW.step !== 3) return;
    let box = side.querySelector('.sgv-side');
    const html = sideHtml();
    if (box) box.outerHTML = html; else { const who = side.querySelector('#sgw-who'); (who || side.firstElementChild).insertAdjacentHTML('afterend', html); }
    box = side.querySelector('.sgv-side');
    box.querySelectorAll('[data-k]').forEach(b => b.onclick = () => { SGW.ftype = b.dataset.k; sideRefresh(); });
    const tk = box.querySelector('#sgv-tk'); if (tk) tk.onchange = () => { SGW.tkind = tk.value; };
    // keterangan di panel bawaan
    const tip = [...side.querySelectorAll('p')].find(p => /Klik di halaman untuk menaruh kotak/.test(p.textContent));
    if (tip) tip.innerHTML = '<b>3.</b> Klik di halaman untuk menaruh kotak <b>tanda tangan</b> penanda tangan yang dipilih. Geser untuk memindah, tarik sudut kanan-bawah untuk ukuran, <i class="fa-solid fa-xmark"></i> untuk menghapus.';
}
(function hookWizard() {
    const base = sgWizard;
    sgWizard = function () {
        const r = base.apply(this, arguments);
        try {
            if (SGW.step === 3 && !SGW.created) {
                sideRefresh();
            }
            if (SGW.step === 4 && !SGW.created) {
                const host = $id('sgw-body') && $id('sgw-body').querySelector('.max-w-xl');
                const L = SGW.fields, c = k => L.filter(f => ftype(f) === k).length;
                if (host && !host.querySelector('.sgv-sum')) host.insertAdjacentHTML('beforeend', `<p class="sgv-sum text-[11.5px] text-slate-600 dark:text-slate-300"><i class="fa-solid fa-table-cells mr-1 text-cyan-600"></i>${Object.keys(KINDS).filter(c).map(k => `${c(k)} ${KINDS[k].short}`).join(' · ')}</p>`);
            }
        } catch (e) { console.warn('sgv wiz', e); }
        return r;
    };
    // langkah 3 → 4: tiap penanda tangan minimal satu kotak (jenis apa pun)
    const bs = sgStep;
    sgStep = async function (dir) {
        return bs.apply(this, arguments);
    };
    const bn = sgNew;
    sgNew = function () { SGW.ftype = 'sign'; const r = bn.apply(this, arguments); return r; };
})();
// kirim & template: sertakan jenis kotak (type / req / label / kind) dan centang paraf
const fieldExtra = f => Object.assign({}, f.type && f.type !== 'sign' ? { type: f.type } : {}, f.req !== undefined ? { req: !!f.req } : {}, f.label ? { label: f.label } : {}, f.kind ? { kind: f.kind } : {});
(function hookPayload() {
    const base = sbRpc;
    sbRpc = function (fn, body) {
        try {
            if (fn === 'sg_create' && body && body.p_doc && Array.isArray(body.p_doc.fields)) {
                const by = new Map(SGW.fields.map(f => [f.id, f]));
                body.p_doc.fields = body.p_doc.fields.map(f => Object.assign({}, f, fieldExtra(by.get(f.id) || {})));
            }
            if (fn === 'sg_tpl_save' && body && body.p_tpl) {
                if (Array.isArray(body.p_tpl.fields) && body.p_tpl.fields.length === SGW.fields.length) body.p_tpl.fields = body.p_tpl.fields.map((f, i) => Object.assign({}, f, fieldExtra(SGW.fields[i])));
                if (Array.isArray(body.p_tpl.signers)) body.p_tpl.signers = body.p_tpl.signers.map((g, i) => Object.assign({}, g, {}));
            }
        } catch (e) { console.warn('sgv payload', e); }
        return base.apply(this, arguments);
    };
})();

/* =====================================================================
   PENGIRIM — status "Sebagian", reset PIN + WhatsApp, email penanda tangan
   ===================================================================== */
const waNum = v => { let s = String(v || '').replace(/[^0-9]/g, ''); if (s.startsWith('0')) s = '62' + s.slice(1); else if (s.startsWith('8')) s = '62' + s; return s; };
(function hookRows() {
    const br = sgRow;
    sgRow = function (d) {
        let h = br.apply(this, arguments);
        try {
            const part = (d.signers || []).filter(g => g.status !== 'selesai' && g.draft && g.draft.n);
            if (part.length && d.status === 'proses') {
                const tag = `<span class="sgr-tag sgv-parttag" title="${E(part.map(g => `${g.name}: ${g.draft.n}/${g.draft.total} kotak`).join('\n'))}"><i class="fa-solid fa-clock-rotate-left"></i>Sebagian ${part.length === 1 ? part[0].draft.n + '/' + part[0].draft.total : part.length + ' orang'}</span>`;
                h = /<span class="sgr-tags">/.test(h) ? h.replace('<span class="sgr-tags">', '<span class="sgr-tags">' + tag) : h.replace(/(<span class="sgr-t">[\s\S]*?<\/small>)/, `$1<span class="sgr-tags">${tag}</span>`);
            }
        } catch (e) { }
        return h;
    };
    const bd = sgRowDetail;
    sgRowDetail = function (d) {
        let h = bd.apply(this, arguments);
        try {
            (d.signers || []).forEach(g => { if (g.status !== 'selesai' && g.draft && g.draft.n) h = h.replace(`<b>${E(g.name)}`, `<b>${E(g.name)}<span class="sgv-part" title="Disimpan ${E(sgTime(g.draft.at))}">Sebagian ${g.draft.n}/${g.draft.total} kotak</span>`); });
            h = h.replace(/title="Lihat \/ ubah PIN"/g, 'title="Reset PIN & kirim link via WhatsApp"');
        } catch (e) { }
        return h;
    };
})();

// reset PIN: PIN tidak pernah ditampilkan; perangkat yang diingat ikut dikeluarkan; kirim WhatsApp
async function resetPin(o) {      // o: { name, pid, docId, signerId, link }
    if (!confirm(`Reset PIN ${o.name}?\n\nPIN lama tidak berlaku lagi. ${o.name} membuat PIN baru sendiri saat membuka link.`)) return;
    try {
        let r;
        if (o.pid) r = await sbOwner('sg_signer_pin', { p_id: o.pid, p_pin: '' });
        else r = await sbOwner('sg_setpin', { p_id: o.docId, p_signer: o.signerId, p_pin: '' });
        if (r && r.ok === false) throw new Error(r.error);
        if (r && r.doc) sgUpsert(r.doc);
        if (r && r.signer && SG.signers) { const p = SG.signers.find(x => x.id === r.signer.id); if (p) Object.assign(p, r.signer); }
        if (o.docId) { const d = sgDoc(o.docId); if (d) { const g = d.signers.find(x => x.id === o.signerId); if (g) g.hasPin = false; } }
        try { sgRender(); } catch (e) { }
        toast(`PIN ${o.name} direset`, 'success');
    } catch (e) { return toast(e.message, 'error', 7000); }
    await sendReset(o);
}
async function sendReset(o) {
    try { if (!SG.signers && typeof sgSignersLoad === 'function') await sgSignersLoad(); } catch (e) { }
    const p = o.pid && (SG.signers || []).find(x => x.id === o.pid);
    let wa = (p && p.wa) || o.wa || '';
    if (!wa) {
        const v = prompt(`Nomor WhatsApp ${o.name} belum ada.\nKetik nomornya (mis. 0812xxxx) — disimpan ke daftar penanda tangan:`, ''); if (!v || !v.trim()) return toast('Reset selesai — kirim link ke ' + o.name + ' secara manual', 'info', 6000);
        wa = v.trim();
        if (p) { try { await sgSignerSave(Object.assign({}, p, { wa })); } catch (e) { toast('Nomor belum tersimpan: ' + e.message, 'error'); } }
    }
    let link = o.link || '';
    if (!link) { try { const r = await sbOwner('sg_plink', { p_name: o.name, p_app_url: APP_PUBLIC_URL }); link = r.link || ''; } catch (e) { } }
    const msg = `Halo ${o.name}, PIN tanda tangan Anda sudah direset.\nBuka link berikut lalu buat PIN baru (4 angka):\n${link}`;
    window.open(`https://wa.me/${waNum(wa)}?text=${encodeURIComponent(msg)}`, '_blank');
}
window.SGV2.resetPin = resetPin;
sgPinEdit = async function (id, sid) {
    const d = sgDoc(id), g = d && d.signers.find(x => x.id === sid); if (!g) return;
    return resetPin({ name: g.name, pid: g.pid || '', docId: id, signerId: sid, link: sgLink(d.link || '') });
};
// daftar penanda tangan: kolom email (opsional) + reset PIN via WhatsApp
new MutationObserver(() => {
    const m = $id('sg-people'); if (!m) return;
    const wa = m.querySelector('#sgp-wa');
    if (wa && !m.querySelector('#sgp-email')) {
        wa.insertAdjacentHTML('afterend', `<input id="sgp-email" class="field" placeholder="Email (opsional · untuk lupa PIN)" inputmode="email" autocomplete="off">`);
        const add = m.querySelector('#sgp-add'), id = add && (/Simpan\s+(\S+)/.exec(add.textContent) || [])[1];
        const ed = id && (SG.signers || []).find(x => x.id === id);
        if (ed) m.querySelector('#sgp-email').value = ed.email || '';
    }
    m.querySelectorAll('.sgp-row').forEach(row => {
        if (row.dataset.sgv) return; row.dataset.sgv = '1';
        const pinBtn = row.querySelector('[data-pin]'), id = (row.querySelector('[data-e]') || pinBtn || {}).dataset ? ((row.querySelector('[data-e]') || {}).dataset || {}).e : '';
        const p = (SG.signers || []).find(x => x.id === id);
        if (p && p.email) { const sm = row.querySelector('small'); if (sm) sm.insertAdjacentHTML('beforeend', ` · <i class="fa-solid fa-envelope"></i> ${E(p.email)}`); }
        if (pinBtn) {
            pinBtn.title = 'Reset PIN & kirim link via WhatsApp';
            pinBtn.onclick = ev => { ev.stopPropagation(); const q = (SG.signers || []).find(x => x.id === pinBtn.dataset.pin); if (q) resetPin({ name: q.name, pid: q.id, wa: q.wa }); };
        }
    });
}).observe(document.body, { childList: true, subtree: true });
(function hookSignerSave() {
    const base = sbRpc;
    sbRpc = function (fn, body) {
        if (fn === 'sg_signers_save' && body && body.p_item && !('email' in body.p_item)) {
            const inp = $id('sgp-email'), m = $id('sg-people');
            if (inp && m) { const add = m.querySelector('#sgp-add'), id = add && (/Simpan\s+(\S+)/.exec(add.textContent) || [])[1]; if ((body.p_item.id || '') === (id || '')) body.p_item.email = inp.value.trim(); }
        }
        return base.apply(this, arguments);
    };
})();

})();

/* =====================================================================
   Panel miniatur halaman (komputer) + tolak dengan catatan per halaman
   ===================================================================== */
(function () {
const $i = x => document.getElementById(x);
const esc2 = s => String(s == null ? '' : s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));

/* ---------- miniatur halaman ---------- */
const TH = { timer: null, io: null };
function pagesEl() { return $i('sg-pages'); }
function myPageSet() {
    try { const r = SGP.data, d = r.doc, me = r.me; return new Set(d.fields.filter(f => f.signer === me.id && me.status !== 'selesai').map(f => f.page)); } catch (e) { return new Set(); }
}
function thumbsWanted() { const p = pagesEl(); return !!p && window.innerWidth >= 1180 && p.querySelectorAll('.sg-page[data-page]').length >= 2; }
function buildThumbs() {
    let box = $i('sgv-thumbs');
    if (!thumbsWanted()) { if (box) box.remove(); return; }
    const pgs = [...pagesEl().querySelectorAll('.sg-page[data-page]')];
    const mine = myPageSet();
    if (!box) {
        box = document.createElement('nav'); box.id = 'sgv-thumbs'; box.setAttribute('aria-label', 'Halaman dokumen');
        box.innerHTML = '<p>Halaman</p>' + pgs.map(p => { const n = p.dataset.page; return `<button type="button" data-p="${esc2(n)}" title="Ke halaman ${esc2(n)}"><canvas width="1" height="1"></canvas><span>${esc2(n)}</span><i class="fa-solid fa-signature"></i></button>`; }).join('');
        document.body.appendChild(box);
        box.onclick = e => { const b = e.target.closest('button[data-p]'); if (!b) return; TH.lock = Date.now() + 1500; box.querySelectorAll('button.on').forEach(x => x.classList.remove('on')); b.classList.add('on'); const el = pagesEl().querySelector(`.sg-page[data-page="${b.dataset.p}"]`); if (el) el.scrollIntoView({ behavior: 'smooth', block: 'start' }); };
        if (TH.io) TH.io.disconnect();
        TH.io = new IntersectionObserver(es => {
            if (Date.now() < (TH.lock || 0)) return;
            let best = null; es.forEach(en => { if (en.isIntersecting && (!best || en.intersectionRatio > best.intersectionRatio)) best = en; });
            if (best) { box.querySelectorAll('button.on').forEach(b => b.classList.remove('on')); const b = box.querySelector(`button[data-p="${best.target.dataset.page}"]`); if (b) { b.classList.add('on'); const bt = b.offsetTop, h = box.clientHeight; if (bt < box.scrollTop + 24 || bt + b.offsetHeight > box.scrollTop + h - 8) box.scrollTop = bt - h / 2; } }
        }, { threshold: [0.2, 0.5, 0.8] });
        pgs.forEach(p => TH.io.observe(p));
    }
    box.querySelectorAll('button[data-p]').forEach(b => b.classList.toggle('mine', mine.has(+b.dataset.p)));
    // salin gambar halaman yang sudah tergambar (halaman dimuat bertahap)
    box.querySelectorAll('button[data-p]').forEach(b => {
        if (b.dataset.done) return;
        const src = pagesEl().querySelector(`.sg-page[data-page="${b.dataset.p}"] canvas`); if (!src || !src.width || !src.height) return;
        const pe = src.closest('.sg-page'); if (pe && pe.classList.contains('sg-lazy') && !pe.classList.contains('drawn')) return;
        const c = b.querySelector('canvas'), w = 64, h = Math.max(1, Math.round(64 * src.height / src.width));
        try { c.width = w; c.height = h; const x = c.getContext('2d'); x.fillStyle = '#fff'; x.fillRect(0, 0, w, h); x.drawImage(src, 0, 0, w, h); b.dataset.done = '1'; } catch (e) { }
    });
}
function thumbsTick() {
    if (!pagesEl()) { const b = $i('sgv-thumbs'); if (b) b.remove(); return; }
    try { buildThumbs(); } catch (e) { }
}
TH.timer = setInterval(thumbsTick, 1200);
window.addEventListener('resize', () => { try { thumbsTick(); } catch (e) { } });
window.SGV2.thumbs = thumbsTick;

/* ---------- tolak dengan catatan per halaman ---------- */
const MAXR = 500;
function pageCount() { try { const d = SGP.data.doc; return d.pages || Math.max(1, ...d.fields.map(f => f.page)); } catch (e) { return 1; } }
const baseOpen = window.sgRejectOpen, baseGo = window.sgRejectGo;
function composeReason() {
    const rows = [...document.querySelectorAll('#sg-rej .sgv-rj-row')].map(r => ({ p: r.dataset.p, t: r.querySelector('input').value.trim() })).filter(r => r.t);
    const gen = ($i('sgv-rj-gen') || {}).value || '';
    const parts = rows.map(r => `Hal ${r.p}: ${r.t}`);
    if (gen.trim()) parts.push((rows.length ? 'Umum: ' : '') + gen.trim());
    return parts.join('\n');
}
function updCount() {
    const n = composeReason().length, c = $i('sgv-rj-n'); if (!c) return;
    c.textContent = `${n}/${MAXR}`; c.classList.toggle('over', n > MAXR);
}
window.sgRejectOpen = function () {
    baseOpen.apply(this, arguments);
    const m = $i('sg-rej'), ta = $i('sg-rej-t'); if (!m || !ta || m.querySelector('#sgv-rj')) return;
    const N = pageCount();
    ta.style.display = 'none';
    ta.insertAdjacentHTML('beforebegin', `<div id="sgv-rj">
        ${N > 1 ? `<div class="sgv-rj-add"><select id="sgv-rj-pg" class="field"><option value="">Catatan untuk halaman…</option>${Array.from({ length: N }, (_, i) => `<option value="${i + 1}">Halaman ${i + 1}</option>`).join('')}</select></div>` : ''}
        <div id="sgv-rj-rows"></div>
        <textarea id="sgv-rj-gen" rows="3" class="field w-full" placeholder="${N > 1 ? 'Catatan umum (opsional bila sudah ada catatan halaman)' : 'mis. Nilai HP belum sesuai, mohon direvisi'}"></textarea>
        <p class="sgv-rj-ct"><span>Pengirim melihat tiap catatan lengkap dengan nomor halamannya.</span><b id="sgv-rj-n">0/${MAXR}</b></p></div>`);
    const rows = $i('sgv-rj-rows');
    const addRow = p => {
        if (rows.querySelector(`.sgv-rj-row[data-p="${p}"]`)) { rows.querySelector(`.sgv-rj-row[data-p="${p}"] input`).focus(); return; }
        const r = document.createElement('div'); r.className = 'sgv-rj-row'; r.dataset.p = p;
        r.innerHTML = `<b>Hal ${esc2(p)}</b><input class="field" maxlength="300" placeholder="Apa yang perlu diperbaiki di halaman ini?"><button type="button" title="Hapus" aria-label="Hapus catatan halaman ${esc2(p)}"><i class="fa-solid fa-xmark"></i></button>`;
        r.querySelector('input').oninput = updCount; r.querySelector('button').onclick = () => { r.remove(); updCount(); };
        // urut menurut nomor halaman
        const nx = [...rows.children].find(x => +x.dataset.p > +p); rows.insertBefore(r, nx || null); r.querySelector('input').focus(); updCount();
    };
    const sel = $i('sgv-rj-pg'); if (sel) sel.onchange = () => { if (sel.value) addRow(sel.value); sel.value = ''; };
    $i('sgv-rj-gen').oninput = updCount;
    // kalau jendela dibuka dari halaman yang sedang dilihat, langsung tawarkan halaman itu
    window.SGV2.rejAdd = addRow;
    setTimeout(() => { const g = $i('sgv-rj-gen'); if (g) g.focus(); }, 60);
};
window.sgRejectGo = function () {
    const ta = $i('sg-rej-t');
    if (ta && $i('sgv-rj')) {
        const txt = composeReason();
        if (txt.length > MAXR) { const e = $i('sg-rej-msg'); if (e) { e.textContent = `Catatan terlalu panjang (${txt.length}/${MAXR} huruf) — persingkat`; e.classList.remove('hidden'); } return; }
        ta.value = txt;
    }
    return baseGo.apply(this, arguments);
};

/* ---------- tampilan di sisi pengirim: "Hal N" jadi label ---------- */
function fmtReason(h) {
    return h.replace(/(<span class="sgr-why"><i[^>]*><\/i>)([\s\S]*?)(<\/span>)/g, (m, a, t, z) => {
        if (!/(^|\n)\s*(Hal \d+|Umum):/.test(t)) return m;
        return a + '<span class="sgv-rjv">' + t.split(/\n/).map(l => l.replace(/^\s*(Hal \d+|Umum):\s*/, (mm, k) => `<b class="sgv-hp">${k}</b>`)).map(l => `<span>${l}</span>`).join('') + '</span>' + z;
    });
}
(function () {
    const bd = window.sgRowDetail;
    if (typeof bd === 'function') window.sgRowDetail = function () { return fmtReason(bd.apply(this, arguments)); };
})();
})();

