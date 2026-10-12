/* QR転送 app.js — 機能追加版
   追加機能: ①転送速度・残り時間の表示(スライディングウィンドウ)
            ②相手の読み取り状況に応じた自動調整(状況コードQR/手入力)
            ③転送前のファイル一覧(送信側で確認→マニフェスト枠を先頭に送信)
   プロトコル: 互換枠 "Q1|sid|idx|total|base64" + 新設マニフェスト枠 "QM|sid|base64(json)"
               受信側の状況コード "FB1|sid|got|total|recfps"(新設・旧受信側は無視される方向で送信側のみが使う) */
(function () {
  'use strict';

  // ---------- 小道具 ----------
  const $ = (s) => document.querySelector(s);

  /*PURE-START*/
  // CRC32 (IEEE, 反射版)
  const CRC_TABLE = (() => {
    const t = [];
    for (let n = 0; n < 256; n++) {
      let c = n;
      for (let k = 0; k < 8; k++) c = c & 1 ? c >>> 1 ^ -306674912 : c >>> 1;
      t[n] = c >>> 0;
    }
    return t;
  })();
  const crc32 = (bytes) => {
    let c = ~0;
    for (let i = 0; i < bytes.length; i++) c = CRC_TABLE[(c ^ bytes[i]) & 255] ^ c >>> 8;
    return ~c >>> 0;
  };
  const concatBytes = (list) => {
    const out = new Uint8Array(list.reduce((a, b) => a + b.length, 0));
    let o = 0;
    for (const b of list) { out.set(b, o); o += b.length; }
    return out;
  };
  // 複数ファイルをZIP(無圧縮)にまとめる
  function buildZip(entries) {
    const enc = new TextEncoder();
    const locals = [];
    const centrals = [];
    const d = new Date();
    const time = d.getHours() << 11 | d.getMinutes() << 5 | d.getSeconds() >> 1;
    const date = d.getFullYear() - 1980 << 9 | d.getMonth() + 1 << 5 | d.getDate();
    let offset = 0;
    for (const e of entries) {
      const name = enc.encode(e.name);
      const crc = crc32(e.data);
      const sz = e.data.length;
      const lh = new DataView(new ArrayBuffer(30));
      lh.setUint32(0, 67324752, true);
      lh.setUint16(4, 20, true);
      lh.setUint16(6, 2048, true);
      lh.setUint16(10, time, true);
      lh.setUint16(12, date, true);
      lh.setUint32(14, crc, true);
      lh.setUint32(18, sz, true);
      lh.setUint32(22, sz, true);
      lh.setUint16(26, name.length, true);
      locals.push(new Uint8Array(lh.buffer), name, e.data);
      const ch = new DataView(new ArrayBuffer(46));
      ch.setUint32(0, 33639248, true);
      ch.setUint16(4, 20, true);
      ch.setUint16(6, 20, true);
      ch.setUint16(8, 2048, true);
      ch.setUint16(12, time, true);
      ch.setUint16(14, date, true);
      ch.setUint32(16, crc, true);
      ch.setUint32(20, sz, true);
      ch.setUint32(24, sz, true);
      ch.setUint16(28, name.length, true);
      ch.setUint32(42, offset, true);
      centrals.push(new Uint8Array(ch.buffer), name);
      offset += 30 + name.length + sz;
    }
    const cen = concatBytes(centrals);
    const end = new DataView(new ArrayBuffer(22));
    end.setUint32(0, 101010256, true);
    end.setUint16(8, entries.length, true);
    end.setUint16(10, entries.length, true);
    end.setUint32(12, cen.length, true);
    end.setUint32(16, offset, true);
    return concatBytes([...locals, cen, new Uint8Array(end.buffer)]);
  }
  const b64enc = (u8) => btoa(String.fromCharCode.apply(null, u8));
  const b64dec = (s) => Uint8Array.from(atob(s), (c) => c.charCodeAt(0));
  /*PURE-END*/

  const fmtBytes = (n) => n >= 1048576 ? (n / 1048576).toFixed(1) + " MB" : n >= 1024 ? (n / 1024).toFixed(1) + " KB" : Math.round(n) + " B";
  const MAX_FRAMES = 50000;
  const MAX_TOTAL = 16777216;
  const MANIFEST_MAX_FILES = 60; // マニフェストに入るファイル数の上限(超過は「他N件」表記)
  const DANGEROUS_EXT = /\.(exe|bat|cmd|com|scr|pif|msi|msix|appx|dll|cpl|js|jse|mjs|vbs|vbe|wsf|wsh|ps1|psm1|sh|bash|command|py|rb|pl|php|jar|apk|ipa|deb|rpm|dmg|pkg|app|lnk|url|hta|chm|reg|inf|scf|iso|html|htm|xhtml|svg|swf|crx|xpi|docm|xlsm|pptm)$/i;
  const sanitizeName = (s) => {
    let r = String(s).replace(/[\u0000-\u001f\u007f\u200e\u200f\u202a-\u202e\u2066-\u2069]/g, "").replace(/[\\/:*?"<>|]/g, "_").trim().replace(/^\.+/, "").slice(0, 200).replace(/[. ]+$/, "");
    if (/^(con|prn|aux|nul|com[1-9]|lpt[1-9])(\..*)?$/i.test(r)) r = "_" + r;
    return r || "file";
  };
  const toHex = (u8) => [...u8].map((c) => c.toString(16).padStart(2, "0")).join("");
  async function sha256Hex(bytes) {
    try {
      if (window.crypto && crypto.subtle) return toHex(new Uint8Array(await crypto.subtle.digest("SHA-256", bytes)));
    } catch (e) {}
    return null;
  }
  const shortCode = (hex) => { hex = hex.slice(0, 8).toUpperCase(); return hex.slice(0, 4) + "-" + hex.slice(4); };
  const crc32Hex = (n) => n.toString(16).padStart(8, "0");

  function sniffMime(u8) {
    const eq = (o, a) => a.every((b, i) => u8[o + i] === b);
    const cs = (o, s) => eq(o, [...s].map((c) => c.charCodeAt(0)));
    if (eq(0, [137, 80, 78, 71])) return "image/png";
    if (eq(0, [255, 216, 255])) return "image/jpeg";
    if (cs(0, "GIF8")) return "image/gif";
    if (cs(0, "RIFF") && cs(8, "WEBP")) return "image/webp";
    if (cs(0, "BM")) return "image/bmp";
    if (cs(4, "ftyp")) return "video/mp4";
    if (eq(0, [26, 69, 223, 163])) return "video/webm";
    return null;
  }

  async function decompressLimited(bytes, limit) {
    const reader = new Blob([bytes]).stream().pipeThrough(new DecompressionStream("deflate-raw")).getReader();
    const parts = [];
    let total = 0;
    while (true) {
      const { done, value } = await reader.read();
      if (done) break;
      total += value.length;
      if (total > limit) { reader.cancel(); throw new Error("展開後のサイズが宣言と一致しません"); }
      parts.push(value);
    }
    return concatBytes(parts);
  }
  async function compressBytes(bytes, ctor, arg) {
    return new Uint8Array(await new Response(new Blob([bytes]).stream().pipeThrough(new ctor(arg))).arrayBuffer());
  }

  // ---------- QRワーカー(prefix: w-c6f090074a.js) ----------
  const QR_CAP = { L: 2953, M: 2331, Q: 1663, H: 1273 };
  const WORKER_FILE = "w-c6f090074a.js";
  function makeWorkerWrapper(onmsg) {
    let w = null;
    let dead = false;
    const fallback = () => {
      dead = true; w = null;
      if (onmsg) onmsg();
    };
    try {
      if (typeof Worker !== "undefined") {
        w = new Worker(WORKER_FILE);
        w.onmessage = onmsg;
        w.onerror = () => { if (!dead) fallback(); };
      }
    } catch (e) { fallback(); }
    let cb = 0;
    return {
      post(msg, transfer) {
        if (dead) return;
        if (w) { w.postMessage(msg, transfer || []); return; }
        // フォールバック(同期)
        setTimeout(() => {
          const r = window.__wh && window.__wh(msg);
          if (r && onmsg) onmsg({ data: r.r });
        }, 0);
      },
      kill() { if (w) w.terminate(); },
      ok: () => dead || !!w,
      set onmessage(fn) { if (w) w.onmessage = fn; },
      get _cb() { return cb; },
      set _cb(v) { cb = v; }
    };
  }

  // ---------- ステータス表示 ----------
  function setStatus(sel, s, title, sub) {
    const el = $(sel);
    el.dataset.s = s;
    el.querySelector("b").textContent = title;
    el.querySelector("span").textContent = sub || "";
  }

  // ---------- スリープ防止 ----------
  let wakeLock = null;
  async function setWakeLock(on) {
    try {
      if (on) {
        if (!wakeLock && navigator.wakeLock) wakeLock = await navigator.wakeLock.request("screen");
      } else if (wakeLock) {
        await wakeLock.release();
        wakeLock = null;
      }
    } catch (e) { wakeLock = null; }
  }
  document.addEventListener("visibilitychange", () => {
    if (!document.hidden && (sendFile || recvStream && !recvAborted)) setWakeLock(true);
  });

  // ---------- 共有ユーティリティ ----------
  function rangesToText(list) {
    const out = [];
    let a = -1, b = -1;
    const push = () => out.push(a === b ? String(a + 1) : a + 1 + "–" + (b + 1));
    for (const v of list) {
      if (a < 0) a = b = v;
      else if (v === b + 1) b = v;
      else { push(); a = b = v; }
    }
    if (a >= 0) push();
    return out;
  }
  function parseRanges(str, max) {
    const set = new Set();
    for (const tok of String(str).replace(/[–—〜~ー−]/g, "-").split(/[,\s、]+/)) {
      const m = tok.match(/^(\d+)(?:-(\d+))?$/);
      if (!m) continue;
      let x = +m[1], y = m[2] ? +m[2] : x;
      if (x > y) [x, y] = [y, x];
      for (let i = Math.max(1, x); i <= Math.min(max, y); i++) set.add(i - 1);
    }
    return [...set].sort((p, q) => p - q);
  }

  // ---------- タブ ----------
  function switchTab(toSend) {
    $("#pS").classList.toggle("hide", !toSend);
    $("#pR").classList.toggle("hide", toSend);
    $("#tS").classList.toggle("on", toSend);
    $("#tR").classList.toggle("on", !toSend);
    if (toSend) {
      if (sendFile) senderShowStatus();
    } else if (recvStream && !recvAborted) {
      // 受信タブではカメラを維持
    }
  }
  $("#tS").onclick = () => switchTab(true);
  $("#tR").onclick = () => switchTab(false);

  // ---------- 設定 ----------
  const DEFAULTS = { mode: "auto", fps: "8", size: "600", ec: "L", comp: "1", facing: "environment", maxrecv: "4" };
  function loadSettings() {
    let saved = {};
    try { saved = JSON.parse(localStorage.getItem("qrt-settings") || "{}") || {}; } catch (e) {}
    for (const k in DEFAULTS) {
      const el = $("#" + k);
      const v = k in saved ? String(saved[k]) : DEFAULTS[k];
      el.value = v;
      if (el.value !== v) el.value = DEFAULTS[k];
    }
    $("#fpsV").textContent = $("#fps").value;
    updateModeNote();
  }
  function saveSettings() {
    try {
      localStorage.setItem("qrt-settings", JSON.stringify(Object.fromEntries(Object.keys(DEFAULTS).map((k) => [k, $("#" + k).value]))));
    } catch (e) {}
  }
  function updateModeNote() {
    const auto = $("#mode").value === "auto";
    $("#manual").disabled = auto;
    if (!auto) $("#rec").textContent = "手動設定を使用中です";
    else if (!sendFile) $("#rec").textContent = "ファイルを選ぶと、端末とファイルに合わせたおすすめ設定を自動で選びます";
  }
  $("#mode").onchange = () => { saveSettings(); updateModeNote(); refreshSenderPlan(); };
  $("#fps").oninput = (e) => {
    $("#fpsV").textContent = e.target.value;
    saveSettings();
    if (sendFile && !sendAuto) {
      fpsTarget = fpsCurrent = +e.target.value;
      updateSpeedLine();
    }
  };
  $("#size").onchange = () => { saveSettings(); refreshSenderPlan(); };
  $("#ec").onchange = () => { saveSettings(); refreshSenderPlan(); };
  $("#comp").onchange = async () => {
    saveSettings();
    if (!sendFile) return;
    const c = await compressIfNeeded(sendFile.raw);
    sendFile.body = c.body;
    sendFile.c = c.c;
    rebuildHead();
    refreshSenderPlan();
  };
  $("#facing").onchange = saveSettings;
  $("#maxrecv").onchange = saveSettings;
  $("#sreset").onclick = () => {
    for (const k in DEFAULTS) $("#" + k).value = DEFAULTS[k];
    $("#fpsV").textContent = DEFAULTS.fps;
    saveSettings();
    updateModeNote();
    refreshSenderPlan();
  };

  // ============================================================
  // 送信側
  // ============================================================
  const PREVIEW_QR = 24;   // 先読みでQRを作っておく枚数
  const CACHE_MAX = 300;   // 生成済みQRのキャッシュ上限
  let sendFile = null;     // {raw, body, c, k, x, head}
  let sid = "";
  let totalFrames = 0;
  let chunkSize = 600;
  let ecLevel = "L";
  let playOrder = [];      // 表示する枠番号のリスト(再送時は絞る)
  let playPos = 0;
  let cycles = 0;
  let aborted = false;
  let generation = 0;
  let sendAuto = true;
  let fpsTarget = 8;       // 自動調整の上限(ユーザー設定 or 状況コード)
  let fpsCurrent = 8;      // 現在の表示速度
  let frameMs = 16.7;
  let rafSkip = 99;
  let rafLast = 0;
  let qrGenPending = 0;
  let qrDropCount = 0;
  let statLastT = 0;
  let autoLastT = 0;
  let pauseRendering = false;
  let fbFpsApplied = false;
  let fbNote = "";
  const qrCache = new Map();
  const qrInFlight = new Set();
  const tmpCanvas = document.createElement("canvas");
  let sendWorker = null;
  let manifestShownCycle = -1; // マニフェストQRを表示済みの周回
  let manifestFrame = "";  // "QM|sid|b64" (複数ファイル時のみ)
  let stagedFiles = [];    // 転送前確認用

  const newSid = () => { sid = Math.random().toString(36).slice(2, 6); };
  const payloadLen = () => sendFile.head.length + sendFile.body.length;

  function slicePayload(a, b) {
    const hl = sendFile.head.length;
    if (b <= hl) return sendFile.head.subarray(a, b);
    if (a >= hl) return sendFile.body.subarray(a - hl, b - hl);
    return concatBytes([sendFile.head.subarray(a), sendFile.body.subarray(0, b - hl)]);
  }
  const makeFrame = (idx) => ["Q1", sid, idx, totalFrames, b64enc(slicePayload(idx * chunkSize, Math.min((idx + 1) * chunkSize, payloadLen())))].join("|");

  function rebuildHead() {
    const name = sanitizeName($("#fname").value);
    sendFile.head = new TextEncoder().encode(JSON.stringify({
      n: name,
      s: sendFile.raw.length,
      c: sendFile.c,
      k: sendFile.k,
      x: sendFile.x
    }) + "\n");
  }

  async function compressIfNeeded(bytes) {
    let out = bytes, c = 0;
    if ($("#comp").value === "1" && window.CompressionStream) {
      try {
        const z = await compressBytes(bytes, CompressionStream, "deflate-raw");
        if (z.length < bytes.length) { out = z; c = 1; }
      } catch (e) {}
    }
    return { body: out, c };
  }

  // --- ③ 転送前のファイル一覧 ---
  $("#file").onchange = (e) => { stageFiles([...e.target.files]); e.target.value = ""; };
  const dropZone = $("#drop");
  ["dragenter", "dragover"].forEach((t) => dropZone.addEventListener(t, (e) => { e.preventDefault(); dropZone.classList.add("over"); }));
  ["dragleave", "drop"].forEach((t) => dropZone.addEventListener(t, (e) => { e.preventDefault(); dropZone.classList.remove("over"); }));
  dropZone.addEventListener("drop", (e) => stageFiles([...e.dataTransfer.files]));
  ["dragover", "drop"].forEach((t) => window.addEventListener(t, (e) => e.preventDefault()));

  async function stageFiles(files) {
    if (!files.length) return;
    stopSender(true);
    setStatus("#sSt", "warn", "確認中…", "ファイルの一覧を作成しています");
    const list = [];
    for (const f of files) {
      list.push({ name: sanitizeName(f.name), size: f.size, file: f });
    }
    stagedFiles = list;
    renderFileList();
    setStatus("#sSt", "idle", "転送内容の確認", "内容を確認して「この内容で転送」を押してください");
  }
  function renderFileList() {
    const wrap = $("#fListWrap");
    const box = $("#fList");
    box.innerHTML = "";
    let total = 0;
    stagedFiles.slice(0, MANIFEST_MAX_FILES).forEach((f, i) => {
      const div = document.createElement("div");
      const nm = document.createElement("b");
      nm.textContent = f.name;
      nm.style.wordBreak = "break-all";
      const sz = document.createElement("span");
      sz.textContent = fmtBytes(f.size);
      div.append(nm, sz);
      box.appendChild(div);
      total += f.size;
    });
    if (stagedFiles.length > MANIFEST_MAX_FILES) {
      const div = document.createElement("div");
      div.innerHTML = "<b>…他 " + (stagedFiles.length - MANIFEST_MAX_FILES) + " 件</b><span></span>";
      box.appendChild(div);
      total = stagedFiles.reduce((a, f) => a + f.size, 0);
    } else {
      total = stagedFiles.reduce((a, f) => a + f.size, 0);
    }
    $("#fTotal").textContent = stagedFiles.length + " 件 ・ 合計 " + fmtBytes(total) + (stagedFiles.length > 1 ? "(ZIPにまとめて送信します)" : "");
    wrap.classList.toggle("hide", !stagedFiles.length);
  }
  $("#breclear").onclick = () => {
    stagedFiles = [];
    renderFileList();
    stopSender(false);
  };
  $("#bstart").onclick = () => {
    if (!stagedFiles.length) return;
    startFromStaged(stagedFiles).catch(() => {
      stopSender(true);
      setStatus("#sSt", "err", "読み込めませんでした", "フォルダは非対応です。ファイルを選び直してください");
    });
  };

  async function startFromStaged(files) {
    setStatus("#sSt", "warn", "準備中…", "ファイルを読み込み、圧縮とハッシュ計算をしています");
    let raw, name, note = "";
    if (files.length === 1) {
      raw = new Uint8Array(await files[0].file.arrayBuffer());
      name = files[0].name;
    } else {
      const used = {};
      const entries = [];
      for (const f of files) {
        let n = f.name;
        if (used[n]) {
          const dot = n.lastIndexOf(".");
          const i = used[n]++;
          n = dot > 0 ? n.slice(0, dot) + "(" + i + ")" + n.slice(dot) : n + "(" + i + ")";
        } else used[n] = 1;
        entries.push({ name: n, data: new Uint8Array(await f.file.arrayBuffer()) });
      }
      raw = buildZip(entries);
      name = "files.zip";
      note = files.length + "個のファイルをZIPにまとめました。受信側ではZIPとして保存されます";
    }
    if (raw.length > MAX_TOTAL) {
      setStatus("#sSt", "err", "送信できません", "ファイルが大きすぎます(上限16MB)");
      return;
    }
    const c = await compressIfNeeded(raw);
    $("#fname").value = name;
    $("#sNote").textContent = note || "複数選択すると、ZIPにまとめて送信します";
    sendFile = {
      raw,
      body: c.body,
      c: c.c,
      k: crc32(raw),
      x: await sha256Hex(raw),
      head: null
    };
    $("#sFp").textContent = "照合コード: " + shortCode(sendFile.x || crc32Hex(sendFile.k)) + "(受信完了後の表示と一致するか確認できます)";
    rebuildHead();
    newSid();
    // マニフェスト枠(複数ファイル時のみ・新しいセッションIDで作り直す)
    manifestFrame = "";
    if (files.length > 1) {
      const mj = {
        n: files.length,
        f: files.slice(0, MANIFEST_MAX_FILES).map((f) => ({ n: f.name, s: f.size })),
        t: files.reduce((a, f) => a + f.size, 0)
      };
      if (files.length > MANIFEST_MAX_FILES) mj.m = files.length - MANIFEST_MAX_FILES;
      manifestFrame = "QM|" + sid + "|" + b64enc(new TextEncoder().encode(JSON.stringify(mj)));
    }
    refreshSenderPlan();
    $("#fListWrap").classList.add("hide");
  }

  // --- おすすめ設定(自動モード) ---
  function autoRecommend(payloadLen) {
    const cores = navigator.hardwareConcurrency || 4;
    const mem = navigator.deviceMemory || 4;
    const mobile = /Android|iPhone|iPad|Mobi/i.test(navigator.userAgent || "");
    let fps = mobile ? 8 : 12;
    if (cores <= 4 || mem <= 2) fps = Math.min(fps, 6);
    const size = 600;
    return { fps, size, ec: Math.ceil(payloadLen / size) <= 40 ? "M" : "L" };
  }

  function refreshSenderPlan() {
    if (!sendFile) return;
    sendAuto = $("#mode").value === "auto";
    let size, ec, fps, note = "";
    if (sendAuto) {
      const r = autoRecommend(payloadLen());
      size = r.size; ec = r.ec; fps = r.fps;
      $("#rec").textContent = "おすすめ設定を自動選択しました: " + fps + "枚/秒 ・ " + size + "B ・ 誤り訂正" + ec + "(端末の性能に合わせて速度を自動調整します)";
    } else {
      size = +$("#size").value;
      ec = $("#ec").value;
      fps = +$("#fps").value;
    }
    const capOrder = [1000, 600, 400, 200];
    while (Math.ceil(size / 3) * 4 + 20 > QR_CAP[ec] && size > 100) {
      size = capOrder.find((v) => v < size) || 100;
      note = "誤り訂正が強いため、データ量を自動で " + size + "B に下げました";
    }
    if (note && !sendAuto) {
      $("#size").value = String(size);
      saveSettings();
    }
    chunkSize = size;
    ecLevel = ec;
    totalFrames = Math.ceil(payloadLen() / size);
    if (totalFrames > MAX_FRAMES) {
      stopSender(true);
      setStatus("#sSt", "err", "枚数が多すぎます", totalFrames + "枚(上限" + MAX_FRAMES + "枚)。データ量を大きくするか、ファイルを小さくしてください");
      return;
    }
    if (!sendWorker) {
      sendWorker = makeWorkerWrapper(onQrGenerated);
      if (!sendWorker.ok()) {
        setStatus("#sSt", "err", "この環境では動作しません", "Web Workerに対応したブラウザで開いてください");
        return;
      }
    }
    playOrder = [...Array(totalFrames).keys()];
    playPos = 0;
    cycles = 0;
    generation++;
    qrCache.clear();
    qrInFlight.clear();
    qrCache.delete(-1);
    aborted = false;
    manifestShownCycle = -1;
    if (!fbFpsApplied) {
      fpsTarget = fps;
      fpsCurrent = fps;
    }
    rafSkip = 99;
    qrGenPending = qrDropCount = 0;
    fbNote = sendAuto ? fbNote : "";
    $("#bpause").textContent = "⏸ 一時停止";
    $("#qrbox").classList.remove("hide");
    $("#sCtl").classList.remove("hide");
    prefetchQr();
    updateFrameInfo();
    updateSpeedLine();
    senderShowStatus();
    setWakeLock(true);
  }

  function prefetchQr() {
    if (!sendFile || !sendWorker) return;
    const n = playOrder.length;
    const want = Math.min(n, PREVIEW_QR);
    for (let i = 0; i < want; i++) {
      const id = playOrder[(playPos + i) % n];
      if (!qrCache.has(id) && !qrInFlight.has(id)) {
        qrInFlight.add(id);
        sendWorker.post({ k: "qr", id, g: generation, text: makeFrame(id), ec: ecLevel });
      }
    }
    if (qrCache.size > CACHE_MAX) {
      const keep = new Set();
      for (let i = 0; i < want; i++) keep.add(playOrder[(playPos + i) % n]);
      for (const k of [...qrCache.keys()]) {
        if (qrCache.size <= CACHE_MAX) break;
        if (!keep.has(k)) qrCache.delete(k);
      }
    }
  }

  function onQrGenerated(msg) {
    const d = msg.data;
    if (d.k !== "qr" || d.g !== generation) return;
    qrInFlight.delete(d.id);
    if (d.err) {
      setStatus("#sSt", "err", "QRを作れませんでした", "データ量を小さくしてください");
      return;
    }
    qrCache.set(d.id, d);
  }

  function drawQr(qr) {
    const m = qr.n;
    const quiet = 4;
    const dim = m + quiet * 2;
    const ctx = tmpCanvas.getContext("2d");
    tmpCanvas.width = dim;
    tmpCanvas.height = dim;
    const img = ctx.createImageData(dim, dim);
    const px = img.data;
    px.fill(255);
    for (let y = 0; y < m; y++) {
      for (let x = 0; x < m; x++) {
        if (qr.bits[y * m + x]) {
          const o = ((y + quiet) * dim + x + quiet) * 4;
          px[o] = px[o + 1] = px[o + 2] = 0;
        }
      }
    }
    ctx.putImageData(img, 0, 0);
    const cv = $("#qr");
    const c2 = cv.getContext("2d");
    const W = cv.width;
    const scale = Math.max(1, Math.floor(W / dim));
    const size = scale * dim;
    const off = Math.floor((W - size) / 2);
    c2.imageSmoothingEnabled = false;
    c2.fillStyle = "#fff";
    c2.fillRect(0, 0, W, W);
    c2.drawImage(tmpCanvas, 0, 0, dim, dim, off, off, size, size);
  }

  // --- ① 送信側の速度表示(既存の理論値表示) ---
  function updateSpeedLine() {
    $("#sSpeed").textContent = "現在 " + fpsCurrent + "枚/秒 ・ 理論速度 約" + fmtBytes(fpsCurrent * chunkSize) + "/秒 ・ 全" + totalFrames + "枚 ≈ " + Math.ceil(totalFrames / Math.max(fpsCurrent, 1)) + "秒/周" + (fbNote ? " ・ " + fbNote : "");
  }
  function updateFrameInfo() {
    const n = playOrder.length;
    const cur = playOrder[(playPos - 1 + n) % n] + 1;
    $("#sInfo").textContent = cur + " / " + totalFrames + " 枚目 ・ " + (cycles + (playPos === 0 ? 0 : 1) || 1) + "周目" + (n < totalFrames ? " ・ 再送" + n + "枚のみ" : "") + ("(合計 " + fmtBytes(payloadLen()) + ")");
  }
  function senderShowStatus() {
    if (!sendFile) return;
    if (aborted) setStatus("#sSt", "warn", "一時停止中", "「▶ 再開」で続きから表示します");
    else if (playOrder.length < totalFrames) setStatus("#sSt", "run", "再送中", "指定の" + playOrder.length + "枚だけを繰り返し表示しています");
    else setStatus("#sSt", "run", "送信中", "受信側のカメラをこの画面に向けて、そのままお待ちください");
  }

  function renderLoop(t) {
    requestAnimationFrame(renderLoop);
    if (rafLast) {
      const dt = t - rafLast;
      if (dt > 0 && dt < 120) frameMs = frameMs * 0.92 + dt * 0.08;
      if (dt > Math.max(40, frameMs * 2.5)) qrDropCount++;
    }
    rafLast = t;
    if (!sendFile || !playOrder.length) return;
    autoFps(t);
    if (aborted && !pauseRendering) return;
    const need = Math.max(2, Math.round(1000 / fpsCurrent / frameMs));
    if (!pauseRendering && ++rafSkip < need) return;
    // マニフェスト枠: 各周回の先頭で数フレームだけ表示(1周に1回)
    if (manifestFrame && playPos === 0 && cycles > manifestShownCycle && !pauseRendering) {
      if (!qrCache.has(-1) && !qrInFlight.has(-1)) {
        qrInFlight.add(-1);
        sendWorker.post({ k: "qr", id: -1, g: generation, text: manifestFrame, ec: "L" });
      }
      const mq = qrCache.get(-1);
      if (mq) {
        drawQr(mq);
        $("#sInfo").textContent = "ファイル一覧(マニフェスト)を表示中";
        manifestTicks = (manifestTicks || 0) + 1;
        if (manifestTicks >= 15) { // 15フレーム分(約0.25〜1秒)表示したら本編へ
          manifestTicks = 0;
          manifestShownCycle = cycles;
        }
        return;
      }
    }
    const qr = qrCache.get(playOrder[playPos]);
    if (!qr) {
      qrGenPending++;
      rafSkip = need;
      prefetchQr();
      return;
    }
    pauseRendering = false;
    rafSkip = 0;
    drawQr(qr);
    playPos++;
    if (playPos >= playOrder.length) {
      playPos = 0;
      cycles++;
    }
    prefetchQr();
    updateFrameInfo();
  }
  let manifestTicks = 0;
  requestAnimationFrame(renderLoop);

  // 送信側の自律的な速度調整(フレーム落ちに応じて)
  function autoFps(t) {
    if (!autoLastT) { autoLastT = t; return; }
    if (t - autoLastT < 1000) return;
    autoLastT = t;
    const drops = qrGenPending + qrDropCount;
    qrGenPending = qrDropCount = 0;
    if (!sendAuto) return;
    if (drops >= 3 && fpsCurrent > 2) {
      fpsCurrent = Math.max(2, Math.floor(fpsCurrent * 0.75));
      fbNote = "端末の負荷が高いため、速度を" + fpsCurrent + "枚/秒に自動で下げました";
      updateSpeedLine();
    } else if (drops === 0 && fpsCurrent < fpsTarget && ++autoStable >= 5) {
      fpsCurrent++;
      autoStable = 0;
      if (fpsCurrent >= fpsTarget) fbNote = "";
      updateSpeedLine();
    }
  }
  let autoStable = 0;

  function setPaused(p) {
    aborted = p;
    $("#bpause").textContent = p ? "▶ 再開" : "⏸ 一時停止";
    if (!p) rafSkip = 99;
    senderShowStatus();
  }
  function stepFrame(dir) {
    if (!sendFile) return;
    setPaused(true);
    const n = playOrder.length;
    playPos = ((playPos - 1 + dir) % n + n) % n;
    pauseRendering = true;
  }
  function stopSender(keepFiles) {
    sendFile = null;
    playOrder = [];
    qrCache.clear();
    qrInFlight.clear();
    generation++;
    aborted = false;
    manifestFrame = "";
    stagedFiles = keepFiles ? stagedFiles : [];
    if (!keepFiles) renderFileList();
    $("#qrbox").classList.add("hide");
    $("#sCtl").classList.add("hide");
    $("#sInfo").textContent = "";
    $("#sSpeed").textContent = "";
    $("#sFp").textContent = "";
    $("#resend").value = "";
    fbFpsApplied = false;
    fbNote = "";
    $("#fbInfo").textContent = "";
    if (!keepFiles) {
      $("#sNote").textContent = "複数選択すると、ZIPにまとめて送信します";
      setStatus("#sSt", "idle", "待機中", "ファイルを選んでください");
      setWakeLock(false);
    }
  }

  $("#bpause").onclick = () => setPaused(!aborted);
  $("#bprev").onclick = () => stepFrame(-1);
  $("#bnext").onclick = () => stepFrame(1);
  $("#brestart").onclick = () => {
    if (!sendFile) return;
    playOrder = [...Array(totalFrames).keys()];
    playPos = 0;
    cycles = 0;
    $("#resend").value = "";
    setPaused(false);
    prefetchQr();
  };
  $("#bstop").onclick = () => stopSender(false);
  $("#bresend").onclick = () => {
    const list = parseRanges($("#resend").value, totalFrames);
    if (!list.length) {
      $("#sNote").textContent = "1〜" + totalFrames + "の番号を「3, 7, 12-15」のように入力してください";
      return;
    }
    playOrder = list;
    playPos = 0;
    cycles = 0;
    setPaused(false);
    prefetchQr();
    senderShowStatus();
  };
  $("#ball").onclick = () => {
    if (!sendFile) return;
    playOrder = [...Array(totalFrames).keys()];
    playPos = 0;
    cycles = 0;
    $("#resend").value = "";
    prefetchQr();
    senderShowStatus();
  };
  let nameTimer = 0;
  $("#fname").oninput = () => {
    if (!sendFile) return;
    clearTimeout(nameTimer);
    nameTimer = setTimeout(() => {
      rebuildHead();
      newSid();
      if (manifestFrame) manifestFrame = "QM|" + sid + "|" + manifestFrame.split("|")[2];
      refreshSenderPlan();
    }, 350);
  };

  // --- ② 送信側: 相手の状況コードを読み取って速度を調整 ---
  let fbStream = null;
  let fbRaf = 0;
  function stopFbScan() {
    cancelAnimationFrame(fbRaf);
    fbRaf = 0;
    if (fbStream) fbStream.getTracks().forEach((t) => t.stop());
    fbStream = null;
    $("#fbVid").classList.remove("show");
  }
  async function startFbScan() {
    if (!sendFile) { $("#fbInfo").textContent = "先にファイルを選んで転送を開始してください"; return; }
    $("#fbInfo").textContent = "カメラを起動中…";
    try {
      fbStream = await navigator.mediaDevices.getUserMedia({ video: { facingMode: "environment", width: { ideal: 1280 } }, audio: false });
    } catch (e) {
      fbStream = null;
      $("#fbInfo").textContent = "カメラを使えません。カメラ許可を確認するか、手入力を使ってください";
      return;
    }
    const v = $("#fbVid");
    v.srcObject = fbStream;
    v.classList.add("show");
    try { await v.play(); } catch (e) {}
    $("#fbInfo").textContent = "受信側の「状況コード」QRを画面にかざしてください";
    let scanId = 0;
    const cv = document.createElement("canvas");
    const ctx = cv.getContext("2d", { willReadFrequently: true });
    const scan = () => {
      fbRaf = requestAnimationFrame(scan);
      if (v.readyState < 2) return;
      const my = ++scanId;
      const vw = v.videoWidth, vh = v.videoHeight;
      if (!vw) return;
      const scale = Math.min(1, 640 / Math.max(vw, vh));
      const w = Math.round(vw * scale), h = Math.round(vh * scale);
      if (cv.width !== w || cv.height !== h) { cv.width = w; cv.height = h; }
      ctx.drawImage(v, 0, 0, w, h);
      if (my % 2) return; // 1回おきに解析(負荷軽減)
      let res = null;
      try { res = window.jsQR && jsQR(ctx.getImageData(0, 0, w, h).data, w, h, { inversionAttempts: "dontInvert" }); } catch (e) {}
      if (res && res.data) {
        const applied = applyFbCode(res.data);
        if (applied) { stopFbScan(); }
      }
    };
    fbRaf = requestAnimationFrame(scan);
  }
  // 状況コードの解析と反映
  // 形式1: "FB1|sid|got|total|recfps"  形式2: "sid got[/total] [fps]"
  function applyFbCode(text) {
    if (!sendFile) { $("#fbInfo").textContent = "転送を開始してから反映できます"; return false; }
    let sidIn, got, total, recfps;
    if (text.startsWith("FB1|")) {
      const p = text.split("|");
      if (p.length !== 5) return false;
      sidIn = p[1]; got = +p[2]; total = +p[3]; recfps = +p[4];
    } else {
      const m = text.match(/^([a-z0-9]{1,8})[\s,]+(\d+)(?:[\s,/]+(\d+))?(?:[\s,]+(\d+))?$/i);
      if (!m) { $("#fbInfo").textContent = "読み取ったコードを解釈できませんでした: " + text.slice(0, 40); return false; }
      sidIn = m[1]; got = +m[2]; total = m[3] ? +m[3] : 0; recfps = m[4] ? +m[4] : 0;
    }
    if (sidIn !== sid) { $("#fbInfo").textContent = "別の転送の状況コードです(コード: " + sidIn + ")。現在のセッションは " + sid + " です"; return false; }
    let msg = "";
    if (total && got) msg += "受信 " + got + "/" + total + "枚(" + Math.round(got / total * 100) + "%) ・ ";
    if (recfps >= 1 && recfps <= 20) {
      fpsTarget = Math.min(recfps, 20);
      fpsCurrent = Math.max(2, Math.round(fpsTarget));
      fbFpsApplied = true;
      fbNote = "相手の状況コードから速度を" + fpsCurrent + "枚/秒に調整しました";
      msg += "表示速度を " + fpsCurrent + "枚/秒 に変更しました";
    } else {
      msg += "速度の提案はありませんでした";
    }
    $("#fbInfo").textContent = msg;
    updateSpeedLine();
    return true;
  }
  $("#bfbcam").onclick = () => fbStream ? stopFbScan() : startFbScan();
  $("#bfbin").onclick = () => applyFbCode($("#fbCode").value.trim());

  // ============================================================
  // 受信側
  // ============================================================
  let recvStream = null;
  let track = null;
  let camRaf = 0;
  let decWorker = null;
  let camToWorker = false;
  let recvSid = "";
  let frames = null;
  let gotCount = 0;
  let dupCount = 0;
  let maxChunkSeen = 0;
  let gotBytes = 0;
  let statFirstT = 0;
  let statFirstBytes = 0;
  let lastBytes = 0;
  let statTimer = 0;
  let missTimer = 0;
  let decodeFails = 0;
  let torchOn = false;
  let zoomRange = null;
  let recvAborted = false;
  let fbWorker = null;
  let manifestInfo = null;
  let manifestPending = null;
  const blobUrls = [];
  // ① スライディングウィンドウ(直近15秒)のサンプル
  const winSamples = [];
  const WIN_MS = 15000;
  const recvLimit = () => Math.min(MAX_TOTAL, (+$("#maxrecv").value || 4) * 1048576);

  function recvStatusLine() {
    if (recvAborted) return;
    if (!recvStream) {
      setStatus("#rSt", "idle", "カメラ停止中", gotCount ? "受信済み " + gotCount + "/" + totalCount + "枚は保持しています。「カメラを開始」で続きから読み取ります" : "「カメラを開始」を押してください");
    } else if (!frames) {
      setStatus("#rSt", "run", "QRを待っています", "送信側の画面にカメラを向けてください");
    } else {
      setStatus("#rSt", "run", "受信中", gotCount + "/" + totalCount + "枚 ・ 残り" + (totalCount - gotCount) + "枚");
    }
  }
  let totalCount = 0;

  function recvAbort(msg) {
    recvAborted = true;
    stopCamera();
    setStatus("#rSt", "err", "中断しました", "");
    $("#rErr").textContent = msg;
  }

  function resetRecv(keepErr) {
    frames = null;
    recvSid = "";
    totalCount = 0;
    gotCount = 0;
    dupCount = 0;
    maxChunkSeen = 0;
    gotBytes = 0;
    statFirstT = 0;
    statFirstBytes = 0;
    lastBytes = 0;
    winSamples.length = 0;
    manifestInfo = null;
    manifestPending = null;
    recvAborted = false;
    blobUrls.splice(0).forEach((u) => URL.revokeObjectURL(u));
    $("#cGot").textContent = "0";
    $("#cMiss").textContent = "-";
    $("#cAll").textContent = "-";
    $("#pb").style.width = "0";
    $("#grid").innerHTML = "";
    $("#rOut").innerHTML = "";
    $("#rSpeed").textContent = "";
    $("#rInfo").textContent = "";
    $("#rMiss").textContent = "";
    $("#hint").textContent = "";
    $("#rFiles").classList.add("hide");
    $("#rFiles").innerHTML = "";
    $("#fbSend").classList.add("hide");
    if (!keepErr) $("#rErr").textContent = "";
  }

  async function applyCamEnhancements() {
    const caps = track.getCapabilities ? track.getCapabilities() : {};
    const adv = [];
    for (const [k, v] of [["focusMode", "continuous"], ["exposureMode", "continuous"], ["whiteBalanceMode", "continuous"]]) {
      if (caps[k] && caps[k].includes && caps[k].includes(v)) adv.push({ [k]: v });
    }
    if (adv.length) {
      try { await track.applyConstraints({ advanced: adv }); } catch (e) {}
    }
    $("#torch").classList.toggle("hide", !caps.torch);
    torchOn = false;
    $("#torch").textContent = "💡 ライト";
    zoomRange = caps.zoom;
    const z = $("#zoom");
    z.classList.toggle("hide", !zoomRange);
    if (zoomRange) {
      z.min = zoomRange.min;
      z.max = zoomRange.max;
      z.step = zoomRange.step || 0.1;
      z.value = zoomRange.min;
    }
  }

  async function startCamera() {
    $("#rErr").textContent = "";
    try {
      recvStream = await navigator.mediaDevices.getUserMedia({
        video: { facingMode: $("#facing").value, width: { ideal: 1920 }, height: { ideal: 1080 } },
        audio: false
      });
    } catch (e) {
      recvStream = null;
      setStatus("#rSt", "err", "カメラを使えません", "ブラウザのカメラ許可とHTTPS接続を確認してください");
      return;
    }
    track = recvStream.getVideoTracks()[0];
    await applyCamEnhancements();
    const v = $("#vid");
    v.srcObject = recvStream;
    try { await v.play(); } catch (e) {}
    $("#cam").textContent = "カメラを停止";
    if (!decWorker) {
      decWorker = makeWorkerWrapper(onDecoded);
      if (!decWorker.ok()) {
        stopCamera();
        setStatus("#rSt", "err", "この環境では動作しません", "Web Workerに対応したブラウザで開いてください");
        return;
      }
    }
    if (recvAborted || !frames) resetRecv();
    camToWorker = false;
    decodeFails = 0;
    setWakeLock(true);
    recvStatusLine();
    if (!camRaf) camRaf = requestAnimationFrame(camLoop);
  }

  function stopCamera() {
    cancelAnimationFrame(camRaf);
    camRaf = 0;
    if (recvStream) recvStream.getTracks().forEach((t) => t.stop());
    recvStream = null;
    track = null;
    camToWorker = false;
    $("#cam").textContent = "カメラを開始";
    $("#torch").classList.add("hide");
    $("#zoom").classList.add("hide");
    if (!sendFile || aborted) setWakeLock(false);
    recvStatusLine();
  }

  function camLoop() {
    camRaf = requestAnimationFrame(camLoop);
    const v = $("#vid");
    if (!recvStream || v.readyState < 2 || recvAborted || camToWorker || !decWorker) return;
    const vw = v.videoWidth, vh = v.videoHeight;
    if (!vw) return;
    const targetW = decodeFails > 16 && decodeFails % 2 ? 1600 : 960;
    const scale = Math.min(1, targetW / Math.max(vw, vh));
    const w = Math.round(vw * scale), h = Math.round(vh * scale);
    if (!workCanvas) {
      workCanvas = $("#work");
      workCtx = workCanvas.getContext("2d", { willReadFrequently: true });
    }
    if (workCanvas.width !== w || workCanvas.height !== h) {
      workCanvas.width = w;
      workCanvas.height = h;
    }
    workCtx.drawImage(v, 0, 0, w, h);
    const img = workCtx.getImageData(0, 0, w, h);
    camToWorker = true;
    decWorker.post({ k: "dec", id: ++decId, w, h, buf: img.data.buffer }, [img.data.buffer]);
  }
  let workCanvas = null, workCtx = null, decId = 0;

  function onDecoded(msg) {
    const d = msg.data;
    if (d.k !== "dec") return;
    camToWorker = false;
    if (d.data && d.data.startsWith("Q1|")) {
      decodeFails = 0;
      $("#hint").textContent = "";
      handleDataFrame(d.data);
    } else if (d.data && d.data.startsWith("QM|")) {
      handleManifestFrame(d.data);
    } else if (++decodeFails === 40 && recvStream && !recvAborted) {
      $("#hint").textContent = "QRを読み取れません。画面いっぱいに映し、ピントが合う距離まで離して、送信側の画面の明るさを上げてみてください。反射が映り込む場合は角度を変えてください。";
    }
  }

  // --- ① 受信側の速度・残り時間(スライディングウィンドウ) ---
  function pushStat() {
    if (missTimer) return;
    missTimer = setTimeout(updateStats, 100);
  }
  function updateStats() {
    missTimer = 0;
    if (!frames || recvAborted) return;
    const now = performance.now();
    winSamples.push({ t: now, b: gotBytes });
    while (winSamples.length > 2 && now - winSamples[0].t > WIN_MS) winSamples.shift();
    const miss = totalCount - gotCount;
    $("#cGot").textContent = gotCount;
    $("#cMiss").textContent = miss;
    $("#cAll").textContent = totalCount;
    $("#pb").style.width = gotCount / totalCount * 100 + "%";
    // 未取得の番号
    const missing = [];
    for (let i = 0; i < totalCount && missing.length < 5000; i++) {
      if (frames[i] === undefined) missing.push(i);
    }
    const missTxt = rangesToText(missing).join(", ");
    $("#rMiss").textContent = miss ? "未取得 " + miss + "枚: " + (missTxt.length > 240 ? missTxt.slice(0, 240) + "…" : missTxt) : "";
    $("#rInfo").textContent = gotCount + " / " + totalCount + " 枚 受信" + (dupCount ? "(重複 " + dupCount + " 回は無視)" : "");
    // 速度(直近15秒のウィンドウ)・残り時間・進捗率
    if (winSamples.length >= 2) {
      const first = winSamples[0];
      const secs = (now - first.t) / 1000;
      const bytes = gotBytes - first.b;
      if (secs > 0 && bytes > 0) {
        const speed = bytes / secs;
        const estTotal = totalCount * maxChunkSeen;
        const remainBytes = Math.max(0, estTotal - gotBytes);
        const eta = speed > 0 ? Math.ceil(remainBytes / speed) : 0;
        const pct = estTotal ? Math.min(100, gotBytes / estTotal * 100) : 0;
        $("#rSpeed").textContent = "受信速度 " + fmtBytes(speed) + "/秒 ・ 残り約" + eta + "秒(目安) ・ " + pct.toFixed(0) + "% (" + fmtBytes(gotBytes) + (estTotal ? " / " + fmtBytes(estTotal) : "") + ")";
      }
    }
    recvStatusLine();
    updateFbQr();
  }

  // --- データ枠(Q1)の処理 ---
  function handleDataFrame(text) {
    if (recvAborted || text.length > 1500) return;
    const parts = text.split("|");
    if (parts.length !== 5) return;
    const s = parts[1];
    const idx = +parts[2];
    const total = +parts[3];
    const b64 = parts[4];
    if (!/^[a-z0-9]{1,8}$/.test(s) || !Number.isInteger(idx) || !Number.isInteger(total) || total < 1 || total > MAX_FRAMES || idx < 0 || idx >= total || !/^[A-Za-z0-9+/]*={0,2}$/.test(b64)) return;
    if (frames && gotCount > 0 && (s !== recvSid || total !== totalCount)) {
      $("#rErr").textContent = "別の転送のQRを検出したため無視しました。最初からやり直す場合は「最初からやり直す」を押してください。";
      return;
    }
    if (s !== recvSid || total !== totalCount) {
      resetRecv(true);
      recvSid = s;
      totalCount = total;
      frames = new Array(total);
      if (total <= 2000) {
        const grid = $("#grid");
        for (let i = 0; i < total; i++) {
          const b = document.createElement("b");
          b.title = String(i + 1);
          grid.appendChild(b);
        }
      }
      // 待機していたマニフェストを表示
      if (manifestPending && manifestPending.sid === s) {
        showManifest(manifestPending.info);
        manifestPending = null;
      }
    }
    if (frames[idx] !== undefined) {
      dupCount++;
      pushStat();
      return;
    }
    const size = Math.floor(b64.length * 3 / 4);
    const limit = recvLimit();
    maxChunkSeen = Math.max(maxChunkSeen, size);
    if (total * maxChunkSeen > limit * 1.05 + 4096 || gotBytes + size > limit + 4096) {
      return recvAbort("受信サイズの上限(" + fmtBytes(limit) + ")を超えるため中断しました。設定で上限を変更できます。");
    }
    frames[idx] = b64dec(b64);
    gotCount++;
    gotBytes += size;
    const cell = $("#grid").children[idx];
    if (cell) cell.className = "ok";
    pushStat();
    if (gotCount === totalCount) finishRecv();
  }

  // --- ③ マニフェスト枠(QM)の処理 ---
  function handleManifestFrame(text) {
    if (recvAborted || text.length > 4000) return;
    const parts = text.split("|");
    if (parts.length !== 3) return;
    const s = parts[1];
    if (!/^[a-z0-9]{1,8}$/.test(s)) return;
    if (frames && s !== recvSid) return; // 進行中のセッションと別IDは無視
    try {
      const info = JSON.parse(new TextDecoder().decode(b64dec(parts[2])));
      if (!info || !Array.isArray(info.f)) return;
      if (frames && recvSid === s) showManifest(info);
      else manifestPending = { sid: s, info };
    } catch (e) {}
  }
  function showManifest(info) {
    const box = $("#rFiles");
    box.innerHTML = "";
    const title = document.createElement("b");
    title.textContent = "送信ファイル(" + info.n + " 件 ・ 合計 " + fmtBytes(info.t) + ")";
    box.appendChild(title);
    info.f.forEach((f) => {
      const div = document.createElement("div");
      const nm = document.createElement("b");
      nm.textContent = f.n;
      nm.style.wordBreak = "break-all";
      const sz = document.createElement("span");
      sz.textContent = fmtBytes(f.s);
      div.append(nm, sz);
      box.appendChild(div);
    });
    if (info.m) {
      const div = document.createElement("div");
      div.innerHTML = "<b>…他 " + info.m + " 件</b><span></span>";
      box.appendChild(div);
    }
    box.classList.remove("hide");
    manifestInfo = info;
  }

  // --- ② 受信側: 状況コードQRの表示 ---
  function updateFbQr() {
    if (!frames || recvAborted) return;
    const miss = totalCount - gotCount;
    // 読み取り実績(直近15秒)からおすすめの表示速度を提案
    let rec = 0;
    if (winSamples.length >= 2) {
      const now = performance.now();
      const first = winSamples[0];
      const secs = (now - first.t) / 1000;
      if (secs > 0.5 && gotCount > 1) {
        // ウィンドウ内の取得枚数を大まかに推定(サイズ比から)
        const bytes = gotBytes - first.b;
        const per = maxChunkSeen || 1;
        rec = Math.min(20, Math.max(1, Math.round(bytes / secs / per)));
      }
    }
    const pct = totalCount ? Math.round(gotCount / totalCount * 100) : 0;
    const text = "FB1|" + recvSid + "|" + gotCount + "|" + totalCount + "|" + rec;
    $("#fbCodeTxt").textContent = recvSid + " ・ " + pct + "%" + (rec ? " ・ 推奨" + rec + "枚/秒" : "");
    $("#fbSend").classList.remove("hide");
    if (!fbWorker) {
      fbWorker = makeWorkerWrapper((msg) => {
        const d = msg.data;
        if (d.k === "qr" && d.id === "fb" && !d.err) drawFbQr(d);
      });
    }
    fbWorker.post({ k: "qr", id: "fb", text, ec: "L" });
  }
  function drawFbQr(qr) {
    const cv = $("#fbQr");
    const m = qr.n, q = 2;
    const dim = m + q * 2;
    cv.width = dim;
    cv.height = dim;
    const ctx = cv.getContext("2d");
    const img = ctx.createImageData(dim, dim);
    img.data.fill(255);
    for (let y = 0; y < m; y++) {
      for (let x = 0; x < m; x++) {
        if (qr.bits[y * m + x]) {
          const o = ((y + q) * dim + x + q) * 4;
          img.data[o] = img.data[o + 1] = img.data[o + 2] = 0;
        }
      }
    }
    ctx.putImageData(img, 0, 0);
  }

  // --- 受信完了 → 検証・保存 ---
  async function finishRecv() {
    recvAborted = true;
    stopCamera();
    const startT = winSamples.length ? winSamples[0].t : performance.now();
    const secs = Math.max((performance.now() - startT) / 1000, 0.001);
    const got = frames;
    frames = null;
    $("#cGot").textContent = totalCount;
    $("#cMiss").textContent = 0;
    $("#pb").style.width = "100%";
    $("#rMiss").textContent = "";
    $("#rSpeed").textContent = "受信完了: " + fmtBytes(gotBytes) + " を " + secs.toFixed(1) + "秒で受信(平均 " + fmtBytes(gotBytes / secs) + "/秒)";
    setStatus("#rSt", "warn", "検証中…", "サイズ・CRC32・SHA-256を確認しています");
    try {
      const all = concatBytes(got);
      const nl = all.indexOf(10);
      if (nl < 2 || nl > 2048) throw new Error("ヘッダーが不正です");
      const head = JSON.parse(new TextDecoder().decode(all.subarray(0, nl)));
      const limit = recvLimit();
      if (typeof head.n !== "string" || !Number.isInteger(head.s) || head.s < 0 || head.s > limit || !Number.isInteger(head.k) || head.k < 0 || head.k > 4294967295 || head.c !== 0 && head.c !== 1 || head.x !== undefined && !/^[0-9a-f]{64}$/.test(head.x)) {
        throw new Error("ヘッダーが不正です(または受信サイズの上限を超えています)");
      }
      if (all.length > limit + 2048 + 64) throw new Error("受信データが上限を超えています");
      head.n = sanitizeName(head.n);
      let body = all.subarray(nl + 1);
      if (head.c) body = await decompressLimited(body, head.s);
      if (body.length !== head.s || crc32(body) !== head.k) throw new Error("整合性チェック(サイズ/CRC32)に失敗しました");
      let code = crc32Hex(head.k);
      let note = "";
      if (head.x) {
        const x = await sha256Hex(body);
        if (x) {
          if (x !== head.x) throw new Error("SHA-256の検証に失敗しました");
          code = x;
        } else {
          code = head.x;
          note = "(この環境ではSHA-256を検証できませんでした)";
        }
      }
      const url = URL.createObjectURL(new Blob([body], { type: "application/octet-stream" }));
      const a = document.createElement("a");
      a.rel = "noopener";
      blobUrls.push(url);
      const lbl = document.createElement("label");
      const inp = document.createElement("input");
      lbl.textContent = "保存するファイル名(変更できます)";
      inp.type = "text";
      inp.value = head.n;
      inp.autocomplete = "off";
      a.href = url;
      a.className = "btn";
      a.style.marginTop = "10px";
      const fix = () => {
        const n = sanitizeName(inp.value);
        a.download = n;
        a.textContent = "「" + n + "」を保存 (" + fmtBytes(head.s) + ")";
      };
      inp.oninput = fix;
      fix();
      setStatus("#rSt", "ok", "受信完了", "整合性チェックOK。下のボタンから保存できます");
      $("#rInfo").textContent = totalCount + " / " + totalCount + " 枚 受信" + (dupCount ? "(重複 " + dupCount + " 回は無視)" : "");
      const codeDiv = document.createElement("div");
      codeDiv.className = "note bold";
      codeDiv.style.marginTop = "10px";
      codeDiv.textContent = "照合コード: " + shortCode(code) + note + "(送信側の表示と一致するか確認してください)";
      $("#rOut").append(codeDiv, lbl, inp, a);
      if (DANGEROUS_EXT.test(head.n)) {
        $("#rErr").textContent = "⚠ 実行ファイルやスクリプトの可能性があります。送信元が確かな場合のみ開いてください。";
      }
      const mime = sniffMime(body);
      if (/\.(png|jpe?g|gif|webp|bmp|mp4|m4v|webm|mov)$/i.test(head.n) && !mime) {
        $("#rErr").textContent = ($("#rErr").textContent + " ⚠ 拡張子と中身の形式が一致しません。開かないことをおすすめします。").trim();
      }
      if (mime) {
        const murl = URL.createObjectURL(new Blob([body], { type: mime }));
        const isImg = mime.startsWith("image/");
        const media = document.createElement(isImg ? "img" : "video");
        blobUrls.push(murl);
        media.src = murl;
        if (!isImg) {
          media.controls = true;
          media.playsInline = true;
        }
        media.style.cssText = "width:100%;max-height:60vh;object-fit:contain;border-radius:10px;margin-top:12px;background:#000";
        $("#rOut").prepend(media);
      }
      $("#fbSend").classList.add("hide");
    } catch (e) {
      setStatus("#rSt", "err", "受信に失敗しました", "");
      $("#rErr").textContent = "復元に失敗: " + e.message + "。「最初からやり直す」でもう一度お試しください。";
    }
  }

  $("#cam").onclick = () => recvStream ? stopCamera() : startCamera();
  $("#torch").onclick = async () => {
    if (!track) return;
    torchOn = !torchOn;
    try {
      await track.applyConstraints({ advanced: [{ torch: torchOn }] });
    } catch (e) {
      torchOn = !torchOn;
    }
    $("#torch").textContent = torchOn ? "💡 ライトを消す" : "💡 ライト";
  };
  $("#zoom").oninput = (e) => {
    if (track) track.applyConstraints({ advanced: [{ zoom: +e.target.value }] }).catch(() => {});
  };
  $("#rrestart").onclick = () => {
    resetRecv();
    if (recvStream) recvStatusLine();
    else startCamera();
  };
  $("#rabort").onclick = () => {
    stopCamera();
    resetRecv();
    recvStatusLine();
  };

  // ---------- 起動 ----------
  loadSettings();
  recvStatusLine();
  if ("serviceWorker" in navigator) {
    navigator.serviceWorker.register("s-v2.js").catch(() => {});
  }
})();
