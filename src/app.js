// ===== App controller =====
(function (G) {
  const DSV = G.DSV;
  const $ = (id) => document.getElementById(id);
  const esc = (s) => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  const LANGS = [
    { id: 'c', label: 'C', file: 'main.c' },
    { id: 'cpp', label: 'C++', file: 'main.cpp' },
    { id: 'java', label: 'Java', file: 'Main.java' },
    { id: 'python', label: 'Python', file: 'main.py' },
    { id: 'js', label: 'JavaScript', file: 'main.js' },
    { id: 'ts', label: 'TypeScript', file: 'main.ts' },
  ];
  const STORE = 'memscope:v2';
  const load = () => { try { return JSON.parse(localStorage.getItem(STORE) || 'null') || {}; } catch (e) { return {}; } };
  const save = (o) => { try { localStorage.setItem(STORE, JSON.stringify(o)); } catch (e) { } };

  const S = {
    lang: 'c', exId: null, result: null, idx: 0, lastIdx: -1, playing: null, stale: false,
    settings: { showLiterals: false, showAddr: false, markers: true, collapseNull: true, heapTree: true, showFuncs: false, animate: true, maxSteps: 5000 },
    codes: {}, inputs: {},
  };
  let ed, viz;

  function init() {
    const saved = load();
    if (saved.settings) Object.assign(S.settings, saved.settings);
    S.codes = saved.codes || {};
    S.inputs = saved.inputs || {};
    S.lang = saved.lang && LANGS.some(l => l.id === saved.lang) ? saved.lang : 'c';
    S.exByLang = saved.exByLang || {};
    // language buttons
    $('langs').innerHTML = LANGS.map(l => '<button data-lang="' + l.id + '" aria-pressed="false">' + l.label + '</button>').join('');
    $('langs').addEventListener('click', (e) => { const b = e.target.closest('[data-lang]'); if (b) switchLang(b.dataset.lang); });
    ed = new DSV.Editor($('editor'), { onChange: onEdit, onBpChange: () => { drawTimeline(); } });
    viz = new DSV.Viz($('vizwrap'));
    bindControls();
    bindSettings();
    switchLang(S.lang, true);
    run();
  }

  function examplesFor(lang) { return DSV.examples.filter(e => e.lang === lang); }
  function switchLang(lang, initial) {
    if (!initial) persistCode();
    S.lang = lang;
    for (const b of $('langs').children) b.setAttribute('aria-pressed', String(b.dataset.lang === lang));
    const exs = examplesFor(lang);
    let opts = '';
    for (const c of DSV.exCats) {
      const g = exs.filter(e => e.cat === c);
      if (g.length) opts += '<optgroup label="' + esc(c) + '">' + g.map(e => '<option value="' + e.id + '">' + esc(e.title) + '</option>').join('') + '</optgroup>';
    }
    $('exSel').innerHTML = opts + '<optgroup label="其他"><option value="__blank">空白程序</option></optgroup>';
    const meta = LANGS.find(l => l.id === lang);
    $('fileName').textContent = meta.file;
    ed.setLang(lang);
    const exId = S.exByLang[lang] || (exs[0] && exs[0].id);
    const savedCode = S.codes[lang];
    if (savedCode != null) {
      S.exId = exId;
      $('exSel').value = exId || '__blank';
      ed.value = savedCode;
      const inp = S.inputs[lang] || {};
      $('argsIn').value = inp.args != null ? inp.args : '';
      $('stdinIn').value = inp.stdin != null ? inp.stdin : '';
    } else loadExample(exId || '__blank', true);
    updateIoVisibility();
    updateDesc();
    updateDirty();
    if (!initial) { S.result = null; run(); }
  }
  function loadExample(id, quiet) {
    let ex = DSV.examples.find(e => e.id === id);
    S.exId = ex ? ex.id : '__blank';
    S.exByLang[S.lang] = S.exId;
    $('exSel').value = S.exId;
    ed.value = ex ? ex.code : DSV.blankCode[S.lang];
    $('argsIn').value = ex && ex.args ? ex.args : '';
    $('stdinIn').value = ex && ex.stdin ? ex.stdin : '';
    delete S.codes[S.lang];
    delete S.inputs[S.lang];
    ed.bps.clear(); ed.renderMarks();
    updateDesc();
    updateDirty();
    persist();
  }
  function currentExample() { return DSV.examples.find(e => e.id === S.exId); }
  function updateDesc() {
    const ex = currentExample();
    $('exDesc').textContent = ex && ex.desc ? ex.desc : '';
    $('exDesc').title = ex && ex.desc ? ex.desc : '';
  }
  function updateDirty() {
    const ex = currentExample();
    const base = ex ? ex.code : DSV.blankCode[S.lang];
    const dirty = ed.value !== base;
    $('dirtyDot').hidden = !dirty;
    $('resetBtn').hidden = !dirty;
  }
  function updateIoVisibility() {
    const l = S.lang;
    const argsOk = l === 'c' || l === 'cpp' || l === 'java' || l === 'python';
    $('argsBox').hidden = !argsOk;
    $('argsLabel').textContent = l === 'java' ? '命令行参数（args，用空格分隔）' : (l === 'python' ? '命令行参数（sys.argv，用空格分隔）' : '命令行参数（argv，用空格分隔）');
    $('stdinIn').placeholder = { c: 'get_int / scanf 读取，每行一个', cpp: 'cin 读取的内容', java: 'Scanner 读取的内容', python: 'input() 读取，每行一个', js: 'prompt() 读取，每行一个', ts: 'prompt() 读取，每行一个' }[l];
    $('stdinBox').classList.toggle('one', !argsOk);
  }
  function persistCode() {
    const ex = currentExample();
    const base = ex ? ex.code : DSV.blankCode[S.lang];
    if (ed.value !== base) S.codes[S.lang] = ed.value; else delete S.codes[S.lang];
    const exArgs = ex && ex.args ? ex.args : '', exStdin = ex && ex.stdin ? ex.stdin : '';
    if ($('argsIn').value !== exArgs || $('stdinIn').value !== exStdin) S.inputs[S.lang] = { args: $('argsIn').value, stdin: $('stdinIn').value };
    else delete S.inputs[S.lang];
  }
  function persist() { persistCode(); save({ lang: S.lang, codes: S.codes, inputs: S.inputs, settings: S.settings, exByLang: S.exByLang }); }
  let persistT = 0;
  function onEdit() {
    updateDirty();
    if (S.result) { S.stale = true; $('runBtn').classList.add('stale'); $('runBtn').title = '代码已修改，重新运行以更新可视化（Ctrl/⌘ + Enter）'; }
    clearTimeout(persistT); persistT = setTimeout(persist, 600);
  }

  // ================= run =================
  function run() {
    stop();
    persist();
    const code = ed.value;
    const args = $('argsIn').value.trim() ? $('argsIn').value.trim().split(/\s+/) : [];
    const opts = { args, stdin: $('stdinIn').value, maxSteps: +S.settings.maxSteps, progName: './main' };
    let res;
    const t0 = performance.now();
    try { res = DSV.langs[S.lang].run(code, opts); }
    catch (e) { res = { steps: [], out: '', compileError: null, error: { kind: 'internal', msg: '可视化器内部错误：' + e.message, hint: '' } }; console.error(e); }
    res.ms = performance.now() - t0;
    S.result = res;
    S.stale = false;
    $('runBtn').classList.remove('stale');
    $('runBtn').title = '运行并生成可视化（Ctrl/⌘ + Enter）';
    S.lastIdx = -1;
    if (viz.autoFit) viz.scale = 1;
    $('tl').max = Math.max(0, res.steps.length - 1);
    if (res.compileError || !res.steps.length) { showCompileError(res); return; }
    drawTimeline();
    go(0, true);
  }
  function showCompileError(res) {
    const ce = res.compileError;
    ed.setMarks(ce && ce.line ? { [ce.line]: 'err' } : {});
    if (ce && ce.line) ed.scrollToLine(ce.line);
    $('evBadge').className = 'evb error'; $('evBadge').textContent = '语法错误';
    $('where').innerHTML = ce ? '第 <b>' + ce.line + '</b> 行：' + esc(ce.msg) : esc(res.error ? res.error.msg : '没有可执行的步骤');
    viz.clear();
    $('explain').innerHTML = '<div class="errbox"><b>' + (ce ? '代码无法运行（第 ' + ce.line + ' 行）' : '运行失败') + '</b>' + esc(ce ? ce.msg : (res.error ? res.error.msg : '')) + '<p>修正后按 ⌘/Ctrl + Enter 重新运行。可视化器支持的是各语言的常用子集，如果你确定代码没问题，可能是用到了暂不支持的语法。</p></div>';
    $('out').innerHTML = '<span class="dim">（程序没有运行）</span>';
    $('stepNum').textContent = '0 / 0';
    $('tl').max = 0;
    drawTimeline();
    updateButtons();
  }

  // ================= navigation =================
  function go(i, force) {
    const res = S.result;
    if (!res || !res.steps.length) return;
    i = Math.max(0, Math.min(res.steps.length - 1, i));
    if (i === S.idx && !force && S.lastIdx === i) return;
    const adjacent = Math.abs(i - S.idx) === 1 && !force;
    S.idx = i;
    renderStep(adjacent);
    S.lastIdx = i;
  }
  function renderStep(adjacent) {
    const res = S.result;
    const st = res.steps[S.idx];
    const prev = S.idx > 0 ? res.steps[S.idx - 1] : null;
    // editor marks
    const marks = {};
    if (prev && prev.line && prev.line !== st.line) marks[prev.line] = 'prev';
    if (st.line) marks[st.line] = st.ev === 'error' ? 'err' : 'next';
    ed.setMarks(marks);
    if (st.line) ed.scrollToLine(st.line);
    // viz
    try { viz.render(st, prev, S.settings, { adjacent, idx: S.idx }); }
    catch (e) { console.error(e); }
    $('zLabel').textContent = Math.round(viz.scale * 100) + '%';
    // status
    const ev = st.ev;
    const badge = { call: '进入函数', return: '即将返回', error: '出错', end: '结束', line: '执行中' }[ev] || '执行中';
    $('evBadge').className = 'evb ' + ev;
    $('evBadge').textContent = badge;
    const fn = st.fn ? ' · <code>' + esc(st.fn) + '</code>' : '';
    if (ev === 'end') $('where').innerHTML = '程序已经执行完毕' + (res.error ? '' : '');
    else $('where').innerHTML = (ev === 'error' ? '出错位置：第 <b>' + st.line + '</b> 行' : '下一步执行第 <b>' + st.line + '</b> 行') + fn;
    // explain
    $('explain').innerHTML = explainHTML(st, prev);
    // output
    const outNow = res.out.slice(0, st.out);
    const outPrev = prev ? res.out.slice(0, prev.out) : '';
    if (!outNow) $('out').innerHTML = '<span class="dim">（还没有输出）</span>';
    else if (outNow.length > outPrev.length && outNow.startsWith(outPrev)) $('out').innerHTML = esc(outPrev) + '<span class="new">' + esc(outNow.slice(outPrev.length)) + '</span>';
    else $('out').innerHTML = esc(outNow);
    const ob = $('out').parentElement; ob.scrollTop = ob.scrollHeight;
    $('outHint').textContent = outNow ? outNow.split('\n').length - (outNow.endsWith('\n') ? 1 : 0) + ' 行' : '';
    // timeline
    $('tl').value = S.idx;
    $('stepNum').textContent = (S.idx + 1) + ' / ' + res.steps.length;
    $('stepHint').textContent = '第 ' + (S.idx + 1) + ' 步，共 ' + res.steps.length + ' 步';
    updateButtons();
  }
  function explainHTML(st, prev) {
    let h = '';
    const ex = currentExample();
    if (S.idx === 0 && ex && ex.desc && !S.stale && ed.value === ex.code) h += '<div class="desc">' + esc(ex.desc) + '</div>';
    if (prev && prev.ev === 'call') h += '<div class="lineinfo">刚进入函数 <code>' + esc(prev.fn || '') + '</code>，参数已经放进它的栈帧。</div>';
    else if (prev && prev.ev === 'return') h += '<div class="lineinfo">函数 <code>' + esc(prev.fn || '') + '</code> 已经返回，它的栈帧被销毁，回到调用它的地方继续执行。</div>';
    else if (prev && prev.line) {
      const t = ed.lineText(prev.line);
      h += '<div class="lineinfo">刚执行完第 ' + prev.line + ' 行' + (t ? '：<code>' + esc(t) + '</code>' : '') + '</div>';
    } else if (S.idx === 0) h += '<div class="lineinfo">程序从这里开始运行。按 <b>▶</b>（或键盘 →）执行下一步，按 <b>◀</b> 可以随时倒回去。</div>';
    const msgs = (st.msgs || []).filter(m => m.cls !== 'error');
    if (msgs.length) h += '<ul class="msgs">' + msgs.map(m => '<li class="' + m.cls + '">' + esc(m.text) + '</li>').join('') + '</ul>';
    if (st.ev === 'call') h += '<div class="lineinfo">调用栈上新开了一个帧，参数已经复制进去。</div>';
    if (st.ev === 'return') h += '<div class="lineinfo">函数即将返回，返回值显示在帧的底部；返回后这个帧和它的局部变量都会消失。</div>';
    if (st.err) h += '<div class="errbox"><b>' + esc(st.err.msg) + '</b>' + (st.err.hint ? '<p>' + esc(st.err.hint) + '</p>' : '') + '</div>';
    if (st.ev !== 'end' && st.ev !== 'error' && st.line) {
      const t = ed.lineText(st.line);
      h += '<div class="lineinfo">接下来执行第 ' + st.line + ' 行' + (t ? '：<code>' + esc(t) + '</code>' : '') + '</div>';
    }
    if (st.ev === 'end' && S.result.steps.length >= +S.settings.maxSteps) h += '<div class="lineinfo">已达到步数上限，可以在设置里调高。</div>';
    return h || '<div class="lineinfo">（这一步没有特别的事件）</div>';
  }
  function updateButtons() {
    const res = S.result;
    const n = res ? res.steps.length : 0;
    const i = S.idx;
    $('bFirst').disabled = $('bPrev').disabled = !n || i <= 0;
    $('bNext').disabled = $('bLast').disabled = !n || i >= n - 1;
    $('bPlay').disabled = !n || (i >= n - 1 && !S.playing);
    $('bOver').disabled = $('bOut').disabled = !n || i >= n - 1;
    $('bBpPrev').disabled = !n || !ed.bps.size;
    $('bBpNext').disabled = !n || !ed.bps.size;
    $('bPlay').textContent = S.playing ? '❚❚ 暂停' : '▶ 播放';
  }
  const steps = () => S.result ? S.result.steps : [];
  function next() { go(S.idx + 1); }
  function prevStep() { go(S.idx - 1); }
  function stepOver() {
    const ss = steps(); const d = ss[S.idx].depth;
    for (let i = S.idx + 1; i < ss.length; i++) if (ss[i].depth <= d && !(ss[i].ev === 'return' && ss[i].depth === d && false)) { go(i); return; }
    go(ss.length - 1);
  }
  function stepOut() {
    const ss = steps(); const d = ss[S.idx].depth;
    for (let i = S.idx + 1; i < ss.length; i++) if (ss[i].depth < d) { go(i); return; }
    go(ss.length - 1);
  }
  function nextBp() {
    const ss = steps();
    for (let i = S.idx + 1; i < ss.length; i++) if (ed.bps.has(ss[i].line) && ss[i].line !== ss[i - 1].line) { go(i); return true; }
    for (let i = S.idx + 1; i < ss.length; i++) if (ed.bps.has(ss[i].line)) { go(i); return true; }
    toast(ed.bps.size ? '后面没有再经过断点了' : '先点击代码左侧的行号设置断点');
    return false;
  }
  function prevBp() {
    const ss = steps();
    for (let i = S.idx - 1; i >= 0; i--) if (ed.bps.has(ss[i].line)) { go(i); return; }
    toast('前面没有经过断点');
  }
  function play() {
    if (S.playing) { stop(); return; }
    const ss = steps();
    if (!ss.length) return;
    if (S.idx >= ss.length - 1) go(0);
    const tick = () => {
      if (S.idx >= ss.length - 1) { stop(); return; }
      go(S.idx + 1);
      if (ed.bps.has(ss[S.idx].line) && ss[S.idx].line !== ss[S.idx - 1].line) { stop(); toast('在断点（第 ' + ss[S.idx].line + ' 行）处暂停'); return; }
      if (ss[S.idx].ev === 'error') { stop(); return; }
      S.playing = setTimeout(tick, speedMs());
    };
    S.playing = setTimeout(tick, 60);
    updateButtons();
  }
  function stop() { if (S.playing) { clearTimeout(S.playing); S.playing = null; } updateButtons(); }
  function speedMs() { const v = +$('speed').value; return Math.round(1400 / Math.pow(1.45, v - 1)); }

  let toastT = 0;
  function toast(msg) {
    let t = document.querySelector('.toast');
    if (!t) { t = document.createElement('div'); t.className = 'toast'; t.setAttribute('role', 'status'); document.body.appendChild(t); }
    t.textContent = msg; t.hidden = false;
    clearTimeout(toastT); toastT = setTimeout(() => { t.hidden = true; }, 2200);
  }

  // ================= timeline =================
  function drawTimeline() {
    const cv = $('tlCanvas');
    const w = cv.clientWidth || 300;
    const dpr = window.devicePixelRatio || 1;
    cv.width = w * dpr; cv.height = 26 * dpr;
    const c = cv.getContext('2d');
    c.scale(dpr, dpr);
    c.clearRect(0, 0, w, 26);
    const ss = steps();
    if (ss.length < 2) return;
    const css = getComputedStyle(document.documentElement);
    const col = (n) => css.getPropertyValue(n).trim();
    const pad = 7;
    const x = (i) => pad + (w - pad * 2) * i / (ss.length - 1);
    const draw = (i, color, y, h, wd) => { c.fillStyle = color; c.fillRect(Math.round(x(i) - wd / 2), y, wd, h); };
    const stackC = col('--stack'), hotC = col('--hot'), inkC = col('--ink-3'), dangerC = col('--danger');
    for (let i = 0; i < ss.length; i++) {
      const s = ss[i];
      if (s.ev === 'call') draw(i, stackC, 2, 5, 1.5);
      if (s.msgs && s.msgs.some(m => m.cls === 'alloc')) draw(i, hotC, 19, 5, 2);
      if (s.msgs && s.msgs.some(m => m.cls === 'free')) draw(i, inkC, 19, 5, 2);
      if (ed.bps.has(s.line) && (i === 0 || ss[i - 1].line !== s.line)) { c.fillStyle = dangerC; c.beginPath(); c.arc(x(i), 4, 2.4, 0, 6.3); c.fill(); }
      if (s.ev === 'error') draw(i, dangerC, 0, 26, 3);
    }
  }

  // ================= bindings =================
  function bindControls() {
    $('runBtn').onclick = run;
    $('bFirst').onclick = () => go(0);
    $('bPrev').onclick = prevStep;
    $('bNext').onclick = next;
    $('bLast').onclick = () => go(steps().length - 1);
    $('bPlay').onclick = play;
    $('bOver').onclick = stepOver;
    $('bOut').onclick = stepOut;
    $('bBpNext').onclick = nextBp;
    $('bBpPrev').onclick = prevBp;
    $('tl').addEventListener('input', () => { stop(); go(+$('tl').value); });
    $('exSel').addEventListener('change', () => { const v = $('exSel').value; persistCode(); loadExample(v); run(); });
    $('resetBtn').onclick = () => { loadExample(S.exId || '__blank'); run(); };
    $('argsIn').addEventListener('change', () => { persist(); if (S.result) onEdit(); });
    $('stdinIn').addEventListener('change', () => { persist(); if (S.result) onEdit(); });
    $('zIn').onclick = () => { viz.autoFit = false; viz.setScale(viz.scale * 1.15); $('zLabel').textContent = Math.round(viz.scale * 100) + '%'; };
    $('zOut').onclick = () => { viz.autoFit = false; viz.setScale(viz.scale / 1.15); $('zLabel').textContent = Math.round(viz.scale * 100) + '%'; };
    $('zFit').onclick = () => { viz.autoFit = false; if (viz.scale < 0.99) viz.setScale(1); else viz.fit(); $('zLabel').textContent = Math.round(viz.scale * 100) + '%'; };
    document.addEventListener('keydown', (e) => {
      const inEditor = e.target.closest && e.target.closest('textarea, input, select');
      if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') { e.preventDefault(); run(); return; }
      if (e.key === 'F10') { e.preventDefault(); stepOver(); return; }
      if (e.key === 'F11') { e.preventDefault(); if (e.shiftKey) stepOut(); else next(); return; }
      if (e.key === 'F8') { e.preventDefault(); nextBp(); return; }
      if (e.key === 'Escape') { closePops(); return; }
      if (inEditor) return;
      if (e.key === 'ArrowRight') { e.preventDefault(); stop(); go(S.idx + (e.shiftKey ? 10 : 1)); }
      else if (e.key === 'ArrowLeft') { e.preventDefault(); stop(); go(S.idx - (e.shiftKey ? 10 : 1)); }
      else if (e.key === 'Home') { e.preventDefault(); go(0); }
      else if (e.key === 'End') { e.preventDefault(); go(steps().length - 1); }
      else if (e.key === ' ' && !e.target.closest('button')) { e.preventDefault(); play(); }
    });
    // splitter
    const sp = $('splitter');
    sp.addEventListener('pointerdown', (e) => {
      sp.setPointerCapture(e.pointerId);
      const move = (ev) => { const pct = Math.min(70, Math.max(24, ev.clientX / window.innerWidth * 100)); $('work').style.setProperty('--left', pct + '%'); };
      const up = () => { sp.removeEventListener('pointermove', move); sp.removeEventListener('pointerup', up); drawTimeline(); if (S.result && S.result.steps.length) renderStep(false); };
      sp.addEventListener('pointermove', move); sp.addEventListener('pointerup', up);
    });
    let rt = 0;
    window.addEventListener('resize', () => { clearTimeout(rt); rt = setTimeout(() => { drawTimeline(); if (S.result && S.result.steps.length) renderStep(false); }, 150); });
    if (document.fonts && document.fonts.ready) document.fonts.ready.then(() => { ed.refresh(); if (S.result && S.result.steps.length) renderStep(false); });
  }
  function closePops() { for (const [p, b] of [['setPop', 'setBtn'], ['helpPop', 'helpBtn']]) { $(p).hidden = true; $(b).setAttribute('aria-expanded', 'false'); } }
  function bindSettings() {
    const pairs = [['setBtn', 'setPop'], ['helpBtn', 'helpPop']];
    for (const [b, p] of pairs) {
      $(b).onclick = (e) => { e.stopPropagation(); const open = $(p).hidden; closePops(); $(p).hidden = !open; $(b).setAttribute('aria-expanded', String(open)); };
      $(p).addEventListener('click', (e) => e.stopPropagation());
    }
    document.addEventListener('click', closePops);
    const map = { optLits: 'showLiterals', optAddr: 'showAddr', optMarkers: 'markers', optCollapse: 'collapseNull', optHeapTree: 'heapTree', optFuncs: 'showFuncs', optAnim: 'animate' };
    for (const id in map) {
      $(id).checked = !!S.settings[map[id]];
      $(id).addEventListener('change', () => { S.settings[map[id]] = $(id).checked; persist(); if (S.result && S.result.steps.length) renderStep(false); });
    }
    $('optSteps').value = String(S.settings.maxSteps);
    $('optSteps').addEventListener('change', () => { S.settings.maxSteps = +$('optSteps').value; persist(); run(); });
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init); else init();
})(typeof window !== 'undefined' ? window : globalThis);
