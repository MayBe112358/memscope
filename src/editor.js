// ===== Lightweight code editor: textarea overlay + highlighter + gutter =====
(function (G) {
  const DSV = G.DSV;

  const KW = {
    c: 'auto break case char const continue default do double else enum extern float for goto if inline int long register restrict return short signed sizeof static struct switch typedef union unsigned void volatile while bool true false NULL string size_t',
    cpp: 'alignas alignof and auto bool break case catch char class const constexpr const_cast continue decltype default delete do double dynamic_cast else enum explicit export extern false float for friend goto if inline int long mutable namespace new noexcept not nullptr operator or private protected public register reinterpret_cast return short signed sizeof static static_cast struct switch template this throw true try typedef typeid typename union unsigned using virtual void volatile while override final string vector map set stack queue deque pair cout cin endl std unordered_map unordered_set priority_queue size_t list',
    java: 'abstract assert boolean break byte case catch char class const continue default do double else enum extends final finally float for goto if implements import instanceof int interface long native new package private protected public return short static strictfp super switch synchronized this throw throws transient try void volatile while true false null var record String',
    python: 'False None True and as assert async await break class continue def del elif else except finally for from global if import in is lambda nonlocal not or pass raise return try while with yield self',
    js: 'break case catch class const continue debugger default delete do else export extends false finally for function if import in instanceof let new null return super switch this throw true try typeof var void while with yield of undefined async await static get set',
    ts: 'break case catch class const continue debugger default delete do else export extends false finally for function if import in instanceof let new null return super switch this throw true try typeof var void while with yield of undefined static get set interface type enum implements private public protected readonly abstract as number string boolean any unknown never keyof declare namespace',
  };
  const BUILTINS = {
    python: 'print len range int float str list dict set tuple bool input abs min max sum sorted reversed enumerate zip map filter any all isinstance type ord chr round super object open iter next deque defaultdict Counter heapq math',
    js: 'console Math JSON Object Array Map Set String Number Promise parseInt parseFloat Infinity NaN Symbol Error',
    ts: 'console Math JSON Object Array Map Set String Number Promise parseInt parseFloat Infinity NaN Symbol Error Record Partial',
    c: 'printf scanf malloc calloc realloc free strlen strcpy strcmp strcat memset memcpy get_int get_string get_char get_float atoi puts putchar sizeof',
    cpp: 'printf malloc free swap sort max min reverse',
    java: 'System Math Integer ArrayList List HashMap Map HashSet Set Arrays Collections Scanner StringBuilder LinkedList Deque ArrayDeque Queue Stack PriorityQueue Object',
  };
  const sets = {};
  for (const k in KW) sets[k] = { kw: new Set(KW[k].split(' ')), bi: new Set((BUILTINS[k] || '').split(' ')) };

  const esc = (s) => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');

  // tokenise whole text, return array of HTML lines
  function highlight(text, lang) {
    const S = sets[lang] || sets.c;
    const lines = text.split('\n');
    const out = [];
    let state = null; // 'block' | 'tq"' | "tq'" | 'tpl'
    const py = lang === 'python';
    const isJs = lang === 'js' || lang === 'ts';
    const cish = !py;
    for (const line of lines) {
      let h = '', i = 0;
      const n = line.length;
      const span = (cls, s) => { h += '<span class="t-' + cls + '">' + esc(s) + '</span>'; };
      if (state) {
        let end = -1;
        if (state === 'block') end = line.indexOf('*/');
        else if (state === 'tpl') { end = line.indexOf('`'); }
        else end = line.indexOf(state.slice(2).repeat(3));
        if (end < 0) { span(state === 'block' ? 'com' : 'str', line); out.push(h); continue; }
        const len = state === 'block' ? 2 : (state === 'tpl' ? 1 : 3);
        span(state === 'block' ? 'com' : 'str', line.slice(0, end + len));
        i = end + len; state = null;
      }
      if (cish && /^\s*#/.test(line) && (lang === 'c' || lang === 'cpp')) { span('pre', line); out.push(h); continue; }
      while (i < n) {
        const c = line[i];
        if (cish && c === '/' && line[i + 1] === '/') { span('com', line.slice(i)); i = n; break; }
        if (cish && c === '/' && line[i + 1] === '*') {
          const e = line.indexOf('*/', i + 2);
          if (e < 0) { span('com', line.slice(i)); state = 'block'; i = n; break; }
          span('com', line.slice(i, e + 2)); i = e + 2; continue;
        }
        if (py && c === '#') { span('com', line.slice(i)); i = n; break; }
        if (py && c === '@' && /^\s*$/.test(line.slice(0, i))) { const m = /^@[\w.]+/.exec(line.slice(i)); if (m) { span('deco', m[0]); i += m[0].length; continue; } }
        // strings
        const pm = py ? /^([rRbBfFuU]{0,2})("""|'''|"|')/.exec(line.slice(i)) : null;
        if (pm || c === '"' || c === "'" || (isJs && c === '`')) {
          let q, start = i;
          if (pm) { q = pm[2]; i += pm[0].length; }
          else { q = c; i++; }
          if (q.length === 3) {
            const e = line.indexOf(q, i);
            if (e < 0) { span('str', line.slice(start)); state = 'tq' + q[0]; i = n; break; }
            span('str', line.slice(start, e + 3)); i = e + 3; continue;
          }
          let j = i;
          while (j < n && line[j] !== q) { if (line[j] === '\\') j++; j++; }
          if (j >= n && q === '`') { span('str', line.slice(start)); state = 'tpl'; i = n; break; }
          span('str', line.slice(start, Math.min(j + 1, n))); i = j + 1; continue;
        }
        if (/[0-9]/.test(c) || (c === '.' && /[0-9]/.test(line[i + 1] || ''))) {
          const m = /^(0[xXbBoO][0-9a-fA-F_]+|\d[\d_]*\.?\d*([eE][-+]?\d+)?|\.\d+)[uUlLfFnjJ]*/.exec(line.slice(i));
          if (m) { span('num', m[0]); i += m[0].length; continue; }
        }
        if (/[A-Za-z_$]/.test(c) || c.charCodeAt(0) > 127) {
          const m = /^[A-Za-z_$\u0080-￿][\w$\u0080-￿]*/.exec(line.slice(i));
          const w = m[0];
          const after = line.slice(i + w.length);
          if (S.kw.has(w)) span('kw', w);
          else if (S.bi.has(w)) span('bi', w);
          else if (/^\s*\(/.test(after)) span('fn', w);
          else if (/^[A-Z]/.test(w) && w.length > 1 && !/^[A-Z0-9_]+$/.test(w)) span('ty', w);
          else h += esc(w);
          i += w.length; continue;
        }
        if (/[+\-*/%=<>!&|^~?:]/.test(c)) { let j = i; while (j < n && /[+\-*/%=<>!&|^~?:]/.test(line[j])) j++; span('op', line.slice(i, j)); i = j; continue; }
        h += esc(c); i++;
      }
      out.push(h);
    }
    return out;
  }

  class Editor {
    constructor(root, opts) {
      this.root = root;
      this.opts = opts || {};
      this.lang = 'c';
      this.lh = 21;
      this.bps = new Set();
      this.marks = {};       // line -> class
      root.classList.add('ed');
      root.innerHTML =
        '<div class="ed-scroll" id="edScroll">' +
        '<div class="ed-gutter" aria-label="行号（点击设置断点）"></div>' +
        '<div class="ed-main"><div class="ed-bg"></div><pre class="ed-hl" aria-hidden="true"></pre>' +
        '<textarea class="ed-ta" id="code" spellcheck="false" autocomplete="off" autocorrect="off" autocapitalize="off" wrap="off" aria-label="代码编辑器"></textarea></div>' +
        '</div>';
      this.scroll = root.querySelector('.ed-scroll');
      this.gutter = root.querySelector('.ed-gutter');
      this.bg = root.querySelector('.ed-bg');
      this.hl = root.querySelector('.ed-hl');
      this.ta = root.querySelector('.ed-ta');
      this.ta.addEventListener('input', () => { this.refresh(); this.opts.onChange && this.opts.onChange(); });
      this.ta.addEventListener('keydown', (e) => this.onKey(e));
      this.gutter.addEventListener('click', (e) => {
        const ln = e.target.closest('[data-ln]');
        if (!ln) return;
        this.toggleBp(+ln.dataset.ln);
      });
      this.refresh();
    }
    get value() { return this.ta.value; }
    set value(v) { this.ta.value = v; this.refresh(); }
    setLang(l) { this.lang = l; this.refresh(); }
    insert(text) {
      this.ta.focus();
      if (!document.execCommand || !document.execCommand('insertText', false, text)) {
        const s = this.ta.selectionStart, e = this.ta.selectionEnd;
        this.ta.setRangeText(text, s, e, 'end');
        this.ta.dispatchEvent(new Event('input'));
      }
    }
    onKey(e) {
      const ta = this.ta;
      const v = ta.value;
      const s = ta.selectionStart, en = ta.selectionEnd;
      const ind = this.lang === 'python' ? '    ' : (this.lang === 'c' || this.lang === 'cpp' ? '    ' : (this.lang === 'java' ? '    ' : '  '));
      if (e.key === 'Tab' && !e.ctrlKey && !e.metaKey && !e.altKey) {
        e.preventDefault();
        const ls = v.lastIndexOf('\n', s - 1) + 1;
        if (s === en && !e.shiftKey) { this.insert(ind); return; }
        // indent / dedent selected lines
        const le = v.indexOf('\n', en - (en > s && v[en - 1] === '\n' ? 1 : 0));
        const blockEnd = le < 0 ? v.length : le;
        const block = v.slice(ls, blockEnd);
        const nb = e.shiftKey ? block.split('\n').map(l => l.replace(new RegExp('^( {1,' + ind.length + '}|\\t)'), '')).join('\n') : block.split('\n').map(l => ind + l).join('\n');
        ta.setSelectionRange(ls, blockEnd);
        this.insert(nb);
        ta.setSelectionRange(ls, ls + nb.length);
        return;
      }
      if (e.key === 'Enter' && !e.ctrlKey && !e.metaKey && !e.altKey && !e.shiftKey) {
        e.preventDefault();
        const ls = v.lastIndexOf('\n', s - 1) + 1;
        const cur = v.slice(ls, s);
        let lead = /^[ \t]*/.exec(cur)[0];
        const trimmed = cur.trimEnd();
        const opens = this.lang === 'python' ? /:$/.test(trimmed) : /[{(\[]$/.test(trimmed);
        const nextCh = v[en];
        if (opens) {
          if (this.lang !== 'python' && (nextCh === '}' || nextCh === ')' || nextCh === ']')) {
            this.insert('\n' + lead + ind + '\n' + lead);
            const pos = ls + cur.length + 1 + lead.length + ind.length;
            ta.setSelectionRange(pos, pos);
            return;
          }
          lead += ind;
        } else if (this.lang === 'python' && /^\s*(return|pass|break|continue|raise)\b/.test(cur)) lead = lead.slice(0, Math.max(0, lead.length - 4));
        this.insert('\n' + lead);
        return;
      }
      if (e.key === '}' && this.lang !== 'python') {
        const ls = v.lastIndexOf('\n', s - 1) + 1;
        const cur = v.slice(ls, s);
        if (/^[ \t]+$/.test(cur) && s === en) {
          e.preventDefault();
          const ded = cur.slice(0, Math.max(0, cur.length - ind.length));
          ta.setSelectionRange(ls, s);
          this.insert(ded + '}');
          return;
        }
      }
      if (e.key === 'Backspace' && s === en && s > 0) {
        const ls = v.lastIndexOf('\n', s - 1) + 1;
        const cur = v.slice(ls, s);
        if (/^ +$/.test(cur) && cur.length >= 2 && cur.length % ind.length === 0) {
          e.preventDefault();
          ta.setSelectionRange(s - ind.length, s);
          this.insert('');
        }
      }
      if (e.key === '/' && (e.ctrlKey || e.metaKey)) {
        e.preventDefault();
        const ls = v.lastIndexOf('\n', s - 1) + 1;
        const le0 = v.indexOf('\n', en - (en > s && v[en - 1] === '\n' ? 1 : 0));
        const le = le0 < 0 ? v.length : le0;
        const cmt = this.lang === 'python' ? '# ' : '// ';
        const lines = v.slice(ls, le).split('\n');
        const all = lines.every(l => !l.trim() || l.trim().startsWith(cmt.trim()));
        const nb = lines.map(l => { if (!l.trim()) return l; if (all) return l.replace(new RegExp('^(\\s*)' + cmt.trim().replace(/\//g, '\\/') + ' ?'), '$1'); const m = /^\s*/.exec(l)[0]; return m + cmt + l.slice(m.length); }).join('\n');
        ta.setSelectionRange(ls, le);
        this.insert(nb);
      }
    }
    refresh() {
      const text = this.ta.value;
      const lines = highlight(text, this.lang);
      this.hl.innerHTML = lines.map(l => '<div class="ed-l">' + (l || ' ') + '</div>').join('');
      const n = lines.length;
      // remove breakpoints past end
      for (const b of [...this.bps]) if (b > n) this.bps.delete(b);
      let g = '';
      for (let i = 1; i <= n; i++) g += '<div class="ed-ln" data-ln="' + i + '" title="点击设置/取消断点"><span class="bp"></span><span class="mk"></span>' + i + '</div>';
      this.gutter.innerHTML = g;
      const maxLen = Math.max(20, ...text.split('\n').map(l => l.replace(/\t/g, '    ').length));
      this.ta.style.height = (n * this.lh + 16) + 'px';
      this.ta.style.width = 'calc(' + (maxLen + 4) + 'ch + 24px)';
      this.hl.style.minWidth = this.ta.style.width;
      this.nLines = n;
      this.renderMarks();
    }
    toggleBp(line) {
      if (this.bps.has(line)) this.bps.delete(line); else this.bps.add(line);
      this.renderMarks();
      this.opts.onBpChange && this.opts.onBpChange();
    }
    setMarks(marks) { this.marks = marks || {}; this.renderMarks(); }
    renderMarks() {
      const rows = this.gutter.children;
      for (let i = 0; i < rows.length; i++) {
        const ln = i + 1;
        const r = rows[i];
        r.classList.toggle('has-bp', this.bps.has(ln));
        r.classList.remove('m-next', 'm-prev', 'm-err');
        const m = this.marks[ln];
        if (m) r.classList.add('m-' + m);
      }
      let bg = '';
      for (const k in this.marks) {
        const ln = +k;
        bg += '<div class="ed-mark m-' + this.marks[k] + '" style="top:' + (8 + (ln - 1) * this.lh) + 'px"></div>';
      }
      this.bg.innerHTML = bg;
    }
    scrollToLine(line) {
      const top = 8 + (line - 1) * this.lh;
      const sc = this.scroll;
      if (top < sc.scrollTop + 30 || top > sc.scrollTop + sc.clientHeight - 50) {
        sc.scrollTo({ top: Math.max(0, top - sc.clientHeight / 2), behavior: 'smooth' });
      }
    }
    lineText(line) { return (this.ta.value.split('\n')[line - 1] || '').trim(); }
  }

  DSV.Editor = Editor;
  DSV.highlight = highlight;
})(typeof window !== 'undefined' ? window : globalThis);
