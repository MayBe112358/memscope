// ===== Shared core: trace recording, errors, helpers =====
(function (G) {
  const DSV = G.DSV || (G.DSV = {});

  class CompileError extends Error {
    constructor(msg, line, col) { super(msg); this.line = line || 0; this.col = col || 0; this.isCompile = true; }
  }
  // kind: segfault | uaf | oob | uninit | div0 | stack | exception | limit | runtime
  class RunError extends Error {
    constructor(msg, kind, hint) { super(msg); this.kind = kind || 'runtime'; this.hint = hint || ''; this.isRun = true; }
  }
  class StepLimit extends Error { constructor() { super('step limit'); this.isLimit = true; } }
  class ExitSignal { constructor(code) { this.code = code; } }

  class Recorder {
    constructor(opts) {
      this.steps = [];
      this.out = '';
      this.maxSteps = (opts && opts.maxSteps) || 5000;
      this.pending = [];     // messages produced since the last recorded step
      this.lastLine = 0;
    }
    note(text, cls) { this.pending.push({ text, cls: cls || 'info' }); }
    write(s) { this.out += s; }
    // snapFn builds the visual snapshot of the program state
    record(line, ev, snapFn, extra) {
      if (this.steps.length >= this.maxSteps) throw new StepLimit();
      const snap = snapFn();
      if (snap.heap !== this._lastHeapRef) {
        this._lastHeapRef = snap.heap;
        this.budget = (this.budget || 0) + snap.heap.length + 1;
        if (this.budget > 1500000 && ev !== 'error' && ev !== 'end') { const e = new StepLimit(); e.budget = true; throw e; }
      }
      const st = { line, ev: ev || 'line', snap, out: this.out.length, msgs: this.pending };
      if (extra) Object.assign(st, extra);
      this.pending = [];
      this.steps.push(st);
      this.lastLine = line;
      return st;
    }
  }

  // Value descriptors used by the renderer
  const V = {
    prim: (text, type) => ({ k: 'prim', text: String(text), type }),
    str: (text) => ({ k: 'str', text }),
    nul: (text) => ({ k: 'null', text: text || 'NULL' }),
    ref: (id, sub, flags) => Object.assign({ k: 'ref', id, sub }, flags || {}),
    uninit: () => ({ k: 'uninit' }),
  };

  function fmtNum(n, isFloat) {
    if (typeof n === 'bigint') return n.toString();
    if (!isFloat) return String(n);
    if (!isFinite(n)) return n > 0 ? 'inf' : (n < 0 ? '-inf' : 'nan');
    if (Number.isInteger(n) && Math.abs(n) < 1e15) return n.toFixed(1);
    const s = String(+n.toPrecision(12));
    return s;
  }
  function escChar(c) {
    switch (c) {
      case '\n': return '\\n'; case '\t': return '\\t'; case '\r': return '\\r';
      case '\0': return '\\0'; case '\\': return '\\\\'; case '\'': return "\\'";
    }
    const code = c.charCodeAt(0);
    if (code < 32 || code === 127) return '\\x' + code.toString(16).padStart(2, '0');
    return c;
  }
  function quoteStr(s, q) {
    q = q || '"';
    let r = '';
    for (const c of s) {
      if (c === q) r += '\\' + q;
      else if (c === '\n') r += '\\n'; else if (c === '\t') r += '\\t';
      else if (c === '\\') r += '\\\\'; else if (c === '\0') r += '\\0';
      else r += c;
    }
    return q + r + q;
  }

  // printf-style formatting shared by C/C++/Java
  // getArg(kind) returns next arg; kind: 'int','float','str','char','ptr'
  function formatPrintf(fmt, nextArg) {
    let out = '';
    for (let i = 0; i < fmt.length; i++) {
      const c = fmt[i];
      if (c !== '%') { out += c; continue; }
      i++;
      if (fmt[i] === '%') { out += '%'; continue; }
      let flags = '';
      while ('-+ 0#'.includes(fmt[i])) flags += fmt[i++];
      let width = '';
      while (/[0-9*]/.test(fmt[i] || '')) width += fmt[i++];
      if (width === '*') width = String(nextArg('int'));
      let prec = null;
      if (fmt[i] === '.') { i++; prec = ''; while (/[0-9*]/.test(fmt[i] || '')) prec += fmt[i++]; if (prec === '*') prec = String(nextArg('int')); prec = prec === '' ? 0 : +prec; }
      while ('hlLqjzt'.includes(fmt[i]) && fmt[i]) i++;
      const conv = fmt[i];
      let s = '';
      switch (conv) {
        case 'd': case 'i': { let v = nextArg('int'); v = typeof v === 'bigint' ? v : Math.trunc(Number(v)); s = String(v); if (flags.includes('+') && v >= 0) s = '+' + s; if (prec !== null) { const neg = s[0] === '-'; let d = neg ? s.slice(1) : s; d = d.padStart(prec, '0'); s = (neg ? '-' : '') + d; } break; }
        case 'u': { let v = Number(nextArg('int')); if (v < 0) v = v >>> 0; s = String(v); break; }
        case 'f': case 'F': { const v = Number(nextArg('float')); s = isFinite(v) ? v.toFixed(prec === null ? 6 : prec) : (isNaN(v) ? 'nan' : (v > 0 ? 'inf' : '-inf')); if (flags.includes('+') && v >= 0) s = '+' + s; break; }
        case 'e': case 'E': { const v = Number(nextArg('float')); s = v.toExponential(prec === null ? 6 : prec).replace(/e([+-])(\d)$/, 'e$10$2'); if (conv === 'E') s = s.toUpperCase(); break; }
        case 'g': case 'G': { const v = Number(nextArg('float')); s = String(+v.toPrecision(prec === null ? 6 : (prec || 1))); break; }
        case 'x': case 'X': { let v = Number(nextArg('int')); if (v < 0) v = v >>> 0; s = v.toString(16); if (conv === 'X') s = s.toUpperCase(); if (flags.includes('#')) s = '0x' + s; break; }
        case 'o': { let v = Number(nextArg('int')); if (v < 0) v = v >>> 0; s = v.toString(8); break; }
        case 'c': { const v = nextArg('char'); s = typeof v === 'string' ? v : String.fromCharCode(Number(v)); break; }
        case 's': { s = String(nextArg('str')); if (prec !== null) s = s.slice(0, prec); break; }
        case 'p': { s = String(nextArg('ptr')); break; }
        case 'b': { s = String(nextArg('bool')); break; }
        case 'n': { s = '\n'; break; }
        default: s = '%' + (conv || '');
      }
      if (width) {
        const w = +width;
        if (flags.includes('-')) s = s.padEnd(w);
        else if (flags.includes('0') && /[diufxXeEgG]/.test(conv)) { const neg = s[0] === '-' || s[0] === '+'; s = neg ? s[0] + s.slice(1).padStart(w - 1, '0') : s.padStart(w, '0'); }
        else s = s.padStart(w);
      }
      out += s;
    }
    return out;
  }

  // simple stdin reader
  class Stdin {
    constructor(text) { this.text = text || ''; this.pos = 0; }
    eof() { return this.pos >= this.text.length; }
    skipWs() { while (this.pos < this.text.length && /\s/.test(this.text[this.pos])) this.pos++; }
    token() { this.skipWs(); let s = ''; while (this.pos < this.text.length && !/\s/.test(this.text[this.pos])) s += this.text[this.pos++]; return s === '' ? null : s; }
    line() {
      if (this.pos >= this.text.length) return null;
      const nl = this.text.indexOf('\n', this.pos);
      let s;
      if (nl < 0) { s = this.text.slice(this.pos); this.pos = this.text.length; }
      else { s = this.text.slice(this.pos, nl); this.pos = nl + 1; }
      return s.replace(/\r$/, '');
    }
    char() { if (this.pos >= this.text.length) return null; return this.text[this.pos++]; }
    restOfLine() { // after token reads (Java Scanner nextLine semantics)
      return this.line();
    }
  }

  // deterministic RNG for rand()/random
  function makeRng(seed) {
    let s = seed >>> 0 || 1;
    return function () { s = (Math.imul(s, 1103515245) + 12345) >>> 0; return (s >>> 1) & 0x7fffffff; };
  }

  DSV.CompileError = CompileError;
  DSV.RunError = RunError;
  DSV.StepLimit = StepLimit;
  DSV.ExitSignal = ExitSignal;
  DSV.Recorder = Recorder;
  DSV.V = V;
  DSV.fmtNum = fmtNum;
  DSV.escChar = escChar;
  DSV.quoteStr = quoteStr;
  DSV.formatPrintf = formatPrintf;
  DSV.Stdin = Stdin;
  DSV.makeRng = makeRng;
  DSV.langs = DSV.langs || {};

  // Common driver: wraps interpreter run and normalises results
  DSV.finishRun = function (rec, err, extra) {
    const res = { steps: rec.steps, out: rec.out, error: null };
    if (err) {
      if (err.isCompile) res.compileError = { msg: err.message, line: err.line };
      else if (err.isLimit && err.budget) res.error = { kind: 'limit', msg: '程序创建的对象太多，可视化器只能记录到这里（每一步都要保存整个堆的画面）。', hint: '可视化适合学习用的小规模数据。试着把数据量调小，例如只插入 10~20 个元素。' };
      else if (err.isLimit) res.error = { kind: 'limit', msg: '达到最大步数上限（' + rec.maxSteps + ' 步），程序可能陷入了死循环，或者需要在设置里调高步数上限。' };
      else if (err.isRun) res.error = { kind: err.kind, msg: err.message, hint: err.hint };
      else if (err instanceof RangeError && /call stack/i.test(err.message)) res.error = { kind: 'stack', msg: '栈溢出（Stack overflow）：递归层数太深。', hint: '检查递归是否有正确的终止条件（base case）。' };
      else res.error = { kind: 'internal', msg: '可视化器内部错误：' + (err && err.message), hint: '这可能是用到了暂不支持的语法。' };
      if (res.error && rec.steps.length) {
        // attach error to last step
        const last = rec.steps[rec.steps.length - 1];
        last.err = res.error;
      }
    }
    if (extra) Object.assign(res, extra);
    return res;
  };
})(typeof window !== 'undefined' ? window : globalThis);
