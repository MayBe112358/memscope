// ===== Python interpreter =====
(function (G) {
  const DSV = G.DSV;
  const { RunError, CompileError, Recorder, V } = DSV;

  let NID = 0, CUR_STEP = 0, VER = 0;
  const nid = () => 'p' + (++NID);
  class VMap extends Map {
    constructor() { super(); this.ver = 0; }
    set(k, v) { this.ver++; VER++; return super.set(k, v); }
    delete(k) { this.ver++; VER++; return super.delete(k); }
    clear() { this.ver++; VER++; return super.clear(); }
  }
  const isPyObj = (v) => v !== null && typeof v === 'object';
  class PyList { constructor(items) { this.id = nid(); this.items = items || []; this.born = CUR_STEP; } }
  class PyTuple { constructor(items) { this.id = nid(); this.items = items || []; this.born = CUR_STEP; } }
  class PyDict { constructor() { this.id = nid(); this.map = new Map(); this.born = CUR_STEP; } }
  class PySet { constructor() { this.id = nid(); this.map = new Map(); this.born = CUR_STEP; this.tsize = 8; } }
  class PyDeque { constructor(items) { this.id = nid(); this.items = items || []; this.born = CUR_STEP; this.maxlen = null; } }
  class PyObj { constructor(cls) { this.id = nid(); this.cls = cls; this.attrs = new VMap(); this.born = CUR_STEP; } }
  class PyClass {
    constructor(name, bases, attrs) {
      this.id = nid(); this.name = name; this.bases = bases || []; this.attrs = attrs || new Map();
      this.mro = [this];
      for (const b of this.bases) for (const c of b.mro) if (!this.mro.includes(c)) this.mro.push(c);
    }
    lookup(name) { for (const c of this.mro) if (c.attrs.has(name)) return c.attrs.get(name); return undefined; }
  }
  class PyFunc { constructor(def, env, defaults, name) { this.id = nid(); this.def = def; this.env = env; this.defaults = defaults; this.name = name || def.name; this.attrs = new Map(); } }
  class PyBuiltin { constructor(name, fn) { this.id = nid(); this.name = name; this.fn = fn; } }
  class PyBound { constructor(self, fn) { this.self = self; this.fn = fn; this.id = nid(); } }
  class PyModule { constructor(name, attrs) { this.id = nid(); this.name = name; this.attrs = attrs; } }
  class PyRange { constructor(a, b, c) { this.id = nid(); this.start = a; this.stop = b; this.step = c; } }
  class PyIter { constructor(items, label) { this.id = nid(); this.items = items; this.i = 0; this.label = label || 'iterator'; this.born = CUR_STEP; } }
  class PyProperty { constructor(fget) { this.fget = fget; this.fset = null; this.id = nid(); } }
  class PyStatic { constructor(fn) { this.fn = fn; } }
  class PyClassMethod { constructor(fn) { this.fn = fn; } }
  class PySuper { constructor(cls, self) { this.cls = cls; this.self = self; } }
  class PyExc extends Error { constructor(obj, msg) { super(msg || 'python exception'); this.obj = obj; } }
  class Ret { constructor(v, line) { this.v = v; this.line = line; } }
  const BREAK = { brk: 1 }, CONTINUE = { cont: 1 };

  class Env {
    constructor(parent, kind, info) { this.vars = new Map(); this.parent = parent; this.kind = kind; this.info = info || null; }
  }

  // ---------- static analysis of function locals ----------
  function collectLocals(def) {
    const locals = new Set(), globals = new Set(), nonlocals = new Set();
    for (const p of def.params) locals.add(p.name);
    let hasYield = false;
    const addTarget = (t) => {
      if (!t) return;
      if (t.type === 'Name') locals.add(t.id);
      else if (t.type === 'Tuple' || t.type === 'List') t.elts.forEach(addTarget);
      else if (t.type === 'Starred') addTarget(t.value);
    };
    const walkExpr = (e) => {
      if (!e || typeof e !== 'object') return;
      if (e.type === 'NamedExpr') addTarget(e.target);
      if (e.type === 'Yield' || e.type === 'YieldFrom') hasYield = true;
      if (e.type === 'Lambda') return;
      for (const k in e) {
        const v = e[k];
        if (k === 'line') continue;
        if (Array.isArray(v)) v.forEach(x => { if (x && typeof x === 'object') { if (x.type) walkExpr(x); else { walkExpr(x.value); walkExpr(x.expr); walkExpr(x.iter); (x.ifs || []).forEach(walkExpr); } } });
        else if (v && typeof v === 'object' && v.type) walkExpr(v);
      }
    };
    const walk = (stmts) => {
      for (const s of stmts) {
        switch (s.type) {
          case 'Assign': s.targets.forEach(addTarget); walkExpr(s.value); break;
          case 'AugAssign': case 'AnnAssign': addTarget(s.target); walkExpr(s.value); break;
          case 'For': addTarget(s.target); walkExpr(s.iter); walk(s.body); walk(s.orelse); break;
          case 'While': walkExpr(s.test); walk(s.body); walk(s.orelse); break;
          case 'If': walkExpr(s.test); walk(s.body); walk(s.orelse); break;
          case 'With': s.items.forEach(it => { walkExpr(it.e); addTarget(it.as); }); walk(s.body); break;
          case 'Try': walk(s.body); s.handlers.forEach(h => { if (h.name) locals.add(h.name); walk(h.body); }); walk(s.orelse); walk(s.finalbody); break;
          case 'FuncDef': case 'ClassDef': locals.add(s.name); (s.decos || []).forEach(walkExpr); break;
          case 'Import': s.names.forEach(n => locals.add(n.as || n.name.split('.')[0])); break;
          case 'ImportFrom': s.names.forEach(n => locals.add(n.as || n.name)); break;
          case 'Global': s.names.forEach(n => globals.add(n)); break;
          case 'Nonlocal': s.names.forEach(n => nonlocals.add(n)); break;
          case 'Del': s.targets.forEach(addTarget); break;
          case 'Expr': case 'Return': walkExpr(s.value); break;
          case 'Raise': walkExpr(s.exc); break;
          case 'Assert': walkExpr(s.test); break;
        }
      }
    };
    walk(def.body);
    for (const g of globals) locals.delete(g);
    for (const g of nonlocals) locals.delete(g);
    return { locals, globals, nonlocals, hasYield };
  }

  // ---------- float repr ----------
  function floatRepr(x) {
    if (isNaN(x)) return 'nan';
    if (!isFinite(x)) return x > 0 ? 'inf' : '-inf';
    if (x === 0) return Object.is(x, -0) ? '-0.0' : '0.0';
    const [m, e] = x.toExponential().split('e');
    const exp = parseInt(e, 10);
    const digits = m.replace('-', '').replace('.', '');
    const neg = x < 0 ? '-' : '';
    if (exp >= -5 && exp < 16) {
      let s;
      if (exp >= 0) {
        if (digits.length <= exp + 1) s = digits + '0'.repeat(exp + 1 - digits.length) + '.0';
        else s = digits.slice(0, exp + 1) + '.' + digits.slice(exp + 1);
      } else s = '0.' + '0'.repeat(-exp - 1) + digits;
      return neg + s;
    }
    const mant = digits.length > 1 ? digits[0] + '.' + digits.slice(1) : digits;
    return neg + mant + 'e' + (exp < 0 ? '-' : '+') + String(Math.abs(exp)).padStart(2, '0');
  }
  function strRepr(s) {
    const q = s.includes("'") && !s.includes('"') ? '"' : "'";
    let r = '';
    for (const c of s) {
      if (c === q) r += '\\' + q;
      else if (c === '\\') r += '\\\\';
      else if (c === '\n') r += '\\n';
      else if (c === '\t') r += '\\t';
      else if (c === '\r') r += '\\r';
      else if (c.charCodeAt(0) < 32) r += '\\x' + c.charCodeAt(0).toString(16).padStart(2, '0');
      else r += c;
    }
    return q + r + q;
  }

  class PyInterp {
    constructor(mod, opts) {
      this.mod = mod;
      this.opts = opts || {};
      this.rec = new Recorder(opts);
      this.stdin = new DSV.Stdin(this.opts.stdin || '');
      this.frames = [];
      this.rng = DSV.makeRng(42);
      this.depthLimit = 300;
      this.curLine = 0;
      this.builtins = new Map();
      this.setupBuiltins();
      this.globalEnv = new Env(null, 'module');
      this.globalEnv.label = 'Global';
      this.globalEnv.vars.set('__name__', '__main__');
      // CS61A 环境图模式：帧编号、父帧、保留已返回的帧
      this.envMode = !!this.opts.envMode;
      this.callSeq = 0;
      this.exitedFrames = [];
      this._noted = null;
      this.hidden = new Set(['__name__']);
      this.handling = [];
    }
    get frame() { return this.frames[this.frames.length - 1]; }
    get env() { return this.frame.env; }

    // ================= errors =================
    raise(clsName, msg, hint) {
      const cls = this.builtins.get(clsName);
      const obj = new PyObj(cls);
      obj.attrs.set('args', new PyTuple(msg != null ? [msg] : []));
      if (hint) obj.hint = hint;
      throw new PyExc(obj, msg);
    }
    typeName(v) {
      if (v === null || v === undefined) return 'NoneType';
      switch (typeof v) {
        case 'bigint': return 'int'; case 'number': return 'float'; case 'string': return 'str'; case 'boolean': return 'bool';
      }
      if (v instanceof PyList) return 'list';
      if (v instanceof PyTuple) return v.cls ? v.cls.name : 'tuple';
      if (v instanceof PyDict) return v.kind || 'dict';
      if (v instanceof PySet) return v.frozen ? 'frozenset' : 'set';
      if (v instanceof PyDeque) return 'deque';
      if (v instanceof PyObj) return v.cls.name;
      if (v instanceof PyFunc) return 'function';
      if (v instanceof PyBuiltin) return 'builtin_function_or_method';
      if (v instanceof PyBound) return 'method';
      if (v instanceof PyClass) return 'type';
      if (v instanceof PyModule) return 'module';
      if (v instanceof PyRange) return 'range';
      if (v instanceof PyIter) return v.label;
      return 'object';
    }

    // ================= stepping =================
    step(line, ev, extra) {
      this.curLine = line;
      if (this.frame) this.frame.line = line;
      CUR_STEP = this.rec.steps.length;
      this.rec.record(line, ev || 'line', () => this.snapshot(), Object.assign({ depth: this.frames.length, fn: this.frame ? this.frame.name : '' }, extra || {}));
      CUR_STEP = this.rec.steps.length;
    }

    run() {
      let err = null;
      this.frames.push({ id: 'g', name: '全局', env: this.globalEnv, isGlobal: true, line: 1 });
      try {
        try {
          const r = this.execBlock(this.mod.body);
          this.rec.note('程序结束。', 'end');
          this.rec.maxSteps += 1;
          const lastLine = this.lastLineOf(this.mod.body);
          this.step(lastLine, 'end');
        } catch (e) {
          if (e instanceof PyExc) {
            const name = e.obj.cls.name;
            const args = e.obj.attrs.get('args');
            const msg = args && args.items && args.items.length ? this.str(args.items[0]) : '';
            if (name === 'SystemExit') { this.rec.note('程序调用 exit() 退出', 'end'); this.rec.maxSteps += 1; this.step(this.curLine, 'end'); }
            else {
              const ex = new RunError(name + (msg ? ': ' + msg : ''), 'exception', e.obj.hint || this.hintFor(name, msg));
              ex.py = true;
              throw ex;
            }
          } else throw e;
        }
      } catch (e) {
        err = e;
        if (e instanceof RangeError) err = new RunError('RecursionError: maximum recursion depth exceeded（递归太深）', 'stack', '检查递归函数是否有正确的终止条件（base case）。');
        if (err && err.isRun) {
          try {
            this.rec.pending.push({ text: err.message, cls: 'error' });
            this.rec.maxSteps += 1;
            this.rec.record(this.curLine, 'error', () => this.snapshot(), { depth: this.frames.length, err: { kind: err.kind, msg: err.message, hint: err.hint } });
          } catch (e2) { }
        }
      }
      return DSV.finishRun(this.rec, err);
    }
    lastLineOf(body) {
      let l = 1;
      const walk = (ss) => { for (const s of ss) { if (s.line > l) l = s.line; for (const k of ['body', 'orelse', 'finalbody']) if (s[k]) walk(s[k]); if (s.handlers) s.handlers.forEach(h => walk(h.body)); if (s.endLine && s.endLine > l) l = s.endLine; } };
      walk(body);
      return l;
    }
    hintFor(name, msg) {
      if (name === 'AttributeError' && /NoneType/.test(msg)) return '你在 None 上访问了属性。常见原因：链表遍历走到了末尾（None）还继续访问 .next；或者函数忘记 return，返回了 None。';
      if (name === 'IndexError') return '下标的范围是 0 ~ len-1（负数下标从末尾数）。检查循环边界，或者在 pop() 前检查列表是否为空。';
      if (name === 'KeyError') return '字典里没有这个键。可以先用 key in d 判断，或者用 d.get(key, 默认值)。';
      if (name === 'ZeroDivisionError') return '除数不能为 0，在除法前先检查。';
      if (name === 'TypeError' && /NoneType/.test(msg)) return '有一个值是 None。常见原因：函数没有 return 语句，或者 list.sort() / append() 这类方法本身返回 None。';
      if (name === 'TypeError') return '检查参与运算的值的类型，例如数字和字符串不能直接相加，可以用 str() 或 int() 转换。';
      if (name === 'NameError') return '检查变量名是否拼写正确，以及是否在使用前已经赋值。';
      if (name === 'UnboundLocalError') return '函数里给这个变量赋值了，Python 就把它当作局部变量。如果要修改全局变量，需要先写 global 变量名。';
      if (name === 'RecursionError') return '检查递归函数是否有正确的终止条件（base case）。';
      if (name === 'ValueError') return '值的格式不对，例如 int("abc") 无法转换。';
      if (name === 'EOFError') return '程序需要读取输入，但“输入 (stdin)”框里的内容已经读完了。';
      return '';
    }

    // ================= statements =================
    execBlock(stmts) {
      for (const s of stmts) {
        const r = this.exec(s);
        if (r) return r;
      }
      return null;
    }
    exec(s) {
      switch (s.type) {
        case 'Expr': this.step(s.line); this.eval(s.value); return null;
        case 'Assign': {
          this.step(s.line);
          const v = this.eval(s.value);
          for (const t of s.targets) this.assign(t, v);
          return null;
        }
        case 'AugAssign': {
          this.step(s.line);
          this.augAssign(s);
          return null;
        }
        case 'AnnAssign': {
          this.step(s.line);
          if (s.value) this.assign(s.target, this.eval(s.value));
          else if (this.env.kind === 'class') { this.env.annotations = this.env.annotations || []; this.env.annotations.push(s.target.id); }
          if (s.value && this.env.kind === 'class') { this.env.annotations = this.env.annotations || []; this.env.annotations.push(s.target.id); }
          return null;
        }
        case 'If': {
          this.step(s.line);
          if (this.truthy(this.eval(s.test))) return this.execBlock(s.body);
          return this.execBlock(s.orelse);
        }
        case 'While': {
          for (;;) {
            this.step(s.line);
            if (!this.truthy(this.eval(s.test))) break;
            const r = this.execBlock(s.body);
            if (r === BREAK) return null;
            if (r === CONTINUE) continue;
            if (r) return r;
          }
          return this.execBlock(s.orelse);
        }
        case 'For': {
          this.step(s.line);
          const itv = this.eval(s.iter);
          const next = this.iterator(itv);
          let first = true;
          for (;;) {
            if (!first) this.step(s.line);
            first = false;
            const r0 = next();
            if (r0.done) break;
            this.assign(s.target, r0.value);
            const r = this.execBlock(s.body);
            if (r === BREAK) return null;
            if (r === CONTINUE) continue;
            if (r) return r;
          }
          return this.execBlock(s.orelse);
        }
        case 'FuncDef': {
          this.step(s.line);
          const fn = this.makeFunc(s);
          let v = fn;
          for (let i = s.decos.length - 1; i >= 0; i--) v = this.applyDeco(s.decos[i], v);
          this.setName(s.name, v);
          return null;
        }
        case 'ClassDef': return this.execClass(s);
        case 'Return': {
          this.step(s.line);
          const v = s.value ? this.eval(s.value) : null;
          if (this.frame.isGlobal) this.raise('SyntaxError', "'return' outside function");
          return new Ret(v, s.line);
        }
        case 'Pass': this.step(s.line); return null;
        case 'Break': this.step(s.line); return BREAK;
        case 'Continue': this.step(s.line); return CONTINUE;
        case 'Global': case 'Nonlocal': return null;
        case 'Del': {
          this.step(s.line);
          for (const t of s.targets) this.del(t);
          return null;
        }
        case 'Import': {
          this.step(s.line);
          for (const n of s.names) {
            const m = this.getModule(n.name);
            this.setName(n.as || n.name.split('.')[0], m);
            this.hidden.add(n.as || n.name.split('.')[0]);
          }
          return null;
        }
        case 'ImportFrom': {
          this.step(s.line);
          const m = this.getModule(s.module);
          for (const n of s.names) {
            if (n.name === '*') { for (const [k, v] of m.attrs) { this.setName(k, v); this.hidden.add(k); } continue; }
            if (!m.attrs.has(n.name)) this.raise('ImportError', "cannot import name '" + n.name + "' from '" + s.module + "'", '可视化器只内置了部分标准库（math、random、collections、heapq、functools、itertools、bisect、copy、dataclasses、typing 等）。');
            const v = m.attrs.get(n.name);
            this.setName(n.as || n.name, v);
            if (!(v instanceof PyClass && !v.builtin) ) this.hidden.add(n.as || n.name);
          }
          return null;
        }
        case 'Try': return this.execTry(s);
        case 'Raise': {
          this.step(s.line);
          if (!s.exc) {
            const cur = this.handling[this.handling.length - 1];
            if (!cur) this.raise('RuntimeError', 'No active exception to reraise');
            throw cur;
          }
          let e = this.eval(s.exc);
          if (e instanceof PyClass) e = this.callValue(e, [], new Map());
          if (!(e instanceof PyObj) || !this.isExcClass(e.cls)) this.raise('TypeError', 'exceptions must derive from BaseException');
          const msgArgs = e.attrs.get('args');
          this.rec.note('抛出异常 ' + e.cls.name + (msgArgs && msgArgs.items.length ? ': ' + this.str(msgArgs.items[0]) : ''), 'warn');
          throw new PyExc(e);
        }
        case 'Assert': {
          this.step(s.line);
          if (!this.truthy(this.eval(s.test))) this.raise('AssertionError', s.msg ? this.str(this.eval(s.msg)) : null, 'assert 的条件不成立，说明程序状态和预期不一样。');
          return null;
        }
        case 'With': {
          this.step(s.line);
          for (const it of s.items) { const v = this.eval(it.e); if (it.as) this.assign(it.as, v); }
          return this.execBlock(s.body);
        }
      }
      throw new RunError('暂不支持的语句：' + s.type, 'runtime');
    }
    execTry(s) {
      const fdepth = this.frames.length;
      let result = null;
      try {
        result = this.execBlock(s.body);
        if (!result && s.orelse.length) result = this.execBlock(s.orelse);
      } catch (e) {
        let exc = e;
        if (e instanceof RangeError) { try { this.raise('RecursionError', 'maximum recursion depth exceeded'); } catch (e2) { exc = e2; } }
        if (!(exc instanceof PyExc)) { if (s.finalbody.length) this.finallyRun(s, fdepth); throw e; }
        while (this.frames.length > fdepth) this.frames.pop();
        const h = s.handlers.find(h => !h.typ || this.excMatches(exc.obj, this.eval(h.typ)));
        if (!h) { if (s.finalbody.length) { const fr = this.execBlock(s.finalbody); if (fr) return fr; } throw exc; }
        this.step(h.line);
        this.rec.note('异常被 except 捕获：' + exc.obj.cls.name, 'info');
        if (h.name) this.setName(h.name, exc.obj);
        this.handling.push(exc);
        try { result = this.execBlock(h.body); }
        finally { this.handling.pop(); }
      }
      if (s.finalbody.length) { const fr = this.execBlock(s.finalbody); if (fr) return fr; }
      return result;
    }
    finallyRun(s, fdepth) { while (this.frames.length > fdepth) this.frames.pop(); this.execBlock(s.finalbody); }
    excMatches(obj, typ) {
      if (typ instanceof PyTuple) return typ.items.some(t => this.excMatches(obj, t));
      if (typ instanceof PyClass) return obj.cls.mro.includes(typ);
      return false;
    }
    isExcClass(cls) { return cls.mro.includes(this.builtins.get('BaseException')); }
    execClass(s) {
      this.step(s.line);
      const bases = [];
      for (const a of s.bases) { if (a.kind === 'pos') { const b = this.eval(a.value); if (!(b instanceof PyClass)) this.raise('TypeError', '基类必须是一个类'); if (b !== this.builtins.get('object')) bases.push(b); } }
      const env = new Env(this.env, 'class');
      const saveEnv = this.frame.env;
      this.frame.env = env;
      let r;
      try { r = this.execBlock(s.body); }
      finally { this.frame.env = saveEnv; }
      const cls = new PyClass(s.name, bases, env.vars);
      cls.annotations = env.annotations || [];
      cls.line = s.line;
      for (const v of env.vars.values()) if (v instanceof PyFunc) v.cls = cls;
      for (const v of env.vars.values()) if (v instanceof PyStatic || v instanceof PyClassMethod) v.fn.cls = cls;
      for (const v of env.vars.values()) if (v instanceof PyProperty) { v.fget.cls = cls; if (v.fset) v.fset.cls = cls; }
      let val = cls;
      for (let i = s.decos.length - 1; i >= 0; i--) val = this.applyDeco(s.decos[i], val);
      this.setName(s.name, val);
      return null;
    }
    applyDeco(decoExpr, v) {
      const d = this.eval(decoExpr);
      return this.callValue(d, [v], new Map());
    }
    makeFunc(def) {
      if (!def.info) def.info = collectLocals(def);
      const defaults = def.params.map(p => p.def ? this.eval(p.def) : undefined);
      const fn = new PyFunc(def, this.env, defaults);
      fn.qualname = this.env.kind === 'class' ? null : def.name;
      let pe = this.env;
      while (pe && !pe.label) pe = pe.parent;
      fn.parentLabel = pe ? pe.label : 'Global';
      if (pe && pe.kind === 'function') pe.captured = true;
      if (this.envMode && this.env.kind !== 'class') {
        if (def.isLambda) this.rec.note('创建 λ 函数（第 ' + def.line + ' 行），父帧 = ' + fn.parentLabel + '（创建它时所在的帧）', 'info');
        else this.rec.note('定义函数 ' + def.name + '：创建函数对象，父帧 = ' + fn.parentLabel + '（定义它时所在的帧）', 'info');
      }
      return fn;
    }
    envNote(key, text) {
      if (this._notedStep !== this.rec.steps.length) { this._notedStep = this.rec.steps.length; this._noted = new Set(); }
      if (this._noted.has(key)) return;
      this._noted.add(key);
      this.rec.note(text, 'info');
    }

    // ================= names =================
    lookup(name, line) {
      let env = this.env;
      // first env: function with static locals
      for (let e = env; e; e = e.parent) {
        if (e.kind === 'function') {
          const info = e.info;
          if (info.globals.has(name)) return this.lookupGlobal(name);
          if (info.locals.has(name)) {
            if (e.vars.has(name)) {
              if (e !== env && this.envMode && e.label && env.label) this.envNote(name, '当前帧 ' + env.label + ' 里没有 ' + name + '，沿父帧往上找，在 ' + e.label + ' 中找到 ' + name + ' = ' + this.shortRepr(e.vars.get(name)));
              return e.vars.get(name);
            }
            if (e === env) this.raise('UnboundLocalError', "cannot access local variable '" + name + "' where it is not associated with a value");
            this.raise('NameError', "free variable '" + name + "' referenced before assignment");
          }
          continue;
        }
        if (e.kind === 'class') { if (e === env && e.vars.has(name)) return e.vars.get(name); continue; }
        if (e.kind === 'comp') { if (e.vars.has(name)) return e.vars.get(name); continue; }
        if (e.kind === 'module') break;
      }
      return this.lookupGlobal(name);
    }
    lookupGlobal(name) {
      if (this.globalEnv.vars.has(name)) return this.globalEnv.vars.get(name);
      if (this.builtins.has(name)) return this.builtins.get(name);
      let hint = '';
      if (name === 'true' || name === 'false') hint = 'Python 的布尔值首字母大写：True / False。';
      else if (name === 'null' || name === 'nil' || name === 'NULL') hint = 'Python 里空值写作 None。';
      else if (name === 'this') hint = 'Python 的方法用 self 表示当前对象。';
      this.raise('NameError', "name '" + name + "' is not defined", hint || undefined);
    }
    setName(name, v) {
      const env = this.env;
      if (isPyObj(v) || isPyObj(env.vars.get(name))) VER++;
      if (env.kind === 'function') {
        if (env.info.globals.has(name)) { this.globalEnv.vars.set(name, v); return; }
        if (env.info.nonlocals.has(name)) {
          for (let e = env.parent; e; e = e.parent) if (e.kind === 'function' && (e.vars.has(name) || e.info.locals.has(name))) { e.vars.set(name, v); VER++; if (this.envMode && e.label) this.envNote('nl:' + name, 'nonlocal：修改的是父帧 ' + e.label + ' 里的 ' + name + '（不是在当前帧新建变量）'); return; }
          this.raise('SyntaxError', "no binding for nonlocal '" + name + "' found");
        }
      }
      env.vars.set(name, v);
    }
    delName(name) {
      const env = this.env;
      if (env.kind === 'function' && env.info.globals.has(name)) { this.globalEnv.vars.delete(name); return; }
      if (!env.vars.has(name)) this.raise('NameError', "name '" + name + "' is not defined");
      env.vars.delete(name);
    }

    // ================= assignment =================
    assign(t, v) {
      switch (t.type) {
        case 'Name': this.setName(t.id, v); return;
        case 'Attribute': this.setattr(this.eval(t.obj), t.name, v); return;
        case 'Subscript': this.setitem(this.eval(t.obj), this.evalIndex(t.index), v); return;
        case 'Tuple': case 'List': {
          const items = this.toArray(v);
          const starIdx = t.elts.findIndex(x => x.type === 'Starred');
          if (starIdx < 0) {
            if (items.length !== t.elts.length) this.raise('ValueError', items.length > t.elts.length ? 'too many values to unpack (expected ' + t.elts.length + ')' : 'not enough values to unpack (expected ' + t.elts.length + ', got ' + items.length + ')');
            t.elts.forEach((e, i) => this.assign(e, items[i]));
          } else {
            const after = t.elts.length - starIdx - 1;
            if (items.length < t.elts.length - 1) this.raise('ValueError', 'not enough values to unpack');
            t.elts.slice(0, starIdx).forEach((e, i) => this.assign(e, items[i]));
            this.assign(t.elts[starIdx].value, new PyList(items.slice(starIdx, items.length - after)));
            t.elts.slice(starIdx + 1).forEach((e, i) => this.assign(e, items[items.length - after + i]));
          }
          return;
        }
        case 'Starred': this.assign(t.value, v); return;
      }
      this.raise('SyntaxError', 'cannot assign to expression');
    }
    augAssign(s) {
      const t = s.target;
      const rhs = this.eval(s.value);
      if (t.type === 'Name') { const cur = this.lookup(t.id); this.setName(t.id, this.inplace(s.op, cur, rhs)); return; }
      if (t.type === 'Attribute') { const o = this.eval(t.obj); const cur = this.getattr(o, t.name); this.setattr(o, t.name, this.inplace(s.op, cur, rhs)); return; }
      if (t.type === 'Subscript') { const o = this.eval(t.obj); const k = this.evalIndex(t.index); const cur = this.getitem(o, k); this.setitem(o, k, this.inplace(s.op, cur, rhs)); return; }
      this.raise('SyntaxError', 'illegal expression for augmented assignment');
    }
    inplace(op, a, b) {
      VER++;
      if (a instanceof PyList && op === '+') { a.items.push(...this.toArray(b)); return a; }
      if (a instanceof PyList && op === '*') { const n = Number(this.toInt(b)); const it = a.items.slice(); a.items.length = 0; for (let i = 0; i < n; i++) a.items.push(...it); return a; }
      if (a instanceof PySet && (op === '|' || op === '&' || op === '-' || op === '^')) { const r = this.binop(op, a, b); a.map = r.map; return a; }
      if (a instanceof PyDict && op === '|') { for (const [k, e] of b.map) a.map.set(k, e); return a; }
      if (a instanceof PyObj) { const m = a.cls.lookup('__i' + DUNDER[op] + '__'); if (m) return this.callValue(this.bind(a, m), [b], new Map()); }
      return this.binop(op, a, b);
    }
    del(t) {
      if (t.type === 'Name') return this.delName(t.id);
      if (t.type === 'Subscript') return this.delitem(this.eval(t.obj), this.evalIndex(t.index));
      if (t.type === 'Attribute') { const o = this.eval(t.obj); if (o instanceof PyObj && o.attrs.has(t.name)) { o.attrs.delete(t.name); return; } this.raise('AttributeError', t.name); }
      if (t.type === 'Tuple') return t.elts.forEach(x => this.del(x));
    }

    // ================= expressions =================
    eval(e) {
      switch (e.type) {
        case 'Const': return e.v;
        case 'Name': return this.lookup(e.id, e.line);
        case 'FString': {
          let s = '';
          for (const p of e.parts) {
            if (typeof p === 'string') { s += p; continue; }
            let v = this.eval(p.expr);
            if (p.conv === 'r') v = this.repr(v);
            else if (p.conv === 's') v = this.str(v);
            let spec = p.spec;
            if (p.specParts) spec = p.specParts.map(x => typeof x === 'string' ? x : this.str(this.eval(x.expr))).join('');
            s += this.format(v, spec || '');
          }
          return s;
        }
        case 'BinOp': return this.binop(e.op, this.eval(e.left), this.eval(e.right));
        case 'UnaryOp': {
          const v = this.eval(e.operand);
          if (e.op === 'not') return !this.truthy(v);
          if (e.op === '-') {
            if (typeof v === 'bigint') return -v;
            if (typeof v === 'boolean') return -BigInt(v ? 1 : 0);
            if (typeof v === 'number') return -v;
            if (v instanceof PyObj) { const m = v.cls.lookup('__neg__'); if (m) return this.callValue(this.bind(v, m), [], new Map()); }
            this.raise('TypeError', "bad operand type for unary -: '" + this.typeName(v) + "'");
          }
          if (e.op === '+') return typeof v === 'boolean' ? BigInt(v ? 1 : 0) : v;
          if (e.op === '~') return ~this.toInt(v);
          break;
        }
        case 'BoolOp': {
          let v;
          for (const x of e.values) {
            v = this.eval(x);
            if (e.op === 'and' && !this.truthy(v)) return v;
            if (e.op === 'or' && this.truthy(v)) return v;
          }
          return v;
        }
        case 'Compare': {
          let left = this.eval(e.left);
          for (let i = 0; i < e.ops.length; i++) {
            const right = this.eval(e.comps[i]);
            if (!this.compare(e.ops[i], left, right)) return false;
            left = right;
          }
          return true;
        }
        case 'IfExp': return this.truthy(this.eval(e.test)) ? this.eval(e.body) : this.eval(e.orelse);
        case 'Lambda': {
          const def = e.def || (e.def = { name: '<lambda>', params: e.params, body: [{ type: 'Return', value: e.body, line: e.line }], line: e.line, endLine: e.line, isLambda: true });
          return this.makeFunc(def);
        }
        case 'Call': return this.evalCall(e);
        case 'Attribute': return this.getattr(this.eval(e.obj), e.name, e);
        case 'Subscript': return this.getitem(this.eval(e.obj), this.evalIndex(e.index));
        case 'List': return new PyList(this.evalElts(e.elts));
        case 'Tuple': return new PyTuple(this.evalElts(e.elts));
        case 'Set': { const s = new PySet(); for (const v of this.evalElts(e.elts)) this.setAdd(s, v); return s; }
        case 'Dict': {
          const d = new PyDict();
          e.keys.forEach((k, i) => {
            if (k === null) { const src = this.eval(e.values[i]); if (src instanceof PyDict) for (const [kk, en] of src.map) d.map.set(kk, [en[0], en[1]]); return; }
            this.dictSet(d, this.eval(k), this.eval(e.values[i]));
          });
          return d;
        }
        case 'ListComp': { const out = []; this.comprehension(e.gens, () => out.push(this.eval(e.elt))); return new PyList(out); }
        case 'GeneratorExp': { const out = []; this.comprehension(e.gens, () => out.push(this.eval(e.elt))); return new PyIter(out, 'generator'); }
        case 'SetComp': { const s = new PySet(); this.comprehension(e.gens, () => this.setAdd(s, this.eval(e.elt))); return s; }
        case 'DictComp': { const d = new PyDict(); this.comprehension(e.gens, () => this.dictSet(d, this.eval(e.key), this.eval(e.value))); return d; }
        case 'NamedExpr': { const v = this.eval(e.value); this.assign(e.target, v); return v; }
        case 'Starred': this.raise('SyntaxError', "can't use starred expression here");
        case 'Slice': return { slice: true, lo: e.lo ? this.eval(e.lo) : null, hi: e.hi ? this.eval(e.hi) : null, step: e.step ? this.eval(e.step) : null };
        case 'Yield': {
          if (!this.frame.yields) this.raise('SyntaxError', "'yield' outside function");
          this.frame.yields.push(e.value ? this.eval(e.value) : null);
          return null;
        }
        case 'YieldFrom': { if (!this.frame.yields) this.raise('SyntaxError', "'yield' outside function"); this.frame.yields.push(...this.toArray(this.eval(e.value))); return null; }
      }
      throw new RunError('暂不支持的表达式：' + e.type, 'runtime');
    }
    evalIndex(idx) {
      if (idx.type === 'Slice') return this.eval(idx);
      if (idx.type === 'Tuple' && idx.elts.some(x => x.type === 'Slice')) return new PyTuple(idx.elts.map(x => this.eval(x)));
      return this.eval(idx);
    }
    evalElts(elts) {
      const out = [];
      for (const x of elts) { if (x.type === 'Starred') out.push(...this.toArray(this.eval(x.value))); else out.push(this.eval(x)); }
      return out;
    }
    comprehension(gens, body) {
      const env = new Env(this.env, 'comp');
      const save = this.frame.env;
      this.frame.env = env;
      try {
        const run = (gi) => {
          if (gi >= gens.length) { body(); return; }
          const g = gens[gi];
          // first iterable is evaluated in enclosing scope
          let itv;
          if (gi === 0) { this.frame.env = save; itv = this.eval(g.iter); this.frame.env = env; } else itv = this.eval(g.iter);
          const next = this.iterator(itv);
          for (;;) {
            const r = next();
            if (r.done) break;
            this.assignComp(env, g.target, r.value);
            if (g.ifs.every(c => this.truthy(this.eval(c)))) run(gi + 1);
          }
        };
        run(0);
      } finally { this.frame.env = save; }
    }
    assignComp(env, t, v) {
      if (t.type === 'Name') { env.vars.set(t.id, v); return; }
      if (t.type === 'Tuple' || t.type === 'List') { const items = this.toArray(v); if (items.length !== t.elts.length) this.raise('ValueError', 'cannot unpack'); t.elts.forEach((x, i) => this.assignComp(env, x, items[i])); return; }
      this.assign(t, v);
    }

    evalCall(e) {
      const args = [], kwargs = new Map();
      let fv;
      fv = this.eval(e.func);
      for (const a of e.args) {
        if (a.kind === 'pos') args.push(this.eval(a.value));
        else if (a.kind === 'star') args.push(...this.toArray(this.eval(a.value)));
        else if (a.kind === 'kw') kwargs.set(a.name, this.eval(a.value));
        else if (a.kind === 'kwstar') { const d = this.eval(a.value); for (const [, en] of d.map) kwargs.set(en[0], en[1]); }
      }
      return this.callValue(fv, args, kwargs, e);
    }
    callValue(f, args, kwargs, e) {
      kwargs = kwargs || new Map();
      if (f instanceof PyFunc) return this.callFunc(f, args, kwargs);
      if (f instanceof PyBound) {
        if (f.fn instanceof PyFunc) return this.callFunc(f.fn, [f.self, ...args], kwargs);
        return this.callValue(f.fn, [f.self, ...args], kwargs, e);
      }
      if (f instanceof PyBuiltin) { VER++; const sv = this.builtinDepth || 0; this.builtinDepth = sv + 1; let r; try { r = f.fn(args, kwargs, e); } finally { this.builtinDepth = sv; } VER++; return r; }
      if (f instanceof PyClass) return this.instantiate(f, args, kwargs, e);
      if (f instanceof PyObj) { const m = f.cls.lookup('__call__'); if (m) return this.callValue(this.bind(f, m), args, kwargs, e); }
      let hint;
      if (f === null) hint = '你调用的值是 None。可能是变量没有被正确赋值，或者函数没有 return。';
      else if (typeof f === 'bigint' || typeof f === 'number') hint = '数字不能被调用。是不是在数字和括号之间漏写了 * 乘号？';
      this.raise('TypeError', "'" + this.typeName(f) + "' object is not callable", hint);
    }
    instantiate(cls, args, kwargs, e) {
      if (cls.native) return cls.native(args, kwargs, e);
      if (cls.isAbstract) this.raise('TypeError', "Can't instantiate abstract class " + cls.name);
      const obj = new PyObj(cls);
      if (this.isExcClass(cls)) obj.attrs.set('args', new PyTuple(args));
      const init = cls.lookup('__init__');
      if (init) {
        const r = this.callValue(this.bind(obj, init), args, kwargs, e);
        if (r !== null && r !== undefined) this.raise('TypeError', '__init__() should return None');
      } else if ((args.length || kwargs.size) && !this.isExcClass(cls)) this.raise('TypeError', cls.name + '() takes no arguments', '如果要在创建对象时传参数，需要在类里定义 __init__(self, ...) 方法。');
      return obj;
    }
    bind(self, f) {
      if (f instanceof PyStatic) return f.fn;
      if (f instanceof PyClassMethod) return new PyBound(self instanceof PyClass ? self : self.cls, f.fn);
      if (f instanceof PyFunc || f instanceof PyBuiltin) return new PyBound(self, f);
      return f;
    }
    callFunc(fn, args, kwargs) {
      const def = fn.def;
      if (this.frames.length > this.depthLimit) this.raise('RecursionError', 'maximum recursion depth exceeded', '递归层数太深（可视化器上限 ' + this.depthLimit + ' 层）。检查递归函数是否有正确的终止条件（base case），以及每次递归是否在向终止条件靠近。');
      const env = new Env(fn.env, 'function', def.info);
      // bind params
      const params = def.params;
      let ai = 0;
      const used = new Set();
      for (let i = 0; i < params.length; i++) {
        const p = params[i];
        if (p.kind === 'normal') {
          if (ai < args.length) { env.vars.set(p.name, args[ai++]); used.add(p.name); }
          else if (kwargs.has(p.name)) { env.vars.set(p.name, kwargs.get(p.name)); used.add(p.name); }
          else if (fn.defaults[i] !== undefined) env.vars.set(p.name, fn.defaults[i]);
          else {
            const missing = params.filter((q, j) => q.kind === 'normal' && j >= i && fn.defaults[j] === undefined && !kwargs.has(q.name)).map(q => "'" + q.name + "'");
            const isMethod = params[0] && params[0].name === 'self';
            this.raise('TypeError', this.fnName(fn) + "() missing " + missing.length + " required positional argument" + (missing.length > 1 ? 's' : '') + ': ' + missing.join(' and '), isMethod && i === 0 ? '调用方法时 self 会自动传入；如果直接用类名调用方法，需要手动传入对象。' : '调用函数时传入的参数个数比定义的少。');
          }
        } else if (p.kind === 'varargs') { env.vars.set(p.name, new PyTuple(args.slice(ai))); ai = args.length; }
        else if (p.kind === 'kwonly') {
          if (kwargs.has(p.name)) { env.vars.set(p.name, kwargs.get(p.name)); used.add(p.name); }
          else if (fn.defaults[i] !== undefined) env.vars.set(p.name, fn.defaults[i]);
          else this.raise('TypeError', this.fnName(fn) + "() missing required keyword-only argument: '" + p.name + "'");
        } else if (p.kind === 'kwargs') {
          const d = new PyDict();
          for (const [k, v] of kwargs) if (!used.has(k)) this.dictSet(d, k, v);
          env.vars.set(p.name, d);
          for (const k of kwargs.keys()) used.add(k);
        }
      }
      if (ai < args.length) {
        const n = params.filter(p => p.kind === 'normal').length;
        const isMethod = params[0] && params[0].name === 'self';
        this.raise('TypeError', this.fnName(fn) + '() takes ' + (isMethod ? n : n) + ' positional argument' + (n !== 1 ? 's' : '') + ' but ' + args.length + (args.length === 1 ? ' was' : ' were') + ' given', isMethod ? '定义方法时第一个参数必须是 self；调用时 self 会自动传入，不需要再写。' : '调用时传入的参数比函数定义的多。');
      }
      for (const k of kwargs.keys()) if (!used.has(k) && !params.some(p => p.kind === 'kwargs')) this.raise('TypeError', this.fnName(fn) + "() got an unexpected keyword argument '" + k + "'");
      const name = def.isLambda ? 'λ' : this.fnName(fn);
      const fromBuiltin = (this.builtinDepth || 0) > 0;
      const saveBD = this.builtinDepth || 0;
      this.builtinDepth = 0;
      const seq = ++this.callSeq;
      env.label = 'f' + seq;
      const frame = { id: 'f' + (++NID), name, env, fn, line: def.line, callLine: this.curLine, seq, label: 'f' + seq, parent: fn.parentLabel || 'Global' };
      if (def.info.hasYield) frame.yields = [];
      const argsShown = params.filter(p => env.vars.has(p.name) && p.name !== 'self').map(p => this.shortRepr(env.vars.get(p.name)));
      let msg = '调用 ' + name + '(' + argsShown.join(', ') + ')';
      const depth = this.frames.filter(f => f.fn === fn).length;
      if (depth) msg += '（递归，第 ' + (depth + 1) + ' 层）';
      if (this.envMode) msg += '：新建帧 ' + frame.label + '，父帧 = ' + frame.parent + '（' + (def.isLambda ? '这个 λ 函数' : name) + ' 是在 ' + frame.parent + ' 中' + (def.isLambda ? '创建' : '定义') + '的）';
      this.rec.note(msg, 'call');
      this.frames.push(frame);
      VER++;
      this.step(def.line, 'call');
      const r = this.execBlock(def.body);
      let rv = r instanceof Ret ? r.v : null;
      if (r === BREAK || r === CONTINUE) this.raise('SyntaxError', "'break' outside loop");
      if (frame.yields) { rv = new PyIter(frame.yields, 'generator'); this.rec.note('（生成器函数被一次性执行完，产生了 ' + frame.yields.length + ' 个值）', 'info'); }
      frame.retVal = rv;
      frame.returning = true;
      this.rec.note(name + ' 返回 ' + this.shortRepr(rv), 'ret');
      this.step(r instanceof Ret ? r.line : (def.endLine || def.line), 'return');
      this.frames.pop();
      frame.exited = true;
      this.builtinDepth = saveBD;
      if (this.envMode && (env.captured || (!fromBuiltin && (this.keptPlain = (this.keptPlain || 0) + 1) <= 25))) this.exitedFrames.push(frame);
      VER++;
      return rv;
    }
    fnName(fn) { return fn.cls ? fn.cls.name + '.' + fn.name : fn.name; }
    shortRepr(v) {
      try {
        if (v instanceof PyObj && !v.cls.lookup('__repr__')) return v.cls.name + ' 对象';
        if (v instanceof PyFunc) return v.def.isLambda ? 'λ 函数（第 ' + v.def.line + ' 行）' : 'function ' + v.name;
        const s = this.reprNoCall(v);
        return s.length > 40 ? s.slice(0, 37) + '…' : s;
      } catch (e) { return '…'; }
    }
    reprNoCall(v, depth) {
      depth = depth || 0;
      if (depth > 3) return '…';
      if (v instanceof PyObj) return v.cls.name + ' 对象';
      if (v instanceof PyList) return '[' + v.items.slice(0, 8).map(x => this.reprNoCall(x, depth + 1)).join(', ') + (v.items.length > 8 ? ', …' : '') + ']';
      if (v instanceof PyTuple) return '(' + v.items.map(x => this.reprNoCall(x, depth + 1)).join(', ') + (v.items.length === 1 ? ',' : '') + ')';
      if (v instanceof PyDict) return '{' + [...v.map.values()].slice(0, 6).map(en => this.reprNoCall(en[0], depth + 1) + ': ' + this.reprNoCall(en[1], depth + 1)).join(', ') + (v.map.size > 6 ? ', …' : '') + '}';
      return this.repr(v);
    }

    // ================= attributes =================
    getattr(o, name, e) {
      if (o instanceof PyObj) {
        if (o.attrs.has(name)) return o.attrs.get(name);
        const v = o.cls.lookup(name);
        if (v !== undefined) {
          if (v instanceof PyProperty) return this.callValue(v.fget, [o], new Map());
          if (v instanceof PyFunc || v instanceof PyBuiltin || v instanceof PyClassMethod || v instanceof PyStatic) return this.bind(o, v);
          return v;
        }
        if (this.isExcClass(o.cls) && name === 'args') return new PyTuple([]);
        const ga = o.cls.lookup('__getattr__');
        if (ga) return this.callValue(this.bind(o, ga), [name], new Map());
        const has = [...o.attrs.keys()];
        this.raise('AttributeError', "'" + o.cls.name + "' object has no attribute '" + name + "'", has.length ? '这个对象现有的属性：' + has.join(', ') + '。检查拼写，或者是否在 __init__ 里用 self.' + name + ' = ... 赋过值。' : '检查拼写，或者是否在 __init__ 里用 self.' + name + ' = ... 赋过值。');
      }
      if (o instanceof PyClass) {
        const v = o.lookup(name);
        if (v !== undefined) {
          if (v instanceof PyClassMethod) return new PyBound(o, v.fn);
          if (v instanceof PyStatic) return v.fn;
          return v;
        }
        if (name === '__name__') return o.name;
        if (o.native && o.methods && o.methods[name]) return new PyBuiltin(o.name + '.' + name, (args, kw) => o.methods[name](args[0], args.slice(1), kw));
        this.raise('AttributeError', "type object '" + o.name + "' has no attribute '" + name + "'");
      }
      if (o instanceof PyModule) {
        if (o.attrs.has(name)) return o.attrs.get(name);
        this.raise('AttributeError', "module '" + o.name + "' has no attribute '" + name + "'", '可视化器只实现了这个模块里常用的部分。');
      }
      if (o instanceof PySuper) {
        const mro = o.self instanceof PyClass ? o.self.mro : o.self.cls.mro;
        const i = mro.indexOf(o.cls);
        for (let k = i + 1; k < mro.length; k++) {
          if (mro[k].attrs.has(name)) { const v = mro[k].attrs.get(name); return this.bind(o.self, v); }
        }
        if (name === '__init__') return new PyBuiltin('object.__init__', () => null);
        this.raise('AttributeError', "'super' object has no attribute '" + name + "'");
      }
      if (o instanceof PyFunc && o.attrs.has(name)) return o.attrs.get(name);
      if (o instanceof PyFunc && name === '__name__') return o.name;
      // builtin type methods
      const m = this.builtinMethod(o, name);
      if (m) return m;
      if (o === null) this.raise('AttributeError', "'NoneType' object has no attribute '" + name + "'");
      this.raise('AttributeError', "'" + this.typeName(o) + "' object has no attribute '" + name + "'", this.typeName(o) === 'list' && name === 'push' ? '列表添加元素用 append()。' : (this.typeName(o) === 'str' && ['append', 'reverse', 'sort'].includes(name) ? '字符串是不可变的，没有这个方法。' : undefined));
    }
    setattr(o, name, v) {
      if (o instanceof PyObj) {
        const p = o.cls.lookup(name);
        if (p instanceof PyProperty) { if (!p.fset) this.raise('AttributeError', "can't set attribute '" + name + "'"); this.callValue(p.fset, [o, v], new Map()); return; }
        if (o.cls.slotsFrozen) this.raise('AttributeError', 'cannot assign to field ' + name);
        o.attrs.set(name, v); return;
      }
      if (o instanceof PyClass) { o.attrs.set(name, v); return; }
      if (o instanceof PyFunc) { o.attrs.set(name, v); return; }
      if (o === null) this.raise('AttributeError', "'NoneType' object has no attribute '" + name + "'");
      this.raise('AttributeError', "'" + this.typeName(o) + "' object has no attribute '" + name + "'");
    }

    // ================= truth / numbers =================
    truthy(v) {
      if (v === null || v === undefined) return false;
      switch (typeof v) {
        case 'boolean': return v; case 'bigint': return v !== 0n; case 'number': return v !== 0; case 'string': return v.length > 0;
      }
      if (v instanceof PyList || v instanceof PyTuple || v instanceof PyDeque) return v.items.length > 0;
      if (v instanceof PyDict || v instanceof PySet) return v.map.size > 0;
      if (v instanceof PyRange) return this.rangeLen(v) > 0;
      if (v instanceof PyObj) {
        const b = v.cls.lookup('__bool__');
        if (b) return this.truthy(this.callValue(this.bind(v, b), [], new Map()));
        const l = v.cls.lookup('__len__');
        if (l) return this.toInt(this.callValue(this.bind(v, l), [], new Map())) !== 0n;
      }
      return true;
    }
    toInt(v) {
      if (typeof v === 'bigint') return v;
      if (typeof v === 'boolean') return v ? 1n : 0n;
      if (v instanceof PyObj) { const m = v.cls.lookup('__index__'); if (m) return this.toInt(this.callValue(this.bind(v, m), [], new Map())); }
      this.raise('TypeError', "'" + this.typeName(v) + "' object cannot be interpreted as an integer", typeof v === 'number' ? '这里需要整数，但得到的是浮点数。可以用 int(x)，或者用整除 // 代替 /。' : undefined);
    }
    toNum(v) {
      if (typeof v === 'number') return v;
      if (typeof v === 'bigint') return Number(v);
      if (typeof v === 'boolean') return v ? 1 : 0;
      this.raise('TypeError', 'must be real number, not ' + this.typeName(v));
    }
    isNum(v) { return typeof v === 'bigint' || typeof v === 'number' || typeof v === 'boolean'; }

    binop(op, a, b) {
      if (typeof a === 'boolean') a = a ? 1n : 0n;
      if (typeof b === 'boolean') b = b ? 1n : 0n;
      const ta = typeof a, tb = typeof b;
      if (ta === 'bigint' && tb === 'bigint') {
        switch (op) {
          case '+': return a + b; case '-': return a - b; case '*': return a * b;
          case '/': if (b === 0n) this.raise('ZeroDivisionError', 'division by zero'); return Number(a) / Number(b);
          case '//': if (b === 0n) this.raise('ZeroDivisionError', 'integer division or modulo by zero'); { let q = a / b; if ((a % b !== 0n) && ((a < 0n) !== (b < 0n))) q -= 1n; return q; }
          case '%': if (b === 0n) this.raise('ZeroDivisionError', 'integer modulo by zero'); { let r = a % b; if (r !== 0n && ((r < 0n) !== (b < 0n))) r += b; return r; }
          case '**': if (b < 0n) return Math.pow(Number(a), Number(b)); if (b > 100000n) this.raise('OverflowError', 'exponent too large'); return a ** b;
          case '<<': return a << b; case '>>': return a >> b;
          case '&': return a & b; case '|': return a | b; case '^': return a ^ b;
        }
      }
      if ((ta === 'bigint' || ta === 'number') && (tb === 'bigint' || tb === 'number')) {
        const x = Number(a), y = Number(b);
        switch (op) {
          case '+': return x + y; case '-': return x - y; case '*': return x * y;
          case '/': if (y === 0) this.raise('ZeroDivisionError', 'float division by zero'); return x / y;
          case '//': if (y === 0) this.raise('ZeroDivisionError', 'float floor division by zero'); return Math.floor(x / y);
          case '%': if (y === 0) this.raise('ZeroDivisionError', 'float modulo'); { const r = x % y; return r !== 0 && (r < 0) !== (y < 0) ? r + y : r; }
          case '**': return Math.pow(x, y);
        }
      }
      if (ta === 'string' && tb === 'string' && op === '+') return a + b;
      if (ta === 'string' && op === '*' && tb === 'bigint') return b > 0n ? a.repeat(Number(b)) : '';
      if (tb === 'string' && op === '*' && ta === 'bigint') return a > 0n ? b.repeat(Number(a)) : '';
      if (ta === 'string' && op === '%') return this.percentFormat(a, b);
      if (a instanceof PyList && b instanceof PyList && op === '+') return new PyList(a.items.concat(b.items));
      if (a instanceof PyTuple && b instanceof PyTuple && op === '+') return new PyTuple(a.items.concat(b.items));
      if ((a instanceof PyList || a instanceof PyTuple) && tb === 'bigint' && op === '*') { const out = []; for (let i = 0n; i < b; i++) out.push(...a.items); return a instanceof PyList ? new PyList(out) : new PyTuple(out); }
      if ((b instanceof PyList || b instanceof PyTuple) && ta === 'bigint' && op === '*') return this.binop('*', b, a);
      if (a instanceof PySet && b instanceof PySet) {
        const r = new PySet();
        if (op === '|') { for (const [k, v] of a.map) r.map.set(k, v); for (const [k, v] of b.map) r.map.set(k, v); return r; }
        if (op === '&') { for (const [k, v] of a.map) if (b.map.has(k)) r.map.set(k, v); return r; }
        if (op === '-') { for (const [k, v] of a.map) if (!b.map.has(k)) r.map.set(k, v); return r; }
        if (op === '^') { for (const [k, v] of a.map) if (!b.map.has(k)) r.map.set(k, v); for (const [k, v] of b.map) if (!a.map.has(k)) r.map.set(k, v); return r; }
      }
      if (a instanceof PyDict && b instanceof PyDict && op === '|') { const r = new PyDict(); for (const [k, e] of a.map) r.map.set(k, e.slice()); for (const [k, e] of b.map) r.map.set(k, e.slice()); return r; }
      if (a instanceof PyDict && a.kind === 'Counter' && b instanceof PyDict && (op === '+' || op === '-')) { const r = this.newCounter(); for (const [k, e] of a.map) r.map.set(k, e.slice()); for (const [k, e] of b.map) { const cur = r.map.get(k); const nv = (cur ? cur[1] : 0n) + (op === '+' ? e[1] : -e[1]); if (nv > 0n) r.map.set(k, [e[0], nv]); else r.map.delete(k); } return r; }
      // dunder
      const dn = DUNDER[op];
      if (a instanceof PyObj && dn) { const m = a.cls.lookup('__' + dn + '__'); if (m) return this.callValue(this.bind(a, m), [b], new Map()); }
      if (b instanceof PyObj && dn) { const m = b.cls.lookup('__r' + dn + '__'); if (m) return this.callValue(this.bind(b, m), [a], new Map()); }
      let hint;
      if ((ta === 'string' && (tb === 'bigint' || tb === 'number')) || (tb === 'string' && (ta === 'bigint' || ta === 'number'))) hint = '字符串和数字不能直接用 ' + op + ' 运算。拼接字符串时可以用 str(数字) 转换，或者使用 f-string：f"{x}"。';
      if (a === null || b === null) hint = '有一个操作数是 None。检查变量是否被正确赋值，或者函数是否忘记 return。';
      this.raise('TypeError', 'unsupported operand type(s) for ' + op + ": '" + this.typeName(a) + "' and '" + this.typeName(b) + "'", hint);
    }
    compare(op, a, b) {
      switch (op) {
        case '==': return this.eq(a, b);
        case '!=': return !this.eq(a, b);
        case 'is': return this.is(a, b);
        case 'is not': return !this.is(a, b);
        case 'in': return this.contains(b, a);
        case 'not in': return !this.contains(b, a);
      }
      const c = this.order(a, b, op);
      switch (op) { case '<': return c < 0; case '>': return c > 0; case '<=': return c <= 0; case '>=': return c >= 0; }
    }
    is(a, b) {
      if (a === null || b === null) return a === b;
      if (typeof a !== 'object' || typeof b !== 'object') { if (typeof a !== typeof b) return false; return a === b; }
      return a === b;
    }
    eq(a, b) {
      if (a === b) return true;
      if (this.isNum(a) && this.isNum(b)) {
        if (typeof a === 'boolean') a = a ? 1n : 0n; if (typeof b === 'boolean') b = b ? 1n : 0n;
        if (typeof a === 'bigint' && typeof b === 'bigint') return a === b;
        return Number(a) === Number(b);
      }
      if (typeof a === 'string' || typeof b === 'string') return a === b;
      if (a === null || b === null) {
        if (a instanceof PyObj) { const m = a.cls.lookup('__eq__'); if (m) return this.truthy(this.callValue(this.bind(a, m), [b], new Map())); }
        return false;
      }
      if (a instanceof PyList && b instanceof PyList || a instanceof PyTuple && b instanceof PyTuple || a instanceof PyDeque && b instanceof PyDeque) {
        if (a.items.length !== b.items.length) return false;
        return a.items.every((x, i) => this.eq(x, b.items[i]));
      }
      if (a instanceof PyDict && b instanceof PyDict) {
        if (a.map.size !== b.map.size) return false;
        for (const [k, en] of a.map) { const o = b.map.get(k); if (!o || !this.eq(en[1], o[1])) return false; }
        return true;
      }
      if (a instanceof PySet && b instanceof PySet) { if (a.map.size !== b.map.size) return false; for (const k of a.map.keys()) if (!b.map.has(k)) return false; return true; }
      if (a instanceof PyRange && b instanceof PyRange) return this.eq(new PyList(this.toArray(a)), new PyList(this.toArray(b)));
      if (a instanceof PyObj) { const m = a.cls.lookup('__eq__'); if (m) { const r = this.callValue(this.bind(a, m), [b], new Map()); if (r !== this.NotImplemented) return this.truthy(r); } }
      if (b instanceof PyObj) { const m = b.cls.lookup('__eq__'); if (m) { const r = this.callValue(this.bind(b, m), [a], new Map()); if (r !== this.NotImplemented) return this.truthy(r); } }
      return false;
    }
    order(a, b, op) {
      if (this.isNum(a) && this.isNum(b)) {
        if (typeof a === 'boolean') a = a ? 1n : 0n; if (typeof b === 'boolean') b = b ? 1n : 0n;
        if (typeof a === 'bigint' && typeof b === 'bigint') return a < b ? -1 : a > b ? 1 : 0;
        const x = Number(a), y = Number(b); return x < y ? -1 : x > y ? 1 : (x === y ? 0 : NaN);
      }
      if (typeof a === 'string' && typeof b === 'string') return a < b ? -1 : a > b ? 1 : 0;
      if ((a instanceof PyList && b instanceof PyList) || (a instanceof PyTuple && b instanceof PyTuple)) {
        const n = Math.min(a.items.length, b.items.length);
        for (let i = 0; i < n; i++) { if (!this.eq(a.items[i], b.items[i])) return this.order(a.items[i], b.items[i], op); }
        return a.items.length - b.items.length;
      }
      if (a instanceof PySet && b instanceof PySet) {
        const sub = [...a.map.keys()].every(k => b.map.has(k)), sup = [...b.map.keys()].every(k => a.map.has(k));
        if (sub && sup) return 0; if (sub) return -1; if (sup) return 1; return NaN;
      }
      if (a instanceof PyObj) {
        const nm = { '<': '__lt__', '>': '__gt__', '<=': '__le__', '>=': '__ge__' }[op || '<'];
        let m = a.cls.lookup(nm);
        if (m) { const r = this.truthy(this.callValue(this.bind(a, m), [b], new Map())); return op === '<' || op === '<=' ? (r ? -1 : 1) : (r ? 1 : -1); }
        if (op === '>' || op === '>=') { const m2 = a.cls.lookup(op === '>' ? '__lt__' : '__le__'); if (m2 && b instanceof PyObj) { const r = this.truthy(this.callValue(this.bind(b, m2), [a], new Map())); return r ? 1 : -1; } }
        if (!op || op === '<') { const m3 = a.cls.lookup('__gt__'); if (m3 && b instanceof PyObj) { const r = this.truthy(this.callValue(this.bind(b, m3), [a], new Map())); return r ? -1 : 1; } }
      }
      if (b instanceof PyObj && op) {
        const nm = { '<': '__gt__', '>': '__lt__', '<=': '__ge__', '>=': '__le__' }[op];
        const m = b.cls.lookup(nm);
        if (m) { const r = this.truthy(this.callValue(this.bind(b, m), [a], new Map())); return op === '<' || op === '<=' ? (r ? -1 : 1) : (r ? 1 : -1); }
      }
      let hint;
      if (a === null || b === null) hint = '有一个值是 None，不能比较大小。检查变量是否被正确赋值。';
      else if (a instanceof PyObj || b instanceof PyObj) hint = '自定义类的对象要比较大小（例如放进 heapq 或排序），需要在类里定义 __lt__ 方法；或者把 (优先级, 计数, 对象) 这样的元组放进堆。';
      else if (typeof a === 'string' || typeof b === 'string') hint = '字符串和数字不能比较大小，检查是否需要用 int() 转换输入。';
      this.raise('TypeError', "'" + (op || '<') + "' not supported between instances of '" + this.typeName(a) + "' and '" + this.typeName(b) + "'", hint);
    }
    contains(c, x) {
      if (typeof c === 'string') { if (typeof x !== 'string') this.raise('TypeError', "'in <string>' requires string as left operand, not " + this.typeName(x)); return c.includes(x); }
      if (c instanceof PyList || c instanceof PyTuple || c instanceof PyDeque) return c.items.some(y => this.eq(y, x));
      if (c instanceof PyDict) return c.map.has(this.keyOf(x));
      if (c instanceof PySet) return c.map.has(this.keyOf(x));
      if (c instanceof PyRange) { if (typeof x !== 'bigint') return false; const { start, stop, step } = c; if (step > 0n ? (x < start || x >= stop) : (x > start || x <= stop)) return false; return (x - start) % step === 0n; }
      if (c instanceof PyIter) { while (c.i < c.items.length) if (this.eq(c.items[c.i++], x)) return true; return false; }
      if (c instanceof PyObj) {
        const m = c.cls.lookup('__contains__');
        if (m) return this.truthy(this.callValue(this.bind(c, m), [x], new Map()));
        const it = c.cls.lookup('__iter__');
        if (it) return this.toArray(c).some(y => this.eq(y, x));
      }
      this.raise('TypeError', "argument of type '" + this.typeName(c) + "' is not iterable");
    }

    // ================= hashing & containers =================
    keyOf(v) {
      if (v === null) return 'N';
      switch (typeof v) {
        case 'bigint': return 'i' + v;
        case 'boolean': return 'i' + (v ? 1 : 0);
        case 'number': return Number.isInteger(v) ? 'i' + BigInt(v) : 'f' + v;
        case 'string': return 's' + v;
      }
      if (v instanceof PyTuple) return 't(' + v.items.map(x => this.keyOf(x)).join(',') + ')';
      if (v instanceof PySet && v.frozen) return 'F(' + [...v.map.keys()].sort().join(',') + ')';
      if (v instanceof PyList || v instanceof PyDict || v instanceof PySet || v instanceof PyDeque) this.raise('TypeError', "unhashable type: '" + this.typeName(v) + "'", '列表、字典、集合是可变的，不能作为字典的键或放进集合。可以改用元组 tuple。');
      if (v instanceof PyObj) {
        const h = v.cls.lookup('__hash__');
        if (h) return 'h' + this.str(this.callValue(this.bind(v, h), [], new Map()));
        if (v.cls.lookup('__eq__') && !v.cls.dataclassFrozen) this.raise('TypeError', "unhashable type: '" + v.cls.name + "'", '定义了 __eq__ 的类需要同时定义 __hash__ 才能作为字典的键。');
        return 'o' + v.id;
      }
      if (v.id) return 'o' + v.id;
      return 'x' + String(v);
    }
    dictSet(d, k, v) {
      const key = this.keyOf(k);
      const ex = d.map.get(key);
      if (ex) ex[1] = v; else d.map.set(key, [k, v]);
    }
    dictGet(d, k) {
      const en = d.map.get(this.keyOf(k));
      if (en) return en[1];
      if (d.defaultFactory !== undefined && d.defaultFactory !== null) { const v = this.callValue(d.defaultFactory, [], new Map()); this.dictSet(d, k, v); return v; }
      if (d.kind === 'Counter') return 0n;
      this.raise('KeyError', this.repr(k), '字典里没有键 ' + this.repr(k) + '。可以先用 in 判断，或者用 d.get(key, 默认值)。');
    }
    setAdd(s, v) {
      const k = this.keyOf(v);
      if (!s.map.has(k)) { s.map.set(k, v); this.setGrow(s); }
    }
    setGrow(s) { const used = s.map.size; while ((used) * 5 >= (s.tsize - 1) * 3) s.tsize *= 4; }
    setOrder(s) {
      const vals = [...s.map.values()];
      if (vals.length && vals.every(v => typeof v === 'bigint' || typeof v === 'boolean')) {
        const mask = BigInt(s.tsize - 1);
        const slot = (v) => { const x = typeof v === 'boolean' ? (v ? 1n : 0n) : v; const h = x === -1n ? -2n : x; return Number(((h % BigInt(s.tsize)) + BigInt(s.tsize)) & mask); };
        const used = new Set(), out = new Array(s.tsize);
        const ins = [...vals];
        for (const v of ins) { let i = slot(v); while (used.has(i)) i = (i + 1) % s.tsize; used.add(i); out[i] = v; }
        return out.filter(x => x !== undefined);
      }
      return vals;
    }
    newCounter() { const d = new PyDict(); d.kind = 'Counter'; return d; }

    // iterate: returns next() function
    iterator(v) {
      if (v instanceof PyList || v instanceof PyDeque) {
        let i = 0;
        return () => i < v.items.length ? { value: v.items[i++] } : { done: true };
      }
      if (v instanceof PyIter) return () => { VER++; return v.i < v.items.length ? { value: v.items[v.i++] } : { done: true }; };
      if (v instanceof PyRange) {
        let x = v.start;
        return () => { if (v.step > 0n ? x < v.stop : x > v.stop) { const r = x; x += v.step; return { value: r }; } return { done: true }; };
      }
      if (v instanceof PyObj) {
        const it = v.cls.lookup('__iter__');
        if (it) { const r = this.callValue(this.bind(v, it), [], new Map()); if (r === v) { const nx = v.cls.lookup('__next__'); return () => { try { return { value: this.callValue(this.bind(v, nx), [], new Map()) }; } catch (e) { if (e instanceof PyExc && e.obj.cls.name === 'StopIteration') return { done: true }; throw e; } }; } return this.iterator(r); }
        const gi = v.cls.lookup('__getitem__');
        if (gi) { let i = 0n; return () => { try { return { value: this.callValue(this.bind(v, gi), [i++], new Map()) }; } catch (e) { if (e instanceof PyExc && (e.obj.cls.name === 'IndexError' || e.obj.cls.name === 'StopIteration')) return { done: true }; throw e; } }; }
      }
      const arr = this.toArray(v);
      let i = 0;
      return () => i < arr.length ? { value: arr[i++] } : { done: true };
    }
    toArray(v) {
      if (v instanceof PyList || v instanceof PyTuple || v instanceof PyDeque) return v.items.slice();
      if (typeof v === 'string') return [...v];
      if (v instanceof PyDict) return [...v.map.values()].map(en => en[0]);
      if (v instanceof PySet) return this.setOrder(v);
      if (v instanceof PyRange) { const out = []; const n = this.rangeLen(v); if (n > 1e6) this.raise('MemoryError', 'range 太大'); for (let x = v.start, k = 0; k < n; k++, x += v.step) out.push(x); return out; }
      if (v instanceof PyIter) { const r = v.items.slice(v.i); v.i = v.items.length; return r; }
      if (v instanceof PyObj && (v.cls.lookup('__iter__') || v.cls.lookup('__getitem__'))) { const next = this.iterator(v); const out = []; for (;;) { const r = next(); if (r.done) break; out.push(r.value); if (out.length > 1e5) break; } return out; }
      this.raise('TypeError', "'" + this.typeName(v) + "' object is not iterable", v === null ? '你在遍历 None。检查变量是否被正确赋值，或者函数是否忘记 return。' : (typeof v === 'bigint' ? '整数不能被遍历。如果想循环 n 次，请写 for i in range(n)。' : undefined));
    }
    rangeLen(r) {
      const { start, stop, step } = r;
      if (step > 0n) return stop > start ? Number((stop - start + step - 1n) / step) : 0;
      return start > stop ? Number((start - stop - step - 1n) / -step) : 0;
    }

    // ================= indexing =================
    normIndex(i, len, what) {
      let k = this.toInt(i);
      const n = BigInt(len);
      if (k < 0n) k += n;
      if (k < 0n || k >= n) {
        const kind = what || 'list';
        this.raise('IndexError', kind + ' index out of range', kind + ' 的长度是 ' + len + '，合法的下标是 0 ~ ' + (len - 1) + '（或 -' + len + ' ~ -1），而你用的下标是 ' + this.toInt(i) + '。' + (len === 0 ? '这个 ' + kind + ' 是空的。' : ''));
      }
      return Number(k);
    }
    sliceIdx(sl, len) {
      const step = sl.step === null ? 1 : Number(this.toInt(sl.step));
      if (step === 0) this.raise('ValueError', 'slice step cannot be zero');
      let lo, hi;
      const norm = (v, def) => { if (v === null) return def; let x = Number(this.toInt(v)); if (x < 0) x += len; return x; };
      if (step > 0) { lo = Math.min(Math.max(norm(sl.lo, 0), 0), len); hi = Math.min(Math.max(norm(sl.hi, len), 0), len); }
      else { lo = Math.min(Math.max(norm(sl.lo, len - 1), -1), len - 1); hi = sl.hi === null ? -1 : Math.min(Math.max(norm(sl.hi, -1), -1), len - 1); }
      const idx = [];
      if (step > 0) for (let i = lo; i < hi; i += step) idx.push(i);
      else for (let i = lo; i > hi; i += step) idx.push(i);
      return idx;
    }
    getitem(o, k) {
      if (o instanceof PyList || o instanceof PyTuple || o instanceof PyDeque) {
        if (k && k.slice) { const idx = this.sliceIdx(k, o.items.length); const items = idx.map(i => o.items[i]); return o instanceof PyTuple ? new PyTuple(items) : (o instanceof PyDeque ? new PyDeque(items) : new PyList(items)); }
        return o.items[this.normIndex(k, o.items.length, o instanceof PyTuple ? 'tuple' : (o instanceof PyDeque ? 'deque' : 'list'))];
      }
      if (typeof o === 'string') {
        if (k && k.slice) return this.sliceIdx(k, o.length).map(i => o[i]).join('');
        return o[this.normIndex(k, o.length, 'string')];
      }
      if (o instanceof PyDict) return this.dictGet(o, k);
      if (o instanceof PyRange) { const arr = this.toArray(o); if (k && k.slice) return new PyList(this.sliceIdx(k, arr.length).map(i => arr[i])); return arr[this.normIndex(k, arr.length, 'range object')]; }
      if (o instanceof PyObj) { const m = o.cls.lookup('__getitem__'); if (m) return this.callValue(this.bind(o, m), [k && k.slice ? this.sliceObj(k) : k], new Map()); }
      if (o instanceof PyClass) return o; // typing generics like List[int]
      if (o instanceof PyBuiltin && o.typing) return o;
      this.raise('TypeError', "'" + this.typeName(o) + "' object is not subscriptable", o === null ? '你在对 None 使用下标 []。检查变量是否被正确赋值。' : (o instanceof PySet ? '集合是无序的，不能用下标访问。' : undefined));
    }
    sliceObj(k) { const o = new PyObj(this.builtins.get('slice')); o.attrs.set('start', k.lo); o.attrs.set('stop', k.hi); o.attrs.set('step', k.step); return o; }
    setitem(o, k, v) {
      VER++;
      if (o instanceof PyList || o instanceof PyDeque) {
        if (k && k.slice) {
          const vals = this.toArray(v);
          if (k.step === null || this.toInt(k.step) === 1n) {
            const idx = this.sliceIdx(k, o.items.length);
            const lo = idx.length ? idx[0] : Math.min(Math.max(k.lo === null ? 0 : Number(this.toInt(k.lo)) < 0 ? Number(this.toInt(k.lo)) + o.items.length : Number(this.toInt(k.lo)), 0), o.items.length);
            o.items.splice(lo, idx.length, ...vals);
          } else { const idx = this.sliceIdx(k, o.items.length); if (idx.length !== vals.length) this.raise('ValueError', 'attempt to assign sequence of size ' + vals.length + ' to extended slice of size ' + idx.length); idx.forEach((i, j) => o.items[i] = vals[j]); }
          return;
        }
        const i = (() => { try { return this.normIndex(k, o.items.length); } catch (e) { if (e instanceof PyExc) this.raise('IndexError', 'list assignment index out of range', '列表长度是 ' + o.items.length + '。给新位置赋值不能用下标，要用 append() 追加元素。'); throw e; } })();
        o.items[i] = v; return;
      }
      if (o instanceof PyDict) { this.dictSet(o, k, v); return; }
      if (o instanceof PyObj) { const m = o.cls.lookup('__setitem__'); if (m) { this.callValue(this.bind(o, m), [k, v], new Map()); return; } }
      if (typeof o === 'string') this.raise('TypeError', "'str' object does not support item assignment", '字符串是不可变的。可以先转换成列表 list(s)，修改后再用 "".join(...) 拼回字符串。');
      if (o instanceof PyTuple) this.raise('TypeError', "'tuple' object does not support item assignment", '元组是不可变的，不能修改其中的元素。需要修改的话请使用列表。');
      this.raise('TypeError', "'" + this.typeName(o) + "' object does not support item assignment");
    }
    delitem(o, k) {
      VER++;
      if (o instanceof PyList || o instanceof PyDeque) {
        if (k && k.slice) { const idx = new Set(this.sliceIdx(k, o.items.length)); o.items = o.items.filter((_, i) => !idx.has(i)); return; }
        o.items.splice(this.normIndex(k, o.items.length), 1); return;
      }
      if (o instanceof PyDict) { const key = this.keyOf(k); if (!o.map.has(key)) this.raise('KeyError', this.repr(k)); o.map.delete(key); return; }
      if (o instanceof PyObj) { const m = o.cls.lookup('__delitem__'); if (m) { this.callValue(this.bind(o, m), [k], new Map()); return; } }
      this.raise('TypeError', "'" + this.typeName(o) + "' object doesn't support item deletion");
    }

    // ================= str / repr / format =================
    str(v) {
      if (typeof v === 'string') return v;
      if (v instanceof PyObj) {
        const m = v.cls.lookup('__str__');
        if (m) return this.checkStr(this.callValue(this.bind(v, m), [], new Map()), '__str__');
        if (this.isExcClass(v.cls)) { const a = v.attrs.get('args'); if (!a || !a.items.length) return ''; if (a.items.length === 1) return this.str(a.items[0]); return this.repr(a); }
      }
      return this.repr(v);
    }
    checkStr(r, nm) { if (typeof r !== 'string') this.raise('TypeError', nm + ' returned non-string (type ' + this.typeName(r) + ')', nm + ' 方法必须 return 一个字符串。'); return r; }
    repr(v, seen) {
      if (v === null || v === undefined) return 'None';
      switch (typeof v) {
        case 'boolean': return v ? 'True' : 'False';
        case 'bigint': return v.toString();
        case 'number': return floatRepr(v);
        case 'string': return strRepr(v);
      }
      seen = seen || new Set();
      if (seen.has(v)) return v instanceof PyList ? '[...]' : '{...}';
      if (v instanceof PyList) { seen.add(v); const r = '[' + v.items.map(x => this.repr(x, seen)).join(', ') + ']'; seen.delete(v); return r; }
      if (v instanceof PyTuple) {
        if (v.cls) return v.cls.name + '(' + v.cls.fields.map((f, i) => f + '=' + this.repr(v.items[i], seen)).join(', ') + ')';
        return '(' + v.items.map(x => this.repr(x, seen)).join(', ') + (v.items.length === 1 ? ',' : '') + ')';
      }
      if (v instanceof PyDeque) return 'deque([' + v.items.map(x => this.repr(x, seen)).join(', ') + ']' + (v.maxlen !== null ? ', maxlen=' + v.maxlen : '') + ')';
      if (v instanceof PyDict) {
        seen.add(v);
        const body = '{' + [...v.map.values()].map(en => this.repr(en[0], seen) + ': ' + this.repr(en[1], seen)).join(', ') + '}';
        seen.delete(v);
        if (v.kind === 'Counter') return 'Counter(' + (v.map.size ? '{' + [...v.map.values()].sort((a, b) => Number(b[1] - a[1])).map(en => this.repr(en[0]) + ': ' + this.repr(en[1])).join(', ') + '}' : '') + ')';
        if (v.kind === 'defaultdict') return 'defaultdict(' + this.repr(v.defaultFactory) + ', ' + body + ')';
        if (v.kind === 'OrderedDict') return 'OrderedDict(' + body + ')';
        return body;
      }
      if (v instanceof PySet) { const items = this.setOrder(v); if (!items.length) return v.frozen ? 'frozenset()' : 'set()'; const b = '{' + items.map(x => this.repr(x, seen)).join(', ') + '}'; return v.frozen ? 'frozenset(' + b + ')' : b; }
      if (v instanceof PyRange) return 'range(' + v.start + ', ' + v.stop + (v.step !== 1n ? ', ' + v.step : '') + ')';
      if (v instanceof PyObj) {
        const m = v.cls.lookup('__repr__');
        if (m) return this.checkStr(this.callValue(this.bind(v, m), [], new Map()), '__repr__');
        if (this.isExcClass(v.cls)) { const a = v.attrs.get('args'); return v.cls.name + '(' + (a ? a.items.map(x => this.repr(x)).join(', ') : '') + ')'; }
        if (v.cls.dataclassFields) return v.cls.name + '(' + v.cls.dataclassFields.map(f => f.name + '=' + this.repr(v.attrs.get(f.name), seen)).join(', ') + ')';
        return '<__main__.' + v.cls.name + ' object at 0x7f' + (parseInt(v.id.slice(1)) * 48 + 0x3a2b10).toString(16).padStart(8, '0') + '>';
      }
      if (v instanceof PyFunc) return '<function ' + (v.cls ? v.cls.name + '.' : '') + v.name + ' at 0x7f' + (parseInt(v.id.slice(1)) * 48 + 0x1c00).toString(16).padStart(8, '0') + '>';
      if (v instanceof PyClass) return "<class '" + (v.builtin ? '' : '__main__.') + v.name + "'>";
      if (v instanceof PyBuiltin) return '<built-in function ' + v.name + '>';
      if (v instanceof PyBound) return '<bound method ' + (v.fn.name || '') + '>';
      if (v instanceof PyModule) return "<module '" + v.name + "'>";
      if (v instanceof PyIter) return '<' + v.label + ' object at 0x7f' + (parseInt(v.id.slice(1)) * 48).toString(16).padStart(8, '0') + '>';
      if (v === this.NotImplemented) return 'NotImplemented';
      return String(v);
    }
    format(v, spec) {
      if (v instanceof PyObj) { const m = v.cls.lookup('__format__'); if (m) return this.callValue(this.bind(v, m), [spec], new Map()); if (!spec) return this.str(v); }
      if (!spec) return this.str(v);
      const m = /^(?:(.)?([<>=^]))?([+\- ])?(#)?(0)?(\d+)?([,_])?(?:\.(\d+))?([bcdeEfFgGnosxX%])?$/.exec(spec);
      if (!m) this.raise('ValueError', "Invalid format specifier '" + spec + "'");
      let [, fill, align, sign, alt, zero, width, group, prec, type] = m;
      let s;
      const isNumV = this.isNum(v);
      if (typeof v === 'boolean' && !type) { s = this.str(v); }
      else if (type === 'd' || (type === undefined && typeof v === 'bigint')) {
        if (typeof v === 'number') this.raise('ValueError', "Unknown format code 'd' for object of type 'float'", '浮点数要用 .2f 这类格式，或者先用 int() 转换。');
        if (!isNumV) this.raise('ValueError', "Unknown format code 'd' for object of type '" + this.typeName(v) + "'");
        let n = this.toInt(v); s = (n < 0n ? -n : n).toString();
        if (group) s = s.replace(/\B(?=(\d{3})+(?!\d))/g, group);
        s = (n < 0n ? '-' : (sign === '+' ? '+' : sign === ' ' ? ' ' : '')) + s;
      } else if ('fFeEgG%'.includes(type || '_') || (type === undefined && typeof v === 'number')) {
        if (!isNumV) this.raise('ValueError', "Unknown format code '" + type + "' for object of type '" + this.typeName(v) + "'");
        let x = this.toNum(v);
        const p = prec === undefined ? 6 : +prec;
        if (type === '%') { x *= 100; s = Math.abs(x).toFixed(p) + '%'; }
        else if (type === 'e' || type === 'E') { s = Math.abs(x).toExponential(p).replace(/e([+-])(\d)$/, 'e$10$2'); if (type === 'E') s = s.toUpperCase(); }
        else if (type === 'g' || type === 'G') s = String(+Math.abs(x).toPrecision(p || 1));
        else if (type === undefined) s = prec !== undefined ? String(+Math.abs(x).toPrecision(+prec)) : floatRepr(Math.abs(x));
        else s = Math.abs(x).toFixed(p);
        if (group) { const [ip, fp] = s.split('.'); s = ip.replace(/\B(?=(\d{3})+(?!\d))/g, group) + (fp !== undefined ? '.' + fp : ''); }
        s = (x < 0 || Object.is(x, -0) && type ? '-' : (sign === '+' ? '+' : sign === ' ' ? ' ' : '')) + s;
      } else if (type === 'x' || type === 'X' || type === 'b' || type === 'o') {
        const n = this.toInt(v); const base = { x: 16, X: 16, b: 2, o: 8 }[type];
        s = (n < 0n ? -n : n).toString(base); if (type === 'X') s = s.toUpperCase();
        if (alt) s = '0' + (type === 'o' ? 'o' : type.toLowerCase() === 'x' ? type : 'b') + s;
        if (n < 0n) s = '-' + s;
      } else if (type === 'c') s = String.fromCharCode(Number(this.toInt(v)));
      else { s = this.str(v); if (prec !== undefined) s = s.slice(0, +prec); }
      if (width) {
        const w = +width;
        if (zero && !align) { fill = '0'; align = '='; }
        fill = fill || ' ';
        if (!align) align = isNumV && typeof v !== 'boolean' ? '>' : '<';
        if (s.length < w) {
          const pad = w - s.length;
          if (align === '<') s = s + fill.repeat(pad);
          else if (align === '>') s = fill.repeat(pad) + s;
          else if (align === '^') s = fill.repeat(Math.floor(pad / 2)) + s + fill.repeat(Math.ceil(pad / 2));
          else if (align === '=') { const sg = /^[+\- ]/.test(s) ? s[0] : ''; s = sg + fill.repeat(pad) + s.slice(sg.length); }
        }
      }
      return s;
    }
    percentFormat(fmt, args) {
      const list = args instanceof PyTuple ? args.items : [args];
      let i = 0;
      const out = fmt.replace(/%(\((\w+)\))?([-+ 0#]*)(\d+|\*)?(?:\.(\d+))?([sdirfFeEgGxXoc%])/g, (all, _p, key, flags, width, prec, conv) => {
        if (conv === '%') return '%';
        let v = key ? this.dictGet(args, key) : list[i++];
        if (v === undefined) this.raise('TypeError', 'not enough arguments for format string');
        let s;
        switch (conv) {
          case 's': s = this.str(v); break;
          case 'r': s = this.repr(v); break;
          case 'd': case 'i': s = (typeof v === 'number' ? BigInt(Math.trunc(v)) : this.toInt(v)).toString(); break;
          case 'f': case 'F': s = this.toNum(v).toFixed(prec === undefined ? 6 : +prec); break;
          case 'e': case 'E': s = this.toNum(v).toExponential(prec === undefined ? 6 : +prec).replace(/e([+-])(\d)$/, 'e$10$2'); break;
          case 'g': case 'G': s = String(+this.toNum(v).toPrecision(prec === undefined ? 6 : +prec)); break;
          case 'x': s = this.toInt(v).toString(16); break; case 'X': s = this.toInt(v).toString(16).toUpperCase(); break;
          case 'o': s = this.toInt(v).toString(8); break;
          case 'c': s = typeof v === 'string' ? v : String.fromCharCode(Number(v)); break;
        }
        if (flags.includes('+') && /^[0-9]/.test(s) && 'dif'.includes(conv)) s = '+' + s;
        if (width) { const w = +width; if (flags.includes('-')) s = s.padEnd(w); else if (flags.includes('0')) s = s.startsWith('-') ? '-' + s.slice(1).padStart(w - 1, '0') : s.padStart(w, '0'); else s = s.padStart(w); }
        return s;
      });
      if (i < list.length && !(args instanceof PyDict)) this.raise('TypeError', 'not all arguments converted during string formatting');
      return out;
    }
  }
  const DUNDER = { '+': 'add', '-': 'sub', '*': 'mul', '/': 'truediv', '//': 'floordiv', '%': 'mod', '**': 'pow', '<<': 'lshift', '>>': 'rshift', '&': 'and', '|': 'or', '^': 'xor', '@': 'matmul' };

  DSV.PyInterp = PyInterp;
  DSV.pyRT = { ver: () => VER, bump: () => { VER++; }, PyList, PyTuple, PyDict, PySet, PyDeque, PyObj, PyClass, PyFunc, PyBuiltin, PyBound, PyModule, PyRange, PyIter, PyProperty, PyStatic, PyClassMethod, PySuper, PyExc, Env, floatRepr, strRepr, collectLocals, setCurStep: (n) => { CUR_STEP = n; } };
})(typeof window !== 'undefined' ? window : globalThis);
