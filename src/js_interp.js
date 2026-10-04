// ===== JavaScript / TypeScript interpreter =====
(function (G) {
  const DSV = G.DSV;
  const { RunError, Recorder } = DSV;

  let NID = 0, CUR_STEP = 0, VER = 0;
  const nid = () => 'j' + (++NID);
  class VMap extends Map {
    constructor() { super(); this.ver = 0; }
    set(k, v) { this.ver++; VER++; return super.set(k, v); }
    delete(k) { this.ver++; VER++; return super.delete(k); }
    clear() { this.ver++; VER++; return super.clear(); }
  }
  const HOLE = { hole: true };
  class Slot { constructor(v, e) { this.v = v; this.e = e !== false; } }
  class Acc { constructor(get, set, e) { this.get = get; this.set = set; this.e = !!e; this.acc = true; } }
  class JSO { constructor(proto) { this.id = nid(); this.proto = proto || null; this.props = new VMap(); this.born = CUR_STEP; } }
  class JSArr extends JSO { constructor(proto, items) { super(proto); this.items = items || []; } }
  class JSFunc extends JSO { constructor(proto) { super(proto); this.fname = ''; } }
  class JSMap extends JSO { constructor(proto) { super(proto); this.m = new Map(); } }
  class JSSet extends JSO { constructor(proto) { super(proto); this.m = new Map(); } }
  class JSGen extends JSO { constructor(proto, items) { super(proto); this.items = items; this.i = 0; } }
  class JSRegExp extends JSO { constructor(proto, re) { super(proto); this.re = re; } }
  class Throw { constructor(v) { this.v = v; } }
  class Scope {
    constructor(parent, kind) { this.vars = new Map(); this.parent = parent; this.kind = kind; }
  }
  class Ret { constructor(v, line) { this.v = v; this.line = line; } }
  class Brk { constructor(label) { this.label = label; } }
  class Cont { constructor(label) { this.label = label; } }

  const isObj = (v) => v instanceof JSO;
  const ITER = '@@iterator';

  class JSInterp {
    constructor(prog, opts, ts) {
      this.prog = prog;
      this.ts = ts;
      this.opts = opts || {};
      this.rec = new Recorder(opts);
      this.stdin = new DSV.Stdin(this.opts.stdin || '');
      this.frames = [];
      this.rng = DSV.makeRng(7);
      this.depthLimit = 350;
      this.curLine = 0;
      this.warned = new Set();
      this.setupGlobals();
    }
    get frame() { return this.frames[this.frames.length - 1]; }
    get scope() { return this.frame.scope; }
    set scope(s) { this.frame.scope = s; }

    // ================= errors =================
    throwErr(type, msg, hint) {
      const ctor = this.globalScope.parent.vars.get(type).v;
      const e = this.makeError(ctor.props.get('prototype').v, msg);
      if (hint) e.hint = hint;
      throw new Throw(e);
    }
    makeError(proto, msg) {
      const e = new JSO(proto);
      e.props.set('message', new Slot(msg === undefined ? '' : String(msg), false));
      e.props.set('stack', new Slot(this.errName(e) + ': ' + msg, false));
      return e;
    }
    errName(e) { const n = this.get(e, 'name'); return typeof n === 'string' ? n : 'Error'; }

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
      this.frames.push({ id: 'g', name: '全局', scope: this.globalScope, fnScope: this.globalScope, isGlobal: true, line: 1 });
      try {
        try {
          this.hoist(this.prog.body, this.globalScope, true);
          const r = this.execList(this.prog.body);
          this.runTimers();
          this.rec.note('程序结束。', 'end');
          this.rec.maxSteps += 1;
          this.step(this.lastLine(), 'end');
        } catch (e) {
          if (e instanceof Throw) {
            const v = e.v;
            let msg, hint = '';
            if (isObj(v) && this.isError(v)) { msg = this.errName(v) + ': ' + this.get(v, 'message'); hint = v.hint || this.hintFor(msg); }
            else msg = 'Uncaught ' + this.inspect(v);
            const re = new RunError(msg, 'exception', hint);
            throw re;
          }
          throw e;
        }
      } catch (e) {
        err = e;
        if (e instanceof RangeError) err = new RunError('RangeError: Maximum call stack size exceeded（调用栈溢出）', 'stack', '检查递归函数是否有正确的终止条件（base case）。');
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
    lastLine() {
      let l = 1;
      const walk = (n) => { if (!n || typeof n !== 'object') return; if (n.line > l) l = n.line; if (n.endLine > l) l = n.endLine; for (const k in n) { const v = n[k]; if (Array.isArray(v)) v.forEach(walk); else if (v && typeof v === 'object' && k !== 'fn') walk(v); } };
      this.prog.body.forEach(walk);
      return l;
    }
    hintFor(msg) {
      if (/Cannot read properties of (null|undefined)/.test(msg)) return '访问属性时，对象是 null 或 undefined。常见原因：链表遍历走到了末尾（null）还继续访问 .next；数组下标越界得到了 undefined；或者函数忘记 return。';
      if (/Cannot set properties of (null|undefined)/.test(msg)) return '给 null 或 undefined 的属性赋值。检查对象是否已经创建（例如 new Node(...)）。';
      if (/is not defined/.test(msg)) return '检查变量名是否拼写正确，以及是否用 let / const 声明过。';
      if (/is not a function/.test(msg)) return '被调用的值不是函数。检查方法名拼写，或者对象是否真的有这个方法。';
      if (/before initialization/.test(msg)) return 'let / const 声明的变量在声明语句执行之前不能使用（暂时性死区）。';
      if (/constant variable/.test(msg)) return 'const 声明的变量不能重新赋值。如果需要修改，请改用 let。';
      if (/is not iterable/.test(msg)) return 'for...of 和展开运算符只能用于数组、字符串、Map、Set 等可迭代对象。遍历普通对象可以用 Object.keys(obj)。';
      return '';
    }
    isError(v) { const ep = this.ErrorProto; for (let p = v.proto; p; p = p.proto) if (p === ep) return true; return false; }

    // ================= hoisting =================
    hoist(stmts, scope, isFunctionBody) {
      if (isFunctionBody) {
        const vars = new Set();
        const walk = (s) => {
          if (!s) return;
          switch (s.type) {
            case 'Var': if (s.kind === 'var') s.decls.forEach(d => this.patternNames(d.id).forEach(n => vars.add(n))); break;
            case 'If': walk(s.cons); walk(s.alt); break;
            case 'For': walk(s.init); walk(s.body); break;
            case 'ForOf': case 'ForIn': if (s.kind === 'var') this.patternNames(s.left).forEach(n => vars.add(n)); walk(s.body); break;
            case 'While': case 'DoWhile': case 'Labeled': walk(s.body); break;
            case 'Block': s.body.forEach(walk); break;
            case 'Try': walk(s.block); walk(s.handler); walk(s.finalizer); break;
            case 'Switch': s.cases.forEach(c => c.body.forEach(walk)); break;
          }
        };
        stmts.forEach(walk);
        for (const n of vars) if (!scope.vars.has(n)) scope.vars.set(n, { v: undefined, kind: 'var' });
      }
      this.hoistLexical(stmts, scope);
    }
    hoistLexical(stmts, scope) {
      for (const s of stmts) {
        if (s.type === 'Var' && s.kind !== 'var') for (const d of s.decls) for (const n of this.patternNames(d.id)) scope.vars.set(n, { v: undefined, kind: s.kind, tdz: true });
        if (s.type === 'ClassDecl') scope.vars.set(s.cls.name, { v: undefined, kind: 'let', tdz: true });
        if (s.type === 'Enum') scope.vars.set(s.name, { v: undefined, kind: 'const', tdz: true });
      }
      for (const s of stmts) if (s.type === 'FuncDecl') scope.vars.set(s.fn.name, { v: this.makeFunction(s.fn, scope), kind: 'var' });
    }
    patternNames(p) {
      if (!p) return [];
      switch (p.type) {
        case 'Id': return [p.name];
        case 'ArrPat': return [].concat(...p.elems.map(e => e ? this.patternNames(e.type === 'Rest' ? e.arg : e) : []));
        case 'ObjPat': return [].concat(...p.props.map(pr => this.patternNames(pr.rest || pr.target)));
        case 'Default': return this.patternNames(p.target);
        case 'Rest': return this.patternNames(p.arg);
      }
      return [];
    }

    // ================= variables =================
    lookupRef(name) {
      for (let s = this.scope; s; s = s.parent) { const v = s.vars.get(name); if (v) return v; }
      return null;
    }
    getVar(name) {
      if (name === 'undefined') return undefined;
      const r = this.lookupRef(name);
      if (!r) this.throwErr('ReferenceError', name + ' is not defined');
      if (r.tdz) this.throwErr('ReferenceError', "Cannot access '" + name + "' before initialization");
      return r.v;
    }
    setVar(name, v, line) {
      const r = this.lookupRef(name);
      if (!r) this.throwErr('ReferenceError', name + ' is not defined', '给未声明的变量赋值。请先用 let 或 const 声明它，例如 let ' + name + ' = ...;');
      if (r.tdz) this.throwErr('ReferenceError', "Cannot access '" + name + "' before initialization");
      if (r.kind === 'const') this.throwErr('TypeError', 'Assignment to constant variable.');
      if (r.builtin) this.throwErr('TypeError', '不能修改内置对象 ' + name);
      if (isObj(v) || isObj(r.v)) VER++;
      r.v = v;
    }
    declare(scope, name, v, kind) {
      if (isObj(v)) VER++;
      const ex = scope.vars.get(name);
      if (ex && kind !== 'var' && !ex.tdz && ex.kind !== 'var' && scope.kind !== 'global-redecl') this.throwErr('SyntaxError', "Identifier '" + name + "' has already been declared");
      if (ex) { ex.v = v; ex.tdz = false; if (kind) ex.kind = kind; return; }
      scope.vars.set(name, { v, kind: kind || 'let' });
    }
    bindPattern(p, v, kind, scope) {
      // kind: 'var'|'let'|'const'|null(assignment)
      switch (p.type) {
        case 'Id':
          if (kind) this.declare(kind === 'var' ? this.varScope() : (scope || this.scope), p.name, v, kind);
          else this.setVar(p.name, v);
          return;
        case 'Member': {
          const obj = this.eval(p.obj);
          const key = p.computed ? this.toKey(this.eval(p.prop)) : p.prop.v;
          this.put(obj, key, v);
          return;
        }
        case 'Default': return this.bindPattern(p.target, v === undefined ? this.evalNamed(p.def, p.target) : v, kind, scope);
        case 'ArrPat': {
          if (v === null || v === undefined) this.throwErr('TypeError', this.typeOf(v) + ' is not iterable (cannot destructure)');
          const next = this.iterator(v);
          for (const el of p.elems) {
            if (el === null) { next(); continue; }
            if (el.type === 'Rest') { const rest = []; for (;;) { const r = next(); if (r.done) break; rest.push(r.value); } this.bindPattern(el.arg, this.newArray(rest), kind, scope); break; }
            const r = next();
            this.bindPattern(el, r.done ? undefined : r.value, kind, scope);
          }
          return;
        }
        case 'ObjPat': {
          if (v === null || v === undefined) this.throwErr('TypeError', 'Cannot destructure \'' + v + '\' as it is ' + v + '.');
          const used = new Set();
          for (const pr of p.props) {
            if (pr.rest) {
              const o = this.newObject();
              for (const k of this.ownKeys(v)) if (!used.has(k)) o.props.set(k, new Slot(this.get(v, k)));
              this.bindPattern(pr.rest, o, kind, scope);
              continue;
            }
            const key = pr.computed ? this.toKey(this.eval(pr.key)) : pr.key;
            used.add(key);
            this.bindPattern(pr.target, this.get(v, key), kind, scope);
          }
          return;
        }
      }
      this.throwErr('SyntaxError', 'Invalid destructuring target');
    }
    evalNamed(e, target) {
      const v = this.eval(e);
      if (v instanceof JSFunc && !v.fname && target && target.type === 'Id') v.fname = target.name;
      return v;
    }
    varScope() { for (let s = this.scope; s; s = s.parent) if (s.kind === 'function' || s.kind === 'global') return s; return this.globalScope; }
    thisScope() { for (let s = this.scope; s; s = s.parent) if ((s.kind === 'function' && !s.arrow) || s.kind === 'global' || s.kind === 'fieldinit') return s; return this.globalScope; }

    // ================= statements =================
    execList(list) {
      for (const s of list) { const r = this.exec(s); if (r) return r; }
      return null;
    }
    execBlock(b) {
      const sc = new Scope(this.scope, 'block');
      const save = this.scope;
      this.scope = sc;
      this.hoistLexical(b.body, sc);
      try { return this.execList(b.body); }
      finally { this.scope = save; }
    }
    execSub(s) { if (s.type === 'Block') return this.execBlock(s); return this.exec(s); }
    exec(s, label) {
      switch (s.type) {
        case 'Expr': this.step(s.line); this.eval(s.expr); return null;
        case 'Var': {
          this.step(s.line);
          for (const d of s.decls) {
            if (s.kind === 'var' && !d.init) continue;
            const v = d.init ? this.evalNamed(d.init, d.id) : undefined;
            this.bindPattern(d.id, v, s.kind);
          }
          return null;
        }
        case 'FuncDecl': return null;
        case 'ClassDecl': {
          this.step(s.line);
          const c = this.makeClass(s.cls);
          this.declare(this.scope, s.cls.name, c, 'let');
          return null;
        }
        case 'Enum': {
          this.step(s.line);
          const o = this.newObject();
          let n = 0;
          for (const m of s.members) {
            const v = m.init ? this.eval(m.init) : n;
            if (typeof v === 'number') { n = v + 1; o.props.set(String(v), new Slot(m.k)); }
            o.props.set(m.k, new Slot(v));
          }
          this.declare(this.scope, s.name, o, 'const');
          return null;
        }
        case 'Block': return this.execBlock(s);
        case 'Empty': return null;
        case 'If': {
          this.step(s.line);
          if (this.truthy(this.eval(s.test))) return this.execSub(s.cons);
          if (s.alt) return this.execSub(s.alt);
          return null;
        }
        case 'While': {
          for (;;) {
            this.step(s.line);
            if (!this.truthy(this.eval(s.test))) break;
            const r = this.execSub(s.body);
            if (r instanceof Brk) { if (!r.label || r.label === label) break; return r; }
            if (r instanceof Cont) { if (!r.label || r.label === label) continue; return r; }
            if (r) return r;
          }
          return null;
        }
        case 'DoWhile': {
          for (;;) {
            const r = this.execSub(s.body);
            if (r instanceof Brk) { if (!r.label || r.label === label) break; return r; }
            if (r instanceof Cont) { if (r.label && r.label !== label) return r; }
            else if (r) return r;
            this.step(s.testLine || s.line);
            if (!this.truthy(this.eval(s.test))) break;
          }
          return null;
        }
        case 'For': return this.execFor(s, label);
        case 'ForOf': case 'ForIn': return this.execForOf(s, label);
        case 'Labeled': {
          const r = this.exec(s.body, s.label);
          if (r instanceof Brk && r.label === s.label) return null;
          return r;
        }
        case 'Return': {
          this.step(s.line);
          if (this.frame.isGlobal) this.throwErr('SyntaxError', 'Illegal return statement');
          return new Ret(s.arg ? this.eval(s.arg) : undefined, s.line);
        }
        case 'Break': this.step(s.line); return new Brk(s.label);
        case 'Continue': this.step(s.line); return new Cont(s.label);
        case 'Throw': {
          this.step(s.line);
          const v = this.eval(s.arg);
          this.rec.note('抛出异常 ' + (isObj(v) && this.isError(v) ? this.errName(v) + ': ' + this.get(v, 'message') : this.inspect(v)), 'warn');
          throw new Throw(v);
        }
        case 'Try': return this.execTry(s);
        case 'Switch': {
          this.step(s.line);
          const d = this.eval(s.disc);
          let start = -1;
          for (let i = 0; i < s.cases.length; i++) if (s.cases[i].test && this.strictEq(d, this.eval(s.cases[i].test))) { start = i; break; }
          if (start < 0) start = s.cases.findIndex(c => !c.test);
          if (start < 0) return null;
          const sc = new Scope(this.scope, 'block');
          const save = this.scope; this.scope = sc;
          try {
            for (const c of s.cases) this.hoistLexical(c.body, sc);
            for (let i = start; i < s.cases.length; i++) {
              const r = this.execList(s.cases[i].body);
              if (r instanceof Brk && !r.label) return null;
              if (r) return r;
            }
          } finally { this.scope = save; }
          return null;
        }
      }
      throw new RunError('暂不支持的语句：' + s.type, 'runtime');
    }
    execFor(s, label) {
      const outer = this.scope;
      let sc = new Scope(outer, 'block');
      this.scope = sc;
      try {
        this.step(s.line);
        let letNames = [];
        if (s.init) {
          if (s.init.type === 'Var') {
            for (const d of s.init.decls) this.bindPattern(d.id, d.init ? this.evalNamed(d.init, d.id) : undefined, s.init.kind);
            if (s.init.kind !== 'var') letNames = [].concat(...s.init.decls.map(d => this.patternNames(d.id)));
          } else this.eval(s.init.expr);
        }
        for (;;) {
          if (s.test && !this.truthy(this.eval(s.test))) break;
          const r = this.execSub(s.body);
          if (r instanceof Brk) { if (!r.label || r.label === label) break; return r; }
          if (r instanceof Cont) { if (r.label && r.label !== label) return r; }
          else if (r) return r;
          // fresh binding per iteration
          if (letNames.length) { const ns = new Scope(outer, 'block'); for (const n of letNames) ns.vars.set(n, Object.assign({}, sc.vars.get(n))); sc = ns; this.scope = sc; }
          this.step(s.line);
          if (s.update) this.eval(s.update);
        }
      } finally { this.scope = outer; }
      return null;
    }
    execForOf(s, label) {
      this.step(s.line);
      const outer = this.scope;
      const src = this.eval(s.right);
      let next;
      if (s.type === 'ForIn') {
        if (src === null || src === undefined) return null;
        const keys = this.forInKeys(src);
        let i = 0;
        next = () => i < keys.length ? { value: keys[i++] } : { done: true };
      } else next = this.iterator(src);
      let first = true;
      try {
        for (;;) {
          if (!first) this.step(s.line);
          first = false;
          const r0 = next();
          if (r0.done) break;
          const sc = new Scope(outer, 'block');
          this.scope = sc;
          if (s.kind) this.bindPattern(s.left, r0.value, s.kind, sc);
          else this.bindPattern(s.left, r0.value, null);
          const r = this.execSub(s.body);
          this.scope = outer;
          if (r instanceof Brk) { if (!r.label || r.label === label) break; return r; }
          if (r instanceof Cont) { if (r.label && r.label !== label) return r; continue; }
          if (r) return r;
        }
      } finally { this.scope = outer; }
      return null;
    }
    forInKeys(o) {
      if (typeof o === 'string') return [...o].map((_, i) => String(i));
      if (!isObj(o)) return [];
      const keys = [];
      const seen = new Set();
      for (let p = o; p; p = p.proto) {
        for (const k of this.ownKeys(p, true)) if (!seen.has(k)) { seen.add(k); keys.push(k); }
        if (p === this.ObjectProto || p === this.ArrayProto) break;
      }
      return keys;
    }
    execTry(s) {
      const fdepth = this.frames.length;
      const savedScope = this.scope;
      let result = null;
      try {
        result = this.execBlock(s.block);
      } catch (e) {
        let ex = e;
        if (e instanceof RangeError) { try { this.throwErr('RangeError', 'Maximum call stack size exceeded'); } catch (e2) { ex = e2; } }
        if (!(ex instanceof Throw) || !s.handler) { this.unwind(fdepth, savedScope); if (s.finalizer) { const fr = this.execBlock(s.finalizer); if (fr) return fr; } throw ex; }
        this.unwind(fdepth, savedScope);
        this.step(s.hline || s.line);
        this.rec.note('异常被 catch 捕获', 'info');
        const sc = new Scope(this.scope, 'block');
        const save = this.scope;
        this.scope = sc;
        try {
          if (s.param) this.bindPattern(s.param, ex.v, 'let', sc);
          result = this.execBlock(s.handler);
        } catch (e2) {
          this.scope = save;
          if (s.finalizer) { const fr = this.execBlock(s.finalizer); if (fr) return fr; }
          throw e2;
        } finally { this.scope = save; }
      }
      if (s.finalizer) { const fr = this.execBlock(s.finalizer); if (fr) return fr; }
      return result;
    }
    unwind(fdepth, scope) { while (this.frames.length > fdepth) this.frames.pop(); this.scope = scope; }

    // ================= functions =================
    makeFunction(node, scope, homeObject) {
      const f = new JSFunc(this.FunctionProto);
      f.node = node;
      f.env = scope;
      f.fname = node.name || '';
      f.homeObject = homeObject || null;
      if (!node.arrow && !node.isMethod) {
        const proto = this.newObject();
        proto.props.set('constructor', new Slot(f, false));
        f.props.set('prototype', new Slot(proto, false));
      }
      return f;
    }
    makeClass(c) {
      let parent = null, parentProto = this.ObjectProto;
      if (c.superClass) {
        parent = this.eval(c.superClass);
        if (parent === null) parentProto = null;
        else if (!(parent instanceof JSFunc)) this.throwErr('TypeError', 'Class extends value ' + this.inspect(parent) + ' is not a constructor or null');
        else parentProto = this.get(parent, 'prototype');
      }
      const classScope = new Scope(this.scope, 'block');
      const F = new JSFunc(parent || this.FunctionProto);
      F.fname = c.name || '';
      F.isClass = true;
      F.parentClass = parent;
      F.classScope = classScope;
      if (c.name) classScope.vars.set(c.name, { v: F, kind: 'const' });
      const proto = new JSO(parentProto);
      proto.props.set('constructor', new Slot(F, false));
      F.props.set('prototype', new Slot(proto, false));
      F.fields = [];
      F.line = c.line;
      const saveScope = this.scope;
      this.scope = classScope;
      try {
        for (const m of c.members) {
          if (m.kind === 'ctor') { F.node = m.fn; F.env = classScope; F.homeObject = proto; continue; }
          const key = m.computed ? this.toKey(this.eval(m.key)) : m.key;
          const target = m.isStatic ? F : proto;
          if (m.kind === 'field') {
            if (m.isStatic) {
              const fs = new Scope(classScope, 'fieldinit'); fs.thisVal = F;
              this.scope = fs; const v = m.init ? this.eval(m.init) : undefined; this.scope = classScope;
              F.props.set(key, new Slot(v));
            } else F.fields.push({ key, init: m.init });
            continue;
          }
          if (m.kind === 'staticBlock') { const fs = new Scope(classScope, 'fieldinit'); fs.thisVal = F; this.scope = fs; this.execBlock(m.body); this.scope = classScope; continue; }
          const fn = this.makeFunction(m.fn, classScope, target);
          fn.fname = key;
          if (m.kind === 'get' || m.kind === 'set') {
            const ex = target.props.get(key);
            const acc = ex && ex.acc ? ex : new Acc(null, null, false);
            if (m.kind === 'get') acc.get = fn; else acc.set = fn;
            target.props.set(key, acc);
          } else target.props.set(key, new Slot(fn, false));
        }
      } finally { this.scope = saveScope; }
      if (this.ts) F.paramProps = c.members.find(m => m.kind === 'ctor') ? c.members.find(m => m.kind === 'ctor').fn.params.paramProps : null;
      return F;
    }
    callFunction(f, thisV, args, newTarget, line) {
      if (!(f instanceof JSFunc)) {
        this.throwErr('TypeError', this.inspect(f) + ' is not a function');
      }
      if (f.native) { VER++; const r = f.native.call(this, thisV, args, newTarget); VER++; return r; }
      if (f.bound) return this.callFunction(f.bound.target, f.bound.thisV, f.bound.args.concat(args), newTarget, line);
      if (f.isClass && !newTarget) this.throwErr('TypeError', "Class constructor " + f.fname + " cannot be invoked without 'new'", '类需要用 new 来创建对象：new ' + f.fname + '(...)');
      if (this.frames.length > this.depthLimit) this.throwErr('RangeError', 'Maximum call stack size exceeded', '递归层数太深（可视化器上限 ' + this.depthLimit + ' 层）。检查递归函数是否有正确的终止条件（base case）。');
      const node = f.node;
      const sc = new Scope(f.env, 'function');
      sc.fn = f;
      if (node && node.arrow) sc.arrow = true;
      else { sc.thisVal = thisV; sc.newTarget = newTarget; sc.homeObject = f.homeObject; }
      const name = this.funcDisplayName(f, thisV);
      const frame = { id: 'f' + (++NID), name, scope: sc, fnScope: sc, fn: f, line: node ? node.line : 0, callLine: this.curLine, thisV: node && !node.arrow ? thisV : undefined };
      if (node && node.gen) frame.yields = [];
      // arguments object
      if (node && !node.arrow) { const a = this.newArray(args.slice()); sc.vars.set('arguments', { v: a, kind: 'var', hidden: true }); }
      this.frames.push(frame);
      VER++;
      // params
      if (node) {
        node.params.forEach((p, i) => {
          if (p.type === 'Rest') this.bindPattern(p.arg, this.newArray(args.slice(i)), 'let', sc);
          else this.bindPattern(p, args[i], 'let', sc);
        });
        if (f.isClass && f.paramProps) for (const pn of f.paramProps) this.put(thisV, pn, sc.vars.get(pn).v);
        this.hoist(node.body.body, sc, true);
      }
      const shown = node ? node.params.map((p, i) => this.shortInspect(args[i])) : [];
      let msg = (newTarget ? 'new ' : '调用 ') + name + '(' + shown.join(', ') + ')';
      const depth = this.frames.filter(fr => fr.fn === f).length;
      if (depth > 1) msg += '（递归，第 ' + depth + ' 层）';
      this.rec.note(msg, 'call');
      this.step(node ? node.line : this.curLine, 'call');
      if (newTarget && f.isClass && !f.parentClass) this.initFields(f, thisV);
      let r = node ? this.execList(node.body.body) : null;
      let rv = r instanceof Ret ? r.v : undefined;
      if (frame.yields) { rv = new JSGen(this.GenProto, frame.yields); this.rec.note('（生成器函数被一次性执行完，产生了 ' + frame.yields.length + ' 个值）', 'info'); }
      frame.retVal = rv;
      frame.returning = true;
      if (!(newTarget && rv === undefined)) this.rec.note(name + ' 返回 ' + this.shortInspect(rv), 'ret');
      this.step(r instanceof Ret ? r.line : (node ? node.endLine || node.line : this.curLine), 'return');
      this.frames.pop();
      VER++;
      return rv;
    }
    funcDisplayName(f, thisV) {
      if (f.isClass) return f.fname + '.constructor';
      if (f.homeObject && f.homeObject !== this.ObjectProto) {
        const ctor = f.homeObject instanceof JSFunc ? f.homeObject : (f.homeObject.props.get('constructor') ? f.homeObject.props.get('constructor').v : null);
        if (ctor && ctor.fname) return ctor.fname + '.' + (f.fname || '');
      }
      return f.fname || '(匿名函数)';
    }
    initFields(F, obj) {
      if (!F.fields || !F.fields.length) return;
      const fs = new Scope(F.classScope, 'fieldinit');
      fs.thisVal = obj;
      const save = this.scope;
      this.scope = fs;
      try { for (const fd of F.fields) this.put(obj, fd.key, fd.init ? this.eval(fd.init) : undefined, true); }
      finally { this.scope = save; }
    }
    construct(F, args, line) {
      if (!(F instanceof JSFunc)) this.throwErr('TypeError', this.inspect(F) + ' is not a constructor');
      if (F.native) {
        if (F.noNew) this.throwErr('TypeError', F.fname + ' is not a constructor');
        return F.native.call(this, undefined, args, F);
      }
      if (F.node && F.node.arrow) this.throwErr('TypeError', (F.fname || 'anonymous') + ' is not a constructor', '箭头函数不能用 new 调用。');
      const protoV = this.get(F, 'prototype');
      // find the root native ancestor (Error etc.)
      let obj = new JSO(isObj(protoV) ? protoV : this.ObjectProto);
      if (this.inheritsFrom(F, this.globalScope.parent.vars.get('Error').v)) { obj.props.set('message', new Slot('', false)); }
      if (this.inheritsFrom(F, this.ArrayCtor)) { const a = new JSArr(obj.proto, []); obj = a; }
      if (this.inheritsFrom(F, this.MapCtor)) { const a = new JSMap(obj.proto); obj = a; }
      if (this.inheritsFrom(F, this.SetCtor)) { const a = new JSSet(obj.proto); obj = a; }
      obj.born = this.rec.steps.length;
      const r = this.runCtor(F, obj, args, line);
      if (isObj(r)) return r;
      return obj;
    }
    inheritsFrom(F, base) { for (let c = F; c; c = c.parentClass || null) if (c === base) return true; return false; }
    runCtor(F, obj, args, line) {
      if (F.native) { F.native.call(this, obj, args, F, true); return obj; }
      if (!F.node) {
        // default constructor
        if (F.parentClass) { this.runCtor(F.parentClass, obj, args, line); }
        if (F.isClass) this.initFields(F, obj);
        return obj;
      }
      return this.callFunction(F, obj, args, F, line);
    }

    // ================= expressions =================
    eval(e) {
      switch (e.type) {
        case 'Num': return e.v;
        case 'Str': return e.v;
        case 'Bool': return e.v;
        case 'Null': return null;
        case 'Undef': return undefined;
        case 'Id': return this.getVar(e.name);
        case 'This': {
          const s = this.thisScope();
          if (s.kind === 'global') return undefined;
          if (s.thisUninit) this.throwErr('ReferenceError', "Must call super constructor in derived class before accessing 'this'");
          return s.thisVal;
        }
        case 'Tpl': {
          let s = e.quasis[0];
          e.exprs.forEach((x, i) => { s += this.toStr(this.eval(x)) + e.quasis[i + 1]; });
          return s;
        }
        case 'Regex': { let re; try { re = new RegExp(e.body, e.flags); } catch (er) { this.throwErr('SyntaxError', 'Invalid regular expression: /' + e.body + '/'); } return new JSRegExp(this.RegExpProto, re); }
        case 'Array': {
          const items = [];
          for (const x of e.elems) {
            if (x === null) items.push(HOLE);
            else if (x.type === 'Spread') { const next = this.iterator(this.eval(x.arg)); for (;;) { const r = next(); if (r.done) break; items.push(r.value); } }
            else items.push(this.eval(x));
          }
          return this.newArray(items);
        }
        case 'Object': {
          const o = this.newObject();
          for (const p of e.props) {
            if (p.spread) { const src = this.eval(p.value); if (isObj(src)) for (const k of this.ownKeys(src)) o.props.set(k, new Slot(this.get(src, k))); else if (typeof src === 'string') [...src].forEach((c, i) => o.props.set(String(i), new Slot(c))); continue; }
            const key = p.computed ? this.toKey(this.eval(p.key)) : p.key;
            if (p.kind === 'get' || p.kind === 'set') {
              const fn = this.makeFunction(p.value, this.scope, o);
              const ex = o.props.get(key);
              const acc = ex && ex.acc ? ex : new Acc(null, null, true);
              if (p.kind === 'get') acc.get = fn; else acc.set = fn;
              o.props.set(key, acc);
              continue;
            }
            let v;
            if (p.kind === 'method') { v = this.makeFunction(p.value, this.scope, o); v.fname = key; }
            else { v = this.eval(p.value); if (v instanceof JSFunc && !v.fname) v.fname = key; }
            o.props.set(key, new Slot(v));
          }
          return o;
        }
        case 'Function': {
          const f = this.makeFunction(e, this.scope);
          if (e.arrow) f.isArrow = true;
          return f;
        }
        case 'Class': return this.makeClass(e);
        case 'Unary': return this.evalUnary(e);
        case 'Update': {
          const old = this.toNumeric(this.eval(e.arg));
          const nv = typeof old === 'bigint' ? (e.op === '++' ? old + 1n : old - 1n) : (e.op === '++' ? old + 1 : old - 1);
          this.assignTo(e.arg, nv);
          return e.prefix ? nv : old;
        }
        case 'Binary': return this.binop(e.op, this.eval(e.left), this.eval(e.right), e);
        case 'Logical': {
          const l = this.eval(e.left);
          if (e.op === '&&') return this.truthy(l) ? this.eval(e.right) : l;
          if (e.op === '||') return this.truthy(l) ? l : this.eval(e.right);
          return l === null || l === undefined ? this.eval(e.right) : l;
        }
        case 'Cond': return this.truthy(this.eval(e.test)) ? this.eval(e.cons) : this.eval(e.alt);
        case 'Assign': return this.evalAssign(e);
        case 'Seq': { let v; for (const x of e.list) v = this.eval(x); return v; }
        case 'Member': {
          const r = this.evalMember(e);
          return r.short ? undefined : r.v;
        }
        case 'Call': return this.evalCall(e);
        case 'New': {
          const F = this.eval(e.callee);
          const args = this.evalArgs(e.args);
          if (!(F instanceof JSFunc)) this.throwErr('TypeError', this.exprText(e.callee) + ' is not a constructor');
          return this.construct(F, args, e.line);
        }
        case 'Super': this.throwErr('SyntaxError', "'super' keyword unexpected here");
        case 'Yield': {
          const fr = this.frames.slice().reverse().find(f => f.yields);
          if (!fr) this.throwErr('SyntaxError', 'yield 只能在生成器函数（function*）里使用');
          if (e.delegate) { const next = this.iterator(this.eval(e.arg)); for (;;) { const r = next(); if (r.done) break; fr.yields.push(r.value); } }
          else fr.yields.push(e.arg ? this.eval(e.arg) : undefined);
          return undefined;
        }
      }
      throw new RunError('暂不支持的表达式：' + e.type, 'runtime');
    }
    exprText(e) {
      switch (e.type) {
        case 'Id': return e.name;
        case 'Member': return this.exprText(e.obj) + (e.computed ? '[' + this.exprText(e.prop) + ']' : (e.optional ? '?.' : '.') + e.prop.v);
        case 'This': return 'this';
        case 'Call': return this.exprText(e.callee) + '(...)';
        case 'Num': return String(e.v);
        case 'Str': return JSON.stringify(e.v);
      }
      return '表达式';
    }
    evalArgs(args) {
      const out = [];
      for (const a of args) {
        if (a.type === 'Spread') { const next = this.iterator(this.eval(a.arg)); for (;;) { const r = next(); if (r.done) break; out.push(r.value); } }
        else out.push(this.eval(a));
      }
      return out;
    }
    evalMember(e) {
      if (e.obj.type === 'Super') {
        const s = this.thisScope();
        const home = this.findHome();
        const key = e.computed ? this.toKey(this.eval(e.prop)) : e.prop.v;
        const base = home ? home.proto : null;
        return { v: base ? this.get(base, key, s.thisVal) : undefined, obj: s.thisVal };
      }
      const obj = this.eval(e.obj);
      if (e.optional && (obj === null || obj === undefined)) return { short: true };
      const key = e.computed ? this.toKey(this.eval(e.prop)) : e.prop.v;
      if (obj === null || obj === undefined) this.throwErr('TypeError', "Cannot read properties of " + obj + " (reading '" + key + "')", this.nullHint(e.obj, obj));
      if (obj instanceof JSArr && e.computed && /^\d+$/.test(key) && Number(key) >= obj.items.length) {
        const wk = 'oob' + e.line;
        if (!this.warned.has(wk)) { this.warned.add(wk); this.rec.note('⚠ 下标 ' + key + ' 超出了数组长度 ' + obj.items.length + '，JavaScript 不会报错，而是得到 undefined。', 'warn'); }
      }
      return { v: this.get(obj, key), obj };
    }
    nullHint(objExpr, v) {
      const t = this.exprText(objExpr);
      return '“' + t + '” 的值是 ' + v + '，不能读取它的属性。常见原因：链表遍历走到了末尾（null）还继续访问 .next；数组下标越界得到了 undefined；或者函数忘记 return。';
    }
    findHome() { for (let s = this.scope; s; s = s.parent) if (s.kind === 'function' && !s.arrow) return s.homeObject; return null; }
    evalCall(e) {
      const c = e.callee;
      if (c.type === 'Super') {
        // super(...) in derived constructor
        const s = this.thisScope();
        const F = s.fn;
        if (!F || !F.parentClass) this.throwErr('SyntaxError', "'super' keyword unexpected here");
        const args = this.evalArgs(e.args);
        this.runCtor(F.parentClass, s.thisVal, args, e.line);
        this.initFields(F, s.thisVal);
        return undefined;
      }
      let fn, thisV;
      if (c.type === 'Member') {
        const r = this.evalMember(c);
        if (r.short) return undefined;
        fn = r.v; thisV = r.obj;
        if (e.optional && (fn === null || fn === undefined)) return undefined;
        if (!(fn instanceof JSFunc)) {
          const key = c.computed ? '[...]' : c.prop.v;
          let hint = '';
          if (thisV instanceof JSArr && key === 'add') hint = '数组添加元素用 push()。';
          else if (thisV instanceof JSArr && key === 'size') hint = '数组的长度是 arr.length（属性，不是方法）。';
          else if (thisV instanceof JSMap && key === 'length') hint = 'Map 的大小是 map.size。';
          else if (fn === undefined) hint = '对象上没有名为 ' + key + ' 的方法。检查方法名拼写，或者它是否定义在类里。';
          this.throwErr('TypeError', this.exprText(c) + ' is not a function', hint);
        }
      } else {
        fn = this.eval(c);
        if (e.optional && (fn === null || fn === undefined)) return undefined;
        thisV = undefined;
        if (!(fn instanceof JSFunc)) this.throwErr('TypeError', this.exprText(c) + ' is not a function');
      }
      const args = this.evalArgs(e.args);
      return this.callFunction(fn, thisV, args, undefined, e.line);
    }
    evalAssign(e) {
      const t = e.target;
      if (e.op === '=') {
        const v = this.evalNamed(e.right, t);
        if (t.type === 'ArrPat' || t.type === 'ObjPat') { this.bindPattern(t, v, null); return v; }
        this.assignTo(t, v);
        return v;
      }
      if (e.op === '&&=' || e.op === '||=' || e.op === '??=') {
        const cur = this.eval(t);
        const go = e.op === '&&=' ? this.truthy(cur) : e.op === '||=' ? !this.truthy(cur) : (cur === null || cur === undefined);
        if (!go) return cur;
        const v = this.eval(e.right); this.assignTo(t, v); return v;
      }
      if (t.type === 'Member') {
        const obj = this.eval(t.obj);
        const key = t.computed ? this.toKey(this.eval(t.prop)) : t.prop.v;
        if (obj === null || obj === undefined) this.throwErr('TypeError', "Cannot read properties of " + obj + " (reading '" + key + "')", this.nullHint(t.obj, obj));
        const cur = this.get(obj, key);
        const v = this.binop(e.op.slice(0, -1), cur, this.eval(e.right), e);
        this.put(obj, key, v);
        return v;
      }
      const cur = this.eval(t);
      const v = this.binop(e.op.slice(0, -1), cur, this.eval(e.right), e);
      this.assignTo(t, v);
      return v;
    }
    assignTo(t, v) {
      if (t.type === 'Id') { this.setVar(t.name, v); return; }
      if (t.type === 'Member') {
        if (t.obj.type === 'Super') { const s = this.thisScope(); this.put(s.thisVal, t.computed ? this.toKey(this.eval(t.prop)) : t.prop.v, v); return; }
        const obj = this.eval(t.obj);
        const key = t.computed ? this.toKey(this.eval(t.prop)) : t.prop.v;
        if (obj === null || obj === undefined) this.throwErr('TypeError', "Cannot set properties of " + obj + " (setting '" + key + "')", '“' + this.exprText(t.obj) + '” 的值是 ' + obj + '，不能给它的属性赋值。检查对象是否已经创建。');
        this.put(obj, key, v);
        return;
      }
      this.bindPattern(t, v, null);
    }
    evalUnary(e) {
      if (e.op === 'typeof') {
        if (e.arg.type === 'Id' && !this.lookupRef(e.arg.name)) return 'undefined';
        return this.typeOf(this.eval(e.arg));
      }
      if (e.op === 'delete') {
        if (e.arg.type !== 'Member') return true;
        const obj = this.eval(e.arg.obj);
        const key = e.arg.computed ? this.toKey(this.eval(e.arg.prop)) : e.arg.prop.v;
        if (obj instanceof JSArr && /^\d+$/.test(key)) { VER++; if (Number(key) < obj.items.length) obj.items[Number(key)] = HOLE; return true; }
        if (isObj(obj)) { if (obj.frozen) return false; obj.props.delete(key); }
        return true;
      }
      const v = this.eval(e.arg);
      switch (e.op) {
        case '!': return !this.truthy(v);
        case '-': { const n = this.toNumeric(v); return -n; }
        case '+': return this.toNum(v);
        case '~': { const n = this.toNumeric(v); return typeof n === 'bigint' ? ~n : ~n; }
        case 'void': return undefined;
      }
    }
    typeOf(v) {
      if (v === null) return 'object';
      if (v instanceof JSFunc) return 'function';
      if (isObj(v)) return 'object';
      return typeof v;
    }

    // ================= conversions =================
    truthy(v) {
      if (isObj(v)) return true;
      return !!v;
    }
    toPrimitive(v, hint) {
      if (!isObj(v)) return v;
      const order = hint === 'string' ? ['toString', 'valueOf'] : ['valueOf', 'toString'];
      for (const m of order) {
        const f = this.get(v, m);
        if (f instanceof JSFunc) { const r = this.callFunction(f, v, []); if (!isObj(r)) return r; }
      }
      this.throwErr('TypeError', 'Cannot convert object to primitive value');
    }
    toNum(v) {
      if (typeof v === 'number') return v;
      if (v === undefined) return NaN;
      if (v === null) return 0;
      if (typeof v === 'boolean') return v ? 1 : 0;
      if (typeof v === 'string') { const s = v.trim(); if (s === '') return 0; if (/^0[xX][0-9a-fA-F]+$/.test(s)) return parseInt(s, 16); return /^[-+]?(\d+\.?\d*|\.\d+)([eE][-+]?\d+)?$|^[-+]?Infinity$/.test(s) ? Number(s) : NaN; }
      if (typeof v === 'bigint') this.throwErr('TypeError', 'Cannot convert a BigInt value to a number');
      return this.toNum(this.toPrimitive(v, 'number'));
    }
    toNumeric(v) { if (typeof v === 'bigint') return v; const p = isObj(v) ? this.toPrimitive(v, 'number') : v; return typeof p === 'bigint' ? p : this.toNum(p); }
    toStr(v) {
      if (typeof v === 'string') return v;
      if (v === undefined) return 'undefined';
      if (v === null) return 'null';
      if (typeof v === 'number') return numStr(v);
      if (typeof v === 'boolean' || typeof v === 'bigint') return String(v);
      return this.toStr(this.toPrimitive(v, 'string'));
    }
    toKey(v) { if (typeof v === 'string') return v; if (typeof v === 'number') return numStr(v); if (isObj(v) && v.isSymbol) return v.key; return this.toStr(v); }
    strictEq(a, b) { return a === b; }
    looseEq(a, b) {
      if (a === b) return true;
      if ((a === null || a === undefined) && (b === null || b === undefined)) return true;
      if (a === null || a === undefined || b === null || b === undefined) return false;
      if (isObj(a) && isObj(b)) return false;
      if (typeof a === 'number' && typeof b === 'string') return a === this.toNum(b);
      if (typeof a === 'string' && typeof b === 'number') return this.toNum(a) === b;
      if (typeof a === 'bigint' || typeof b === 'bigint') { try { return BigInt(a) === BigInt(b); } catch (e) { return false; } }
      if (typeof a === 'boolean') return this.looseEq(a ? 1 : 0, b);
      if (typeof b === 'boolean') return this.looseEq(a, b ? 1 : 0);
      if (isObj(a)) return this.looseEq(this.toPrimitive(a), b);
      if (isObj(b)) return this.looseEq(a, this.toPrimitive(b));
      return false;
    }
    binop(op, a, b, e) {
      switch (op) {
        case '===': return a === b;
        case '!==': return a !== b;
        case '==': return this.looseEq(a, b);
        case '!=': return !this.looseEq(a, b);
        case 'instanceof': {
          if (!(b instanceof JSFunc)) this.throwErr('TypeError', "Right-hand side of 'instanceof' is not callable");
          if (!isObj(a)) return false;
          const proto = this.get(b, 'prototype');
          for (let p = a.proto; p; p = p.proto) if (p === proto) return true;
          return false;
        }
        case 'in': {
          if (!isObj(b)) this.throwErr('TypeError', "Cannot use 'in' operator to search for '" + this.toStr(a) + "' in " + this.toStr(b));
          return this.hasProp(b, this.toKey(a));
        }
        case '+': {
          const pa = this.toPrimitive(a), pb = this.toPrimitive(b);
          if (typeof pa === 'string' || typeof pb === 'string') return this.toStr(pa) + this.toStr(pb);
          if (typeof pa === 'bigint' && typeof pb === 'bigint') return pa + pb;
          if (typeof pa === 'bigint' || typeof pb === 'bigint') this.throwErr('TypeError', 'Cannot mix BigInt and other types, use explicit conversions');
          return this.toNum(pa) + this.toNum(pb);
        }
        case '<': case '>': case '<=': case '>=': {
          const pa = this.toPrimitive(a, 'number'), pb = this.toPrimitive(b, 'number');
          let r;
          if (typeof pa === 'string' && typeof pb === 'string') r = pa < pb ? -1 : pa > pb ? 1 : 0;
          else { const x = typeof pa === 'bigint' ? pa : this.toNum(pa), y = typeof pb === 'bigint' ? pb : this.toNum(pb); if (Number.isNaN(x) || Number.isNaN(y)) return false; r = x < y ? -1 : x > y ? 1 : 0; }
          return op === '<' ? r < 0 : op === '>' ? r > 0 : op === '<=' ? r <= 0 : r >= 0;
        }
      }
      const x = this.toNumeric(a), y = this.toNumeric(b);
      if (typeof x === 'bigint' || typeof y === 'bigint') {
        if (typeof x !== 'bigint' || typeof y !== 'bigint') this.throwErr('TypeError', 'Cannot mix BigInt and other types, use explicit conversions');
        switch (op) {
          case '-': return x - y; case '*': return x * y;
          case '/': if (y === 0n) this.throwErr('RangeError', 'Division by zero'); return x / y;
          case '%': if (y === 0n) this.throwErr('RangeError', 'Division by zero'); return x % y;
          case '**': return x ** y; case '&': return x & y; case '|': return x | y; case '^': return x ^ y; case '<<': return x << y; case '>>': return x >> y;
        }
      }
      switch (op) {
        case '-': return x - y; case '*': return x * y; case '/': return x / y; case '%': return x % y; case '**': return x ** y;
        case '&': return x & y; case '|': return x | y; case '^': return x ^ y;
        case '<<': return x << y; case '>>': return x >> y; case '>>>': return x >>> y;
      }
      throw new RunError('未知运算符 ' + op, 'runtime');
    }

    // ================= properties =================
    protoOf(v) {
      if (isObj(v)) return v.proto;
      switch (typeof v) {
        case 'string': return this.StringProto; case 'number': return this.NumberProto; case 'boolean': return this.BooleanProto; case 'bigint': return this.BigIntProto;
      }
      return null;
    }
    findSlot(o, key) {
      for (let p = o; p; p = p.proto) { const s = p.props.get(key); if (s) return s; }
      return null;
    }
    get(o, key, receiver) {
      if (typeof o === 'string') {
        if (key === 'length') return o.length;
        if (/^\d+$/.test(key)) { const i = Number(key); return i < o.length ? o[i] : undefined; }
        const s = this.findSlot(this.StringProto, key);
        return s ? (s.acc ? (s.get ? this.callFunction(s.get, o, []) : undefined) : s.v) : undefined;
      }
      if (!isObj(o)) {
        if (o === null || o === undefined) this.throwErr('TypeError', "Cannot read properties of " + o + " (reading '" + key + "')");
        const s = this.findSlot(this.protoOf(o), key);
        return s ? (s.acc ? (s.get ? this.callFunction(s.get, o, []) : undefined) : s.v) : undefined;
      }
      if (o instanceof JSArr) {
        if (key === 'length') return o.items.length;
        if (isIndex(key)) { const v = o.items[Number(key)]; return v === HOLE ? undefined : v; }
      }
      if (o instanceof JSFunc) {
        if (key === 'name' && !o.props.has('name')) return o.fname;
        if (key === 'length' && !o.props.has('length')) return o.node ? o.node.params.filter(p => p.type !== 'Rest' && p.type !== 'Default').length : 0;
      }
      if (o instanceof JSMap || o instanceof JSSet) { if (key === 'size') return o.m.size; }
      if (o instanceof JSRegExp) { if (key === 'source') return o.re.source; if (key === 'flags') return o.re.flags; if (key === 'lastIndex') return o.re.lastIndex; if (key === 'global') return o.re.global; }
      const s = this.findSlot(o, key);
      if (!s) return undefined;
      if (s.acc) return s.get ? this.callFunction(s.get, receiver || o, []) : undefined;
      return s.v;
    }
    hasProp(o, key) {
      if (o instanceof JSArr && (key === 'length' || (isIndex(key) && Number(key) < o.items.length && o.items[Number(key)] !== HOLE))) return true;
      return !!this.findSlot(o, key);
    }
    put(o, key, v, define) {
      VER++;
      if (!isObj(o)) {
        if (o === null || o === undefined) this.throwErr('TypeError', "Cannot set properties of " + o + " (setting '" + key + "')");
        this.throwErr('TypeError', "Cannot create property '" + key + "' on " + this.typeOf(o) + " '" + this.toStr(o) + "'", typeof o === 'string' ? '字符串是不可变的，不能修改其中的字符。' : undefined);
      }
      if (o.frozen) this.throwErr('TypeError', "Cannot assign to read only property '" + key + "' of object", '这个对象被 Object.freeze 冻结了。');
      if (o instanceof JSArr) {
        if (key === 'length') { const n = this.toNum(v); if (!Number.isInteger(n) || n < 0) this.throwErr('RangeError', 'Invalid array length'); if (n < o.items.length) o.items.length = n; else while (o.items.length < n) o.items.push(HOLE); return; }
        if (isIndex(key)) {
          const i = Number(key);
          if (i > o.items.length + 1e6) this.throwErr('RangeError', '数组下标太大');
          if (i >= o.items.length) {
            if (i > o.items.length) { const wk = 'gap' + this.curLine; if (!this.warned.has(wk)) { this.warned.add(wk); this.rec.note('⚠ 给数组下标 ' + i + ' 赋值，但数组长度只有 ' + o.items.length + '，中间会出现空位（empty）。', 'warn'); } }
            while (o.items.length < i) o.items.push(HOLE);
          }
          o.items[i] = v; return;
        }
      }
      if (!define) {
        const s = this.findSlot(o, key);
        if (s && s.acc) { if (!s.set) this.throwErr('TypeError', "Cannot set property " + key + " of " + this.inspect(o) + " which has only a getter"); this.callFunction(s.set, o, [v]); return; }
      }
      const own = o.props.get(key);
      if (own && !own.acc) { own.v = v; return; }
      if (o.sealed) this.throwErr('TypeError', 'Cannot add property ' + key + ', object is not extensible');
      o.props.set(key, new Slot(v));
    }
    ownKeys(o, enumOnly) {
      const out = [];
      if (o instanceof JSArr) o.items.forEach((v, i) => { if (v !== HOLE) out.push(String(i)); });
      const ints = [], strs = [];
      for (const [k, s] of o.props) {
        if (enumOnly !== false && !s.e) continue;
        if (k.startsWith('@@')) continue;
        if (isIndex(k)) ints.push(k); else strs.push(k);
      }
      ints.sort((a, b) => Number(a) - Number(b));
      return out.concat(ints, strs);
    }

    // ================= objects =================
    newObject() { return new JSO(this.ObjectProto); }
    newArray(items) { return new JSArr(this.ArrayProto, items); }
    mapKey(v) {
      if (isObj(v)) return 'o' + v.id;
      if (typeof v === 'number') return Number.isNaN(v) ? 'nNaN' : 'n' + (v === 0 ? 0 : v);
      return typeof v + ':' + String(v);
    }
    iterator(v) {
      if (v instanceof JSArr) { let i = 0; return () => { if (i >= v.items.length) return { done: true }; const x = v.items[i++]; return { value: x === HOLE ? undefined : x }; }; }
      if (typeof v === 'string') { const a = [...v]; let i = 0; return () => i < a.length ? { value: a[i++] } : { done: true }; }
      if (v instanceof JSMap) { const a = [...v.m.values()]; let i = 0; return () => i < a.length ? { value: this.newArray([a[i][0], a[i++][1]]) } : { done: true }; }
      if (v instanceof JSSet) { const a = [...v.m.values()]; let i = 0; return () => i < a.length ? { value: a[i++] } : { done: true }; }
      if (v instanceof JSGen) return () => { VER++; return v.i < v.items.length ? { value: v.items[v.i++] } : { done: true }; };
      if (isObj(v)) {
        const f = this.get(v, ITER);
        if (f instanceof JSFunc) {
          const it = this.callFunction(f, v, []);
          if (it instanceof JSGen) return () => it.i < it.items.length ? { value: it.items[it.i++] } : { done: true };
          const nx = this.get(it, 'next');
          return () => { const r = this.callFunction(nx, it, []); if (this.truthy(this.get(r, 'done'))) return { done: true }; return { value: this.get(r, 'value') }; };
        }
      }
      this.throwErr('TypeError', (v === null || v === undefined ? String(v) : this.shortInspect(v)) + ' is not iterable');
    }
    toArray(v) { const next = this.iterator(v); const out = []; for (;;) { const r = next(); if (r.done) break; out.push(r.value); if (out.length > 1e6) break; } return out; }

    runTimers() {
      if (!this.timers || !this.timers.length) return;
      this.rec.note('主程序执行完毕，开始执行 setTimeout 安排的回调（事件循环）', 'info');
      let guard = 0;
      while (this.timers.length && guard++ < 1000) {
        this.timers.sort((a, b) => a.t - b.t || a.seq - b.seq);
        const tm = this.timers.shift();
        this.callFunction(tm.fn, undefined, tm.args);
      }
    }
  }
  function isIndex(k) { return typeof k === 'string' && /^(0|[1-9]\d*)$/.test(k) && Number(k) < 4294967295; }
  function numStr(v) { if (Object.is(v, -0)) return '0'; return String(v); }

  DSV.JSInterp = JSInterp;
  DSV.jsRT = { ver: () => VER, bump: () => { VER++; }, JSO, JSArr, JSFunc, JSMap, JSSet, JSGen, JSRegExp, Slot, Acc, Throw, Scope, HOLE, isObj, isIndex, numStr, ITER, setCurStep: (n) => { CUR_STEP = n; } };
})(typeof window !== 'undefined' ? window : globalThis);
