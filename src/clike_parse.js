// ===== C / C++ / Java parser =====
(function (G) {
  const DSV = G.DSV;
  const { CompileError } = DSV;

  // ---------- types ----------
  const T = {};
  function prim(name, size, signed, fl, extra) { return Object.assign({ k: 'prim', name, size, align: size, signed, fl: !!fl }, extra || {}); }
  T.char = prim('char', 1, true);
  T.schar = prim('signed char', 1, true);
  T.uchar = prim('unsigned char', 1, false);
  T.short = prim('short', 2, true);
  T.ushort = prim('unsigned short', 2, false);
  T.int = prim('int', 4, true);
  T.uint = prim('unsigned int', 4, false);
  T.long = prim('long', 8, true);
  T.ulong = prim('unsigned long', 8, false);
  T.llong = prim('long long', 8, true);
  T.ullong = prim('unsigned long long', 8, false);
  T.size_t = prim('size_t', 8, false);
  T.float = prim('float', 4, true, true);
  T.double = prim('double', 8, true, true);
  T.ldouble = prim('long double', 8, true, true);
  T.bool = prim('bool', 1, false, false, { isBool: true });
  T.jboolean = prim('boolean', 1, false, false, { isBool: true });
  T.jchar = prim('char', 2, false, false, { isChar: true });
  T.byte = prim('byte', 1, true);
  T.char.isChar = true; T.schar.isChar = true; T.uchar.isChar = true;
  T.void = { k: 'void', name: 'void', size: 1, align: 1 };
  T.string = { k: 'string', name: 'string', size: 32, align: 8 };
  T.jstring = { k: 'string', name: 'String', size: 8, align: 8, java: true };
  T.any = { k: 'any', name: 'Object', size: 8, align: 8 };
  T.auto = { k: 'auto', name: 'auto', size: 8, align: 8 };
  T.nullptr = { k: 'nullptr', name: 'nullptr_t', size: 8, align: 8 };
  T.ptr = (to, extra) => Object.assign({ k: 'ptr', to, size: 8, align: 8 }, extra || {});
  T.arr = (of, len, lenExpr) => ({ k: 'arr', of, len, lenExpr });
  T.ref = (to) => ({ k: 'ref', to, size: 8, align: 8 });
  T.func = (ret, params) => ({ k: 'func', ret, params, size: 8, align: 8 });
  T.cont = (name, args) => ({ k: 'cont', name, args: args || [], size: 24, align: 8 });
  T.stream = (name) => ({ k: 'stream', name, size: 8, align: 8 });

  const CONTAINERS_CPP = new Set(['vector', 'stack', 'queue', 'deque', 'list', 'map', 'unordered_map', 'set', 'unordered_set', 'priority_queue', 'pair', 'multiset', 'multimap']);
  const CONTAINERS_JAVA = new Set(['ArrayList', 'List', 'LinkedList', 'Stack', 'Deque', 'ArrayDeque', 'Queue', 'PriorityQueue', 'HashMap', 'Map', 'TreeMap', 'LinkedHashMap', 'HashSet', 'Set', 'TreeSet', 'LinkedHashSet', 'StringBuilder', 'Scanner', 'Iterator', 'Random', 'Collection', 'Vector']);
  const JAVA_ANY = new Set(['Integer', 'Long', 'Short', 'Byte', 'Double', 'Float', 'Character', 'Boolean', 'Object', 'Number', 'Comparable', 'Map.Entry', 'Entry']);

  function typeName(t) {
    if (!t) return '?';
    switch (t.k) {
      case 'prim': return t.name;
      case 'ptr':
        if (t.jarr) return typeName(t.to) + '[]';
        if (t.jref) return typeName(t.to);
        if (t.to.k === 'func') return typeName(t.to.ret) + ' (*)(' + t.to.params.map(typeName).join(', ') + ')';
        { const inner = typeName(t.to); return inner + (inner.endsWith('*') ? '*' : ' *'); }
      case 'arr': return typeName(t.of) + '[' + (t.len != null ? t.len : '') + ']';
      case 'ref': return typeName(t.to) + ' &';
      case 'struct': return t.typedefName || ((t.tag === 'struct' && !t.cpp && !t.java ? 'struct ' : (t.tag === 'union' ? 'union ' : '')) + t.name);
      case 'cont': return t.name + (t.args.length ? '<' + t.args.map(typeName).join(', ') + '>' : '');
      case 'func': return typeName(t.ret) + '(' + t.params.map(typeName).join(', ') + ')';
      default: return t.name || t.k;
    }
  }
  T.name = typeName;

  // ---------- parser ----------
  const C_TYPE_KW = new Set(['void', 'char', 'short', 'int', 'long', 'float', 'double', 'signed', 'unsigned', '_Bool', 'bool', 'size_t', 'struct', 'union', 'enum', 'const', 'volatile', 'static', 'extern', 'register', 'inline', 'auto', 'uint8_t', 'uint16_t', 'uint32_t', 'uint64_t', 'int8_t', 'int16_t', 'int32_t', 'int64_t', 'BYTE', 'WORD', 'DWORD', 'LONG', 'ssize_t', 'ptrdiff_t', 'FILE', 'string', 'class', 'mutable', 'virtual', 'explicit', 'constexpr', 'typename', 'unsigned', 'wchar_t', 'char16_t', 'char32_t', 'friend']);
  const J_PRIMS = { int: T.int, long: T.long, short: T.short, byte: T.byte, double: T.double, float: T.float, boolean: T.jboolean, char: T.jchar, void: T.void };
  const J_MODS = new Set(['public', 'private', 'protected', 'static', 'final', 'abstract', 'synchronized', 'transient', 'volatile', 'native', 'strictfp', 'default', 'sealed', 'non-sealed']);

  class Parser {
    constructor(toks, dialect) {
      this.toks = toks; this.p = 0; this.d = dialect;
      this.typedefs = new Map();
      this.structs = new Map();   // tag name -> struct type
      this.enumConsts = new Map();
      this.funcs = [];
      this.globals = [];
      this.classes = [];          // struct types with methods (C++/Java)
      this.tplParams = [];        // stack of sets of template param names
      this.protos = new Map();
      this.prescan();
    }
    // ---- token helpers ----
    peek(o) { return this.toks[Math.min(this.p + (o || 0), this.toks.length - 1)]; }
    next() { return this.toks[this.p++] || this.toks[this.toks.length - 1]; }
    is(v, o) { const t = this.peek(o); return (t.t === 'op' || t.t === 'id') && t.v === v; }
    isId(o) { return this.peek(o).t === 'id'; }
    accept(v) { if (this.is(v)) { return this.next(); } return null; }
    expect(v, what) {
      if (this.is(v)) return this.next();
      const t = this.peek();
      throw new CompileError('这里应该是 “' + v + '”' + (what ? '（' + what + '）' : '') + '，但遇到了 “' + t.v + '”', t.line, t.col);
    }
    ident(what) {
      const t = this.peek();
      if (t.t !== 'id') throw new CompileError('这里应该是一个名字' + (what ? '（' + what + '）' : '') + '，但遇到了 “' + t.v + '”', t.line, t.col);
      this.p++; return t.v;
    }
    err(msg, t) { t = t || this.peek(); throw new CompileError(msg, t.line, t.col); }
    line() { return this.peek().line; }

    prescan() {
      for (let i = 0; i < this.toks.length - 1; i++) {
        const t = this.toks[i], n = this.toks[i + 1];
        if (t.t === 'id' && (t.v === 'class' || t.v === 'struct' || t.v === 'interface' || t.v === 'enum' || t.v === 'record') && n.t === 'id') {
          if (this.d === 'c' && t.v !== 'class') continue;
          if (this.d === 'java' || this.d === 'cpp') {
            if (!this.structs.has(n.v)) {
              if (t.v === 'enum') { this.structs.set(n.v, { k: 'enumT', name: n.v }); continue; }
              this.structs.set(n.v, this.newStruct(n.v, t.v === 'interface' ? 'interface' : (t.v === 'struct' ? 'struct' : 'class')));
            }
          }
        }
      }
    }
    newStruct(name, tag) {
      return { k: 'struct', name, tag, fields: [], methods: new Map(), ctors: [], dtor: null, base: null, complete: false, size: 0, align: 1, cpp: this.d === 'cpp', java: this.d === 'java', staticFields: [], staticInit: [], fieldInits: [], isInterface: tag === 'interface' };
    }

    isTplParam(name) { for (const s of this.tplParams) if (s.has(name)) return true; return false; }

    // is the token at offset o the start of a type?
    isTypeStart(o) {
      o = o || 0;
      const t = this.peek(o);
      if (t.t !== 'id') return false;
      const v = t.v;
      if (this.d === 'java') {
        if (J_PRIMS[v] || v === 'var' || v === 'final') return true;
        if (v === 'String' || JAVA_ANY.has(v) || CONTAINERS_JAVA.has(v) || this.isTplParam(v)) return true;
        const s = this.structs.get(v); if (s) return true;
        return false;
      }
      if (C_TYPE_KW.has(v)) {
        if (v === 'string' && this.d === 'c' && !this.typedefs.has('string')) return false;
        if (v === 'class' && this.d === 'c') return false;
        return true;
      }
      if (this.typedefs.has(v)) return true;
      if (this.d === 'cpp') {
        if (v === 'std' && this.is('::', o + 1)) return this.isTypeStart(o + 2);
        if (CONTAINERS_CPP.has(v) || v === 'string' || v === 'ostream' || v === 'istream') return true;
        if (this.structs.has(v)) return true;
        if (this.isTplParam(v)) return true;
      }
      return false;
    }

    // ================= C / C++ =================
    parseProgram() {
      if (this.d === 'java') return this.parseJavaProgram();
      const decls = [];
      while (this.peek().t !== 'eof') this.parseTopDecl(decls);
      return this.result(decls);
    }
    result(decls) {
      return { decls, funcs: this.funcs, globals: this.globals, structs: this.structs, typedefs: this.typedefs, enumConsts: this.enumConsts, classes: this.classes, dialect: this.d, protos: this.protos };
    }

    parseTopDecl(decls) {
      if (this.accept(';')) return;
      const line = this.line();
      if (this.is('using')) { while (!this.is(';') && this.peek().t !== 'eof') this.next(); this.accept(';'); return; }
      if (this.is('namespace')) {
        this.next(); if (this.isId()) this.next(); this.expect('{');
        while (!this.is('}') && this.peek().t !== 'eof') this.parseTopDecl(decls);
        this.expect('}'); return;
      }
      if (this.is('extern') && this.peek(1).t === 'str') { this.next(); this.next(); if (this.accept('{')) { while (!this.is('}')) this.parseTopDecl(decls); this.expect('}'); } return; }
      if (this.is('template')) {
        this.next(); this.expect('<');
        const names = new Set();
        while (!this.is('>')) {
          if (this.accept('typename') || this.accept('class')) { names.add(this.ident('模板参数')); if (this.accept('=')) this.parseType(); }
          else { this.parseType(); if (this.isId()) this.next(); }
          if (!this.accept(',')) break;
        }
        this.expect('>');
        this.tplParams.push(names);
        try { this.parseTopDecl(decls); } finally { this.tplParams.pop(); }
        return;
      }
      if (this.is('typedef')) { this.parseTypedef(); return; }
      // out-of-class constructor / destructor:  Name::Name(...)  or Name::~Name()
      if (this.d === 'cpp' && this.isId() && this.is('::', 1) && this.structs.get(this.peek().v) && this.structs.get(this.peek().v).k === 'struct') {
        const cname = this.peek().v;
        if ((this.peek(2).v === cname && this.is('(', 3)) || (this.is('~', 2) && this.peek(3).v === cname)) {
          this.next(); this.next();
          const isD = !!this.accept('~'); this.next();
          const st = this.structs.get(cname);
          const f = this.parseFuncRest(isD ? '~' + cname : cname, T.void, line, st, { isCtor: !isD, isDtor: isD });
          return;
        }
      }
      const spec = this.parseDeclSpec();
      if (this.accept(';')) return; // struct/enum definition only
      let first = true;
      for (;;) {
        const dl = this.line();
        const d = this.parseDeclarator(spec.type, true);
        if (d.isFunc) {
          if (this.is('{') || this.is(':') && d.ownerClass) {
            this.finishFunc(d, spec, dl);
            return;
          }
          // prototype
          this.protos.set(d.name, d);
          if (this.accept(',')) continue;
          this.expect(';'); return;
        }
        const init = this.parseInitializer(d.type);
        const g = { type: 'VarDecl', name: d.name, vtype: d.type, init: init.init, ctorArgs: init.ctorArgs, line: dl, isStatic: spec.isStatic, isConst: spec.isConst };
        if (d.ownerClass) { g.ownerClass = d.ownerClass; }
        this.globals.push(g);
        if (this.accept(',')) { first = false; continue; }
        this.expect(';', '声明结尾');
        return;
      }
    }

    finishFunc(d, spec, line) {
      const owner = d.ownerClass;
      const fn = this.parseFuncRest(d.name, d.type.ret, line, owner, { params: d.params, isStatic: spec.isStatic, preParsedParams: true });
      return fn;
    }

    // parses params (unless preParsed) and body
    parseFuncRest(name, ret, line, owner, opts) {
      opts = opts || {};
      let params = opts.params;
      if (!opts.preParsedParams) { params = this.parseParams(); }
      // trailing qualifiers
      while (this.is('const') || this.is('override') || this.is('noexcept') || this.is('final')) this.next();
      if (this.accept('->')) this.parseType(); // trailing return type
      let initList = null;
      if (this.accept(':')) {
        initList = [];
        do {
          const il = this.line();
          const nm = this.ident('初始化列表成员');
          let args;
          if (this.accept('{')) { args = this.parseArgs('}'); }
          else { this.expect('('); args = this.parseArgs(')'); }
          initList.push({ name: nm, args, line: il });
        } while (this.accept(','));
      }
      if (this.accept(';')) { if (owner) this.addMethod(owner, { name, ret, params, body: null, line, isStatic: !!opts.isStatic, isCtor: !!opts.isCtor, isDtor: !!opts.isDtor }); return null; }
      if (this.is('=')) { this.next(); this.next(); this.expect(';'); return null; } // = default / = delete / = 0
      const body = this.parseBlock();
      const fn = { type: 'Func', name, ret, params, body, line, endLine: this.toks[this.p - 1].line, owner, isStatic: !!opts.isStatic, isCtor: !!opts.isCtor, isDtor: !!opts.isDtor, initList, isVirtual: !!opts.isVirtual };
      if (owner) this.addMethod(owner, fn);
      else this.funcs.push(fn);
      return fn;
    }
    addMethod(st, fn) {
      if (fn.isCtor) { const i = st.ctors.findIndex(c => !c.body && c.params.length === fn.params.length); if (i >= 0) st.ctors.splice(i, 1); st.ctors.push(fn); return; }
      if (fn.isDtor) { if (fn.body || !st.dtor) st.dtor = fn; return; }
      if (!st.methods.has(fn.name)) st.methods.set(fn.name, []);
      const list = st.methods.get(fn.name);
      const i = list.findIndex(c => !c.body && c.params.length === fn.params.length);
      if (i >= 0) list.splice(i, 1);
      list.push(fn);
    }

    parseTypedef() {
      this.expect('typedef');
      const spec = this.parseDeclSpec();
      do {
        const d = this.parseDeclarator(spec.type, false);
        if (!d.name) this.err('typedef 缺少名字');
        this.typedefs.set(d.name, d.type);
        if (d.type.k === 'struct' && !d.type.typedefName && d.type.name.startsWith('<anon')) d.type.typedefName = d.name;
        if (d.type.k === 'struct' && !d.type.typedefName && d.type.name === d.name) d.type.typedefName = d.name;
        if (d.type.k === 'struct' && !d.type.typedefName) d.type.typedefName = d.name;
      } while (this.accept(','));
      this.expect(';', 'typedef 结尾');
    }

    // decl-specifiers: qualifiers + base type (may define struct/enum)
    parseDeclSpec() {
      let isStatic = false, isConst = false, isVirtual = false;
      let signedness = null, longs = 0, short = false, base = null, sawInt = false;
      const startTok = this.peek();
      for (;;) {
        const t = this.peek();
        if (t.t !== 'id') break;
        const v = t.v;
        if (v === 'const' || v === 'volatile' || v === 'register' || v === 'inline' || v === 'extern' || v === 'mutable' || v === 'explicit' || v === 'constexpr' || v === 'friend' || v === 'typename' || v === '__inline') { if (v === 'const' || v === 'constexpr') isConst = true; this.next(); continue; }
        if (v === 'static') { isStatic = true; this.next(); continue; }
        if (v === 'virtual') { isVirtual = true; this.next(); continue; }
        if (v === 'signed' || v === 'unsigned') { signedness = v; this.next(); continue; }
        if (v === 'long') { longs++; this.next(); continue; }
        if (v === 'short') { short = true; this.next(); continue; }
        if (base) break;
        if (v === 'int') { sawInt = true; this.next(); if (signedness || longs || short) continue; base = T.int; continue; }
        if (v === 'char') { this.next(); base = signedness === 'unsigned' ? T.uchar : (signedness === 'signed' ? T.schar : T.char); continue; }
        if (v === 'wchar_t' || v === 'char16_t' || v === 'char32_t') { this.next(); base = T.int; continue; }
        if (v === 'float') { this.next(); base = T.float; continue; }
        if (v === 'double') { this.next(); base = longs ? T.ldouble : T.double; longs = 0; continue; }
        if (v === 'void') { this.next(); base = T.void; continue; }
        if (v === 'bool' || v === '_Bool') { this.next(); base = T.bool; continue; }
        if (v === 'auto') { this.next(); base = T.auto; continue; }
        if (signedness || longs || short || sawInt) break;
        if (v === 'struct' || v === 'union' || v === 'class') { base = this.parseStructSpec(); continue; }
        if (v === 'enum') { base = this.parseEnumSpec(); continue; }
        if (v === 'size_t' || v === 'uint64_t' || v === 'uintptr_t') { this.next(); base = T.size_t; continue; }
        if (v === 'ssize_t' || v === 'ptrdiff_t' || v === 'int64_t' || v === 'intptr_t' || v === 'LONG') { this.next(); base = T.long; continue; }
        if (v === 'uint32_t' || v === 'DWORD') { this.next(); base = T.uint; continue; }
        if (v === 'int32_t') { this.next(); base = T.int; continue; }
        if (v === 'uint16_t' || v === 'WORD') { this.next(); base = T.ushort; continue; }
        if (v === 'int16_t') { this.next(); base = T.short; continue; }
        if (v === 'uint8_t' || v === 'BYTE') { this.next(); base = T.uchar; continue; }
        if (v === 'int8_t') { this.next(); base = T.schar; continue; }
        if (v === 'FILE') { this.next(); base = T.stream('FILE'); continue; }
        if (this.typedefs.has(v)) { this.next(); base = this.typedefs.get(v); continue; }
        if (this.d === 'cpp') {
          if (v === 'std' && this.is('::', 1)) { this.next(); this.next(); continue; }
          if (v === 'string') { this.next(); base = T.string; continue; }
          if (v === 'ostream' || v === 'istream') { this.next(); base = T.stream(v); continue; }
          if (CONTAINERS_CPP.has(v)) { this.next(); base = T.cont(v, this.parseTplArgs()); continue; }
          if (this.isTplParam(v)) { this.next(); base = T.any; continue; }
          const st = this.structs.get(v);
          if (st) {
            // Name::Name( is a constructor def, handled elsewhere
            this.next();
            if (st.k === 'enumT') { base = T.int; continue; }
            if (this.is('<')) this.parseTplArgs();
            base = st; continue;
          }
        }
        break;
      }
      if (!base) {
        if (signedness || longs || short || sawInt) {
          if (short) base = signedness === 'unsigned' ? T.ushort : T.short;
          else if (longs >= 2) base = signedness === 'unsigned' ? T.ullong : T.llong;
          else if (longs === 1) base = signedness === 'unsigned' ? T.ulong : T.long;
          else base = signedness === 'unsigned' ? T.uint : T.int;
        } else {
          this.err('这里应该是一个类型名，但遇到了 “' + startTok.v + '”。如果这是你自己定义的类型，请检查拼写和定义顺序。', startTok);
        }
      } else if (base === T.int && signedness === 'unsigned') base = T.uint;
      return { type: base, isStatic, isConst, isVirtual };
    }

    parseTplArgs() {
      const args = [];
      if (!this.accept('<')) return args;
      for (;;) {
        if (this.is('>')) break;
        if (this.is('>>')) break;
        if (this.peek().t === 'num') { this.next(); }
        else if (this.isId() && (this.peek().v === 'greater' || this.peek().v === 'less') || (this.peek().v === 'std' && this.is('::', 1) && (this.peek(2).v === 'greater' || this.peek(2).v === 'less'))) {
          if (this.peek().v === 'std') { this.next(); this.next(); }
          const nm = this.next().v; if (this.is('<')) this.parseTplArgs();
          args.push({ k: 'cmp', name: nm, size: 1, align: 1 });
        }
        else if (this.isId() && !this.isTypeStart() && this.d === 'cpp') { this.next(); args.push({ k: 'cmp', name: 'custom', size: 1, align: 1 }); }
        else {
          const t = this.parseType();
          args.push(t);
        }
        if (!this.accept(',')) break;
      }
      this.closeAngle();
      return args;
    }
    closeAngle() {
      if (this.accept('>')) return;
      const t = this.peek();
      if (t.t === 'op' && (t.v === '>>' || t.v === '>>>' || t.v === '>=' || t.v === '>>=')) {
        // split token
        const rest = t.v.slice(1);
        this.toks[this.p] = Object.assign({}, t, { v: rest });
        return;
      }
      this.expect('>');
    }

    parseType() {
      // type-id: decl-spec + abstract declarator (pointers/refs)
      if (this.d === 'java') return this.parseJavaType();
      const spec = this.parseDeclSpec();
      let t = spec.type;
      for (;;) {
        if (this.accept('*')) { t = T.ptr(t); while (this.accept('const')); continue; }
        if (this.accept('&') || this.accept('&&')) { t = T.ref(t); continue; }
        break;
      }
      if (this.is('[') && this.is(']', 1)) { this.next(); this.next(); t = T.ptr(t); }
      return t;
    }

    parseStructSpec() {
      const kw = this.next().v; // struct/union/class
      const line = this.peek().line;
      let name = null;
      if (this.isId() && !this.is('{')) {
        name = this.next().v;
      }
      while (this.is('final')) this.next();
      const tag = kw === 'union' ? 'union' : (kw === 'class' ? 'class' : 'struct');
      let st;
      const key = (this.d === 'c' ? kw + ' ' : '') + (name || '');
      if (name) {
        st = this.structs.get(key) || this.structs.get(name);
        if (!st || st.k !== 'struct') { st = this.newStruct(name, tag); this.structs.set(key, st); if (this.d !== 'c') this.structs.set(name, st); }
        if (this.d === 'cpp' && this.is('<')) this.parseTplArgs();
      } else {
        st = this.newStruct('<anon@' + line + '>', tag);
      }
      st.tag = tag;
      if (this.d === 'cpp' && this.accept(':')) {
        do { while (this.is('public') || this.is('private') || this.is('protected') || this.is('virtual')) this.next(); const bt = this.parseType(); if (bt.k === 'struct') st.base = bt; } while (this.accept(','));
      }
      if (this.accept('{')) {
        if (st.complete) this.err('结构体 ' + name + ' 重复定义');
        this.parseStructBody(st);
        st.complete = true;
        st.line = line;
        if (this.d === 'cpp') this.classes.push(st);
      }
      return st;
    }

    parseStructBody(st) {
      while (!this.accept('}')) {
        if (this.peek().t === 'eof') this.err('结构体定义缺少 }');
        if (this.accept(';')) continue;
        if ((this.is('public') || this.is('private') || this.is('protected')) && this.is(':', 1)) { this.next(); this.next(); continue; }
        const line = this.line();
        if (this.d === 'cpp') {
          if (this.is('template')) { this.next(); this.expect('<'); let depth = 1; while (depth) { if (this.is('<')) depth++; if (this.is('>')) depth--; this.next(); } }
          if (this.is('friend')) { while (!this.is(';') && !this.is('{')) this.next(); if (this.is('{')) this.skipBalanced(); else this.next(); continue; }
          // constructor / destructor
          if (this.is('~') && this.peek(1).v === st.name) { this.next(); this.next(); this.parseFuncRest('~' + st.name, T.void, line, st, { isDtor: true }); continue; }
          let p0 = this.p;
          while (this.is('explicit') || this.is('inline') || this.is('virtual') || this.is('constexpr')) this.next();
          if (this.peek().v === st.name && this.is('(', 1)) { this.next(); this.parseFuncRest(st.name, T.void, line, st, { isCtor: true }); continue; }
          this.p = p0;
          if (this.is('using') || this.is('typedef')) { if (this.is('typedef')) this.parseTypedef(); else { while (!this.is(';')) this.next(); this.next(); } continue; }
          if (this.is('operator') || (this.isTypeStart() && this.lookAheadOperator())) { this.skipOperatorDef(); continue; }
          if ((this.is('struct') || this.is('class') || this.is('enum') || this.is('union')) && (this.is('{', 2) || (this.is('{', 1)))) {
            const spec = this.parseDeclSpec();
            if (this.accept(';')) continue;
            this.parseMemberDeclarators(st, spec, line); continue;
          }
        }
        const spec = this.parseDeclSpec();
        if (this.accept(';')) {
          // anonymous struct/union member: flatten its fields
          if (spec.type.k === 'struct' && spec.type.name.startsWith('<anon')) { for (const f of spec.type.fields) st.fields.push(Object.assign({}, f)); }
          continue;
        }
        this.parseMemberDeclarators(st, spec, line);
      }
    }
    lookAheadOperator() {
      for (let i = 0; i < 8; i++) { if (this.is('operator', i)) return true; if (this.is(';', i) || this.is('(', i) || this.is('{', i)) return false; }
      return false;
    }
    skipOperatorDef() {
      while (!this.is('(')) this.next();
      // operator() special
      if (this.is('(') && this.is(')', 1) && this.is('(', 2)) { this.next(); this.next(); }
      this.skipBalancedParens();
      while (!this.is('{') && !this.is(';')) this.next();
      if (this.is('{')) this.skipBalanced(); else this.next();
    }
    skipBalancedParens() { let depth = 0; do { if (this.is('(')) depth++; if (this.is(')')) depth--; this.next(); } while (depth > 0); }
    skipBalanced() { let depth = 0; do { if (this.is('{')) depth++; if (this.is('}')) depth--; this.next(); } while (depth > 0 && this.peek().t !== 'eof'); }

    parseMemberDeclarators(st, spec, line) {
      for (;;) {
        const dl = this.line();
        const d = this.parseDeclarator(spec.type, true);
        if (d.isFunc) {
          this.parseFuncRest(d.name, d.type.ret, dl, st, { params: d.params, preParsedParams: true, isStatic: spec.isStatic, isVirtual: spec.isVirtual });
          return;
        }
        let bits = null;
        if (this.accept(':')) { bits = this.parseAssign(); }
        let init = null;
        if (this.accept('=')) init = this.is('{') ? this.parseInitList() : this.parseAssign();
        else if (this.d === 'cpp' && this.is('{')) init = this.parseInitList();
        if (spec.isStatic) st.staticFields.push({ name: d.name, type: d.type, init, line: dl });
        else st.fields.push({ name: d.name, type: d.type, init, line: dl });
        if (this.accept(',')) continue;
        this.expect(';', '成员声明结尾');
        return;
      }
    }

    parseEnumSpec() {
      this.expect('enum');
      if (this.is('class') || this.is('struct')) this.next();
      let name = null;
      if (this.isId() && !this.is('{')) name = this.next().v;
      if (this.accept(':')) this.parseType();
      if (this.accept('{')) {
        let val = 0;
        while (!this.accept('}')) {
          const nm = this.ident('枚举值');
          if (this.accept('=')) { val = this.constEval(this.parseAssign()); }
          this.enumConsts.set(nm, val);
          if (name) this.enumConsts.set(name + '::' + nm, val);
          val++;
          if (!this.accept(',')) { this.expect('}'); break; }
        }
      }
      if (name) { const tdef = T.int; this.typedefs.set(name, tdef); if (this.d === 'c') this.typedefs.delete(name); }
      return T.int;
    }
    constEval(e) {
      if (e.type === 'Num') return e.v;
      if (e.type === 'Char') return e.v;
      if (e.type === 'Unary' && e.op === '-') return -this.constEval(e.e);
      if (e.type === 'Ident' && this.enumConsts.has(e.name)) return this.enumConsts.get(e.name);
      if (e.type === 'Binary') {
        const a = this.constEval(e.l), b = this.constEval(e.r);
        switch (e.op) { case '+': return a + b; case '-': return a - b; case '*': return a * b; case '/': return Math.trunc(a / b); case '<<': return a << b; case '>>': return a >> b; case '|': return a | b; case '&': return a & b; }
      }
      this.err('枚举值需要是常量');
    }

    // declarator: pointers, name, arrays, function params
    parseDeclarator(base, allowQualified) {
      let t = base;
      let isRef = false;
      for (;;) {
        if (this.accept('*')) { t = T.ptr(t); while (this.is('const') || this.is('volatile') || this.is('restrict') || this.is('__restrict')) this.next(); continue; }
        if (this.d === 'cpp' && (this.accept('&') || this.accept('&&'))) { isRef = true; continue; }
        break;
      }
      // function pointer: (*name)(params)
      if (this.is('(') && this.is('*', 1)) {
        this.next(); this.next();
        const name = this.isId() ? this.next().v : null;
        let dims = [];
        while (this.accept('[')) { dims.push(this.is(']') ? null : this.parseAssign()); this.expect(']'); }
        this.expect(')');
        const params = this.parseParams();
        let ft = T.ptr(T.func(t, params.map(p => p.type)));
        for (let i = dims.length - 1; i >= 0; i--) ft = T.arr(ft, null, dims[i]);
        return { name, type: ft, isFunc: false };
      }
      let name = null, ownerClass = null;
      if (this.isId() && !this.isTypeKeywordNotName()) {
        name = this.next().v;
        if (allowQualified && this.d === 'cpp' && this.is('::')) {
          const st = this.structs.get(name);
          this.next();
          if (this.is('operator')) { this.skipOperatorDef(); return { name: null, isFunc: false, type: t, skipped: true }; }
          ownerClass = st; name = this.ident('成员名');
        }
        if (name === 'operator') { this.p--; this.skipOperatorDef(); return { name: null, isFunc: true, skipped: true, type: T.func(t, []), params: [] }; }
      }
      // function?
      if (this.is('(') && name) {
        // distinguish  T x(args)  (ctor call, C++) from function declaration
        if (this.d === 'cpp' && !ownerClass && this.looksLikeCtorCall()) {
          // treat as variable with constructor args; caller handles '('
          return { name, type: isRef ? T.ref(t) : t, isFunc: false };
        }
        const params = this.parseParams();
        return { name, type: T.func(t, params.map(p => p.type)), isFunc: true, params, ownerClass };
      }
      const dims = [];
      while (this.accept('[')) {
        if (this.accept(']')) { dims.push({ len: null }); continue; }
        const e = this.parseExpr();
        this.expect(']');
        if (e.type === 'Num') dims.push({ len: e.v });
        else {
          let cv = null;
          try { cv = this.constEval(e); } catch (er) { cv = null; }
          dims.push(cv != null ? { len: cv } : { len: null, expr: e });
        }
      }
      for (let i = dims.length - 1; i >= 0; i--) t = T.arr(t, dims[i].len, dims[i].expr);
      if (isRef) t = T.ref(t);
      return { name, type: t, isFunc: false, ownerClass };
    }
    isTypeKeywordNotName() { return false; }
    looksLikeCtorCall() {
      // after name, '(' : if next token starts a type or is ')' -> function decl, else ctor call
      const t1 = this.peek(1);
      if (t1.v === ')' ) return false; // T x(); most vexing parse -> function decl
      if (this.isTypeStart(1)) return false;
      return true;
    }

    parseParams() {
      this.expect('(');
      const params = [];
      if (this.accept(')')) return params;
      if (this.is('void') && this.is(')', 1)) { this.next(); this.next(); return params; }
      for (;;) {
        if (this.accept('...')) { params.push({ name: '...', type: T.void, varargs: true }); break; }
        const line = this.line();
        const spec = this.parseDeclSpec();
        const d = this.parseDeclarator(spec.type, false);
        let t = d.type;
        // array params decay
        if (t.k === 'arr') t = T.ptr(t.of);
        if (t.k === 'func') t = T.ptr(t);
        const p = { name: d.name, type: t, line };
        if (this.accept('=')) p.def = this.parseAssign();
        params.push(p);
        if (!this.accept(',')) break;
      }
      this.expect(')', '参数列表结尾');
      return params;
    }

    parseInitializer(type) {
      if (this.accept('=')) {
        if (this.is('{')) return { init: this.parseInitList() };
        return { init: this.parseAssign() };
      }
      if (this.d === 'cpp' && this.is('(')) { this.next(); return { ctorArgs: this.parseArgs(')') }; }
      if (this.d === 'cpp' && this.is('{')) { const il = this.parseInitList(); return { init: il, braceInit: true }; }
      return {};
    }
    parseInitList() {
      const line = this.line();
      this.expect('{');
      const items = [];
      while (!this.accept('}')) {
        let designator = null;
        if (this.is('.') && this.isId(1) && this.is('=', 2)) { this.next(); designator = { field: this.next().v }; this.next(); }
        else if (this.is('[') ) { this.next(); const idx = this.parseAssign(); this.expect(']'); this.expect('='); designator = { index: idx }; }
        const v = this.is('{') ? this.parseInitList() : this.parseAssign();
        items.push(designator ? { type: 'Designated', des: designator, value: v, line: v.line } : v);
        if (!this.accept(',')) { this.expect('}', '初始化列表结尾'); break; }
      }
      return { type: 'InitList', items, line };
    }

    // ================= statements =================
    parseBlock() {
      const line = this.line();
      this.expect('{', '代码块开头');
      const body = [];
      while (!this.is('}')) {
        if (this.peek().t === 'eof') this.err('缺少右花括号 }，代码块没有闭合', this.toks[this.toks.length - 1]);
        body.push(this.parseStmt());
      }
      const endLine = this.next().line;
      return { type: 'Block', body, line, endLine };
    }

    parseStmt() {
      const t = this.peek();
      const line = t.line;
      if (t.t === 'op') {
        if (t.v === '{') return this.parseBlock();
        if (t.v === ';') { this.next(); return { type: 'Empty', line }; }
      }
      if (t.t === 'id') {
        switch (t.v) {
          case 'if': {
            this.next(); this.expect('('); const cond = this.parseExpr(); this.expect(')', 'if 条件结尾');
            const then = this.parseStmt();
            let els = null;
            if (this.accept('else')) els = this.parseStmt();
            return { type: 'If', cond, then, els, line };
          }
          case 'while': {
            this.next(); this.expect('('); const cond = this.parseExpr(); this.expect(')', 'while 条件结尾');
            const body = this.parseStmt();
            return { type: 'While', cond, body, line };
          }
          case 'do': {
            this.next(); const body = this.parseStmt(); const wl = this.line(); this.expect('while'); this.expect('('); const cond = this.parseExpr(); this.expect(')'); this.expect(';');
            return { type: 'DoWhile', cond, body, line, condLine: wl };
          }
          case 'for': return this.parseFor();
          case 'switch': {
            this.next(); this.expect('('); const disc = this.parseExpr(); this.expect(')'); this.expect('{');
            const cases = []; let cur = null;
            while (!this.accept('}')) {
              const cl = this.line();
              if (this.accept('case')) {
                const test = this.parseCondExpr();
                if (this.d === 'java' && this.accept('->')) { cur = { test, body: [], line: cl, arrow: true }; cases.push(cur); cur.body.push(this.is('{') ? this.parseBlock() : this.parseStmt()); cur.body.push({ type: 'Break', line: cl }); cur = null; continue; }
                this.expect(':', 'case 后面'); cur = { test, body: [], line: cl }; cases.push(cur); continue;
              }
              if (this.accept('default')) {
                if (this.d === 'java' && this.accept('->')) { cur = { test: null, body: [], line: cl }; cases.push(cur); cur.body.push(this.is('{') ? this.parseBlock() : this.parseStmt()); cur.body.push({ type: 'Break', line: cl }); cur = null; continue; }
                this.expect(':'); cur = { test: null, body: [], line: cl }; cases.push(cur); continue;
              }
              if (!cur) this.err('switch 里的语句必须写在 case 或 default 后面');
              cur.body.push(this.parseStmt());
            }
            return { type: 'Switch', disc, cases, line };
          }
          case 'break': this.next(); this.expect(';'); return { type: 'Break', line };
          case 'continue': this.next(); this.expect(';'); return { type: 'Continue', line };
          case 'return': {
            this.next(); let e = null;
            if (!this.is(';')) e = this.is('{') ? this.parseInitList() : this.parseExpr();
            this.expect(';', 'return 语句结尾');
            return { type: 'Return', e, line };
          }
          case 'goto': this.err('暂不支持 goto 语句');
          case 'try': return this.parseTry();
          case 'throw': {
            this.next(); const e = this.is(';') ? null : this.parseExpr(); this.expect(';'); return { type: 'Throw', e, line };
          }
          case 'typedef': this.parseTypedef(); return { type: 'Empty', line };
          case 'using': while (!this.is(';')) this.next(); this.next(); return { type: 'Empty', line };
          case 'assert': if (this.d === 'java') { this.next(); const cond = this.parseExpr(); let msg = null; if (this.accept(':')) msg = this.parseExpr(); this.expect(';'); return { type: 'ExprStmt', e: { type: 'Call', callee: { type: 'Ident', name: '__jassert', line }, args: msg ? [cond, msg] : [cond], line }, line }; } break;
        }
        // label: skip it
        if (this.is(':', 1) && this.d !== 'java' && !this.isTypeStart() && t.v !== 'default' && t.v !== 'case') { this.next(); this.next(); if (this.is('}')) return { type: 'Empty', line }; return this.parseStmt(); }
        // declaration?
        if (this.d === 'java' ? this.isJavaDeclStart() : this.isTypeStart()) {
          const save = this.p;
          try {
            return this.parseLocalDecl();
          } catch (e) {
            if (!e.isCompile) throw e;
            const declErr = e;
            this.p = save;
            try {
              const ex = this.parseExpr();
              this.expect(';', '语句结尾');
              return { type: 'ExprStmt', e: ex, line };
            } catch (e2) { throw declErr; }
          }
        }
      }
      const e = this.parseExpr();
      if (!this.is(';')) {
        const nt = this.peek();
        throw new CompileError('语句末尾缺少分号 “;”（遇到了 “' + nt.v + '”）', this.toks[this.p - 1].line, 0);
      }
      this.next();
      return { type: 'ExprStmt', e, line };
    }

    parseTry() {
      const line = this.line();
      this.expect('try');
      let resources = null;
      if (this.d === 'java' && this.accept('(')) { resources = []; while (!this.accept(')')) { resources.push(this.parseLocalDecl(true)); this.accept(';'); } }
      const block = this.parseBlock();
      const handlers = [];
      while (this.is('catch')) {
        const cl = this.line(); this.next(); this.expect('(');
        let types = [], name = null;
        if (this.accept('...')) { types.push('*'); }
        else {
          if (this.d === 'java') { while (this.is('final')) this.next(); types.push(this.parseJavaTypeName()); while (this.accept('|')) types.push(this.parseJavaTypeName()); name = this.ident(); }
          else { let t = this.parseType(); while (t.k === 'ref') t = t.to; types.push(t.k === 'struct' ? t.name : T.name(t)); if (this.isId()) name = this.next().v; }
        }
        this.expect(')');
        handlers.push({ types, name, body: this.parseBlock(), line: cl });
      }
      let fin = null;
      if (this.accept('finally')) fin = this.parseBlock();
      return { type: 'Try', block, handlers, fin, line, resources };
    }
    parseJavaTypeName() { let n = this.ident('类型'); while (this.accept('.')) n = this.ident(); return n; }

    parseFor() {
      const line = this.line();
      this.expect('for');
      this.expect('(');
      // range-based / enhanced for
      const save = this.p;
      if ((this.d === 'java' ? this.isJavaDeclStart() : this.isTypeStart())) {
        try {
          let vt, isRef = false, name;
          if (this.d === 'java') { while (this.is('final')) this.next(); vt = this.parseJavaType(); name = this.ident(); }
          else { const spec = this.parseDeclSpec(); let t = spec.type; while (this.accept('*')) t = T.ptr(t); if (this.accept('&') || this.accept('&&')) isRef = true; vt = t; if (this.accept('[')) { const names = []; do { names.push(this.ident()); } while (this.accept(',')); this.expect(']'); name = names; } else name = this.ident(); }
          if (this.accept(':')) {
            const iter = this.parseExpr();
            this.expect(')');
            const body = this.parseStmt();
            return { type: 'ForEach', vtype: vt, isRef, name, iter, body, line };
          }
        } catch (e) { if (!e.isCompile) throw e; }
        this.p = save;
      }
      let init = null;
      if (!this.accept(';')) {
        if (this.d === 'java' ? this.isJavaDeclStart() : this.isTypeStart()) init = this.parseLocalDecl();
        else { const e = this.parseExpr(); this.expect(';'); init = { type: 'ExprStmt', e, line }; }
      }
      const cond = this.is(';') ? null : this.parseExpr();
      this.expect(';', 'for 循环条件后面');
      const update = this.is(')') ? null : this.parseExpr();
      this.expect(')', 'for 循环头结尾');
      const body = this.parseStmt();
      return { type: 'For', init, cond, update, body, line };
    }

    parseLocalDecl(noSemi) {
      const line = this.line();
      if (this.d === 'java') return this.parseJavaLocalDecl(noSemi);
      const spec = this.parseDeclSpec();
      if (this.accept(';')) return { type: 'Empty', line };
      const decls = [];
      for (;;) {
        const dl = this.line();
        // structured bindings: auto [a, b] = ...
        if (this.d === 'cpp' && this.is('[')) {
          this.next(); const names = []; do { names.push(this.ident()); } while (this.accept(','));
          this.expect(']'); this.expect('='); const init = this.parseAssign();
          decls.push({ name: names, vtype: spec.type, init, line: dl, bind: true });
          if (this.accept(',')) continue; break;
        }
        const d = this.parseDeclarator(spec.type, false);
        if (d.isFunc) { this.protos.set(d.name, d); if (this.accept(',')) continue; break; }
        if (!d.name) this.err('声明缺少变量名');
        const init = this.parseInitializer(d.type);
        decls.push({ name: d.name, vtype: d.type, init: init.init, ctorArgs: init.ctorArgs, braceInit: init.braceInit, line: dl, isStatic: spec.isStatic, isConst: spec.isConst });
        if (!this.accept(',')) break;
      }
      if (!noSemi) {
        if (!this.is(';')) throw new CompileError('声明末尾缺少分号 “;”', this.toks[this.p - 1].line);
        this.next();
      }
      return { type: 'Decl', decls, line };
    }

    // ================= expressions =================
    parseExpr() {
      let e = this.parseAssign();
      if (this.is(',') && this.d !== 'java') {
        const list = [e];
        while (this.accept(',')) list.push(this.parseAssign());
        e = { type: 'Comma', list, line: e.line };
      }
      return e;
    }
    parseArgs(close) {
      const args = [];
      if (this.accept(close)) return args;
      for (;;) {
        args.push(this.is('{') ? this.parseInitList() : this.parseAssign());
        if (this.accept(close)) break;
        this.expect(',', '参数之间');
      }
      return args;
    }
    parseAssign() {
      const line = this.line();
      // java lambda:  x -> ..., (a, b) -> ...
      if (this.d === 'java') {
        if (this.isId() && this.is('->', 1)) { const p = this.next().v; this.next(); return this.parseLambdaBody([p], line); }
        if (this.is('(')) {
          let j = 1, ok = true, params = [];
          if (this.is(')', 1) && this.is('->', 2)) { this.next(); this.next(); this.next(); return this.parseLambdaBody([], line); }
          for (;;) {
            if (this.peek(j).t !== 'id') { ok = false; break; }
            // allow typed params: (int a, int b)
            if (this.peek(j + 1).t === 'id') j++;
            params.push(this.peek(j).v); j++;
            if (this.is(',', j)) { j++; continue; }
            if (this.is(')', j) && this.is('->', j + 1)) break;
            ok = false; break;
          }
          if (ok) { this.p += j + 2; return this.parseLambdaBody(params, line); }
        }
      }
      if (this.d === 'cpp' && this.is('[') && this.isLambdaStart()) return this.parseCppLambda();
      const l = this.parseCond();
      const t = this.peek();
      if (t.t === 'op' && ['=', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '<<=', '>>=', '>>>='].includes(t.v)) {
        this.next();
        const r = this.is('{') && this.d === 'cpp' ? this.parseInitList() : this.parseAssign();
        return { type: 'Assign', op: t.v, l, r, line: t.line };
      }
      return l;
    }
    isLambdaStart() {
      // [capture](params){...}
      let j = 1;
      while (!this.is(']', j)) { if (this.peek(j).t === 'eof' || this.is(';', j)) return false; j++; }
      return this.is('(', j + 1) || this.is('{', j + 1);
    }
    parseCppLambda() {
      const line = this.line();
      this.expect('[');
      while (!this.accept(']')) this.next();
      let params = [];
      if (this.is('(')) params = this.parseParams();
      while (this.is('mutable') || this.is('noexcept')) this.next();
      if (this.accept('->')) this.parseType();
      const body = this.parseBlock();
      return { type: 'Lambda', params: params.map(p => p.name), ptypes: params.map(p => p.type), body, line };
    }
    parseLambdaBody(params, line) {
      if (this.is('{')) return { type: 'Lambda', params, body: this.parseBlock(), line };
      const e = this.parseAssign();
      return { type: 'Lambda', params, body: { type: 'Block', body: [{ type: 'Return', e, line }], line, endLine: line }, line, exprBody: true };
    }
    parseCond() {
      const c = this.parseBin(0);
      if (this.is('?')) {
        const line = this.next().line;
        const a = this.parseExpr2();
        this.expect(':', '三目运算符');
        const b = this.parseAssignNoComma();
        return { type: 'Cond', c, a, b, line };
      }
      return c;
    }
    parseCondExpr() { return this.parseCond(); }
    parseExpr2() { return this.parseAssign(); }
    parseAssignNoComma() { return this.parseAssign(); }

    binPrec(t) {
      if (t.t !== 'op' && !(t.t === 'id' && t.v === 'instanceof')) return -1;
      switch (t.v) {
        case '||': return 1; case '&&': return 2; case '|': return 3; case '^': return 4; case '&': return 5;
        case '==': case '!=': return 6;
        case '<': case '>': case '<=': case '>=': case 'instanceof': return 7;
        case '<<': case '>>': case '>>>': return 8;
        case '+': case '-': return 9;
        case '*': case '/': case '%': return 10;
      }
      return -1;
    }
    parseBin(minPrec) {
      let l = this.parseUnary();
      for (;;) {
        const t = this.peek();
        const pr = this.binPrec(t);
        if (pr < 0 || pr <= minPrec - 0 && pr < minPrec + 1 && pr <= minPrec) { if (pr <= minPrec) break; }
        if (pr <= minPrec) break;
        this.next();
        if (t.v === 'instanceof') { const tn = this.parseJavaType(); let bind = null; if (this.isId()) bind = this.next().v; l = { type: 'InstanceOf', e: l, tname: tn, bind, line: t.line }; continue; }
        const r = this.parseBin(pr);
        l = { type: 'Binary', op: t.v, l, r, line: t.line };
      }
      return l;
    }
    parseUnary() {
      const t = this.peek();
      const line = t.line;
      if (t.t === 'op') {
        switch (t.v) {
          case '++': case '--': { this.next(); const e = this.parseUnary(); return { type: 'PreInc', op: t.v, e, line }; }
          case '+': case '-': case '!': case '~': { this.next(); const e = this.parseUnary(); if (t.v === '-' && e.type === 'Num') return Object.assign({}, e, { v: -e.v }); return { type: 'Unary', op: t.v, e, line }; }
          case '*': if (this.d !== 'java') { this.next(); const e = this.parseUnary(); return { type: 'Deref', e, line }; } break;
          case '&': if (this.d !== 'java') { this.next(); const e = this.parseUnary(); return { type: 'AddrOf', e, line }; } break;
          case '(': {
            // cast?
            if (this.isCastAhead()) {
              this.next();
              const ty = this.parseType();
              this.expect(')');
              const e = this.parseUnary();
              return { type: 'Cast', ty, e, line };
            }
            break;
          }
          case '::': this.next(); return this.parseUnary();
        }
      }
      if (t.t === 'id') {
        if (t.v === 'sizeof' && this.d !== 'java') {
          this.next();
          if (this.is('(') && this.isTypeStartAfterParen()) { this.next(); const ty = this.parseType(); let dims = []; while (this.accept('[')) { dims.push(this.parseExpr()); this.expect(']'); } this.expect(')'); let tt = ty; for (let i = dims.length - 1; i >= 0; i--) tt = T.arr(tt, dims[i].type === 'Num' ? dims[i].v : null, dims[i]); return { type: 'SizeofType', ty: tt, line }; }
          const e = this.parseUnary();
          return { type: 'SizeofExpr', e, line };
        }
        if (t.v === 'new') return this.parsePostfix(this.parseNew());
        if (t.v === 'delete' && this.d === 'cpp') {
          this.next(); let arr = false;
          if (this.is('[')) { this.next(); this.expect(']'); arr = true; }
          const e = this.parseUnary();
          return { type: 'Delete', e, arr, line };
        }
        if ((t.v === 'static_cast' || t.v === 'reinterpret_cast' || t.v === 'const_cast' || t.v === 'dynamic_cast') && this.d === 'cpp') {
          this.next(); this.expect('<'); const ty = this.parseType(); this.closeAngle(); this.expect('('); const e = this.parseExpr(); this.expect(')');
          return this.parsePostfix({ type: 'Cast', ty, e, line });
        }
      }
      return this.parsePostfix(this.parsePrimary());
    }
    isTypeStartAfterParen() {
      return this.d === 'java' ? false : this.isTypeStart(1);
    }
    isCastAhead() {
      // '(' type ')' followed by something that can start a unary expr
      if (this.d === 'java') {
        const t1 = this.peek(1);
        if (t1.t !== 'id') return false;
        if (J_PRIMS[t1.v]) {
          // (int) x   or (int[]) x
          let j = 2; while (this.is('[', j) && this.is(']', j + 1)) j += 2;
          return this.is(')', j);
        }
        if (!(t1.v === 'String' || JAVA_ANY.has(t1.v) || this.structs.has(t1.v) || CONTAINERS_JAVA.has(t1.v) || this.isTplParam(t1.v))) return false;
        let j = 2;
        if (this.is('<', j)) { let depth = 0; do { if (this.is('<', j)) depth++; if (this.is('>', j)) depth--; if (this.is('>>', j)) depth -= 2; j++; } while (depth > 0 && j < 40); }
        while (this.is('[', j) && this.is(']', j + 1)) j += 2;
        if (!this.is(')', j)) return false;
        const after = this.peek(j + 1);
        return after.t === 'id' || after.t === 'num' || after.t === 'str' || after.t === 'chr' || (after.t === 'op' && (after.v === '(' || after.v === '!' || after.v === '~'));
      }
      if (!this.isTypeStart(1)) return false;
      // ensure it's not e.g. (x) where x is typedef-shadowed... scan to ')'
      const save = this.p;
      try {
        this.next(); this.parseType();
        const ok = this.is(')');
        this.p = save;
        return ok;
      } catch (e) { this.p = save; return false; }
    }
    parseNew() {
      const line = this.line();
      this.expect('new');
      if (this.d === 'java') {
        // new int[5], new int[]{..}, new Node(..), new ArrayList<>(), new int[3][4]
        let base;
        const tn = this.peek().v;
        if (J_PRIMS[tn]) { this.next(); base = J_PRIMS[tn]; }
        else {
          let name = this.ident('类型');
          while (this.accept('.')) name = this.ident();
          let targs = [];
          if (this.is('<')) targs = this.parseJavaTplArgs();
          base = this.javaTypeFromName(name, targs);
        }
        if (this.is('[')) {
          const dims = [];
          let extra = 0;
          while (this.is('[')) {
            this.next();
            if (this.accept(']')) { extra++; continue; }
            dims.push(this.parseExpr()); this.expect(']');
          }
          let init = null;
          if (this.is('{')) init = this.parseJavaArrayInit();
          return { type: 'NewArray', elem: base, dims, extraDims: extra, init, line };
        }
        this.expect('(', 'new 后面的构造参数');
        const args = this.parseArgs(')');
        if (this.is('{')) { this.skipBalanced(); } // anonymous class body unsupported
        return { type: 'New', ty: base, args, line };
      }
      // C++
      if (this.is('(')) { this.next(); const ty = this.parseType(); this.expect(')'); return { type: 'New', ty, args: [], line }; }
      const spec = this.parseDeclSpec();
      let ty = spec.type;
      while (this.accept('*')) ty = T.ptr(ty);
      if (this.accept('[')) {
        const len = this.parseExpr(); this.expect(']');
        let init = null;
        if (this.is('(') && this.is(')', 1)) { this.next(); this.next(); init = 'zero'; }
        else if (this.is('{')) init = this.parseInitList();
        return { type: 'NewArray', elem: ty, dims: [len], init, line };
      }
      let args = [], brace = false;
      if (this.is('(')) { this.next(); args = this.parseArgs(')'); }
      else if (this.is('{')) { this.next(); args = this.parseArgs('}'); brace = true; }
      return { type: 'New', ty, args, brace, line };
    }
    parseJavaArrayInit() {
      const line = this.line();
      this.expect('{');
      const items = [];
      while (!this.accept('}')) {
        items.push(this.is('{') ? this.parseJavaArrayInit() : this.parseAssign());
        if (!this.accept(',')) { this.expect('}'); break; }
      }
      return { type: 'InitList', items, line };
    }

    parsePostfix(e) {
      for (;;) {
        const t = this.peek();
        if (t.t !== 'op') break;
        if (t.v === '(') {
          this.next();
          const args = this.parseArgs(')');
          e = { type: 'Call', callee: e, args, line: t.line };
          continue;
        }
        if (t.v === '[') {
          this.next(); const idx = this.parseExpr(); this.expect(']', '下标');
          e = { type: 'Index', obj: e, idx, line: t.line };
          continue;
        }
        if (t.v === '.' || t.v === '->') {
          this.next();
          if (this.d === 'java' && this.is('<')) this.parseJavaTplArgs(); // obj.<T>method()
          let name;
          if (this.d === 'java' && this.is('class')) { this.next(); name = 'class'; }
          else if (this.is('~')) { this.next(); name = '~' + this.ident(); }
          else name = this.ident('成员名');
          if (this.d === 'cpp' && this.is('<') && (name === 'template')) this.parseTplArgs();
          e = { type: 'Member', obj: e, name, arrow: t.v === '->', line: t.line };
          continue;
        }
        if (t.v === '::' && this.d === 'java') {
          this.next(); const name = this.is('new') ? (this.next(), 'new') : this.ident();
          e = { type: 'MethodRef', obj: e, name, line: t.line };
          continue;
        }
        if (t.v === '++' || t.v === '--') {
          this.next();
          e = { type: 'PostInc', op: t.v, e, line: t.line };
          continue;
        }
        break;
      }
      return e;
    }

    parsePrimary() {
      const t = this.next();
      const line = t.line;
      switch (t.t) {
        case 'num': {
          let ct = t.isFloat ? (t.suffix.includes('f') && this.d !== 'java' ? T.float : (t.suffix.includes('f') ? T.float : T.double)) : (t.suffix.includes('l') ? T.long : (t.suffix.includes('u') ? T.uint : T.int));
          if (!t.isFloat && Math.abs(t.v) > 2147483647 && ct === T.int) ct = T.long;
          return { type: 'Num', v: t.v, ct, line };
        }
        case 'chr': return { type: 'Char', v: t.v, line };
        case 'str': {
          let s = t.v;
          while (this.peek().t === 'str' && this.d !== 'java') s += this.next().v;
          return { type: 'Str', v: s, line };
        }
        case 'op':
          if (t.v === '(') {
            const e = this.parseExpr();
            this.expect(')', '括号');
            return e;
          }
          if (t.v === '{' && this.d === 'cpp') { this.p--; return this.parseInitList(); }
          throw new CompileError('这里不能出现 “' + t.v + '”', t.line, t.col);
        case 'id': {
          switch (t.v) {
            case 'true': return { type: 'Bool', v: 1, line };
            case 'false': return { type: 'Bool', v: 0, line };
            case 'NULL': if (this.d !== 'java') return { type: 'Null', line }; break;
            case 'nullptr': return { type: 'Null', line, cpp: true };
            case 'null': if (this.d === 'java') return { type: 'Null', line }; break;
            case 'this': return { type: 'This', line };
            case 'super': if (this.d === 'java') return { type: 'Super', line }; break;
          }
          let name = t.v;
          // std:: / Class:: qualified names
          if (this.d === 'cpp') {
            while (this.is('::')) {
              this.next();
              const nx = this.ident('名字');
              if (name === 'std') name = nx; else name = name + '::' + nx;
            }
            // container type used as expression (e.g. vector<int>(5, 0), pair<int,int>(1,2), make_pair)
            if ((CONTAINERS_CPP.has(name) || name === 'string') && (this.is('<') || this.is('(') || this.is('{'))) {
              const args = name === 'string' ? [] : this.parseTplArgs();
              const ty = name === 'string' ? T.string : T.cont(name, args);
              if (this.is('(')) { this.next(); return { type: 'Construct', ty, args: this.parseArgs(')'), line }; }
              if (this.is('{')) { this.next(); return { type: 'Construct', ty, args: this.parseArgs('}'), line, brace: true }; }
              return { type: 'Construct', ty, args: [], line };
            }
            const st = this.structs.get(name);
            if (st && st.k === 'struct' && (this.is('(') || this.is('{'))) {
              if (this.is('(')) { this.next(); return { type: 'Construct', ty: st, args: this.parseArgs(')'), line }; }
              this.next(); return { type: 'Construct', ty: st, args: this.parseArgs('}'), line, brace: true };
            }
            if (this.is('<') && (name === 'max' || name === 'min' || name === 'swap' || name === 'make_pair' || name === 'greater' || name === 'less')) {
              this.parseTplArgs();
              if (name === 'greater' || name === 'less') { this.expect('('); this.expect(')'); return { type: 'Ident', name: '__' + name, line }; }
            }
          }
          if (this.d === 'java' && this.is('<') && this.structs.has(name)) {
            // generic static call like Foo.<T>bar handled elsewhere
          }
          if (this.enumConsts.has(name) && this.d !== 'java') return { type: 'Num', v: this.enumConsts.get(name), ct: T.int, line };
          return { type: 'Ident', name, line };
        }
      }
      throw new CompileError('这里应该是一个表达式，但遇到了 “' + t.v + '”', t.line, t.col);
    }

    // ================= Java =================
    parseJavaProgram() {
      const decls = [];
      while (this.peek().t !== 'eof') {
        if (this.accept(';')) continue;
        if (this.is('package') || this.is('import')) { while (!this.is(';')) this.next(); this.next(); continue; }
        if (this.is('@')) { this.skipAnnotation(); continue; }
        this.parseJavaTypeDecl(null);
      }
      return this.result(decls);
    }
    skipAnnotation() {
      this.expect('@');
      this.ident();
      while (this.accept('.')) this.ident();
      if (this.is('(')) this.skipBalancedParens();
    }
    parseJavaMods() {
      const mods = new Set();
      for (;;) {
        if (this.is('@') && !this.is('interface', 1)) { this.skipAnnotation(); continue; }
        if (this.isId() && J_MODS.has(this.peek().v)) {
          // "default" in interface methods; in switch it's a label - not here
          mods.add(this.next().v); continue;
        }
        break;
      }
      return mods;
    }
    parseJavaTypeDecl(outer) {
      const mods = this.parseJavaMods();
      const line = this.line();
      if (this.accept('enum')) {
        const name = this.ident('枚举名');
        this.expect('{');
        const st = this.structs.get(name);
        const consts = [];
        while (!this.is('}') && !this.is(';')) {
          consts.push(this.ident('枚举常量'));
          if (this.is('(')) this.skipBalancedParens();
          if (this.is('{')) this.skipBalanced();
          if (!this.accept(',')) break;
        }
        if (this.accept(';')) { while (!this.is('}')) this.next(); }
        this.expect('}');
        const es = this.newStruct(name, 'class');
        es.isEnum = true; es.enumConsts = consts; es.complete = true;
        this.structs.set(name, es);
        this.classes.push(es);
        return;
      }
      if (this.is('@') && this.is('interface', 1)) { this.next(); this.next(); this.ident(); this.skipBalanced(); return; }
      const kind = this.next().v;
      if (kind !== 'class' && kind !== 'interface' && kind !== 'record') this.err('这里应该是 class 定义', this.toks[this.p - 1]);
      const name = this.ident('类名');
      const st = this.structs.get(name) || this.newStruct(name, kind);
      this.structs.set(name, st);
      st.line = line;
      st.outer = outer;
      const tp = new Set();
      this.tplParams.push(tp);
      try {
        if (this.is('<')) { this.parseJavaTypeParams(tp); }
        if (kind === 'record') {
          this.expect('(');
          while (!this.accept(')')) { const ft = this.parseJavaType(); const fnm = this.ident(); st.fields.push({ name: fnm, type: ft, line }); st.methods.set(fnm, [{ type: 'Func', name: fnm, ret: ft, params: [], body: { type: 'Block', body: [{ type: 'Return', e: { type: 'Member', obj: { type: 'This', line }, name: fnm, line }, line }], line, endLine: line }, line, owner: st, synthetic: true }]); this.accept(','); }
          st.isRecord = true;
        }
        if (this.accept('extends')) {
          const bt = this.parseJavaType();
          if (kind === 'class' && bt.k === 'ptr' && bt.to.k === 'struct') st.base = bt.to;
          while (this.accept(',')) this.parseJavaType();
        }
        if (this.accept('implements')) { do { this.parseJavaType(); } while (this.accept(',')); }
        if (this.accept('permits')) { do { this.parseJavaType(); } while (this.accept(',')); }
        this.expect('{', '类体');
        while (!this.accept('}')) {
          if (this.peek().t === 'eof') this.err('类 ' + name + ' 缺少右花括号 }');
          this.parseJavaMember(st);
        }
      } finally { this.tplParams.pop(); }
      st.complete = true;
      this.classes.push(st);
    }
    parseJavaTypeParams(set) {
      this.expect('<');
      for (;;) {
        while (this.is('@')) this.skipAnnotation();
        set.add(this.ident('类型参数'));
        if (this.accept('extends')) { this.parseJavaType(); while (this.accept('&')) this.parseJavaType(); }
        if (!this.accept(',')) break;
      }
      this.closeAngle();
    }
    parseJavaMember(st) {
      if (this.accept(';')) return;
      const line = this.line();
      if (this.is('{') || (this.is('static') && this.is('{', 1))) {
        const isStatic = !!this.accept('static');
        const b = this.parseBlock();
        if (isStatic) st.staticInit.push(b); else st.fieldInits.push({ block: b });
        return;
      }
      const save = this.p;
      const mods = this.parseJavaMods();
      if (this.is('class') || this.is('interface') || this.is('enum') || this.is('record') || (this.is('@') && this.is('interface', 1))) {
        this.p = save; this.parseJavaTypeDecl(st); return;
      }
      const tp = new Set();
      this.tplParams.push(tp);
      try {
        if (this.is('<')) this.parseJavaTypeParams(tp);
        // constructor
        if (this.peek().v === st.name && this.is('(', 1)) {
          this.next();
          const params = this.parseJavaParams();
          if (this.accept('throws')) { do { this.parseJavaType(); } while (this.accept(',')); }
          const body = this.parseBlock();
          this.addMethod(st, { type: 'Func', name: st.name, ret: T.void, params, body, line, endLine: this.toks[this.p - 1].line, owner: st, isCtor: true, isStatic: false });
          return;
        }
        // compact record constructor
        if (st.isRecord && this.peek().v === st.name && this.is('{', 1)) { this.next(); this.skipBalanced(); return; }
        const ty = this.parseJavaType();
        const name = this.ident('成员名');
        if (this.is('(')) {
          const params = this.parseJavaParams();
          while (this.accept('[')) this.expect(']');
          if (this.accept('throws')) { do { this.parseJavaType(); } while (this.accept(',')); }
          let body = null;
          if (this.is('{')) body = this.parseBlock(); else this.expect(';');
          this.addMethod(st, { type: 'Func', name, ret: ty, params, body, line, endLine: this.toks[this.p - 1].line, owner: st, isStatic: mods.has('static') || st.isInterface && !body && false });
          return;
        }
        // fields
        let fname = name;
        for (;;) {
          let ft = ty;
          while (this.accept('[')) { this.expect(']'); ft = T.ptr(ft, { jarr: true }); }
          let init = null;
          if (this.accept('=')) init = this.is('{') ? this.parseJavaArrayInit() : this.parseAssign();
          const f = { name: fname, type: ft, init, line };
          if (mods.has('static') || st.isInterface) st.staticFields.push(f); else st.fields.push(f);
          if (!this.accept(',')) break;
          fname = this.ident('字段名');
        }
        this.expect(';', '字段声明结尾');
      } finally { this.tplParams.pop(); }
    }
    parseJavaParams() {
      this.expect('(');
      const params = [];
      if (this.accept(')')) return params;
      for (;;) {
        while (this.is('final') || this.is('@')) { if (this.is('@')) this.skipAnnotation(); else this.next(); }
        let t = this.parseJavaType();
        let varargs = false;
        if (this.accept('...')) { t = T.ptr(t, { jarr: true }); varargs = true; }
        const name = this.ident('参数名');
        while (this.accept('[')) { this.expect(']'); t = T.ptr(t, { jarr: true }); }
        params.push({ name, type: t, varargs, line: this.line() });
        if (!this.accept(',')) break;
      }
      this.expect(')', '参数列表结尾');
      return params;
    }
    parseJavaTplArgs() {
      const args = [];
      this.expect('<');
      if (this.is('>')) { this.next(); return args; }
      for (;;) {
        if (this.accept('?')) { if (this.accept('extends') || this.accept('super')) args.push(this.parseJavaType()); else args.push(T.any); }
        else args.push(this.parseJavaType());
        if (!this.accept(',')) break;
      }
      this.closeAngle();
      return args;
    }
    javaTypeFromName(name, targs) {
      if (J_PRIMS[name]) return J_PRIMS[name];
      if (name === 'String' || name === 'CharSequence') return T.jstring;
      if (name === 'var') return T.auto;
      if (CONTAINERS_JAVA.has(name)) return T.cont(name, targs || []);
      if (this.isTplParam(name)) return T.any;
      const st = this.structs.get(name);
      if (st) {
        if (st.k === 'enumT') return T.int;
        return T.ptr(st, { jref: true });
      }
      if (JAVA_ANY.has(name)) return Object.assign({}, T.any, { name, boxName: name });
      return null;
    }
    parseJavaType() {
      const t = this.peek();
      if (t.t !== 'id') this.err('这里应该是一个类型名');
      let name = this.next().v;
      while (this.is('.') && this.isId(1) && /^[A-Z]/.test(this.peek(1).v)) { this.next(); name = this.next().v; }
      if (name === 'Map' && false) {}
      let targs = [];
      if (this.is('<')) targs = this.parseJavaTplArgs();
      let ty = this.javaTypeFromName(name, targs);
      if (!ty) this.err('未知的类型 “' + name + '”。如果是你自己写的类，请检查类名拼写。', t);
      while (this.is('[') && this.is(']', 1)) { this.next(); this.next(); ty = T.ptr(ty, { jarr: true }); }
      return ty;
    }
    isJavaDeclStart() {
      const t = this.peek();
      if (t.t !== 'id') return false;
      if (t.v === 'final') return true;
      if (t.v === 'var') return this.isId(1) && this.is('=', 2);
      if (!this.isTypeStart()) return false;
      // Type name  |  Type<...> name  |  Type[] name
      let j = 1;
      while (this.is('.', j) && this.isId(j + 1) && /^[A-Z]/.test(this.peek(j + 1).v)) j += 2;
      if (this.is('<', j)) {
        let depth = 0;
        do {
          if (this.is('<', j)) depth++;
          else if (this.is('>', j)) depth--;
          else if (this.is('>>', j)) depth -= 2;
          else if (this.is('>>>', j)) depth -= 3;
          else if (this.peek(j).t === 'eof' || this.is(';', j)) return false;
          j++;
        } while (depth > 0);
      }
      while (this.is('[', j) && this.is(']', j + 1)) j += 2;
      return this.peek(j).t === 'id';
    }
    parseJavaLocalDecl(noSemi) {
      const line = this.line();
      while (this.is('final') || this.is('@')) { if (this.is('@')) this.skipAnnotation(); else this.next(); }
      const ty = this.parseJavaType();
      const decls = [];
      for (;;) {
        const dl = this.line();
        const name = this.ident('变量名');
        let t = ty;
        while (this.accept('[')) { this.expect(']'); t = T.ptr(t, { jarr: true }); }
        let init = null;
        if (this.accept('=')) init = this.is('{') ? this.parseJavaArrayInit() : this.parseAssign();
        decls.push({ name, vtype: t, init, line: dl });
        if (!this.accept(',')) break;
      }
      if (!noSemi) {
        if (!this.is(';')) throw new CompileError('声明末尾缺少分号 “;”', this.toks[this.p - 1].line);
        this.next();
      }
      return { type: 'Decl', decls, line };
    }
  }

  DSV.CT = T;
  DSV.clikeParseToks = function (toks, dialect, includes) {
    const p = new Parser(toks, dialect);
    if (dialect !== 'java' && includes && includes.some(h => /cs50/.test(h))) p.typedefs.set('string', T.ptr(T.char));
    const prog = p.parseProgram();
    prog.includes = includes || [];
    return prog;
  };
  DSV.clikeParse = function (src, dialect) {
    const lx = DSV.clikeLex(src, dialect);
    return DSV.clikeParseToks(lx.toks, dialect, lx.includes);
  };
})(typeof window !== 'undefined' ? window : globalThis);
