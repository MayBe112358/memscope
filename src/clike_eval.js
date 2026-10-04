// ===== C / C++ / Java expression evaluation =====
(function (G) {
  const DSV = G.DSV;
  const { RunError } = DSV;
  const T = DSV.CT;
  const { Block, Ptr, NULLP, MObj, Lambda, FnRef, ThrowSignal, StreamObj, MemLV, ElemLV, MapLV, StrCharLV, SbCharLV, TmpLV, isInt, isFlt, isArith, isPtrT } = DSV.clikeRT;
  const P = DSV.ClikeInterp.prototype;

  const CONSTS = {
    INT_MAX: [2147483647, T.int], INT_MIN: [-2147483648, T.int], UINT_MAX: [4294967295, T.uint],
    LONG_MAX: [9223372036854775807, T.long], LONG_MIN: [-9223372036854775808, T.long], LLONG_MAX: [9223372036854775807, T.llong], LLONG_MIN: [-9223372036854775808, T.llong],
    CHAR_MAX: [127, T.int], CHAR_MIN: [-128, T.int], SHRT_MAX: [32767, T.int], RAND_MAX: [2147483647, T.int], EOF: [-1, T.int],
    EXIT_SUCCESS: [0, T.int], EXIT_FAILURE: [1, T.int], SIZE_MAX: [18446744073709551615, T.size_t],
    INFINITY: [Infinity, T.double], NAN: [NaN, T.double], M_PI: [Math.PI, T.double], M_E: [Math.E, T.double],
    FLT_MAX: [3.4028234663852886e38, T.float], DBL_MAX: [Number.MAX_VALUE, T.double], INT32_MAX: [2147483647, T.int], INT32_MIN: [-2147483648, T.int], INT64_MAX: [9223372036854775807, T.long],
    true: [1, T.bool], false: [0, T.bool], npos: [-1, T.long], 'string::npos': [-1, T.long],
  };

  P.boolT = function () { return this.java ? T.jboolean : (this.cpp ? T.bool : T.int); };
  P.mkBool = function (b) { return { t: this.boolT(), v: b ? 1 : 0 }; };

  // value with .lv for reference binding
  P.evArg = function (e) {
    if (this.isLvalueExpr(e)) {
      const lv = this.lv(e);
      const v = this.load(lv);
      return Object.assign({}, v, { lv });
    }
    return this.ev(e);
  };

  // ======================= rvalue evaluation =======================
  P.ev = function (e, discard) {
    switch (e.type) {
      case 'Num': return { t: e.ct, v: e.v };
      case 'Char': return { t: this.java ? T.jchar : (this.cpp ? T.char : T.int), v: e.v, isCharLit: true };
      case 'Bool': return { t: this.java ? T.jboolean : (this.cpp ? T.bool : T.int), v: e.v };
      case 'Str':
        if (this.java) return { t: T.jstring, v: e.v };
        return { t: T.ptr(T.char), v: this.strLit(e.v), strLit: e.v };
      case 'Null': return { t: T.nullptr, v: NULLP, isNull: true };
      case 'Ident': return this.evIdent(e);
      case 'This': {
        const fr = this.thisFrame();
        if (!fr || !fr.thisPtr) throw new RunError('只能在成员函数里使用 this', 'runtime');
        return { t: T.ptr(fr.cls, this.java ? { jref: true } : undefined), v: fr.thisPtr };
      }
      case 'Binary': return this.evBinary(e);
      case 'Assign': return this.evAssign(e, discard);
      case 'Unary': return this.evUnary(e);
      case 'PreInc': case 'PostInc': return this.evIncDec(e);
      case 'Deref': {
        const p = this.ev(e.e);
        if (p.t.k === 'iter') return this.load(this.iterLV(p.v));
        if (p.t.k === 'ptr' && p.t.to.k === 'func') return p;
        return this.load(this.derefLV(p, e));
      }
      case 'AddrOf': {
        if (e.e.type === 'Ident' && !this.lookupVarOrMember(e.e.name)) { const fv = this.evIdent(e.e); if (fv.t.k === 'func' || fv.t.k === 'ptr' && fv.t.to.k === 'func') return fv; }
        const lv = this.lv(e.e);
        if (!(lv instanceof MemLV)) {
          if (lv instanceof ElemLV && lv.obj.ctype === 'vector') return { t: { k: 'iter' }, v: { obj: lv.obj, idx: lv.idx } };
          throw new RunError('不支持对这种表达式取地址', 'runtime');
        }
        return { t: T.ptr(lv.t), v: new Ptr(lv.blk, lv.off) };
      }
      case 'Index': case 'Member': {
        if (e.type === 'Member') { const sv = this.evMemberSpecial(e); if (sv) return sv; }
        return this.load(this.lv(e));
      }
      case 'Call': return this.evCall(e, discard);
      case 'Cond': {
        const c = this.truthy(this.ev(e.c));
        const a = this.ev(c ? e.a : e.b);
        if (a.t.k === 'prim') {
          // usual arithmetic conversion with other branch type (static-ish)
          try { const ot = this.typeOfExpr(c ? e.b : e.a); if (ot && ot.k === 'prim' && ot.fl && !a.t.fl) return this.convert(a, ot); } catch (er) { }
        }
        return a;
      }
      case 'Comma': { let r; for (const x of e.list) r = this.ev(x, true); return r; }
      case 'Cast': {
        const v = this.ev(e.e);
        let t = e.ty;
        if (t.k === 'ptr' && t.jref) {
          // java cast check
          if (v.v && v.v.blk && v.v.blk.type && v.v.blk.type.k === 'struct' && !this.isSubclass(v.v.blk.type, t.to)) throw new RunError('ClassCastException：' + v.v.blk.type.name + ' 不能转换为 ' + t.to.name, 'runtime');
          if (v.t.k === 'any' && v.v) return this.convert(v.v, t);
          return { t, v: v.v };
        }
        if (t.k === 'ptr' && v.t.k === 'ptr' && v.v && v.v.blk) this.inferViewType(v.v.blk, t.to);
        if (t.k === 'prim' && v.t.k === 'any') return this.convert(v.v, t);
        if (t.k === 'any' && v.t.k !== 'any') return { t: v.t, v: v.v };
        if (t.k === 'void') return { t: T.void, v: 0 };
        if (t.k === 'string' && v.t.k === 'any') return this.convert(v.v, t);
        return this.convert(v, t);
      }
      case 'SizeofType': return { t: T.size_t, v: this.sizeOf(this.resolveVLA(e.ty)) };
      case 'SizeofExpr': {
        const t = this.typeOfExpr(e.e);
        return { t: T.size_t, v: this.sizeOf(t) };
      }
      case 'New': return this.evNew(e);
      case 'NewArray': return this.evNewArray(e);
      case 'Delete': return this.evDelete(e);
      case 'InitList': {
        // braced list as expression (C++): becomes a list for containers
        return { t: { k: 'initlist' }, v: e.items.map(x => this.ev(x)), node: e };
      }
      case 'Construct': return this.evConstruct(e);
      case 'Lambda': return { t: { k: 'lambda', name: 'lambda' }, v: new Lambda(e, this.frame) };
      case 'InstanceOf': {
        const v = this.ev(e.e);
        let ok = false;
        const tt = e.tname;
        let obj = v;
        if (v.t.k === 'any') obj = v.v;
        if (obj && obj.v != null) {
          if (tt.k === 'ptr' && tt.jref) ok = obj.t.k === 'ptr' && obj.v.blk && this.isSubclass(obj.v.blk.type, tt.to);
          else if (tt.k === 'string') ok = obj.t.k === 'string';
          else if (tt.k === 'any') ok = tt.boxName ? this.boxMatches(obj, tt.boxName) : true;
          else if (tt.k === 'cont') ok = obj.t.k === 'cont';
        }
        if (ok && e.bind) { const vv = this.declareVar(e.bind, tt.k === 'any' ? obj.t : tt, e.line); this.storeInit(this.varLV(vv), obj); }
        return this.mkBool(ok);
      }
      case 'MethodRef': return this.evMethodRef(e);
      case 'Super': {
        const fr = this.thisFrame();
        return { t: T.ptr(fr.cls.base, { jref: true }), v: fr.thisPtr, isSuper: true };
      }
    }
    throw new RunError('暂不支持的表达式：' + e.type, 'runtime');
  };
  P.boxMatches = function (v, name) {
    const t = v.t;
    switch (name) {
      case 'Integer': return t.k === 'prim' && !t.fl && t.size === 4 && !t.isChar && !t.isBool;
      case 'Long': return t.k === 'prim' && !t.fl && t.size === 8;
      case 'Double': return t.k === 'prim' && t.fl && t.size === 8;
      case 'Character': return t.k === 'prim' && t.isChar;
      case 'Boolean': return t.k === 'prim' && t.isBool;
      default: return true;
    }
  };

  P.thisFrame = function () {
    for (let f = this.frame; f; f = f.parent) if (f.thisPtr) return f;
    for (let i = this.frames.length - 1; i >= 0; i--) { const f = this.frames[i]; if (f.thisPtr) return f; if (!f.parent) break; }
    return this.frame && this.frame.thisPtr ? this.frame : null;
  };
  P.curClass = function () {
    for (let f = this.frame; f; f = f.parent) if (f.cls) return f.cls;
    return this.frame ? this.frame.cls : null;
  };

  P.lookupVarOrMember = function (name) {
    if (this.lookupVar(name)) return true;
    const fr = this.thisFrame();
    if (fr && fr.cls && this.findField(fr.cls, name)) return true;
    return false;
  };

  P.evIdent = function (e) {
    const name = e.name;
    const lv = this.identLV(name, e, true);
    if (lv) return this.load(lv);
    // functions
    const cls = this.curClass();
    if (cls) {
      const m = this.findMethods(cls, name);
      if (m) return { t: { k: 'func', name }, v: new FnRef(m[0], this.thisFrame() ? this.thisFrame().thisPtr : null) };
    }
    const fl = this.funcs.get(name);
    if (fl) return { t: T.ptr(T.func(fl[0].ret, fl[0].params.map(p => p.type))), v: new FnRef(fl[0]) };
    if (CONSTS[name]) return { t: CONSTS[name][1], v: CONSTS[name][0] };
    if (this.cpp || !this.java) {
      if (name === 'cout' || name === 'cerr' || name === 'clog') return { t: T.stream('ostream'), v: name === 'cout' ? this.cout : this.cerr };
      if (name === 'cin') return { t: T.stream('istream'), v: this.cin };
      if (name === 'endl') return { t: { k: 'manip', name: 'endl' }, v: 'endl' };
      if (name === 'fixed' || name === 'boolalpha' || name === 'noboolalpha' || name === 'scientific' || name === 'left' || name === 'right') return { t: { k: 'manip', name }, v: name };
      if (name === 'stdin' || name === 'stdout' || name === 'stderr') return { t: T.stream('FILE'), v: name === 'stdin' ? this.cin : this.cout };
      if (name === '__greater' || name === '__less') return { t: { k: 'lambda' }, v: { native: (args) => this.mkBool(name === '__greater' ? this.compareVals(args[0], args[1]) > 0 : this.compareVals(args[0], args[1]) < 0) } };
    }
    if (this.java) {
      // class reference (for static access)
      const st = this.classesByName.get(name);
      if (st) return { t: { k: 'class', st }, v: st };
      if (JAVA_STATIC.has(name)) return { t: { k: 'bclass', name }, v: name };
      if (name === '__jassert') return { t: { k: 'builtin' }, v: name };
    }
    if (this.isBuiltinFunc(name)) return { t: { k: 'builtinfn', name }, v: name };
    throw new RunError('使用了未声明的名字 “' + name + '”。', 'runtime', '检查变量是否已经声明、是否在作用域内，或者名字是否拼错。');
  };
  const JAVA_STATIC = new Set(['Math', 'Integer', 'String', 'Arrays', 'Collections', 'System', 'Character', 'Double', 'Long', 'Boolean', 'Objects', 'List', 'Map', 'Set', 'Thread', 'Float', 'Short', 'Byte', 'StringBuilder']);

  // find a variable / implicit member / static / global as an lvalue
  P.identLV = function (name, e, soft) {
    const v = this.lookupVar(name);
    if (v) return this.varLV(v);
    const fr = this.thisFrame();
    if (fr && fr.cls && fr.thisPtr) {
      const st = fr.thisPtr.blk ? (fr.thisPtr.blk.type && fr.thisPtr.blk.type.k === 'struct' ? fr.cls : fr.cls) : fr.cls;
      const f = this.findField(st, name);
      if (f) return new MemLV(fr.thisPtr.blk, fr.thisPtr.off + f.offset, f.type, false, (this.java ? 'this.' : 'this->') + name);
    }
    // static fields of current class (and outer / base classes)
    for (let cls = this.curClass(); cls; cls = cls.outer || null) {
      for (let s = cls; s; s = s.base) {
        const key = this.java ? s.name + '.' + name : s.name + '::' + name;
        const g = this.globals.get(key);
        if (g) return new MemLV(g.blk, 0, g.t, false, key);
      }
    }
    const g = this.globals.get(name);
    if (g) return new MemLV(g.blk, 0, g.t, false, name);
    if (soft) return null;
    throw new RunError('使用了未声明的变量 “' + name + '”。', 'runtime', '检查变量是否已经声明、是否在当前作用域内，或者名字是否拼错。');
  };

  // ======================= lvalues =======================
  P.lv = function (e) {
    switch (e.type) {
      case 'Ident': {
        const lv = this.identLV(e.name, e, true);
        if (lv) return lv;
        if (CONSTS[e.name] || this.funcs.has(e.name)) throw new RunError('“' + e.name + '” 不是变量，不能被赋值', 'runtime');
        return this.identLV(e.name, e);
      }
      case 'Deref': {
        const p = this.ev(e.e);
        if (p.t.k === 'iter') return this.iterLV(p.v);
        return this.derefLV(p, e);
      }
      case 'Index': return this.indexLV(e);
      case 'Member': return this.memberLV(e);
      case 'This': { const fr = this.thisFrame(); return new TmpLV({ t: T.ptr(fr.cls), v: fr.thisPtr }); }
      case 'Cond': { const c = this.truthy(this.ev(e.c)); return this.lv(c ? e.a : e.b); }
      case 'Assign': { this.ev(e); return this.lv(e.l); }
      case 'PreInc': { this.ev(e); return this.lv(e.e); }
      case 'Call': {
        const r = this.evCall(e);
        if (r && r.lv) return r.lv;
        if (r && r.t.k === 'struct') return r.v;
        return new TmpLV(r);
      }
      case 'Cast': { const v = this.ev(e); return new TmpLV(v); }
    }
    const v = this.ev(e);
    if (v.t.k === 'struct') return v.v;
    throw new RunError('这个表达式不是可以赋值的变量（不是左值）', 'runtime', '赋值号 = 左边必须是变量、数组元素、结构体成员或解引用的指针。');
  };
  P.exprText = function (e) {
    switch (e.type) {
      case 'Ident': return e.name;
      case 'Member': return this.exprText(e.obj) + (e.arrow ? '->' : '.') + e.name;
      case 'Index': return this.exprText(e.obj) + '[' + this.exprText(e.idx) + ']';
      case 'Deref': return '*' + this.exprText(e.e);
      case 'Num': return String(e.v);
      case 'This': return 'this';
      case 'Call': return this.exprText(e.callee) + '(...)';
      case 'Binary': return this.exprText(e.l) + ' ' + e.op + ' ' + this.exprText(e.r);
      case 'Unary': return e.op + this.exprText(e.e);
      case 'PostInc': return this.exprText(e.e) + e.op;
      default: return '…';
    }
  };
  P.derefLV = function (p, e) {
    if (p.t.k === 'any') p = p.v ? p.v : { t: T.nullptr, v: NULLP };
    if (p.t.k !== 'ptr' && p.t.k !== 'nullptr') throw new RunError('只能对指针使用 * 解引用，但 “' + this.exprText(e.e || e) + '” 的类型是 ' + T.name(p.t), 'runtime');
    const ptr = p.v;
    let t = p.t.k === 'nullptr' ? T.int : p.t.to;
    if (t.k === 'void') throw new RunError('不能直接解引用 void* 指针，需要先把它转换成具体的指针类型。', 'runtime', '例如 (int *) p 或者把它赋值给 node * 类型的变量。');
    const lv = new MemLV(ptr.blk, ptr.off, t, true, '*' + this.exprText(e.e || e));
    if (ptr.wild) lv.wild = true;
    return lv;
  };
  P.indexLV = function (e) {
    const base = this.ev(e.obj);
    let idxV = this.ev(e.idx);
    if (base.t.k === 'cont') return this.contIndexLV(base, idxV, e);
    if (base.t.k === 'string') {
      if (this.java) throw new RunError('Java 的字符串不能用 [] 取字符，请使用 s.charAt(i)', 'runtime');
      const lvb = this.isLvalueExpr(e.obj) ? this.lv(e.obj) : new TmpLV(base);
      return new StrCharLV(lvb, this.convert(idxV, T.long).v, T.char);
    }
    if (base.t.k === 'any' && base.v) return this.indexLV({ type: 'Index', obj: { type: '__val', val: base.v }, idx: e.idx, line: e.line });
    let ptrV = base, iv = idxV;
    if (idxV.t.k === 'ptr' && base.t.k === 'prim') { ptrV = idxV; iv = base; } // 2[arr]
    if (ptrV.t.k !== 'ptr') throw new RunError('“' + this.exprText(e.obj) + '” 不是数组或指针，不能使用下标 []', 'runtime');
    const i = this.convert(iv, T.long).v;
    const et = ptrV.t.to;
    const es = this.sizeOf(et);
    const p = ptrV.v;
    const lv = new MemLV(p.blk, p.off + i * es, et, true, this.exprText(e.obj) + '[' + i + ']');
    if (p.wild) lv.wild = true;
    if (this.java && !p.blk) lv.desc = this.exprText(e.obj);
    return lv;
  };
  P.memberLV = function (e) {
    if (e.obj.type === 'Ident' && this.java) {
      // static field access Class.field
      const st = this.classesByName.get(e.obj.name);
      if (st && !this.lookupVar(e.obj.name) && !this.identLV(e.obj.name, e, true)) {
        for (let s = st; s; s = s.base) {
          const g = this.globals.get(s.name + '.' + e.name);
          if (g) return new MemLV(g.blk, 0, g.t, false, s.name + '.' + e.name);
        }
        throw new RunError('类 ' + st.name + ' 没有静态成员 ' + e.name, 'runtime');
      }
    }
    if (e.obj.type === 'Ident' && this.cpp && !this.lookupVar(e.obj.name)) {
      const g = this.globals.get(e.obj.name + '::' + e.name);
      if (g) return new MemLV(g.blk, 0, g.t);
    }
    let objV;
    if (e.obj.type === '__val') objV = e.obj.val;
    else if (!e.arrow && !this.java) {
      const olv = this.lv(e.obj);
      if (olv instanceof MemLV && olv.t.k === 'struct') {
        const f = this.findField(olv.t, e.name);
        if (!f) throw new RunError(T.name(olv.t) + ' 没有名为 “' + e.name + '” 的成员', 'runtime', '检查成员名是否拼写正确。');
        const r = new MemLV(olv.blk, olv.off + f.offset, f.type, olv.check, this.exprText(e));
        if (olv.wild) r.wild = true;
        return r;
      }
      objV = this.load(olv);
    } else objV = this.ev(e.obj);
    if (objV.t.k === 'any') objV = objV.v || { t: T.nullptr, v: NULLP };
    let st, ptr;
    if (objV.t.k === 'ptr' || objV.t.k === 'nullptr') {
      if (!e.arrow && !this.java && objV.t.k === 'ptr') throw new RunError('“' + this.exprText(e.obj) + '” 是指针，访问成员应该用 -> 而不是 .', 'runtime', '例如 ptr->next，或者 (*ptr).next。');
      ptr = objV.v;
      st = objV.t.k === 'ptr' ? objV.t.to : null;
      if (st && st.k === 'void') throw new RunError('不能通过 void* 指针访问成员', 'runtime');
      if (!ptr.blk) {
        const lv = new MemLV(null, 0, T.int, true, this.exprText(e));
        if (ptr.wild) lv.wild = true;
        this.checkAccess(lv);
      }
      if (this.java && ptr.blk && ptr.blk.type && ptr.blk.type.k === 'struct') st = ptr.blk.type;
      if (!st || st.k !== 'struct') {
        if (st && st.k === 'arr' && e.name === 'length') return new TmpLV({ t: T.int, v: st.len });
        if (ptr.blk && ptr.blk.type && ptr.blk.type.k === 'struct') st = ptr.blk.type;
        else if (ptr.blk && ptr.blk.type && ptr.blk.type.k === 'arr' && e.name === 'length') return new TmpLV({ t: T.int, v: ptr.blk.type.len });
        else throw new RunError('“' + this.exprText(e.obj) + '” 不是结构体指针，不能访问成员 ' + e.name, 'runtime');
      }
    } else if (objV.t.k === 'struct') {
      st = objV.t; const loc = objV.v; ptr = new Ptr(loc.blk, loc.off);
      if (e.arrow) throw new RunError('“' + this.exprText(e.obj) + '” 不是指针，访问成员应该用 . 而不是 ->', 'runtime');
    } else if (objV.t.k === 'cont') {
      return this.contMemberLV(objV, e);
    } else if (objV.t.k === 'iter') {
      return this.contMemberLV({ t: objV.t, v: objV.v }, e);
    } else {
      throw new RunError('“' + this.exprText(e.obj) + '” 的类型是 ' + T.name(objV.t) + '，没有成员 ' + e.name, 'runtime');
    }
    const f = this.findField(st, e.name);
    if (!f) {
      if (this.java && e.name === 'length' && st.k === 'arr') return new TmpLV({ t: T.int, v: st.len });
      throw new RunError(T.name(st) + ' 没有名为 “' + e.name + '” 的成员', 'runtime', '检查成员名是否拼写正确。');
    }
    return new MemLV(ptr.blk, ptr.off + f.offset, f.type, true, this.exprText(e));
  };
  // special member values that aren't lvalues (System.out, arr.length, Class.CONST)
  P.evMemberSpecial = function (e) {
    if (!this.java) {
      if (e.obj.type === 'Ident' && this.cpp && !this.lookupVar(e.obj.name)) return null;
      return null;
    }
    if (e.obj.type === 'Ident' && !this.lookupVar(e.obj.name) && !this.identLV(e.obj.name, e, true)) {
      const n = e.obj.name;
      if (n === 'System' && (e.name === 'out' || e.name === 'err')) return { t: T.stream('PrintStream'), v: this.cout };
      if (n === 'System' && e.name === 'in') return { t: T.stream('InputStream'), v: this.cin };
      const st = this.classesByName.get(n);
      if (st && st.isEnum) {
        const i = st.enumConsts.indexOf(e.name);
        if (i >= 0) return this.enumValue(st, i);
      }
      const cv = javaStaticConst(n, e.name);
      if (cv) return cv;
    }
    if (e.name === 'length') {
      const o = this.ev(e.obj);
      let ov = o.t.k === 'any' ? o.v : o;
      if (ov && ov.t.k === 'ptr' && ov.t.jarr) {
        if (!ov.v.blk) throw new RunError('NullPointerException：数组是 null，无法读取 length', 'segfault');
        return { t: T.int, v: ov.v.blk.type.len };
      }
      if (ov && ov.t.k === 'ptr' && ov.v.blk && ov.v.blk.type && ov.v.blk.type.k === 'arr') return { t: T.int, v: ov.v.blk.type.len };
    }
    return null;
  };
  function javaStaticConst(cls, name) {
    const m = {
      'Integer.MAX_VALUE': [2147483647, T.int], 'Integer.MIN_VALUE': [-2147483648, T.int],
      'Long.MAX_VALUE': [9223372036854775807, T.long], 'Long.MIN_VALUE': [-9223372036854775808, T.long],
      'Double.MAX_VALUE': [Number.MAX_VALUE, T.double], 'Double.MIN_VALUE': [Number.MIN_VALUE, T.double],
      'Double.POSITIVE_INFINITY': [Infinity, T.double], 'Double.NEGATIVE_INFINITY': [-Infinity, T.double],
      'Math.PI': [Math.PI, T.double], 'Math.E': [Math.E, T.double], 'Character.MAX_VALUE': [65535, T.jchar],
      'Short.MAX_VALUE': [32767, T.short], 'Byte.MAX_VALUE': [127, T.byte],
    }[cls + '.' + name];
    return m ? { t: m[1], v: m[0] } : null;
  }
  P.enumValue = function (st, i) {
    // enums represented as heap-less tagged value
    st.enumObjs = st.enumObjs || [];
    if (!st.enumObjs[i]) {
      this.layout(st);
      const blk = this.newBlock('global', Math.max(1, st.size), st, st.name + '.' + st.enumConsts[i]);
      blk.zero = true; blk.enumIdx = i; blk.typed = true; blk.isEnum = true;
      st.enumObjs[i] = blk;
    }
    return { t: T.ptr(st, { jref: true }), v: new Ptr(st.enumObjs[i], 0) };
  };

  // ======================= static type inference (for sizeof etc.) =======================
  P.typeOfExpr = function (e) {
    switch (e.type) {
      case 'Ident': {
        const v = this.lookupVar(e.name);
        if (v) return v.t;
        const lv = this.identLV(e.name, e, true);
        if (lv) return lv.t;
        return this.ev(e).t;
      }
      case 'Deref': { const t = this.typeOfExpr(e.e); if (t.k === 'ptr') return t.to; if (t.k === 'arr') return t.of; break; }
      case 'Index': { const t = this.typeOfExpr(e.obj); if (t.k === 'ptr') return t.to; if (t.k === 'arr') return t.of; break; }
      case 'Member': {
        let t = this.typeOfExpr(e.obj);
        if (e.arrow && t.k === 'ptr') t = t.to;
        if (t.k === 'struct') { const f = this.findField(t, e.name); if (f) return f.type; }
        break;
      }
      case 'Num': return e.ct;
      case 'Char': return this.cpp ? T.char : T.int;
      case 'Str': return T.arr(T.char, e.v.length + 1);
      case 'Cast': return e.ty;
      case 'AddrOf': return T.ptr(this.typeOfExpr(e.e));
      case 'SizeofType': case 'SizeofExpr': return T.size_t;
      case 'Call': if (e.callee.type === 'Ident') { const f = this.funcs.get(e.callee.name); if (f) return f[0].ret; } break;
      case 'Binary': {
        if (['==', '!=', '<', '>', '<=', '>=', '&&', '||'].includes(e.op)) return T.int;
        const a = this.typeOfExpr(e.l), b = this.typeOfExpr(e.r);
        if (a.k === 'ptr' || a.k === 'arr') return a.k === 'arr' ? T.ptr(a.of) : a;
        if (a.k === 'prim' && b.k === 'prim') return this.arithType(a, b);
        return a;
      }
      case 'Unary': return this.typeOfExpr(e.e);
    }
    return this.ev(e).t;
  };

  // ======================= arithmetic =======================
  P.arithType = function (a, b) {
    if (a.fl || b.fl) {
      if (this.java) return (a.fl && a.size === 8) || (b.fl && b.size === 8) ? T.double : T.float;
      if ((a.fl && a.size === 4 || !a.fl) && (b.fl && b.size === 4 || !b.fl)) return T.float;
      return T.double;
    }
    const pa = this.promote(a), pb = this.promote(b);
    if (pa.size > pb.size) return pa;
    if (pb.size > pa.size) return pb;
    if (!pa.signed) return pa;
    if (!pb.signed) return pb;
    return pa;
  };
  P.promote = function (t) {
    if (t.size < 4 || t.isBool) return T.int;
    return t;
  };
  P.unboxAny = function (v) {
    if (v && v.t.k === 'any') {
      if (v.v == null) throw new RunError((this.java ? 'NullPointerException：' : '') + '对 null 进行了运算（拆箱）', 'segfault', '包装类型（如 Integer）的变量可能是 null。');
      return v.v;
    }
    return v;
  };

  P.evBinary = function (e) {
    const op = e.op;
    if (op === '&&') {
      const a = this.ev(e.l);
      if (!this.truthy(a)) return this.mkBool(false);
      return this.mkBool(this.truthy(this.ev(e.r)));
    }
    if (op === '||') {
      const a = this.ev(e.l);
      if (this.truthy(a)) return this.mkBool(true);
      return this.mkBool(this.truthy(this.ev(e.r)));
    }
    const a = this.ev(e.l);
    // stream I/O
    if (a.t.k === 'stream' && (op === '<<' || op === '>>')) {
      if (op === '<<') { this.streamOut(a.v, this.ev(e.r)); return a; }
      this.streamIn(a.v, e.r); return a;
    }
    const b = this.ev(e.r);
    return this.binop(op, a, b, e.line, e);
  };

  P.binop = function (op, a, b, line, e) {
    if (a.t.k === 'any' && !(op === '==' || op === '!=') || a.t.k === 'any' && b.t.k !== 'any' && b.t.k !== 'nullptr' && b.t.k !== 'ptr' && b.t.k !== 'string' && b.t.k !== 'cont') a = this.unboxAny(a);
    if (b.t.k === 'any' && !(op === '==' || op === '!=') || b.t.k === 'any' && a.t.k !== 'any' && a.t.k !== 'nullptr' && a.t.k !== 'ptr' && a.t.k !== 'string' && a.t.k !== 'cont') b = this.unboxAny(b);
    const ta = a.t, tb = b.t;
    // string concat / compare
    if (ta.k === 'string' || tb.k === 'string') {
      if (op === '+') {
        if (this.java) return { t: T.jstring, v: this.javaStr(a) + this.javaStr(b) };
        return { t: T.string, v: this.cppStr(a) + this.cppStr(b) };
      }
      if (['==', '!=', '<', '>', '<=', '>='].includes(op)) {
        if (this.java && (op === '==' || op === '!=')) {
          if (ta.k === 'string' && tb.k === 'string' && a.v != null && b.v != null && !this.warnedStrEq) { this.warnedStrEq = true; this.rec.note('⚠ Java 中用 == 比较字符串，比较的是“是不是同一个对象”，而不是内容。比较内容请用 s1.equals(s2)。', 'warn'); }
          const r = (a.v == null || b.v == null) ? a.v === b.v : a.v === b.v;
          return this.mkBool(op === '==' ? r : !r);
        }
        const sa = ta.k === 'string' ? a.v : this.cppStr(a), sb = tb.k === 'string' ? b.v : this.cppStr(b);
        const c = sa < sb ? -1 : sa > sb ? 1 : 0;
        return this.mkBool(cmpOp(op, c));
      }
    }
    if (this.java && op === '+' && (ta.k === 'cont' && ta.name === 'StringBuilder')) return { t: T.jstring, v: this.javaStr(a) + this.javaStr(b) };
    // pointers / references
    const pa = ta.k === 'ptr' || ta.k === 'nullptr' || ta.k === 'func' || ta.k === 'lambda', pb = tb.k === 'ptr' || tb.k === 'nullptr' || tb.k === 'func' || tb.k === 'lambda';
    if (ta.k === 'iter' || tb.k === 'iter') return this.iterBinop(op, a, b);
    if (pa || pb || ta.k === 'any' || tb.k === 'any' || ta.k === 'cont' && (tb.k === 'nullptr' || tb.k === 'cont') || tb.k === 'cont' && ta.k === 'nullptr') {
      if (op === '==' || op === '!=') {
        let r;
        if ((ta.k === 'cont' && tb.k === 'cont') && this.cpp) r = this.compareVals(a, b) === 0;
        else if (ta.k === 'any' || tb.k === 'any') {
          const av = ta.k === 'any' ? a.v : a, bv = tb.k === 'any' ? b.v : b;
          if (av == null || bv == null || av.isNull || bv.isNull) r = (av == null || av.isNull || av.v && av.v.blk === null && !av.v.wild) === (bv == null || bv.isNull || bv.v && bv.v.blk === null && !bv.v.wild);
          else if (av.t.k === 'prim' && bv.t.k === 'prim') r = av.v === bv.v;
          else r = this.sameRef(av.v, bv.v);
        } else r = this.sameRef(a.v, b.v);
        return this.mkBool(op === '==' ? r : !r);
      }
      if (pa && ta.k === 'ptr' && isArith(tb) && (op === '+' || op === '-')) {
        if (!a.v.blk && !a.v.wild && this.java) throw new RunError('不能对引用做算术', 'runtime');
        const es = this.sizeOf(ta.to.k === 'void' ? T.char : ta.to);
        const n = op === '+' ? b.v : -b.v;
        return { t: ta, v: new Ptr(a.v.blk, a.v.off + n * es, a.v.wild) };
      }
      if (pb && tb.k === 'ptr' && isArith(ta) && op === '+') {
        const es = this.sizeOf(tb.to);
        return { t: tb, v: new Ptr(b.v.blk, b.v.off + a.v * es) };
      }
      if (pa && pb && op === '-') {
        const es = this.sizeOf(ta.to.k === 'void' ? T.char : ta.to);
        if (a.v.blk !== b.v.blk) this.rec.note('⚠ 两个指针指向不同的内存块，相减的结果没有意义', 'warn');
        const ad = (a.v.blk ? a.v.blk.addr : 0) + a.v.off, bd = (b.v.blk ? b.v.blk.addr : 0) + b.v.off;
        return { t: T.long, v: Math.trunc((ad - bd) / es) };
      }
      if (pa && pb && ['<', '>', '<=', '>='].includes(op)) {
        const ad = (a.v.blk ? a.v.blk.addr : 0) + a.v.off, bd = (b.v.blk ? b.v.blk.addr : 0) + b.v.off;
        return this.mkBool(cmpOp(op, ad < bd ? -1 : ad > bd ? 1 : 0));
      }
      if (ta.k === 'cont' && tb.k === 'cont' && ['<', '>', '<=', '>='].includes(op)) return this.mkBool(cmpOp(op, this.compareVals(a, b)));
      if (pa && isArith(tb) && (op === '==' || op === '!=')) { const r = !a.v.blk && b.v === 0; return this.mkBool(op === '==' ? r : !r); }
      if ((pa && isArith(tb) || pb && isArith(ta)) && ['<', '>', '<=', '>='].includes(op)) {
        const ad = pa ? (a.v.blk ? a.v.blk.addr + a.v.off : 0) : a.v, bd = pb ? (b.v.blk ? b.v.blk.addr + b.v.off : 0) : b.v;
        return this.mkBool(cmpOp(op, ad < bd ? -1 : ad > bd ? 1 : 0));
      }
      throw new RunError('不能对 ' + T.name(ta) + ' 和 ' + T.name(tb) + ' 使用运算符 ' + op, 'runtime');
    }
    if (ta.k === 'struct' || tb.k === 'struct') {
      throw new RunError('结构体不能直接用 ' + op + ' 运算（C/C++ 不会自动比较结构体）', 'runtime', '比较结构体需要逐个比较成员。');
    }
    if (ta.k === 'cont' || tb.k === 'cont') {
      if (ta.k === 'cont' && tb.k === 'cont') return this.mkBool(cmpOp(op, this.compareVals(a, b)));
      throw new RunError('不能对 ' + T.name(ta) + ' 使用运算符 ' + op, 'runtime');
    }
    if (!isArith(ta) || !isArith(tb)) throw new RunError('不能对 ' + T.name(ta) + ' 和 ' + T.name(tb) + ' 使用运算符 ' + op, 'runtime');
    // comparisons
    if (['==', '!=', '<', '>', '<=', '>='].includes(op)) {
      let x = a.v, y = b.v;
      if (!ta.fl && !tb.fl && ta.signed !== tb.signed && Math.max(ta.size, tb.size) >= 4 && !ta.isBool && !tb.isBool && !this.java) {
        const rt = this.arithType(ta, tb);
        if (!rt.signed) { x = this.wrapInt(x, rt); y = this.wrapInt(y, rt); }
      }
      if (ta.fl && tb.fl && ta.size !== tb.size) { x = Math.fround(x); y = Math.fround(y); }
      return this.mkBool(cmpOp(op, x < y ? -1 : x > y ? 1 : (x === y ? 0 : NaN)));
    }
    if (this.java && (ta.isBool || tb.isBool)) {
      if (op === '&') return this.mkBool(a.v && b.v);
      if (op === '|') return this.mkBool(a.v || b.v);
      if (op === '^') return this.mkBool(!!a.v !== !!b.v);
    }
    const rt = (op === '<<' || op === '>>' || op === '>>>') ? this.promote(ta) : this.arithType(ta, tb);
    let x = a.v, y = b.v;
    if (rt.fl) {
      let r;
      switch (op) {
        case '+': r = x + y; break; case '-': r = x - y; break; case '*': r = x * y; break;
        case '/': r = x / y; break;
        case '%': if (!this.java) throw new RunError('浮点数不能使用 % 运算（请使用 fmod）', 'runtime'); r = x % y; break;
        default: throw new RunError('浮点数不能使用运算符 ' + op, 'runtime');
      }
      return { t: rt, v: rt.size === 4 ? Math.fround(r) : r };
    }
    x = this.wrapInt(x, rt); y = (op === '<<' || op === '>>' || op === '>>>') ? Number(y) : this.wrapInt(y, rt);
    const big = rt.size === 8;
    let r;
    switch (op) {
      case '+': r = x + y; if (big && !Number.isSafeInteger(r)) r = bigOp(x, y, (p, q) => p + q, rt); break;
      case '-': r = x - y; if (big && !Number.isSafeInteger(r)) r = bigOp(x, y, (p, q) => p - q, rt); break;
      case '*':
        if (!big) r = rt.signed ? Math.imul(x, y) : (Math.imul(x, y) >>> 0);
        else { r = x * y; if (!Number.isSafeInteger(r)) r = bigOp(x, y, (p, q) => p * q, rt); }
        break;
      case '/': case '%':
        if (y === 0) {
          if (this.java) throw new RunError('ArithmeticException: / by zero（整数除以零）', 'div0', '整数不能除以 0，检查除数。');
          throw new RunError('整数除以零（Floating point exception）', 'div0', '整数不能除以 0，在除法前检查除数是否为 0。');
        }
        r = op === '/' ? Math.trunc(x / y) : x % y;
        if (big && !Number.isSafeInteger(x)) r = bigOp(x, y, op === '/' ? (p, q) => p / q : (p, q) => p % q, rt);
        break;
      case '&': r = big && (Math.abs(x) > 2 ** 31 || Math.abs(y) > 2 ** 31) ? bigOp(x, y, (p, q) => p & q, rt) : (x & y); break;
      case '|': r = big && (Math.abs(x) > 2 ** 31 || Math.abs(y) > 2 ** 31) ? bigOp(x, y, (p, q) => p | q, rt) : (x | y); break;
      case '^': r = big && (Math.abs(x) > 2 ** 31 || Math.abs(y) > 2 ** 31) ? bigOp(x, y, (p, q) => p ^ q, rt) : (x ^ y); break;
      case '<<': {
        const s = y & (big ? 63 : 31);
        if (big) r = bigOp(x, s, (p, q) => p << q, rt);
        else r = x << s;
        break;
      }
      case '>>': {
        const s = y & (big ? 63 : 31);
        if (big) r = bigOp(x, s, (p, q) => rt.signed ? p >> q : BigInt.asUintN(64, p) >> q, rt);
        else r = rt.signed ? x >> s : x >>> s;
        break;
      }
      case '>>>': {
        const s = y & (big ? 63 : 31);
        if (big) r = bigOp(x, s, (p, q) => BigInt.asUintN(64, p) >> q, rt);
        else r = x >>> s;
        break;
      }
      default: throw new RunError('未知运算符 ' + op, 'runtime');
    }
    return { t: rt, v: this.wrapInt(r, rt) };
  };
  function bigOp(x, y, f, rt) {
    const bx = BigInt(Math.trunc(x)), by = BigInt(Math.trunc(y));
    let r = f(bx, by);
    r = rt.signed ? BigInt.asIntN(64, r) : BigInt.asUintN(64, r);
    return Number(r);
  }
  function cmpOp(op, c) {
    switch (op) {
      case '==': return c === 0; case '!=': return c !== 0; case '<': return c < 0; case '>': return c > 0; case '<=': return c <= 0; case '>=': return c >= 0;
    }
    return false;
  }
  P.cmpOp = cmpOp;
  P.sameRef = function (x, y) {
    if (x instanceof Ptr && y instanceof Ptr) return x.blk === y.blk && x.off === y.off && (!!x.wild === !!y.wild);
    if (x == null || y == null) {
      const xn = x == null || (x instanceof Ptr && !x.blk && !x.wild);
      const yn = y == null || (y instanceof Ptr && !y.blk && !y.wild);
      return xn === yn && (xn || x === y);
    }
    if (x instanceof Ptr && !x.blk) return y == null;
    if (y instanceof Ptr && !y.blk) return x == null;
    return x === y;
  };

  // ======================= assignment & inc/dec =======================
  P.evAssign = function (e, discard) {
    const lv = this.lv(e.l);
    if (e.op === '=') {
      let v;
      if (e.r.type === 'InitList') {
        const t = lv.t;
        if (t.k === 'cont') v = { t, v: this.constructCont(t, [], e.r.items), fresh: true };
        else if (t.k === 'struct') { const blk = this.newBlock('temp', this.sizeOf(t), t, ''); this.initVar(new MemLV(blk, 0, t), t, e.r, null, e.line); v = { t, v: new MemLV(blk, 0, t) }; }
        else v = e.r.items.length ? this.ev(e.r.items[0]) : { t, v: this.zeroOf(t) };
      } else v = this.ev(e.r);
      if (lv.t && lv.t.k === 'struct' && v.t.k === 'struct' && this.cpp) {
        const opm = this.findMethods(lv.t, 'operator=');
        if (opm) { this.callMethod(opm, [v], new Ptr(lv.blk, lv.off), e.line); return discard ? null : this.load(lv); }
      }
      if (lv.t && lv.t.k === 'cont' && this.cpp && v.fresh) this.store(lv, v, true);
      else this.store(lv, v);
      if (lv.t && lv.t.k === 'ptr' && v.v && v.v.blk && v.v.blk.freed && !this.warnedDangling) { this.warnedDangling = true; this.rec.note('⚠ 赋值了一个指向已释放内存的指针（悬空指针）。', 'warn'); }
      return discard ? null : this.load(lv);
    }
    const cur = this.load(lv);
    const r = this.ev(e.r);
    const bop = e.op.slice(0, -1);
    let res = this.binop(bop, cur, r, e.line, e);
    if (lv.t.k === 'any') { this.store(lv, res); return discard ? null : res; }
    this.store(lv, this.convertAssign(res, lv.t));
    return discard ? null : this.load(lv);
  };
  P.convertAssign = function (val, t) {
    if (t.k === 'prim' && val.t.k === 'prim') {
      if (t.fl) return { t, v: t.size === 4 ? Math.fround(val.v) : val.v };
      return { t, v: this.wrapInt(val.t.fl ? Math.trunc(val.v) : val.v, t) };
    }
    return val;
  };
  P.evIncDec = function (e) {
    const lv = this.lv(e.e);
    const cur = this.load(lv);
    let nv;
    const delta = e.op === '++' ? 1 : -1;
    let base = cur;
    if (cur.t.k === 'any') base = this.unboxAny(cur);
    if (base.t.k === 'prim') nv = { t: base.t, v: base.t.fl ? base.v + delta : this.wrapInt(base.v + delta, base.t) };
    else if (base.t.k === 'ptr') nv = { t: base.t, v: new Ptr(base.v.blk, base.v.off + delta * this.sizeOf(base.t.to.k === 'void' ? T.char : base.t.to), base.v.wild) };
    else if (base.t.k === 'iter') nv = { t: base.t, v: this.iterAdvance(base.v, delta) };
    else throw new RunError('不能对 ' + T.name(base.t) + ' 使用 ' + e.op, 'runtime');
    this.store(lv, nv);
    return e.type === 'PreInc' ? this.load(lv) : base;
  };

  P.evUnary = function (e) {
    let v = this.ev(e.e);
    if (v.t.k === 'any') v = this.unboxAny(v);
    switch (e.op) {
      case '!': return this.mkBool(!this.truthy(v));
      case '-': if (!isArith(v.t)) throw new RunError('不能对 ' + T.name(v.t) + ' 取负', 'runtime'); { const t = v.t.fl ? v.t : this.promote(v.t); return { t, v: t.fl ? -v.v : this.wrapInt(-v.v, t) }; }
      case '+': { const t = v.t.fl ? v.t : this.promote(v.t); return { t, v: v.v }; }
      case '~': { const t = this.promote(v.t); return { t, v: t.size === 8 ? Number(BigInt.asIntN(64, ~BigInt(v.v))) : this.wrapInt(~v.v, t) }; }
    }
    throw new RunError('未知运算符 ' + e.op, 'runtime');
  };

  // ======================= new / delete =======================
  P.evNew = function (e) {
    let ty = e.ty;
    if (this.java) {
      if (ty.k === 'ptr' && ty.jref) return this.newJavaObject(ty.to, e.args.map(a => this.ev(a)), e.line);
      if (ty.k === 'cont') return { t: ty, v: this.newJavaCont(ty, e.args.map(a => this.ev(a))) };
      if (ty.k === 'string') { const a = e.args.map(a => this.ev(a)); return { t: T.jstring, v: a.length ? this.javaStringCtor(a) : '' }; }
      if (ty.k === 'any') { const a = e.args.map(a => this.ev(a)); return a.length ? a[0] : { t: T.any, v: null }; }
      throw new RunError('不能 new 这个类型：' + T.name(ty), 'runtime');
    }
    if (ty.k === 'cont') { const m = this.constructCont(ty, e.args.map(a => this.ev(a))); const blk = this.newBlock('heap', 24, ty, ''); blk.typed = true; this.writeCell(blk, 0, ty, m); this.mallocCount++; this.rec.note('new 在堆上创建了一个 ' + T.name(ty), 'alloc'); return { t: T.ptr(ty), v: new Ptr(blk, 0) }; }
    const size = this.sizeOf(ty);
    const blk = this.newBlock('heap', size, ty, '');
    blk.typed = true; blk.viaNew = true;
    this.mallocCount++;
    const lv = new MemLV(blk, 0, ty);
    this.rec.note('new 在堆上创建了一个 ' + T.name(ty) + '（' + size + ' 字节，地址 ' + this.hex(blk.addr) + '）', 'alloc');
    if (ty.k === 'struct') this.constructAt(lv, e.args.map(a => this.evArg(a)), e.brace, false, e.args.length === 0 && false);
    else if (e.args.length) this.store(lv, this.ev(e.args[0]));
    else if (e.brace) this.store(lv, { t: ty, v: this.zeroOf(ty) });
    else this.defaultInit(lv, ty);
    return { t: T.ptr(ty), v: new Ptr(blk, 0) };
  };
  P.evNewArray = function (e) {
    if (this.java) {
      const dims = e.dims.map(d => this.convert(this.ev(d), T.int).v);
      if (e.init) return { t: this.javaArrType(e.elem, 1 + (e.extraDims || 0)), v: this.javaArrayFromInit(e.extraDims > 1 ? this.javaArrType(e.elem, e.extraDims - 1) : e.elem, e.init) };
      return { t: this.javaArrType(e.elem, dims.length + (e.extraDims || 0)), v: this.newJavaArray(e.elem, dims, e.extraDims || 0) };
    }
    const n = this.convert(this.ev(e.dims[0]), T.long).v;
    if (n < 0) throw new RunError('new 的数组长度不能是负数：' + n, 'runtime');
    const ty = e.elem;
    const es = this.sizeOf(ty);
    const at = T.arr(ty, n);
    const blk = this.newBlock('heap', Math.max(1, es * n), at, '');
    blk.typed = true; blk.viaNew = true; blk.newArr = true;
    this.mallocCount++;
    this.rec.note('new[] 在堆上创建了 ' + n + ' 个 ' + T.name(ty) + '（' + es * n + ' 字节）', 'alloc');
    const lv = new MemLV(blk, 0, at);
    if (e.init === 'zero') this.zeroFill(lv, at);
    else if (e.init) this.initList(lv, at, e.init, e.line);
    else this.defaultInit(lv, at);
    return { t: T.ptr(ty), v: new Ptr(blk, 0) };
  };
  P.evDelete = function (e) {
    const p = this.ev(e.e);
    if (p.t.k !== 'ptr' && p.t.k !== 'nullptr') throw new RunError('delete 只能用于指针', 'runtime');
    const ptr = p.v;
    if (!ptr.blk) { if (ptr.wild) throw new RunError('delete 了一个未初始化的指针', 'segfault'); this.rec.note('delete 空指针，什么也不做', 'info'); return { t: T.void, v: 0 }; }
    this.freeBlock(ptr, e.arr ? 'delete[]' : 'delete', e);
    return { t: T.void, v: 0 };
  };
  P.freeBlock = function (ptr, how, e) {
    const blk = ptr.blk;
    const what = how === 'free' ? 'free' : how;
    if (blk.freed) throw new RunError('重复释放（double free）：这块内存已经被释放过了，又对它调用了 ' + what + '。', 'uaf', '每块内存只能释放一次。释放后可以把指针设为 NULL，避免再次释放。');
    if (blk.kind !== 'heap') throw new RunError(what + ' 了一块不是在堆上分配的内存（' + (blk.kind === 'stack' ? '局部变量 “' + blk.name + '”' : blk.kind === 'str' ? '字符串字面量' : '全局/静态内存') + '）。', 'runtime', '只有 malloc/calloc/realloc（或 new）得到的内存才能被 free（或 delete）。');
    if (ptr.off !== 0) throw new RunError(what + ' 的指针没有指向这块内存的开头（偏移了 ' + ptr.off + ' 字节）。', 'runtime', '必须把 malloc 返回的原始指针传给 free。');
    if (this.cpp && how !== 'free') {
      const vt = blk.type;
      if (vt && vt.k === 'struct') this.destroyObject(new MemLV(blk, 0, vt));
      else if (vt && vt.k === 'arr' && vt.of.k === 'struct') { const es = this.sizeOf(vt.of); for (let i = vt.len - 1; i >= 0; i--) this.destroyObject(new MemLV(blk, i * es, vt.of)); }
      if (blk.newArr && how === 'delete') this.rec.note('⚠ 用 new[] 分配的数组应该用 delete[] 释放', 'warn');
    }
    blk.freed = true;
    blk.freedStep = this.rec.steps.length;
    this.freedCount++;
    const tn = blk.type ? T.name(blk.type) : '';
    this.rec.note(what + ' 释放了 ' + this.hex(blk.addr) + ' 处的 ' + blk.size + ' 字节' + (tn ? '（' + tn + '）' : ''), 'free');
  };
  const HEXC = new Map();
  P.hex = function (n) { let h = HEXC.get(n); if (!h) { h = '0x' + Math.round(n).toString(16); if (HEXC.size < 200000) HEXC.set(n, h); } return h; };

  // ======================= C++ objects =======================
  P.findMethods = function (st, name) {
    for (let s = st; s; s = s.base) {
      const m = s.methods && s.methods.get(name);
      if (m && m.length) return m;
    }
    return null;
  };
  P.constructAt = function (lv, args, brace, isDefault) {
    const st = lv.t;
    this.layout(st);
    const thisPtr = new Ptr(lv.blk, lv.off);
    if (st.ctors.length) {
      let ctor;
      // copy construction from same type with no user copy-ctor
      if (args.length === 1 && args[0].t === st && !st.ctors.some(c => c.params.length === 1 && c.params[0].type.k === 'ref' && c.params[0].type.to === st)) {
        this.copyStruct(lv, args[0]); return;
      }
      ctor = this.pickOverload(st.ctors, args, st.name + ' 的构造函数');
      this.callFunction(ctor, args, thisPtr, ctor.line, { beforeBody: (fr) => this.cppMemberInit(st, lv, ctor) });
      return;
    }
    if (args.length === 1 && args[0].t === st) { this.copyStruct(lv, args[0]); return; }
    // aggregate / default
    if (st.base) this.constructAt(new MemLV(lv.blk, lv.off, st.base), [], false, true);
    let i = 0;
    for (const f of st.fields) {
      const flv = new MemLV(lv.blk, lv.off + f.offset, f.type);
      if (i < args.length) { this.storeInit(flv, args[i]); i++; continue; }
      if (f.init) this.initVar(flv, f.type, f.init, null, f.line);
      else if (brace || args.length) this.zeroFill(flv, f.type);
      else this.defaultInit(flv, f.type);
    }
    if (i < args.length) throw new RunError('给 ' + st.name + ' 的初始值太多了', 'runtime');
  };
  P.cppMemberInit = function (st, lv, ctor) {
    const il = ctor.initList || [];
    if (st.base) {
      const ent = il.find(x => x.name === st.base.name);
      this.constructAt(new MemLV(lv.blk, lv.off, st.base), ent ? ent.args.map(a => this.evArg(a)) : [], false, !ent);
    }
    for (const f of st.fields) {
      const flv = new MemLV(lv.blk, lv.off + f.offset, f.type);
      const ent = il.find(x => x.name === f.name);
      if (ent) {
        if (f.type.k === 'struct') this.constructAt(flv, ent.args.map(a => this.evArg(a)), false);
        else if (f.type.k === 'cont') this.store(flv, { t: f.type, v: this.constructCont(f.type, ent.args.map(a => this.ev(a)), ent.args.length === 1 && ent.args[0].type === 'InitList' ? ent.args[0].items : null) }, true);
        else if (f.type.k === 'string') this.store(flv, { t: f.type, v: this.constructString(ent.args.map(a => this.ev(a))) });
        else if (ent.args.length) this.store(flv, this.ev(ent.args[0]));
        else this.store(flv, { t: f.type, v: this.zeroOf(f.type) });
      } else if (f.init) this.initVar(flv, f.type, f.init, null, f.line);
      else this.defaultInit(flv, f.type);
    }
  };
  P.destroyObject = function (lv) {
    const st = lv.t;
    if (!st || st.k !== 'struct') return;
    let dt = null;
    for (let s = st; s; s = s.base) if (s.dtor) { dt = s; break; }
    if (dt && dt.dtor && dt.dtor.body) {
      this.callFunction(dt.dtor, [], new Ptr(lv.blk, lv.off), dt.dtor.line);
    }
    // members
    this.layout(st);
    for (const f of st.allFields) {
      if (f.type.k === 'cont') { const m = this.peekCell(lv.blk, lv.off + f.offset, f.type); if (m) this.killCont(m); }
      else if (f.type.k === 'struct') this.destroyObject(new MemLV(lv.blk, lv.off + f.offset, f.type)), void 0;
    }
  };
  P.evConstruct = function (e) {
    const ty = e.ty;
    const args = e.args.map(a => this.evArg(a));
    if (ty.k === 'struct') {
      const blk = this.newBlock('temp', this.sizeOf(ty), ty, '临时对象');
      const lv = new MemLV(blk, 0, ty);
      this.constructAt(lv, args, e.brace);
      return { t: ty, v: lv };
    }
    if (ty.k === 'cont') return { t: ty, v: this.constructCont(ty, args, e.brace ? e.args : null), fresh: true };
    if (ty.k === 'string') return { t: T.string, v: this.constructString(args) };
    throw new RunError('无法构造 ' + T.name(ty), 'runtime');
  };
  P.makeCppExc = function (st, msg) {
    const blk = this.newBlock('temp', this.sizeOf(st), st, '');
    const lv = new MemLV(blk, 0, st);
    this.constructAt(lv, [{ t: T.string, v: msg }], false);
    return { t: st, v: lv };
  };

  // ======================= Java objects =======================
  P.newJavaObject = function (st, args, line) {
    if (st.isInterface) throw new RunError('不能 new 一个接口（' + st.name + '）', 'runtime');
    this.layout(st);
    const blk = this.newBlock('heap', Math.max(1, st.size), st, '');
    blk.zero = true; blk.typed = true;
    const ptr = new Ptr(blk, 0);
    if (!st.builtin) this.rec.note('new 创建了一个 ' + st.name + ' 对象', 'alloc');
    this.javaConstruct(st, ptr, args, line);
    return { t: T.ptr(st, { jref: true }), v: ptr };
  };
  P.javaConstruct = function (st, ptr, args, line) {
    const ctors = st.ctors;
    if (!ctors.length) {
      if (args.length) throw new RunError('类 ' + st.name + ' 没有定义带参数的构造方法', 'runtime');
      if (st.base) this.javaConstruct(st.base, ptr, [], line);
      this.runFieldInits(st, ptr);
      return;
    }
    const ctor = this.pickOverload(ctors, args, st.name + ' 的构造方法');
    const first = ctor.body && ctor.body.body[0];
    let kind = null;
    if (first && first.type === 'ExprStmt' && first.e.type === 'Call') {
      if (first.e.callee.type === 'Super') kind = 'super';
      else if (first.e.callee.type === 'This') kind = 'this';
    }
    this.callFunction(ctor, args, ptr, line, {
      skipFirst: !!kind,
      beforeBody: (fr) => {
        if (kind === 'this') {
          const a = first.e.args.map(x => this.ev(x));
          this.javaConstruct(st, ptr, a, line);
          return;
        }
        if (kind === 'super') {
          const a = first.e.args.map(x => this.ev(x));
          if (st.base) this.javaConstruct(st.base, ptr, a, line);
        } else if (st.base) this.javaConstruct(st.base, ptr, [], line);
        this.runFieldInits(st, ptr);
      }
    });
  };
  P.runFieldInits = function (st, ptr) {
    const needFrame = !this.frame || this.frame.thisPtr !== ptr;
    if (needFrame) this.frames.push({ name: st.name + '.<init>', scopes: [new Map()], hidden: true, thisPtr: ptr, cls: st, id: ++this.seq });
    for (const f of st.fields) {
      if (f.init) {
        const flv = new MemLV(ptr.blk, ptr.off + f.offset, f.type);
        if (f.init.type === 'InitList') this.store(flv, { t: f.type, v: this.javaArrayFromInit(f.type.to, f.init) });
        else this.store(flv, this.ev(f.init));
      }
    }
    for (const fi of st.fieldInits) this.execBlock(fi.block);
    if (needFrame) this.frames.pop();
  };
  P.javaArrType = function (elem, dims) { let t = elem; for (let i = 0; i < dims; i++) t = T.ptr(t, { jarr: true }); return t; };
  P.newJavaArray = function (elem, dims, extra) {
    const n = dims[0];
    if (n < 0) throw new RunError('NegativeArraySizeException：数组长度不能是负数（' + n + '）', 'runtime');
    const et = this.javaArrType(elem, dims.length - 1 + extra);
    const es = this.sizeOf(et);
    const blk = this.newBlock('heap', Math.max(1, es * n), T.arr(et, n), '');
    blk.zero = true; blk.typed = true; blk.jarr = true;
    if (dims.length > 1) for (let i = 0; i < n; i++) blk.cells.set(i * es, { t: et, v: this.newJavaArray(elem, dims.slice(1), extra) });
    return new Ptr(blk, 0);
  };
  P.makeJavaArray = function (elem, vals) {
    const es = this.sizeOf(elem);
    const blk = this.newBlock('heap', Math.max(1, es * vals.length), T.arr(elem, vals.length), '');
    blk.zero = true; blk.typed = true; blk.jarr = true;
    vals.forEach((v, i) => this.store(new MemLV(blk, i * es, elem), v));
    return new Ptr(blk, 0);
  };
  P.javaArrayFromInit = function (elem, init) {
    const vals = init.items.map(it => {
      if (it.type === 'InitList') return { t: elem, v: this.javaArrayFromInit(elem.to, it) };
      return this.ev(it);
    });
    return this.makeJavaArray(elem, vals);
  };

  // ======================= calls =======================
  P.evCall = function (e, discard) {
    const c = e.callee;
    if (c.type === 'Ident') {
      const name = c.name;
      // local variable holding a function / lambda
      const v = this.lookupVar(name);
      if (v) {
        const fv = this.load(this.varLV(v));
        return this.callValue(fv, e.args.map(a => this.evArg(a)), e.line);
      }
      // methods of current class (implicit this / static)
      const cls = this.curClass();
      if (cls) {
        for (let c2 = cls; c2; c2 = c2.outer || null) {
          const ms = this.findMethods(c2, name);
          if (ms) {
            const args = e.args.map(a => this.evArg(a));
            const m = this.pickOverload(ms, args, name);
            const tf = this.thisFrame();
            const thisPtr = m.isStatic ? null : (tf && c2 === cls ? tf.thisPtr : null);
            if (!m.isStatic && !thisPtr && this.java) throw new RunError('不能在静态方法里直接调用实例方法 ' + name + '()', 'runtime', '要么把 ' + name + ' 声明为 static，要么先创建对象再调用。');
            return this.callMethod([m], args, thisPtr, e.line);
          }
        }
      }
      const fl = this.funcs.get(name);
      if (fl) {
        const args = e.args.map(a => this.evArg(a));
        const f = this.pickOverload(fl, args, name);
        return this.retOrVoid(this.callFunction(f, args, null, e.line));
      }
      if (this.prog.protos.has(name)) throw new RunError('函数 “' + name + '” 只有声明（原型），没有找到它的实现。', 'runtime');
      return this.callBuiltin(name, e, discard);
    }
    if (c.type === 'Member') return this.evMethodCall(e, c, discard);
    if (c.type === 'Super' || c.type === 'This') throw new RunError('super(...) / this(...) 只能写在构造方法的第一行', 'runtime');
    const fv = this.ev(c);
    return this.callValue(fv, e.args.map(a => this.evArg(a)), e.line);
  };
  P.retOrVoid = function (r) { return r || { t: T.void, v: 0 }; };
  P.callMethod = function (list, args, thisPtr, line) {
    let m = this.pickOverload(list, args, list[0].name);
    // dynamic dispatch
    if (thisPtr && thisPtr.blk && !m.isStatic && thisPtr.blk.type && thisPtr.blk.type.k === 'struct' && thisPtr.off === 0) {
      const dyn = this.findMethods(thisPtr.blk.type, m.name);
      if (dyn && dyn !== list) { const dm = this.pickOverload(dyn, args, m.name); if (dm.body) m = dm; }
    }
    if (!m.body) {
      throw new RunError('方法 ' + m.name + ' 没有实现（可能是抽象方法/纯虚函数）', 'runtime');
    }
    return this.retOrVoid(this.callFunction(m, args, m.isStatic ? null : thisPtr, line));
  };
  P.callValue = function (fv, args, line) {
    if (fv.t.k === 'any' && fv.v) fv = fv.v;
    const f = fv.v;
    if (f instanceof FnRef) return this.retOrVoid(this.callFunction(f.fn, args, f.bound || null, line));
    if (f instanceof Lambda) return this.callLambda(f, args, line);
    if (f && f.native) return f.native(args) || { t: T.void, v: 0 };
    if (fv.t.k === 'builtinfn') return this.callBuiltinVals(fv.v, args, line);
    if (fv.t.k === 'ptr' && f && !f.blk) throw new RunError('通过空的函数指针调用函数', 'segfault');
    throw new RunError('这个值不是函数，不能被调用', 'runtime');
  };
  P.callLambda = function (lam, args, line) {
    const node = lam.node;
    if (!node.fn) node.fn = { type: 'Func', name: 'lambda', ret: T.auto, params: node.params.map((n, i) => ({ name: n, type: node.ptypes && node.ptypes[i] ? node.ptypes[i] : T.auto, line: node.line })), body: node.body, line: node.line, endLine: node.body.endLine || node.line };
    const r = this.callFunction(node.fn, args, null, line, { closure: lam.frame, lambda: true });
    return r || { t: T.void, v: 0 };
  };
  P.evMethodCall = function (e, c, discard) {
    const name = c.name;
    // static / builtin class calls
    if (c.obj.type === 'Ident' && !this.lookupVar(c.obj.name) && !this.identLV(c.obj.name, c, true)) {
      const on = c.obj.name;
      if (this.java) {
        const st = this.classesByName.get(on);
        if (st) {
          const ms = this.findMethods(st, name);
          if (ms) { const args = e.args.map(a => this.evArg(a)); return this.callMethod(ms, args, null, e.line); }
          if (st.isEnum && (name === 'values' || name === 'valueOf')) return this.enumStatic(st, name, e.args.map(a => this.ev(a)));
          throw new RunError('类 ' + on + ' 没有静态方法 ' + name + '()', 'runtime');
        }
        if (JAVA_STATIC.has(on)) return this.javaStaticCall(on, name, e.args, e);
      }
      if (this.cpp) {
        const st = this.structs.get(on);
        if (st && st.k === 'struct') {
          const ms = this.findMethods(st, name);
          if (ms) {
            const args = e.args.map(a => this.evArg(a));
            const tf = this.thisFrame();
            return this.callMethod(ms, args, tf && tf.thisPtr && this.isSubclass(tf.cls, st) ? tf.thisPtr : null, e.line);
          }
        }
      }
    }
    if (c.obj.type === 'Member' && this.java && c.obj.obj.type === 'Ident' && c.obj.obj.name === 'System' && !this.lookupVar('System')) {
      if (c.obj.name === 'out' || c.obj.name === 'err') return this.javaPrint(name, e.args.map(a => this.ev(a)), e);
    }
    if (c.obj.type === 'Super') {
      const fr = this.thisFrame();
      const base = fr.cls.base;
      if (!base) {
        if (name === 'toString') return { t: T.jstring, v: fr.cls.name + '@' + this.objHash(fr.thisPtr) };
        throw new RunError('没有父类，不能调用 super.' + name, 'runtime');
      }
      const ms = this.findMethods(base, name);
      if (!ms) throw new RunError('父类 ' + base.name + ' 没有方法 ' + name, 'runtime');
      const args = e.args.map(a => this.evArg(a));
      const m = this.pickOverload(ms, args, name);
      return this.retOrVoid(this.callFunction(m, args, fr.thisPtr, e.line));
    }
    // evaluate object
    let objV, objLV = null;
    if (!c.arrow && this.isLvalueExpr(c.obj) && !this.java) {
      objLV = this.lv(c.obj);
      objV = this.load(objLV);
    } else if (this.isLvalueExpr(c.obj) && this.java) {
      const sv = c.obj.type === 'Member' ? this.evMemberSpecial(c.obj) : null;
      if (sv) objV = sv;
      else { objLV = this.lv(c.obj); objV = this.load(objLV); }
    } else objV = this.ev(c.obj);
    if (objV.t.k === 'any') {
      if (objV.v == null) throw new RunError('NullPointerException：在 null 上调用方法 ' + name + '()', 'segfault', '调用方法前先检查对象是否为 null。');
      objV = objV.v;
    }
    const t = objV.t;
    if (t.k === 'stream') return this.streamMethod(objV.v, name, e.args, e);
    if (t.k === 'string') return this.stringMethod(objV, objLV, name, e.args.map(a => this.ev(a)), e);
    if (t.k === 'cont' || t.k === 'iter') {
      if (t.k === 'cont' && !objV.v) throw new RunError((this.java ? 'NullPointerException：' : '') + '在 null 上调用方法 ' + name + '()', 'segfault', this.java ? '集合变量需要先 new 出来，例如 = new ArrayList<>()。' : '');
      return this.contMethod(objV, name, e.args, e, discard);
    }
    if (t.k === 'prim' && this.java) return this.javaPrimMethod(objV, name, e.args.map(a => this.ev(a)));
    if (t.k === 'lambda' && this.java) return this.callValue(objV, e.args.map(a => this.evArg(a)), e.line);
    let st, ptr;
    if (objV.v instanceof Lambda || objV.v instanceof FnRef || (objV.v && objV.v.native)) return this.callValue(objV, e.args.map(a => this.evArg(a)), e.line);
    if (t.k === 'ptr' || t.k === 'nullptr') {
      if (t.k === 'ptr' && t.to.k === 'cont') { const m = this.load(new MemLV(objV.v.blk, objV.v.off, t.to, true, this.exprText(c.obj))); return this.contMethod(m, name, e.args, e, discard); }
      if (!c.arrow && !this.java) throw new RunError('“' + this.exprText(c.obj) + '” 是指针，调用成员函数应该用 ->', 'runtime');
      ptr = objV.v;
      if (!ptr.blk) {
        if (this.java) throw new RunError('NullPointerException：在 null 上调用方法 ' + name + '()（' + this.exprText(c.obj) + ' 是 null）', 'segfault', '调用方法前先检查对象是否为 null。');
        throw new RunError('段错误：通过空指针 ' + this.exprText(c.obj) + ' 调用成员函数 ' + name + '()', 'segfault', '调用前检查指针是否为 nullptr。');
      }
      if (ptr.blk.freed) throw new RunError('释放后使用：通过已经 delete 的指针调用 ' + name + '()', 'uaf');
      st = t.k === 'ptr' ? t.to : null;
      if (ptr.blk.type && ptr.blk.type.k === 'struct' && ptr.off === 0) st = ptr.blk.type;
      if (t.jarr || (ptr.blk.type && ptr.blk.type.k === 'arr' && this.java)) return this.javaArrayMethod(objV, name, e.args.map(a => this.ev(a)));
    } else if (t.k === 'struct') {
      st = t; ptr = new Ptr(objV.v.blk, objV.v.off);
    } else if (t.k === 'class') {
      st = t.st;
      const ms = this.findMethods(st, name);
      if (!ms) throw new RunError('类 ' + st.name + ' 没有方法 ' + name, 'runtime');
      return this.callMethod(ms, e.args.map(a => this.evArg(a)), null, e.line);
    } else if (t.k === 'bclass') {
      return this.javaStaticCall(objV.v, name, e.args, e);
    } else throw new RunError('“' + this.exprText(c.obj) + '” 的类型是 ' + T.name(t) + '，不能调用方法 ' + name + '()', 'runtime');
    if (!st || st.k !== 'struct') throw new RunError('“' + this.exprText(c.obj) + '” 不是对象，不能调用方法 ' + name + '()', 'runtime');
    const ms = this.findMethods(st, name);
    if (!ms) {
      if (this.java) return this.javaObjectMethod(objV, st, ptr, name, e.args.map(a => this.ev(a)));
      throw new RunError(st.name + ' 没有成员函数 ' + name + '()', 'runtime', '检查函数名是否拼写正确，或者它是否定义在这个类里。');
    }
    const args = e.args.map(a => this.evArg(a));
    return this.callMethod(ms, args, ptr, e.line);
  };
  P.javaObjectMethod = function (objV, st, ptr, name, args) {
    if (st.isEnum || ptr.blk.isEnum) {
      if (name === 'ordinal') return { t: T.int, v: ptr.blk.enumIdx };
      if (name === 'name' || name === 'toString') return { t: T.jstring, v: st.enumConsts[ptr.blk.enumIdx] };
      if (name === 'compareTo') return { t: T.int, v: ptr.blk.enumIdx - args[0].v.blk.enumIdx };
      if (name === 'equals') return this.mkBool(args[0].v && args[0].v.blk === ptr.blk);
    }
    switch (name) {
      case 'equals': return this.mkBool(args[0].v instanceof Ptr && args[0].v.blk === ptr.blk);
      case 'hashCode': return { t: T.int, v: this.objHash(ptr) };
      case 'toString': return { t: T.jstring, v: this.javaStr(objV) };
      case 'getClass': return { t: T.jstring, v: st.name };
      case 'getSimpleName': case 'getName': return { t: T.jstring, v: st.name };
    }
    if (st.isRecord) { const f = this.findField(st, name); if (f) return this.load(new MemLV(ptr.blk, f.offset, f.type)); }
    throw new RunError('类 ' + st.name + ' 没有方法 ' + name + '()', 'runtime', '检查方法名是否拼写正确。');
  };
  P.enumStatic = function (st, name, args) {
    if (name === 'values') return { t: T.ptr(T.ptr(st, { jref: true }), { jarr: true }), v: this.makeJavaArray(T.ptr(st, { jref: true }), st.enumConsts.map((_, i) => this.enumValue(st, i))) };
    const i = st.enumConsts.indexOf(args[0].v);
    if (i < 0) throw new RunError('IllegalArgumentException：没有枚举常量 ' + args[0].v, 'runtime');
    return this.enumValue(st, i);
  };
  P.objHash = function (ptr) {
    if (!ptr || !ptr.blk) return 0;
    const n = parseInt(ptr.blk.id.slice(1));
    return ((n * 2654435761) >>> 8) & 0x7fffffff;
  };
  P.evMethodRef = function (e) {
    const name = e.name;
    const self = this;
    const objName = e.obj.type === 'Ident' ? e.obj.name : null;
    if (objName && (JAVA_STATIC.has(objName) || this.classesByName.has(objName)) && !this.lookupVar(objName)) {
      const st = this.classesByName.get(objName);
      if (name === 'new') return { t: { k: 'lambda' }, v: { native: (args) => st ? self.newJavaObject(st, args, e.line) : self.javaStaticCall(objName, 'new', args.map(a => ({ type: '__val', val: a })), e) } };
      return {
        t: { k: 'lambda' }, v: {
          native: (args) => {
            if (st) {
              const ms = self.findMethods(st, name);
              if (ms && ms[0].isStatic) return self.callMethod(ms, args, null, e.line);
              if (ms) return self.callMethod(ms, args.slice(1), args[0].v, e.line);
            }
            if (JAVA_STATIC.has(objName)) {
              // static e.g. Integer::compare, Math::max  or instance e.g. String::length
              try { return self.javaStaticCall(objName, name, args.map(a => ({ type: '__val', val: a })), e); }
              catch (er) {
                if (!args.length) throw er;
                return self.evMethodCall({ args: args.slice(1).map(a => ({ type: '__val', val: a })), line: e.line }, { type: 'Member', obj: { type: '__val', val: args[0] }, name, line: e.line });
              }
            }
          }
        }
      };
    }
    const objV = this.ev(e.obj);
    return { t: { k: 'lambda' }, v: { native: (args) => self.evMethodCall({ args: args.map(a => ({ type: '__val', val: a })), line: e.line }, { type: 'Member', obj: { type: '__val', val: objV }, name, line: e.line }) } };
  };

  // __val pseudo-node support
  const _ev = P.ev;
  P.ev = function (e, discard) { if (e.type === '__val') return e.val; return _ev.call(this, e, discard); };
  const _isL = P.isLvalueExpr;
  P.isLvalueExpr = function (e) { if (e.type === '__val') return false; return _isL.call(this, e); };
})(typeof window !== 'undefined' ? window : globalThis);
