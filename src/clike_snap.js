// ===== C / C++ / Java: build visual snapshots =====
(function (G) {
  const DSV = G.DSV;
  const T = DSV.CT;
  const { Block, Ptr, MObj, Lambda, FnRef, MemLV, ElemLV, MapLV, StrCharLV, TmpLV } = DSV.clikeRT;
  const P = DSV.ClikeInterp.prototype;
  const MAXE = 120;

  // ---------- reachability ----------
  P.reachable = function () {
    const seen = new Set();
    const stack = [];
    const pushVal = (v) => {
      if (!v) return;
      if (v instanceof Ptr) { if (v.blk && !seen.has(v.blk)) { seen.add(v.blk); stack.push(v.blk); } return; }
      if (v instanceof MObj || (v && v.ctype)) { if (!seen.has(v)) { seen.add(v); stack.push(v); } return; }
      if (v instanceof Block) { if (!seen.has(v)) { seen.add(v); stack.push(v); } return; }
      if (v.t && v.v !== undefined) pushVal(v.v);
    };
    for (const f of this.frames) {
      if (f.thisPtr) pushVal(f.thisPtr);
      for (const sc of f.scopes) for (const v of sc.values()) {
        if (v.blk) { if (!seen.has(v.blk)) { seen.add(v.blk); stack.push(v.blk); } }
        else if (v.lv) this.lvTargets(v.lv).forEach(pushVal);
      }
      if (f.retVal) pushVal(f.retVal);
    }
    for (const g of this.globals.values()) { seen.add(g.blk); stack.push(g.blk); }
    if (this.argvBlock) { seen.add(this.argvBlock); stack.push(this.argvBlock); }
    while (stack.length) {
      const o = stack.pop();
      if (o instanceof Block) {
        for (const c of o.cells.values()) {
          if (!c || c.v == null) continue;
          if (c.t.k === 'ptr' || c.t.k === 'nullptr') pushVal(c.v);
          else if (c.t.k === 'cont') pushVal(c.v);
          else if (c.t.k === 'any') { if (c.v && c.v.v != null) pushVal(c.v.v); }
          else if (c.t.k === 'lambda') { }
        }
      } else if (o.ctype) {
        if (o.ctype === 'mapentry') { pushVal(o.map); continue; }
        for (const it of o.items) if (it) pushVal(it.v);
        if (o.map) for (const en of o.map.values()) { if (en.k) pushVal(en.k.v); if (en.v) pushVal(en.v.v); }
        if (o.src) for (const it of o.src) if (it) pushVal(it.v);
      }
    }
    return seen;
  };
  P.lvTargets = function (lv) {
    if (lv instanceof MemLV) return [new Ptr(lv.blk, lv.off)];
    if (lv instanceof ElemLV || lv instanceof MapLV) return [lv.obj];
    if (lv instanceof StrCharLV) return this.lvTargets(lv.base);
    return [];
  };

  // ---------- descriptors ----------
  P.fmtPrim = function (t, v) {
    if (t.isBool) return v ? 'true' : 'false';
    if (t.isChar && (t.size === 1 || this.java)) {
      const ch = String.fromCharCode(t.size === 1 ? v & 0xff : v);
      return "'" + DSV.escChar(ch) + "'";
    }
    if (t.fl) return this.java ? this.javaDouble(v, t.size === 4) : DSV.fmtNum(t.size === 4 ? +Math.fround(v).toPrecision(7) : v, true);
    return String(v);
  };
  P.subPath = function (blk, off) {
    if (off === 0) return undefined;
    let t = blk.type;
    if (!t) return undefined;
    const parts = [];
    let rel = off;
    for (let guard = 0; guard < 8 && t; guard++) {
      if (t.k === 'arr') {
        const es = this.sizeOf(t.of);
        const i = Math.floor(rel / es);
        if (i < 0) return undefined;
        parts.push(String(i));
        rel -= i * es; t = t.of;
        if (rel === 0 && (t.k !== 'struct' && t.k !== 'arr')) break;
        if (rel === 0) break;
      } else if (t.k === 'struct') {
        this.layout(t);
        let f = null;
        for (const ff of t.allFields) if (ff.offset <= rel && rel < ff.offset + this.sizeOf(ff.type)) { f = ff; }
        if (!f) break;
        parts.push(f.name);
        rel -= f.offset; t = f.type;
        if (rel === 0) break;
      } else break;
    }
    return parts.length ? parts.join('.') : undefined;
  };
  P.descTyped = function (tv) {
    if (!tv) return DSV.V.nul(this.java ? 'null' : 'NULL');
    const t = tv.t, v = tv.v;
    switch (t.k) {
      case 'prim': return DSV.V.prim(this.fmtPrim(t, v), t.name);
      case 'string': return v == null ? DSV.V.nul('null') : DSV.V.str(DSV.quoteStr(v));
      case 'ptr': case 'nullptr': return this.descPtr(t, v);
      case 'cont': if (v && v.ctype === 'pair' && !this.java && !tv.byRef) return this.descMObj(v);
        return v ? (v.ctype === 'mapentry' ? { k: 'struct', name: 'Entry', fields: [{ name: 'key', val: this.descTyped(v.entry.k) }, { name: 'value', val: this.descTyped(v.entry.v) }] } : DSV.V.ref(v.id)) : DSV.V.nul(this.java ? 'null' : 'NULL');
      case 'any': return v == null || tv.isNull ? DSV.V.nul('null') : this.descTyped(v);
      case 'struct': {
        if (v instanceof Block) return this.descMem(v, 0, t, 0);
        if (v instanceof MemLV) return this.descMem(v.blk, v.off, t, 0);
        return { k: 'struct', name: T.name(t), fields: [] };
      }
      case 'lambda': return { k: 'func', text: 'λ' };
      case 'func': return { k: 'func', text: t.name || 'fn' };
      case 'iter': return { k: 'prim', text: 'iterator' + (v && v.idx != null ? '@' + v.idx : '') };
      case 'stream': return { k: 'prim', text: t.name };
    }
    return DSV.V.prim(String(v));
  };
  P.descPtr = function (t, v) {
    if (v === undefined) return DSV.V.uninit();
    if (v instanceof FnRef) return { k: 'func', text: v.fn.name + '()' };
    if (v instanceof Lambda || (v && v.native)) return { k: 'func', text: 'λ' };
    if (!v || !v.blk) {
      if (v && v.wild) return { k: 'null', text: '?', wild: true };
      return DSV.V.nul(this.java ? 'null' : (this.cpp ? 'nullptr' : 'NULL'));
    }
    const blk = v.blk;
    if (blk.isEnum) return DSV.V.prim(blk.type.enumConsts[blk.enumIdx], 'enum');
    const flags = {};
    if (blk.freed) flags.dangling = 'freed';
    else if (blk.dead) flags.dangling = 'dead';
    if (blk.kind === 'temp' && !blk.elem) return { k: 'prim', text: '(临时)' };
    const r = DSV.V.ref(blk.id, this.subPath(blk, v.off), flags);
    if (blk.kind === 'str') r.lit = DSV.quoteStr(this.cstrOf(blk).slice(v.off));
    return r;
  };
  P.descMem = function (blk, off, t, depth) {
    if (depth > 6) return { k: 'prim', text: '…' };
    switch (t.k) {
      case 'arr': {
        const es = this.sizeOf(t.of);
        const n = t.len || 0;
        const elems = [];
        const lim = Math.min(n, MAXE);
        for (let i = 0; i < lim; i++) elems.push(this.descMem(blk, off + i * es, t.of, depth + 1));
        const d = { k: 'arr', elems, total: n, elemType: T.name(t.of) };
        if (t.of.k === 'prim' && t.of.isChar && t.of.size === 1) d.charArr = true;
        return d;
      }
      case 'struct': {
        this.layout(t);
        const fields = [];
        for (const f of t.allFields) fields.push({ name: f.name, val: this.descMem(blk, off + f.offset, f.type, depth + 1) });
        return { k: 'struct', name: T.name(t), fields };
      }
      case 'prim': {
        const v = this.peekCell(blk, off, t);
        if (v === undefined) return DSV.V.uninit();
        return DSV.V.prim(this.fmtPrim(t, v), t.name);
      }
      case 'ptr': case 'nullptr': return this.descPtr(t, this.peekCell(blk, off, t));
      case 'string': { const v = this.peekCell(blk, off, t); if (v === undefined) return t.java ? DSV.V.nul('null') : DSV.V.str('""'); return v == null ? DSV.V.nul('null') : DSV.V.str(DSV.quoteStr(v)); }
      case 'cont': { const v = this.peekCell(blk, off, t); return v ? (v.ctype === 'mapentry' || (v.ctype === 'pair' && !this.java) ? this.descTyped({ t, v }) : DSV.V.ref(v.id)) : DSV.V.nul(this.java ? 'null' : 'NULL'); }
      case 'any': { const v = this.peekCell(blk, off, t); return v == null ? DSV.V.nul('null') : this.descTyped(v); }
      case 'lambda': case 'func': { const v = this.peekCell(blk, off, t); return v ? { k: 'func', text: 'λ' } : DSV.V.nul(); }
    }
    return DSV.V.prim('?');
  };
  P.descBlock = function (blk, t) {
    const RT = DSV.clikeRT;
    const key = blk.cells.ver + ':' + RT.epoch();
    if (blk._dc && blk._dcKey === key && blk._dcT === t) return blk._dc;
    const d = this.descMem(blk, 0, t, 0);
    blk._dc = d; blk._dcKey = key; blk._dcT = t;
    return d;
  };
  P.descMObj = function (m) {
    const kind = this.contKind(m);
    const item = (it) => it ? (it.t.k === 'struct' && it.v instanceof Block ? this.descMem(it.v, 0, it.t, 1) : this.descTyped(it)) : DSV.V.nul();
    if (m.ctype === 'StringBuilder') return { k: 'list', items: [DSV.V.str(DSV.quoteStr(m.str))], kind: 'box' };
    if (m.ctype === 'pair') return { k: 'struct', name: 'pair', fields: [{ name: 'first', val: item(m.items[0]) }, { name: 'second', val: item(m.items[1]) }] };
    if (kind === 'map') {
      const ents = this.mapEntries(m).slice(0, MAXE);
      return { k: 'map', entries: ents.map(en => ({ key: this.descTyped(en.k), val: item(en.v) })), total: m.map.size };
    }
    if (kind === 'set') return { k: 'list', items: this.mapEntries(m).slice(0, MAXE).map(en => this.descTyped(en.k)), kind: 'set', total: m.map.size };
    const lk = { vector: 'array', ArrayList: 'array', Vector: 'array', stack: 'stack', Stack: 'stack', queue: 'queue', deque: 'deque', ArrayDeque: 'deque', LinkedList: 'linked', list: 'linked', priority_queue: 'heap', PriorityQueue: 'heap' }[m.ctype] || 'array';
    const d = { k: 'list', items: m.items.slice(0, MAXE).map(item), kind: lk, total: m.items.length };
    if (m.ctype === 'vector') d.cap = Math.max(m.cap, m.items.length);
    return d;
  };
  P.mobjLabel = function (m) {
    const t = m.t;
    let s = t && t.args && t.args.length && t.args.every(a => a && a.k) ? m.ctype + '<' + t.args.filter(a => a.k !== 'cmp').map(a => a.k === 'any' ? (a.boxName || 'Object') : T.name(a)).join(', ') + '>' : m.ctype;
    if (this.java && t && t.args && t.args.length === 0) s = m.ctype;
    return s;
  };

  // ---------- snapshot ----------
  P.snapshot = function () {
    const RT = DSV.clikeRT;
    const rel = RT.rel();
    const reuse = this._lastHeap && this._lastRel === rel && !this._lastTransient;
    const snap = this.snapshotInner(reuse ? this._lastHeap : null);
    if (!reuse) { this._lastHeap = snap.heap; this._lastRel = RT.rel(); this._lastTransient = this._transient; }
    this._transient = false;
    return snap;
  };
  P.snapshotInner = function (reuseHeap) {
    const frames = [];
    const reach = reuseHeap ? null : this.reachable();
    const heapOrder = [];
    const heapSeen = new Set();
    const addHeap = (o) => { if (o && !heapSeen.has(o)) { heapSeen.add(o); heapOrder.push(o); } };
    const visitDesc = () => { };
    const stepNo = this.rec.steps.length;
    // frames
    const visible = this.frames.filter(f => !f.hidden);
    visible.forEach((f, idx) => {
      const vars = [];
      if (f.thisPtr && f.cls && f.name !== 'lambda') vars.push({ name: 'this', val: this.descPtr(T.ptr(f.cls), f.thisPtr), type: T.name(f.cls) + (this.java ? '' : ' *'), isThis: true });
      for (const sc of f.scopes) for (const v of sc.values()) {
        if (v.isStatic) continue;
        if (v.isRef) {
          const lv = v.lv;
          let val;
          if (lv instanceof MemLV) val = Object.assign(DSV.V.ref(lv.blk.id, this.subPath(lv.blk, lv.off)), { isAlias: true });
          else if (lv instanceof ElemLV) val = Object.assign(DSV.V.ref(lv.obj.id, String(lv.idx)), { isAlias: true });
          else if (lv instanceof MapLV) { try { val = this.descTyped(this.load(lv)); } catch (e) { val = DSV.V.prim('?'); } }
          else val = DSV.V.prim('&');
          vars.push({ name: v.name, val, type: T.name(v.t) + ' &', alias: true });
          continue;
        }
        const d = this.descBlock(v.blk, v.t);
        vars.push({ name: v.name, val: d, type: T.name(v.t), addr: this.java ? undefined : this.hex(v.blk.addr), anchor: v.blk.id, size: this.java ? undefined : v.blk.size });
      }
      const fr = { id: 'f' + f.id, name: f.name, vars, line: f === this.frame ? this.curLine : (visible[idx + 1] ? visible[idx + 1].callLine : f.curLine) };
      if (f.returning) fr.ret = f.retVal ? this.descTyped(f.retVal) : { k: 'prim', text: 'void' };
      frames.push(fr);
    });
    // globals
    let globals = null;
    if (this.globalOrder.length) {
      const gv = this.globalOrder.filter(g => !g.name.startsWith('<'));
      if (gv.length) globals = { id: 'globals', name: this.java ? '静态变量' : '全局变量', vars: gv.map(g => ({ name: g.name, val: this.descBlock(g.blk, g.t), type: T.name(g.t), addr: this.java ? undefined : this.hex(g.blk.addr), anchor: g.blk.id })) };
    }
    if (reuseHeap) return { frames, globals, heap: reuseHeap, lang: this.d, showAddr: !this.java };
    // heap: collect in reach order from roots
    const order = [];
    const pushB = (b) => { if (!b || heapSeen.has(b)) return; heapSeen.add(b); order.push(b); };
    const walkDesc = (d) => {
      if (!d) return;
      if (d.k === 'ref') {
        const tgt = this.byId(d.id);
        if (tgt) pushB(tgt);
        return;
      }
      if (d.k === 'arr') d.elems.forEach(walkDesc);
      else if (d.k === 'struct') d.fields.forEach(f => walkDesc(f.val));
      else if (d.k === 'list') d.items.forEach(walkDesc);
      else if (d.k === 'map') d.entries.forEach(e => { walkDesc(e.key); walkDesc(e.val); });
    };
    this._idx = null;
    if (globals) globals.vars.forEach(v => walkDesc(v.val));
    frames.forEach(f => { f.vars.forEach(v => walkDesc(v.val)); if (f.ret) walkDesc(f.ret); });
    const heap = [];
    for (let i = 0; i < order.length; i++) {
      const o = order[i];
      const ent = this.heapEntry(o, reach, stepNo);
      if (!ent) continue;
      heap.push(ent);
      walkDesc(ent.val);
    }
    // leaked / unreachable heap blocks (C/C++) and just-freed blocks
    if (!this.java) {
      for (const b of this.heapBlocks) {
        if (heapSeen.has(b)) continue;
        if (b.freed && b.freedStep !== stepNo) continue;
        heapSeen.add(b);
        const ent = this.heapEntry(b, reach, stepNo);
        if (ent) { heap.push(ent); walkDesc(ent.val); }
        // anything reachable from the leaked block
        for (let i = order.length; i < order.length; i++) { }
      }
      // process any newly discovered (from leaked blocks' pointers)
      for (let i = 0; i < order.length; i++) {
        const o = order[i];
        if (heap.find(h => h.id === o.id)) continue;
        const ent = this.heapEntry(o, reach, stepNo);
        if (ent) { heap.push(ent); walkDesc(ent.val); }
      }
    }
    return { frames, globals, heap, lang: this.d, showAddr: !this.java };
  };
  P.byId = function (id) {
    if (!this._idx) {
      const m = new Map();
      for (const b of this.heapBlocks) m.set(b.id, b);
      for (const b of this.strLits.values()) m.set(b.id, b);
      for (const o of this.mobjs) m.set(o.id, o);
      if (this.argvBlock) {
        m.set(this.argvBlock.id, this.argvBlock);
        for (const c of this.argvBlock.cells.values()) if (c.v && c.v.blk) m.set(c.v.blk.id, c.v.blk);
      }
      // temp blocks (c_str views etc.) are not indexed
      this._idx = m;
    }
    return this._idx.get(id);
  };
  P.heapEntry = function (o, reach, stepNo) {
    if (o instanceof Block) {
      const b = o;
      if (b.kind === 'stack' || b.kind === 'global' || b.kind === 'temp') return null;
      let val, label;
      const t = b.type;
      if (!t) { val = { k: 'raw', size: b.size, text: b.zero ? b.size + ' 字节（全 0）' : b.size + ' 字节（未初始化）' }; label = 'void *'; }
      else { val = this.descBlock(b, t); label = T.name(t); }
      if (this.java && t && t.k === 'struct') label = t.name;
      if (this.java && t && t.k === 'arr') label = T.name(t.of) + '[' + t.len + ']';
      const flags = {};
      if (b.freed) flags.freed = true;
      if (b.kind === 'heap' && !b.freed && !reach.has(b) && !b.cs50 && !this.java) flags.leak = true;
      if (b.kind === 'str') flags.rodata = true;
      if (b.freed && b.freedStep === stepNo) this._transient = true;
      if (b.kind === 'argv') flags.argv = true;
      return { id: b.id, label, addr: this.java ? undefined : this.hex(b.addr), size: this.java ? undefined : b.size, val, flags, kind: b.kind, born: b.bornStep };
    }
    if (o.ctype) {
      if (o.hidden || o.ctype === 'mapentry' || o.dead) return null;
      if (this.java && !reach.has(o)) return null;
      return { id: o.id, label: this.mobjLabel(o), val: this.descMObj(o), flags: {}, kind: 'cont', born: o.born };
    }
    return null;
  };

  // ======================= language entry points =======================
  const JAVA_PRELUDE = `
class Throwable { String message; Throwable() {} Throwable(String message) { this.message = message; } String getMessage() { return message; } }
class Exception extends Throwable { Exception() {} Exception(String m) { super(m); } }
class RuntimeException extends Exception { RuntimeException() {} RuntimeException(String m) { super(m); } }
class IllegalArgumentException extends RuntimeException { IllegalArgumentException() {} IllegalArgumentException(String m) { super(m); } }
class IllegalStateException extends RuntimeException { IllegalStateException() {} IllegalStateException(String m) { super(m); } }
class IndexOutOfBoundsException extends RuntimeException { IndexOutOfBoundsException() {} IndexOutOfBoundsException(String m) { super(m); } }
class ArrayIndexOutOfBoundsException extends IndexOutOfBoundsException { ArrayIndexOutOfBoundsException() {} ArrayIndexOutOfBoundsException(String m) { super(m); } }
class StringIndexOutOfBoundsException extends IndexOutOfBoundsException { StringIndexOutOfBoundsException() {} StringIndexOutOfBoundsException(String m) { super(m); } }
class NullPointerException extends RuntimeException { NullPointerException() {} NullPointerException(String m) { super(m); } }
class ArithmeticException extends RuntimeException { ArithmeticException() {} ArithmeticException(String m) { super(m); } }
class UnsupportedOperationException extends RuntimeException { UnsupportedOperationException() {} UnsupportedOperationException(String m) { super(m); } }
class NoSuchElementException extends RuntimeException { NoSuchElementException() {} NoSuchElementException(String m) { super(m); } }
class NumberFormatException extends IllegalArgumentException { NumberFormatException() {} NumberFormatException(String m) { super(m); } }
class ClassCastException extends RuntimeException { ClassCastException() {} ClassCastException(String m) { super(m); } }
class EmptyStackException extends RuntimeException { EmptyStackException() {} }
class InputMismatchException extends NoSuchElementException { InputMismatchException() {} InputMismatchException(String m) { super(m); } }
class Error extends Throwable { Error() {} Error(String m) { super(m); } }
class StackOverflowError extends Error { StackOverflowError() {} }
class AssertionError extends Error { AssertionError() {} AssertionError(String m) { super(m); } }
class IOException extends Exception { IOException() {} IOException(String m) { super(m); } }
class InterruptedException extends Exception { InterruptedException() {} }
interface Comparable {} interface Comparator {} interface Runnable {} interface Iterable {} interface Cloneable {} interface Serializable {} interface Function {} interface BiFunction {} interface Consumer {} interface Predicate {} interface Supplier {}
`;
  const CPP_PRELUDE = `
class exception { public: string msg; exception() {} exception(string m) : msg(m) {} string what() { return msg; } };
class logic_error : public exception { public: logic_error(string m) : exception(m) {} };
class runtime_error : public exception { public: runtime_error(string m) : exception(m) {} };
class out_of_range : public logic_error { public: out_of_range(string m) : logic_error(m) {} };
class invalid_argument : public logic_error { public: invalid_argument(string m) : logic_error(m) {} };
class length_error : public logic_error { public: length_error(string m) : logic_error(m) {} };
class overflow_error : public runtime_error { public: overflow_error(string m) : runtime_error(m) {} };
class underflow_error : public runtime_error { public: underflow_error(string m) : runtime_error(m) {} };
`;

  function parseWithPrelude(code, dialect) {
    const prelude = dialect === 'java' ? JAVA_PRELUDE : CPP_PRELUDE;
    // parse prelude + code together; prelude goes on line 0 (all marked builtin)
    const prog0 = DSV.clikeParse(prelude.replace(/\n/g, ' '), dialect);
    const preNames = new Set(prog0.classes.map(c => c.name));
    // feed prelude class names to the real parse by prefixing tokens
    const lx = DSV.clikeLex(code, dialect);
    const plx = DSV.clikeLex(prelude.replace(/\n/g, ' '), dialect);
    for (const t of plx.toks) t.line = 0;
    const toks = plx.toks.slice(0, -1).concat(lx.toks);
    const Parser = DSV._ClikeParser;
    const prog = DSV.clikeParseToks(toks, dialect, lx.includes);
    for (const st of prog.classes) if (preNames.has(st.name) && st.line === 0) {
      st.builtin = true;
      for (const c of st.ctors) c.builtin = true;
      for (const ms of st.methods.values()) for (const m of ms) m.builtin = true;
      if (st.dtor) st.dtor.builtin = true;
    }
    return prog;
  }

  function runClike(dialect) {
    return function (code, opts) {
      opts = opts || {};
      let prog;
      const rec0 = new DSV.Recorder(opts);
      try {
        if (dialect === 'c') prog = DSV.clikeParse(code, 'c');
        else prog = parseWithPrelude(code, dialect);
      } catch (e) {
        if (e.isCompile) return DSV.finishRun(rec0, e);
        return DSV.finishRun(rec0, e);
      }
      const it = new DSV.ClikeInterp(prog, opts);
      return it.run();
    };
  }
  DSV.langs.c = { name: 'C', run: runClike('c') };
  DSV.langs.cpp = { name: 'C++', run: runClike('cpp') };
  DSV.langs.java = { name: 'Java', run: runClike('java') };
})(typeof window !== 'undefined' ? window : globalThis);
