// ===== C / C++ / Java interpreter: memory model + evaluation =====
(function (G) {
  const DSV = G.DSV;
  const { RunError, CompileError, Recorder, V, ExitSignal } = DSV;
  const T = DSV.CT;

  // ---------- runtime objects ----------
  let BLOCK_ID = 0, REL = 0, EPOCH = 0;
  const PTRISH = new Set(['ptr', 'cont', 'any', 'nullptr', 'lambda']);
  // Map that tracks a version number so unchanged blocks can reuse their snapshot
  class VMap extends Map {
    constructor(blk) { super(); this.blk = blk; this.ver = 0; }
    set(k, v) { this.ver++; if (!this.blk || this.blk.kind !== 'stack' || (v && v.t && PTRISH.has(v.t.k))) REL++; return super.set(k, v); }
    delete(k) { this.ver++; REL++; return super.delete(k); }
    clear() { this.ver++; REL++; return super.clear(); }
  }
  class Block {
    constructor(kind, size, type, name) {
      this.id = 'b' + (++BLOCK_ID);
      this.kind = kind;           // stack | heap | global | str | temp | argv
      this.size = size;
      this._type = type;          // view type
      this.name = name || '';
      this.cells = new VMap(this);
      this._freed = false; this._dead = false;
      this.zero = false;          // missing cells read as zero
      this.addr = 0;
      if (kind !== 'stack') REL++;
    }
    get type() { return this._type; }
    set type(v) { this._type = v; EPOCH++; REL++; }
    get freed() { return this._freed; }
    set freed(v) { this._freed = v; EPOCH++; REL++; }
    get dead() { return this._dead; }
    set dead(v) { if (v !== this._dead) { this._dead = v; EPOCH++; REL++; } }
  }
  class Ptr {
    constructor(blk, off, wild) { this.blk = blk; this.off = off; if (wild) this.wild = true; }
  }
  const NULLP = new Ptr(null, 0);
  let MOBJ_ID = 0;
  class MObj {       // managed container object (vector, ArrayList, map...)
    constructor(ctype, t) {
      this.id = 'm' + (++MOBJ_ID);
      this.ctype = ctype; this.t = t;  // t = cont type
      this.items = [];
      this.map = null;     // Map keyKey -> {k, v, seq}
      this.cap = 0;
      this.dead = false;
      this.str = '';       // StringBuilder
    }
  }
  class Lambda { constructor(node, frame, interp) { this.node = node; this.frame = frame; this.id = 'L' + (++MOBJ_ID); } }
  class FnRef { constructor(fn, bound) { this.fn = fn; this.bound = bound; } }
  class ThrowSignal { constructor(val, line) { this.val = val; this.line = line; } }
  class StreamObj { constructor(name) { this.name = name; this.fail = false; this.fixed = false; this.prec = null; this.width = 0; this.boolalpha = false; } }

  const BREAK = { brk: 1 }, CONTINUE = { cont: 1 };
  class Ret { constructor(val) { this.val = val; } }

  // ---------- lvalues ----------
  class MemLV {
    constructor(blk, off, t, check, desc) { this.blk = blk; this.off = off; this.t = t; this.check = check; this.desc = desc; }
  }
  class ElemLV { constructor(obj, idx, t) { this.obj = obj; this.idx = idx; this.t = t; } }
  class MapLV { constructor(obj, key, t) { this.obj = obj; this.key = key; this.t = t; } }
  class StrCharLV { constructor(base, idx, t) { this.base = base; this.idx = idx; this.t = t; } }
  class SbCharLV { constructor(obj, idx, t) { this.obj = obj; this.idx = idx; this.t = t; } }
  class TmpLV { constructor(val) { this.val = val; this.t = val.t; } }

  const isInt = t => t && t.k === 'prim' && !t.fl;
  const isFlt = t => t && t.k === 'prim' && t.fl;
  const isArith = t => t && t.k === 'prim';
  const isPtrT = t => t && (t.k === 'ptr' || t.k === 'nullptr');
  const SCALAR = new Set(['prim', 'ptr', 'string', 'cont', 'any', 'stream', 'nullptr', 'lambda', 'func', 'iter', 'void']);

  const GARBAGE = [32767, 21845, -1219, 4198400, 1702125923, -17958194, 0, 1, 32764, 73];

  class Interp {
    constructor(prog, opts) {
      this.prog = prog;
      this.d = prog.dialect;
      this.java = this.d === 'java';
      this.cpp = this.d === 'cpp';
      this.opts = opts || {};
      this.rec = new Recorder(opts);
      this.stdin = new DSV.Stdin(this.opts.stdin || '');
      this.frames = [];
      this.globals = new Map();     // name -> {t, blk}
      this.globalOrder = [];
      this.blocks = new Set();      // live (non-collected) blocks, incl freed for display
      this.heapBlocks = [];
      this.strLits = new Map();
      this.mobjs = new Set();
      this.heapAddr = 0x5592a3c012a0;
      this.stackAddr = 0x7ffd4e8c3a40;
      this.globalAddr = 0x5592a1e04010;
      this.rodataAddr = 0x5592a1e02004;
      this.curLine = 0;
      this.uninitWarned = new Set();
      this.rng = DSV.makeRng(1);
      this.depthLimit = 400;
      this.funcs = new Map();
      for (const f of prog.funcs) {
        if (!this.funcs.has(f.name)) this.funcs.set(f.name, []);
        this.funcs.get(f.name).push(f);
      }
      this.structs = prog.structs;
      this.classesByName = new Map();
      for (const st of prog.classes) this.classesByName.set(st.name, st);
      this.stepCount = 0;
      this.freedCount = 0;
      this.mallocCount = 0;
      this.cout = new StreamObj('cout');
      this.cin = new StreamObj('cin');
      this.cerr = new StreamObj('cerr');
    }

    // ================= memory =================
    newBlock(kind, size, type, name) {
      const b = new Block(kind, size, type, name);
      if (kind === 'heap') { b.addr = this.heapAddr; this.heapAddr += Math.ceil((size + 16) / 16) * 16; this.heapBlocks.push(b); b.bornStep = this.rec.steps.length; }
      else if (kind === 'stack') { this.stackAddr -= Math.ceil(Math.max(size, 4) / 4) * 4 + (size >= 8 ? 4 : 0); b.addr = this.stackAddr; }
      else if (kind === 'global' || kind === 'argv') { b.addr = this.globalAddr; this.globalAddr += Math.ceil(size / 8) * 8; }
      else if (kind === 'str') { b.addr = this.rodataAddr; this.rodataAddr += size; }
      else { b.addr = 0x7ffd4e8d0000 + (BLOCK_ID % 4096) * 32; }
      return b;
    }
    sizeOf(t) {
      switch (t.k) {
        case 'prim': return t.size;
        case 'ptr': case 'nullptr': case 'any': case 'func': case 'lambda': case 'ref': case 'stream': case 'iter': return 8;
        case 'arr': if (t.len == null) throw new RunError('数组长度未知，无法计算大小', 'runtime'); return t.len * this.sizeOf(t.of);
        case 'struct': this.layout(t); return t.size;
        case 'string': return t.java ? 8 : 32;
        case 'cont': return 24;
        case 'void': return 1;
        case 'auto': return 8;
      }
      return 8;
    }
    alignOf(t) {
      switch (t.k) {
        case 'prim': return t.size;
        case 'arr': return this.alignOf(t.of);
        case 'struct': this.layout(t); return t.align;
      }
      return 8;
    }
    layout(st) {
      if (st.laidOut) return;
      if (!st.complete && !st.fields.length) throw new RunError('类型 “' + T.name(st) + '” 只有声明、没有完整定义，无法使用它的成员或大小', 'runtime');
      st.laidOut = true;
      let off = 0, align = 1;
      const all = [];
      if (st.base) { this.layout(st.base); off = st.base.size; align = st.base.align; all.push(...st.base.allFields); if (st.base.size === 1 && !st.base.allFields.length) off = 0; }
      for (const f of st.fields) {
        if (f.type.k === 'arr' && f.type.len == null) f.type = T.arr(f.type.of, 0);
        const s = this.sizeOf(f.type), a = this.alignOf(f.type);
        if (st.tag === 'union') { f.offset = 0; off = Math.max(off, s); }
        else { off = Math.ceil(off / a) * a; f.offset = off; off += s; }
        align = Math.max(align, a);
        all.push(f);
      }
      st.size = Math.max(1, Math.ceil(off / align) * align);
      st.align = align;
      st.allFields = all;
    }
    findField(st, name) {
      this.layout(st);
      for (let s = st; s; s = s.base) {
        for (const f of s.fields) if (f.name === name) return f;
      }
      return null;
    }
    isSubclass(a, b) { for (let s = a; s; s = s.base) if (s === b) return true; return false; }

    // ---- cells ----
    cellSize(t) { return t.k === 'prim' ? t.size : this.sizeOf(t); }
    writeCell(blk, off, t, v) {
      const sz = this.cellSize(t);
      const ex = blk.cells.get(off);
      if (!(ex && this.cellSize(ex.t) === sz)) {
        for (let o = off - 31; o < off + sz; o++) {
          if (o === off) continue;
          const c = blk.cells.get(o);
          if (c && o + this.cellSize(c.t) > off && o < off + sz) blk.cells.delete(o);
        }
      }
      blk.cells.set(off, { t, v });
    }
    // raw read without warnings; returns undefined if uninitialised
    peekCell(blk, off, t) {
      const c = blk.cells.get(off);
      if (c) {
        if (c.t === t && t.k !== 'any') return c.v;
        if (c.t === t || c.t.k === t.k && this.cellSize(c.t) === this.cellSize(t)) return this.reinterpret(c, t);
        if (t.k === 'prim' && c.t.k === 'prim') return this.reinterpret(c, t);
        if (t.k === 'any') return c.t.k === 'any' ? c.v : { t: c.t, v: c.v };
        if (c.t.k === 'any' && c.v) return this.convert(c.v, t);
        return this.reinterpret(c, t);
      }
      if (t.k === 'prim' && t.size > 1) {
        // compose from bytes
        let v = 0, ok = true;
        for (let i = t.size - 1; i >= 0; i--) {
          const b = blk.cells.get(off + i);
          if (!b || this.cellSize(b.t) !== 1) { ok = false; break; }
          v = v * 256 + (b.v & 0xff);
        }
        if (ok) return this.wrapInt(v, t);
      }
      if (blk.zero) return this.zeroOf(t);
      return undefined;
    }
    reinterpret(c, t) {
      if (t.k === 'prim') {
        if (c.t.k === 'prim') return t.fl ? (c.t.fl ? c.v : c.v) : this.wrapInt(c.t.fl ? Math.trunc(c.v) : c.v, t);
        if (c.t.k === 'ptr') return c.v.blk ? c.v.blk.addr + c.v.off : 0;
        return 0;
      }
      if (t.k === 'ptr') {
        if (c.t.k === 'ptr' || c.t.k === 'nullptr') return c.v;
        if (c.t.k === 'prim') return c.v === 0 ? NULLP : new Ptr(null, c.v, true);
        if (c.t.k === 'any') return c.v ? this.convert(c.v, t) : NULLP;
      }
      return c.v;
    }
    zeroOf(t) {
      switch (t.k) {
        case 'prim': return 0;
        case 'ptr': case 'nullptr': return NULLP;
        case 'string': return t.java ? null : '';
        case 'cont': return null;
        case 'any': return null;
        case 'lambda': case 'func': return null;
      }
      return 0;
    }
    garbage(blk, off, t) {
      const h = Math.abs((parseInt(blk.id.slice(1)) * 2654435761 + off * 40503) | 0);
      if (t.k === 'ptr') return new Ptr(null, 0xbebebebe0000 + (h & 0xffff), true);
      if (t.fl) return [6.9533558e-310, -1.0842022e-19, 4.58e-41, 0][h % 4];
      if (t.size === 1) return t.signed ? ((h % 200) - 100) : h % 256;
      return this.wrapInt(GARBAGE[h % GARBAGE.length], t);
    }
    readCell(blk, off, t, desc) {
      const v = this.peekCell(blk, off, t);
      if (v !== undefined) return v;
      if (t.k === 'string' && !t.java) return '';
      if (t.k === 'cont' || t.k === 'any' || t.k === 'string') return null;
      const key = blk.id + ':' + off;
      if (!this.uninitWarned.has(key)) {
        this.uninitWarned.add(key);
        const where = blk.kind === 'heap' ? '堆上 malloc 得到的内存' : '变量';
        this.rec.note('⚠ 读取了未初始化的' + where + (desc ? ' “' + desc + '”' : (blk.name ? ' “' + blk.name + '”' : '')) + '，它的值是随机的“垃圾值”。' + (blk.kind === 'heap' ? 'malloc 不会把内存清零，可以用 calloc 或手动赋值。' : '记得在使用前先赋值。'), 'warn');
      }
      return this.garbage(blk, off, t);
    }

    // ---- integer helpers ----
    wrapInt(v, t) {
      if (typeof v === 'boolean') v = v ? 1 : 0;
      if (t.isBool) return v ? 1 : 0;
      if (typeof v !== 'number' || !isFinite(v)) v = 0;
      v = Math.trunc(v);
      switch (t.size) {
        case 1: return t.signed ? (v << 24) >> 24 : v & 0xff;
        case 2: return t.signed ? (v << 16) >> 16 : v & 0xffff;
        case 4: return t.signed ? v | 0 : v >>> 0;
        default:
          if (Number.isSafeInteger(v)) return t.signed ? v : (v < 0 ? Number(BigInt.asUintN(64, BigInt(v))) : v);
          try { const b = BigInt(v); return Number(t.signed ? BigInt.asIntN(64, b) : BigInt.asUintN(64, b)); } catch (e) { return v; }
      }
    }

    // ---- access checks ----
    checkAccess(lv, write) {
      const blk = lv.blk;
      const desc = lv.desc ? '“' + lv.desc + '”' : '';
      if (!blk) {
        if (lv.wild) throw new RunError('使用了非法的指针：访问 ' + desc + ' 时，指针没有指向任何有效的内存（可能没有初始化）。', 'segfault', '指针在使用前必须先指向一块合法内存，例如 malloc 的结果或某个变量的地址。');
        if (this.java) throw new RunError('NullPointerException：访问 ' + desc + ' 时，引用的值是 null。', 'segfault', '在访问对象的字段或方法前，先检查它是不是 null。');
        throw new RunError('段错误（Segmentation fault）：访问 ' + desc + ' 时，指针的值是 NULL。', 'segfault', '解引用前先检查指针是否为 NULL，例如 if (ptr != NULL)。遍历链表时，循环条件一般写成 ptr != NULL。');
      }
      if (blk.freed) throw new RunError('释放后使用（use-after-free）：' + desc + ' 指向的内存已经被 ' + (this.cpp ? 'delete/free' : 'free') + ' 释放了。', 'uaf', '释放内存后就不能再通过原来的指针访问它。如果要在释放前读取 next 之类的字段，先用临时变量保存下来。');
      if (blk.dead) throw new RunError('悬空指针：' + desc + ' 指向的局部变量 “' + blk.name + '” 已经随着函数返回或代码块结束被销毁了。', 'uaf', '不要返回局部变量的地址。需要在函数之外继续使用的数据应该用 malloc 分配在堆上。');
      const sz = this.cellSize(lv.t.k === 'arr' || lv.t.k === 'struct' ? lv.t : lv.t);
      if (lv.off < 0 || lv.off + sz > blk.size) {
        const vt = blk.type;
        let more = '';
        if (vt && vt.k === 'arr') {
          const es = this.sizeOf(vt.of);
          more = '这块内存是 ' + T.name(vt) + '，合法下标是 0 ~ ' + (vt.len - 1) + '，而你访问的是下标 ' + Math.floor(lv.off / es) + '。';
        } else more = '这块内存只有 ' + blk.size + ' 字节，你访问的位置是第 ' + lv.off + ' 字节。';
        if (this.java) {
          const len = vt && vt.k === 'arr' ? vt.len : 0, es = vt && vt.k === 'arr' ? this.sizeOf(vt.of) : 1;
          throw new RunError('ArrayIndexOutOfBoundsException：Index ' + Math.floor(lv.off / es) + ' out of bounds for length ' + len + '（数组长度是 ' + len + '，合法下标是 0 ~ ' + (len - 1) + '）', 'oob', '检查循环边界，下标必须满足 0 <= i < arr.length。');
        }
        throw new RunError('越界访问（buffer overflow）：' + desc + ' 超出了它所指向内存的范围。' + more, 'oob', '数组下标从 0 开始，最大是 长度-1。检查循环条件里是不是写成了 <= 。');
      }
      if (write && blk.kind === 'str') throw new RunError('试图修改字符串字面量 “' + this.cstrOf(blk) + '”，它位于只读内存。', 'segfault', '如果要修改字符串，先把它复制到 char 数组或 malloc 出来的内存里。');
    }
    cstrOf(blk) { let s = ''; for (let o = 0; o < blk.size; o++) { const c = blk.cells.get(o); if (!c || !c.v) break; s += String.fromCharCode(c.v); } return s; }

    // ---- generic load/store on lvalues ----
    load(lv) {
      if (lv instanceof MemLV) {
        const t = lv.t;
        if (lv.check) this.checkAccess(lv, false);
        if (t.k === 'arr') return { t: T.ptr(t.of), v: new Ptr(lv.blk, lv.off), arrDecay: t };
        if (t.k === 'struct') return { t, v: lv };
        if (t.k === 'any') {
          const raw = this.peekCell(lv.blk, lv.off, t);
          if (raw == null) return { t: T.nullptr, v: NULLP, isNull: true };
          return raw;
        }
        return { t, v: this.readCell(lv.blk, lv.off, t, lv.desc) };
      }
      if (lv instanceof ElemLV) {
        const it = lv.obj.items[lv.idx];
        if (it === undefined) this.boundsErr(lv.obj, lv.idx);
        if (it.t.k === 'struct') return { t: it.t, v: new MemLV(it.v, 0, it.t) };
        return it;
      }
      if (lv instanceof MapLV) return this.mapGetLV(lv);
      if (lv instanceof StrCharLV) {
        const s = this.load(lv.base).v;
        if (lv.idx < 0 || lv.idx >= s.length) {
          if (lv.idx === s.length && !this.java) return { t: T.char, v: 0 };
          throw new RunError((this.java ? 'StringIndexOutOfBoundsException' : '字符串越界访问') + '：字符串 ' + DSV.quoteStr(s) + ' 的长度是 ' + s.length + '，你访问了下标 ' + lv.idx + '。', 'oob', '字符串下标的范围是 0 ~ 长度-1。');
        }
        return { t: lv.t, v: s.charCodeAt(lv.idx) };
      }
      if (lv instanceof SbCharLV) return { t: T.jchar, v: lv.obj.str.charCodeAt(lv.idx) };
      if (lv instanceof TmpLV) return lv.val;
      throw new Error('bad lvalue');
    }
    store(lv, val, isInit) {
      if (lv instanceof MemLV) {
        const t = lv.t;
        if (lv.check) this.checkAccess(lv, true);
        if (t.k === 'struct') { this.copyStruct(lv, val); return; }
        if (t.k === 'arr') {
          if (val.t.k === 'string' || (val.arrDecay)) { this.copyArray(lv, val); return; }
          throw new RunError('不能直接给数组赋值（数组名不能被赋值），需要逐个元素复制。', 'runtime', '可以用循环逐个赋值，或者使用 memcpy / strcpy。');
        }
        if (t.k === 'any') { this.writeCell(lv.blk, lv.off, t, val.isNull || val.v === null && val.t.k !== 'prim' ? null : this.boxAny(val)); return; }
        let v = this.convert(val, t).v;
        if (t.k === 'cont' && this.cpp && v && !isInit) v = this.cloneCont(v);
        this.writeCell(lv.blk, lv.off, t, v);
        if (t.k === 'ptr' && v && v.blk) this.inferViewType(v.blk, t.to);
        return;
      }
      if (!(lv instanceof MemLV)) DSV.clikeRT.bump();
      if (lv instanceof ElemLV) {
        if (lv.idx < 0 || lv.idx >= lv.obj.items.length) this.boundsErr(lv.obj, lv.idx);
        const et = lv.t || lv.obj.items[lv.idx].t;
        if (et.k === 'struct') { this.copyStruct(new MemLV(lv.obj.items[lv.idx].v, 0, et), val); return; }
        lv.obj.items[lv.idx] = this.elemVal(val, et);
        return;
      }
      if (lv instanceof MapLV) { this.mapSet(lv.obj, lv.key, this.elemVal(val, lv.t)); return; }
      if (lv instanceof StrCharLV) {
        const s = this.load(lv.base).v;
        if (lv.idx < 0 || lv.idx >= s.length) throw new RunError('字符串越界写入：长度是 ' + s.length + '，下标是 ' + lv.idx, 'oob');
        const ns = s.slice(0, lv.idx) + String.fromCharCode(this.convert(val, T.char).v & 0xffff) + s.slice(lv.idx + 1);
        this.store(lv.base, { t: lv.base.t, v: ns });
        return;
      }
      if (lv instanceof SbCharLV) { const s = lv.obj.str; lv.obj.str = s.slice(0, lv.idx) + String.fromCharCode(this.convert(val, T.jchar).v) + s.slice(lv.idx + 1); return; }
      if (lv instanceof TmpLV) { lv.val = val; return; }
      throw new Error('bad lvalue store');
    }
    elemVal(val, et) {
      if (!et || et.k === 'any') {
        if (val.t.k === 'cont' && this.cpp && val.v) return { t: val.t, v: this.cloneCont(val.v) };
        if (val.t.k === 'struct') return this.structToElem(val);
        return { t: val.t, v: val.v, isNull: val.isNull };
      }
      if (et.k === 'struct') return this.structToElem(val, et);
      const c = this.convert(val, et);
      if (et.k === 'cont' && this.cpp && c.v) c.v = this.cloneCont(c.v);
      return c;
    }
    structToElem(val, et) {
      et = et || val.t;
      const blk = this.newBlock('temp', this.sizeOf(et), et, '');
      blk.elem = true;
      this.copyStruct(new MemLV(blk, 0, et), val);
      return { t: et, v: blk };
    }
    boxAny(val) {
      if (val.t.k === 'any') return val.v === undefined ? null : val;
      if (val.t.k === 'struct') return this.structToElem(val);
      return { t: val.t, v: val.v };
    }
    boundsErr(obj, idx) {
      const n = obj.items.length;
      if (this.java) throw new RunError('IndexOutOfBoundsException：Index ' + idx + ' out of bounds for length ' + n, 'oob', '集合的下标范围是 0 ~ size()-1。');
      throw new RunError('越界访问：' + obj.ctype + ' 的大小是 ' + n + '，你访问了下标 ' + idx + '。', 'oob', 'vector 的下标范围是 0 ~ size()-1；用 at() 访问可以得到越界检查。');
    }
    inferViewType(blk, pt) {
      if (!blk || blk.kind !== 'heap' && blk.kind !== 'temp') return;
      if (!pt || pt.k === 'void' || pt.k === 'func') return;
      if (blk.typed) return;
      let es;
      try { es = this.sizeOf(pt); } catch (e) { return; }
      if (es <= 0) return;
      if (blk.size === es && pt.k !== 'prim') blk.type = pt;
      else if (blk.size === es && pt.k === 'prim') blk.type = pt;
      else if (blk.size % es === 0) blk.type = T.arr(pt, blk.size / es);
      else blk.type = T.arr(pt, Math.floor(blk.size / es));
      blk.typed = true;
    }
    copyStruct(dstLV, val) {
      const st = dstLV.t;
      if (val.t.k === 'initlist') return this.constructAt(dstLV, val.v, true);
      let src = val.v;
      if (val.t.k !== 'struct') {
        if (val.t.k === 'prim' && this.cpp) { // conversion constructor
          return this.constructAt(dstLV, [val], false);
        }
        throw new RunError('不能把 ' + T.name(val.t) + ' 赋值给 ' + T.name(st), 'runtime');
      }
      if (src instanceof Block) src = new MemLV(src, 0, val.t);
      if (src.check) this.checkAccess(src, false);
      if (dstLV.check) this.checkAccess(dstLV, true);
      const size = this.sizeOf(st);
      const tmp = [];
      for (const [o, c] of src.blk.cells) if (o >= src.off && o < src.off + size) tmp.push([o - src.off, c]);
      for (const [o, c] of [...dstLV.blk.cells]) if (o >= dstLV.off && o < dstLV.off + size) dstLV.blk.cells.delete(o);
      for (const [o, c] of tmp) {
        let v = c.v;
        if (c.t.k === 'cont' && this.cpp && v) v = this.cloneCont(v);
        dstLV.blk.cells.set(dstLV.off + o, { t: c.t, v });
      }
    }
    copyArray(dstLV, val) {
      if (val.t.k === 'string') { // char arr = "str" handled in init
        const s = val.v;
        for (let i = 0; i < s.length; i++) this.writeCell(dstLV.blk, dstLV.off + i, T.char, s.charCodeAt(i));
        this.writeCell(dstLV.blk, dstLV.off + s.length, T.char, 0);
        return;
      }
      const size = this.sizeOf(dstLV.t);
      const src = val.v;
      for (const [o, c] of src.blk.cells) if (o >= src.off && o < src.off + size) dstLV.blk.cells.set(dstLV.off + o - src.off, { t: c.t, v: c.v });
    }

    // ================= conversions =================
    convert(val, t) {
      if (!t || t.k === 'auto' || t.k === 'void') return val;
      const ft = val.t;
      let v = val.v;
      switch (t.k) {
        case 'prim':
          if (ft.k === 'any') { if (val.v == null || val.isNull) throw new RunError((this.java ? 'NullPointerException：' : '') + '对 null 值做了拆箱（把 null 当作数字使用）', 'segfault'); return this.convert(val.v && val.v.t ? val.v : val, t); }
          if (ft.k === 'prim') {
            if (t.fl) return { t, v: t.size === 4 ? Math.fround(Number(v)) : Number(v) };
            if (t.isBool) return { t, v: v ? 1 : 0 };
            if (ft.fl) { if (!isFinite(v)) v = t.size === 8 ? -9223372036854775808 : -2147483648; return { t, v: this.wrapInt(Math.trunc(v), t) }; }
            return { t, v: ft === t ? v : this.wrapInt(v, t) };
          }
          if (ft.k === 'ptr' || ft.k === 'nullptr') {
            if (t.isBool) return { t, v: v && (v.blk || v.wild) ? 1 : 0 };
            return { t, v: v && v.blk ? v.blk.addr + v.off : (v && v.wild ? v.off : 0) };
          }
          if (ft.k === 'string') { if (t.isBool) return { t, v: 1 }; break; }
          if (ft.k === 'stream') return { t, v: v.fail ? 0 : 1 };
          if (ft.k === 'cont') { if (t.isBool) return { t, v: v ? 1 : 0 }; break; }
          if (ft.k === 'iter') { if (t.isBool) return { t, v: 1 }; break; }
          if (ft.k === 'struct') break;
          return { t, v: Number(v) || 0 };
        case 'ptr':
          if (ft.k === 'ptr') return { t, v };
          if (ft.k === 'nullptr') return { t, v: NULLP };
          if (ft.k === 'prim') { if (Number(v) === 0) return { t, v: NULLP }; return { t, v: new Ptr(null, Number(v), true) }; }
          if (ft.k === 'any') { if (v == null || val.isNull) return { t, v: NULLP }; return this.convert(v, t); }
          if (ft.k === 'func') return { t, v };
          if (ft.k === 'lambda') return { t, v };
          if (ft.k === 'string' && t.java) return { t: ft, v };
          if (ft.k === 'cont' && t.java) return { t: ft, v };
          if (ft.k === 'iter') return { t, v };
          break;
        case 'string':
          if (ft.k === 'string') return { t, v };
          if (ft.k === 'ptr' && ft.to.k === 'prim' && ft.to.size === 1) return { t, v: v.blk ? this.readCString(v) : (t.java ? null : '') };
          if (ft.k === 'nullptr' || (ft.k === 'ptr' && !v.blk)) return { t, v: t.java ? null : '' };
          if (ft.k === 'any') { if (v == null) return { t, v: null }; return this.convert(v, t); }
          if (ft.k === 'prim' && ft.isChar && !this.java) return { t, v: String.fromCharCode(v) };
          if (ft.k === 'cont' && v && v.ctype === 'StringBuilder') return { t, v: v.str };
          break;
        case 'cont':
          if (ft.k === 'initlist') {
            if (t.name === 'pair') return { t, v: this.constructCont(t, v), fresh: true };
            const m = this.constructCont(t, []); for (const x of v) this.contAdd(m, x); return { t, v: m, fresh: true };
          }
          if (ft.k === 'cont' || ft.k === 'nullptr') return { t, v: ft.k === 'nullptr' ? null : v };
          if (ft.k === 'any') return { t, v: v == null ? null : v.v };
          if (ft.k === 'ptr' && !v.blk) return { t, v: null };
          break;
        case 'any':
          return { t: ft, v };
        case 'struct':
          if (ft.k === 'struct') return val;
          if (ft.k === 'initlist') { const blk = this.newBlock('temp', this.sizeOf(t), t, ''); const lv = new MemLV(blk, 0, t); this.constructAt(lv, v, true); return { t, v: lv }; }
          if (ft.k === 'any' && v) return v;
          break;
        case 'lambda': case 'func': return val;
        case 'stream': return val;
        case 'iter': return val;
        case 'nullptr': return val;
        case 'ref': return this.convert(val, t.to);
      }
      if (t.k === 'ptr' && t.jref && ft.k === 'struct') return val;
      if (ft.k === 'cont' && t.k === 'ptr' && t.jarr === undefined) return val;
      throw new RunError('类型不匹配：不能把 ' + T.name(ft) + ' 转换为 ' + T.name(t), 'runtime', '检查赋值或参数两边的类型。');
    }

    // ================= strings =================
    strLit(s) {
      let blk = this.strLits.get(s);
      if (!blk) {
        blk = this.newBlock('str', s.length + 1, T.arr(T.char, s.length + 1), '"' + s + '"');
        for (let i = 0; i < s.length; i++) blk.cells.set(i, { t: T.char, v: s.charCodeAt(i) & 0xff });
        blk.cells.set(s.length, { t: T.char, v: 0 });
        blk.typed = true;
        this.strLits.set(s, blk);
      }
      return new Ptr(blk, 0);
    }
    readCString(p, max) {
      if (!p || !p.blk) {
        if (p && p.wild) throw new RunError('使用了未初始化的字符串指针', 'segfault');
        throw new RunError('段错误：试图把 NULL 当作字符串读取。', 'segfault', '可能是 get_string / malloc 返回了 NULL，或者字符串指针还没有指向任何内存。');
      }
      const blk = p.blk;
      if (blk.freed) throw new RunError('释放后使用：读取的字符串已经被 free 了。', 'uaf');
      let s = '';
      for (let o = p.off; ; o++) {
        if (o >= blk.size) throw new RunError('字符串没有以 \\0 结尾：读取时越过了这块内存的末尾（' + blk.size + ' 字节）。', 'oob', 'C 字符串必须以 \'\\0\' 结尾；分配内存时要多留 1 个字节，例如 malloc(strlen(s) + 1)。');
        const c = this.peekCell(blk, o, T.char);
        if (c === undefined) {
          s += '?'; if (s.length > 4096) break; continue;
        }
        if (c === 0) break;
        s += String.fromCharCode(c & 0xff);
        if (max && s.length >= max) break;
      }
      return s;
    }
    writeCString(p, s, limit) {
      if (!p || !p.blk) throw new RunError('段错误：试图向 NULL 指针写入字符串。', 'segfault');
      const n = s.length + 1;
      if (p.off + n > p.blk.size) throw new RunError('缓冲区溢出：要写入 ' + n + ' 个字节（含 \\0），但目标内存只剩 ' + (p.blk.size - p.off) + ' 个字节。', 'oob', '目标数组/内存要足够大，记得给结尾的 \\0 留位置。');
      if (p.blk.kind === 'str') throw new RunError('试图修改字符串字面量（只读内存）', 'segfault');
      if (p.blk.freed) throw new RunError('释放后使用：向已经 free 的内存写入字符串。', 'uaf');
      for (let i = 0; i < s.length; i++) this.writeCell(p.blk, p.off + i, T.char, s.charCodeAt(i) & 0xff);
      this.writeCell(p.blk, p.off + s.length, T.char, 0);
      if (!p.blk.typed) this.inferViewType(p.blk, T.char);
    }

    // ================= frames & variables =================
    get frame() { return this.frames[this.frames.length - 1]; }
    pushScope() { const m = new Map(); m.sp = this.stackAddr; this.frame.scopes.push(m); }
    popScope() {
      const f = this.frame;
      const sc = f.scopes.pop();
      this.killScope(sc);
      if (sc.sp) this.stackAddr = sc.sp;
    }
    killScope(sc) {
      const vars = [...sc.values()].reverse();
      for (const v of vars) {
        if (v.blk) {
          if (this.cpp && v.t.k === 'struct' && !v.noDtor) this.destroyObject(new MemLV(v.blk, 0, v.t));
          if (this.cpp && v.t.k === 'cont') { const m = this.peekCell(v.blk, 0, v.t); if (m) this.killCont(m); }
          v.blk.dead = true;
        }
      }
    }
    killCont(m) { m.dead = true; for (const it of m.items) if (it && it.t && it.t.k === 'cont' && it.v) this.killCont(it.v); }
    declareVar(name, t, line, opts) {
      opts = opts || {};
      const sc = this.frame.scopes[this.frame.scopes.length - 1];
      const v = { name, t, line, seq: ++this.seq };
      if (t.k === 'ref') { v.lv = opts.lv; v.t = t.to; v.isRef = true; }
      else {
        if (t.k === 'auto') throw new RunError('auto 变量必须有初始值', 'runtime');
        v.blk = this.newBlock('stack', this.sizeOf(t), t, name);
        v.blk.typed = true;
        if (this.java) v.blk.zero = false;
      }
      sc.set(name, v);
      return v;
    }
    lookupVar(name) {
      for (let fr = this.frame; fr; fr = fr.parent) {
        for (let i = fr.scopes.length - 1; i >= 0; i--) {
          const v = fr.scopes[i].get(name);
          if (v) return v;
        }
        if (!fr.parent) break;
      }
      return null;
    }
    varLV(v, desc) {
      if (v.isRef) return v.lv;
      return new MemLV(v.blk, 0, v.t, false, desc || v.name);
    }

    // ================= stepping =================
    step(line, ev, extra) {
      const fr = this.frame;
      if (fr && fr.hidden) return;
      this.curLine = line;
      this.rec.record(line, ev || 'line', () => this.snapshot(), Object.assign({ depth: this.visibleDepth(), fn: fr ? fr.name : '' }, extra || {}));
    }
    visibleDepth() { let n = 0; for (const f of this.frames) if (!f.hidden) n++; return n; }

    // ================= run =================
    run() {
      let err = null;
      this.seq = 0;
      try {
        try {
          if (this.java) this.runJava(); else this.runC();
        } catch (e) {
          if (e instanceof ExitSignal) {
            this.rec.note('程序调用 exit(' + e.code + ') 退出', 'info');
            this.finalStep(this.curLine, e.code);
          } else if (e instanceof ThrowSignal) {
            throw new RunError('未捕获的异常：' + this.excText(e.val), 'exception', '这个异常一直没有被 try/catch 捕获，所以程序终止了。');
          } else throw e;
        }
      } catch (e) {
        err = e;
        if (e && (e.isRun || e instanceof RangeError)) {
          if (e instanceof RangeError) e = new RunError('栈溢出（Stack overflow）：递归层数太深，调用栈被耗尽了。', 'stack', '检查递归函数是否有正确的终止条件（base case），以及每次递归是否在向终止条件靠近。');
          err = e;
          try {
            this.rec.pending.push({ text: e.message, cls: 'error' });
            this.rec.maxSteps += 1;
            this.rec.record(this.curLine, 'error', () => this.snapshot(), { depth: this.visibleDepth(), err: { kind: e.kind, msg: e.message, hint: e.hint } });
          } catch (e2) { }
        }
      }
      return DSV.finishRun(this.rec, err);
    }
    excText(val) {
      if (!val) return 'null';
      if (val.t && val.t.k === 'ptr' && val.v && val.v.blk) {
        const st = val.v.blk.type;
        const f = st && st.k === 'struct' ? this.findField(st, 'message') || this.findField(st, 'msg') : null;
        const m = f ? this.peekCell(val.v.blk, f.offset, f.type) : null;
        return (st ? st.name : '?') + (m != null ? ': ' + m : '');
      }
      if (val.t && val.t.k === 'struct') {
        const lv = val.v;
        const f = this.findField(val.t, 'msg') || this.findField(val.t, 'message');
        const m = f ? this.peekCell(lv.blk, lv.off + f.offset, f.type) : null;
        return val.t.name + (m != null ? ': ' + m : '');
      }
      return this.toDisplay(val);
    }

    runC() {
      // globals
      this.initGlobals();
      const mains = this.funcs.get('main');
      if (!mains) throw new CompileError('找不到 main 函数。程序需要一个 int main(void) 或 int main(int argc, char *argv[]) 作为入口。', 1);
      const main = mains[0];
      const args = [];
      if (main.params.length >= 2) {
        const argv = [this.opts.progName || './a.out', ...(this.opts.args || [])];
        args.push({ t: T.int, v: argv.length });
        const arr = this.newBlock('argv', 8 * (argv.length + 1), T.arr(T.ptr(T.char), argv.length + 1), 'argv');
        arr.typed = true;
        argv.forEach((s, i) => {
          const sb = this.newBlock('argv', s.length + 1, T.arr(T.char, s.length + 1), 'argv[' + i + ']');
          sb.typed = true;
          for (let k = 0; k < s.length; k++) sb.cells.set(k, { t: T.char, v: s.charCodeAt(k) });
          sb.cells.set(s.length, { t: T.char, v: 0 });
          arr.cells.set(i * 8, { t: T.ptr(T.char), v: new Ptr(sb, 0) });
        });
        arr.cells.set(argv.length * 8, { t: T.ptr(T.char), v: NULLP });
        this.argvBlock = arr;
        args.push({ t: T.ptr(T.ptr(T.char)), v: new Ptr(arr, 0) });
      }
      const r = this.callFunction(main, args, null, main.line);
      const code = r ? this.convert(r, T.int).v : 0;
      this.finalStep(main.endLine || this.curLine, code);
    }
    finalStep(line, code) {
      // destroy globals in C++? leave
      const leaks = this.findLeaks();
      this.rec.note('程序结束' + (code !== undefined ? '，返回值 ' + code : '') + '。', 'end');
      if (!this.java && leaks.length) {
        const bytes = leaks.reduce((a, b) => a + b.size, 0);
        this.rec.note('内存泄漏：程序结束时还有 ' + leaks.length + ' 块堆内存（共 ' + bytes + ' 字节）没有被 ' + (this.cpp ? 'delete/free' : 'free') + '。', 'leak');
      } else if (!this.java && this.mallocCount) this.rec.note('所有堆内存都已正确释放，没有内存泄漏。', 'ok');
      this.frames = [];
      this.rec.maxSteps += 1;
      this.rec.record(line, 'end', () => this.snapshot(), { depth: 0, fn: '' });
    }
    findLeaks() {
      const reach = this.reachable();
      return this.heapBlocks.filter(b => !b.freed && !reach.has(b) && !b.cs50);
    }

    initGlobals() {
      this.frames.push({ name: '<全局初始化>', scopes: [new Map()], hidden: true, id: 0 });
      for (const g of this.prog.globals) {
        let t = g.vtype;
        const name = g.ownerClass ? g.ownerClass.name + '::' + g.name : g.name;
        if (t.k === 'arr' && t.len == null && g.init) t = this.inferArrLen(t, g.init);
        if (t.k === 'arr' && t.lenExpr) t = T.arr(t.of, this.convert(this.ev(t.lenExpr), T.long).v);
        if (t.k === 'auto') t = this.ev(g.init).t;
        let gv = this.globals.get(name);
        if (!gv) {
          const blk = this.newBlock('global', this.sizeOf(t), t, name);
          blk.zero = true; blk.typed = true;
          gv = { name, t, blk, line: g.line };
          this.globals.set(name, gv);
          this.globalOrder.push(gv);
        }
        if (g.init || g.ctorArgs) this.initVar(new MemLV(gv.blk, 0, t), t, g.init, g.ctorArgs, g.line);
        else if (this.cpp) this.defaultInit(new MemLV(gv.blk, 0, t), t);
      }
      // C++ static members declared in class without out-of-class definition
      if (this.cpp) for (const st of this.prog.classes) for (const sf of st.staticFields) {
        const name = st.name + '::' + sf.name;
        if (this.globals.has(name)) continue;
        const blk = this.newBlock('global', this.sizeOf(sf.type), sf.type, name);
        blk.zero = true; blk.typed = true;
        const gv = { name, t: sf.type, blk, line: sf.line };
        this.globals.set(name, gv); this.globalOrder.push(gv);
        if (sf.init) this.initVar(new MemLV(blk, 0, sf.type), sf.type, sf.init, null, sf.line);
      }
      this.frames.pop();
    }

    // ================= functions =================
    callFunction(fn, args, thisPtr, callLine, opts) {
      opts = opts || {};
      if (!fn.body) throw new RunError('函数 “' + fn.name + '” 只有声明，没有实现（函数体）。', 'runtime', '检查函数是否写了 { ... } 函数体，或者名字是否拼错。');
      if (this.frames.length > this.depthLimit) throw new RunError('栈溢出（Stack overflow）：函数调用嵌套超过了 ' + this.depthLimit + ' 层。', 'stack', '检查递归是否有正确的终止条件（base case）。');
      const owner = fn.owner;
      const spSave = this.stackAddr;
      const frame = {
        id: ++this.seq, fn, name: owner ? (this.java ? owner.name + '.' + fn.name : (fn.isCtor || fn.isDtor ? owner.name + '::' + fn.name : owner.name + '::' + fn.name)) : fn.name,
        scopes: [new Map()], thisPtr, cls: owner, hidden: !!fn.builtin || (this.frame && this.frame.hidden && opts.inHidden),
        parent: opts.closure || null, callLine,
      };
      if (opts.lambda) { frame.name = 'lambda'; frame.cls = opts.closure ? opts.closure.cls : null; frame.thisPtr = opts.closure ? opts.closure.thisPtr : null; }
      // bind params (evaluate conversions in caller context)
      const binds = [];
      const params = fn.params;
      for (let i = 0; i < params.length; i++) {
        const p = params[i];
        if (p.varargs) {
          if (this.java) {
            const rest = args.slice(i);
            if (rest.length === 1 && rest[0].t.k === 'ptr' && rest[0].t.jarr) binds.push({ p, val: rest[0] });
            else binds.push({ p, val: { t: p.type, v: this.makeJavaArray(p.type.to, rest) } });
          }
          break;
        }
        let a = args[i];
        if (a === undefined) {
          if (p.def) a = this.ev(p.def);
          else throw new RunError('调用 ' + fn.name + ' 时参数个数不对：需要 ' + params.filter(q => !q.def && !q.varargs).length + ' 个参数，实际传了 ' + args.length + ' 个。', 'runtime');
        }
        binds.push({ p, val: a });
      }
      this.frames.push(frame);
      for (const { p, val } of binds) {
        if (!p.name) continue;
        if (p.type.k === 'ref') {
          let lv = val.lv;
          if (!lv) { // binding temporary to const ref
            const v = this.declareVar(p.name, p.type.to, p.line || fn.line);
            this.storeInit(this.varLV(v), val);
            continue;
          }
          this.declareVar(p.name, p.type, p.line || fn.line, { lv });
          continue;
        }
        let pt = p.type;
        if (pt.k === 'auto') pt = val.t;
        const v = this.declareVar(p.name, pt, p.line || fn.line);
        this.storeInit(this.varLV(v), val.lv && val.t.k !== 'struct' ? this.load(val.lv) : val);
      }
      if (!frame.hidden) {
        let msg = '调用 ' + frame.name + '(' + binds.map(b => this.toDisplay(b.val)).join(', ') + ')';
        if (this.frames.length > 2 && this.frames[this.frames.length - 2].fn === fn) msg += '（递归，第 ' + this.frames.filter(f => f.fn === fn).length + ' 层）';
        this.rec.note(msg, 'call');
        this.step(fn.line, 'call');
      }
      if (opts.beforeBody) opts.beforeBody(frame);
      const r = this.execStmts(fn.body.body, opts.skipFirst ? 1 : 0);
      let retVal = r instanceof Ret ? r.val : undefined;
      if (r && r.brk) throw new RunError('break 不在循环或 switch 里', 'runtime');
      if (r instanceof ThrowSignal) throw r;
      const retT = fn.ret;
      if (retVal && retT && retT.k !== 'void' && retT.k !== 'auto' && retT.k !== 'ref' && !(retT.k === 'struct')) retVal = this.convert(retVal, retT);
      if (retVal && retT && retT.k === 'struct' && retVal.t.k === 'struct') {
        // copy into temp
        const blk = this.newBlock('temp', this.sizeOf(retT), retT, '返回值');
        this.copyStruct(new MemLV(blk, 0, retT), retVal);
        retVal = { t: retT, v: new MemLV(blk, 0, retT) };
      }
      if (retVal && retT && retT.k === 'cont' && this.cpp && retVal.v && !retVal.fresh) retVal = { t: retVal.t, v: this.cloneCont(retVal.v), fresh: true };
      if (!retVal && retT && retT.k !== 'void' && retT.k !== 'auto' && !fn.isCtor && !fn.isDtor && fn.name !== 'main' && !this.java) {
        this.rec.note('⚠ 函数 ' + fn.name + ' 应该返回 ' + T.name(retT) + '，但执行到末尾也没有 return，返回值是不确定的。', 'warn');
      }
      if (!frame.hidden) {
        frame.retVal = retVal;
        frame.returning = true;
        const rl = r instanceof Ret ? r.line : (fn.body.endLine || fn.line);
        if (!(fn.name === 'main' && !owner)) this.rec.note(frame.name + ' 返回' + (retVal ? ' ' + this.toDisplay(retVal) : ''), 'ret');
        this.step(rl, 'return');
      }
      // destroy locals
      while (frame.scopes.length) {
        const sc = frame.scopes.pop();
        if (retVal && retVal.v && retVal.t.k === 'cont') { for (const v of sc.values()) if (v.blk && this.peekCell(v.blk, 0, v.t) === retVal.v) v.noDtor = true; }
        this.killScope(sc);
      }
      this.frames.pop();
      this.stackAddr = spSave;
      if (retVal && retVal.lv && fn.ret && fn.ret.k !== 'ref') retVal = this.load(retVal.lv);
      return retVal;
    }

    // overload resolution
    pickOverload(list, args, what) {
      const cands = list.filter(f => {
        const req = f.params.filter(p => !p.def && !p.varargs).length;
        const max = f.params.some(p => p.varargs) ? Infinity : f.params.length;
        return args.length >= req && args.length <= max;
      });
      if (!cands.length) {
        const f = list[0];
        throw new RunError('调用 ' + what + ' 的参数个数不对：需要 ' + f.params.length + ' 个参数，实际传了 ' + args.length + ' 个。', 'runtime');
      }
      if (cands.length === 1) return cands[0];
      let best = cands[0], bestScore = -1;
      for (const f of cands) {
        let score = 0;
        f.params.forEach((p, i) => { if (args[i]) score += this.matchScore(p.type, args[i].t); });
        if (f.body) score += 0.5;
        if (score > bestScore) { bestScore = score; best = f; }
      }
      return best;
    }
    matchScore(pt, at) {
      if (pt.k === 'ref') pt = pt.to;
      if (pt === at) return 4;
      if (pt.k === at.k) {
        if (pt.k === 'prim') return (pt.fl === at.fl ? 2 : 1) + (pt.size === at.size ? 1 : 0) + (!!pt.isChar === !!at.isChar ? 0.5 : 0);
        if (pt.k === 'ptr') return pt.to === at.to || (pt.to.k === at.to.k && pt.to.name === at.to.name) ? 3 : 1;
        if (pt.k === 'struct') return pt === at ? 3 : 0;
        return 2;
      }
      if (pt.k === 'any') return 1;
      if (pt.k === 'string' && at.k === 'ptr') return 1.5;
      return 0;
    }

    // ================= statements =================
    execStmts(list, start) {
      for (let i = start || 0; i < list.length; i++) {
        const r = this.exec(list[i]);
        if (r) return r;
      }
      return null;
    }
    execBlock(b, noScope) {
      if (!noScope) this.pushScope();
      const depth = this.frame.scopes.length;
      const r = this.execStmts(b.body);
      if (!noScope) {
        while (this.frame.scopes.length > depth - 1) this.popScope();
      }
      return r;
    }
    exec(s) {
      switch (s.type) {
        case 'Block': return this.execBlock(s);
        case 'Empty': return null;
        case 'ExprStmt':
          this.step(s.line);
          this.ev(s.e, true);
          return null;
        case 'Decl':
          this.step(s.line);
          for (const d of s.decls) this.execDecl(d);
          return null;
        case 'VarDecl':
          this.execDecl(s);
          return null;
        case 'If': {
          this.step(s.line);
          const c = this.truthy(this.ev(s.cond));
          if (c) return this.execSub(s.then);
          if (s.els) return this.execSub(s.els);
          return null;
        }
        case 'While': {
          for (;;) {
            this.step(s.line);
            if (!this.truthy(this.ev(s.cond))) break;
            const r = this.execSub(s.body);
            if (r === BREAK) break;
            if (r === CONTINUE) continue;
            if (r) return r;
          }
          return null;
        }
        case 'DoWhile': {
          for (;;) {
            const r = this.execSub(s.body);
            if (r === BREAK) break;
            if (r && r !== CONTINUE) return r;
            this.step(s.condLine || s.line);
            if (!this.truthy(this.ev(s.cond))) break;
          }
          return null;
        }
        case 'For': {
          this.pushScope();
          const depth = this.frame.scopes.length;
          this.step(s.line);
          if (s.init) { if (s.init.type === 'Decl') for (const d of s.init.decls) this.execDecl(d); else this.ev(s.init.e, true); }
          let result = null;
          for (;;) {
            if (s.cond && !this.truthy(this.ev(s.cond))) break;
            const r = this.execSub(s.body);
            if (r === BREAK) break;
            if (r && r !== CONTINUE) { result = r; break; }
            this.step(s.line);
            if (s.update) this.ev(s.update, true);
          }
          while (this.frame.scopes.length >= depth) this.popScope();
          return result;
        }
        case 'ForEach': return this.execForEach(s);
        case 'Switch': {
          this.step(s.line);
          const dv = this.ev(s.disc);
          let start = -1;
          for (let i = 0; i < s.cases.length; i++) {
            const c = s.cases[i];
            if (c.test && this.eqVals(dv, this.ev(c.test))) { start = i; break; }
          }
          if (start < 0) start = s.cases.findIndex(c => !c.test);
          if (start < 0) return null;
          this.pushScope();
          const depth = this.frame.scopes.length;
          let result = null;
          outer: for (let i = start; i < s.cases.length; i++) {
            for (const st of s.cases[i].body) {
              const r = this.exec(st);
              if (r === BREAK) break outer;
              if (r) { result = r; break outer; }
            }
          }
          while (this.frame.scopes.length >= depth) this.popScope();
          return result;
        }
        case 'Break': this.step(s.line); return BREAK;
        case 'Continue': this.step(s.line); return CONTINUE;
        case 'Return': {
          this.step(s.line);
          let v;
          if (s.e) {
            const fn = this.frame.fn;
            if (s.e.type === 'InitList' && fn && fn.ret) {
              const tmp = this.newBlock('temp', this.sizeOf(fn.ret), fn.ret, '');
              this.initVar(new MemLV(tmp, 0, fn.ret), fn.ret, s.e, null, s.line);
              v = this.load(new MemLV(tmp, 0, fn.ret));
            } else if (fn && fn.ret && fn.ret.k === 'ref') {
              const lv = this.lv(s.e);
              v = Object.assign({}, this.load(lv), { lv });
            } else v = this.ev(s.e);
          }
          const r = new Ret(v); r.line = s.line;
          return r;
        }
        case 'Throw': {
          this.step(s.line);
          const v = s.e ? this.ev(s.e) : this.lastCaught;
          let val = v;
          if (v && v.t.k === 'struct') val = this.structToElem(v);
          const sig = new ThrowSignal(val && val.t.k === 'struct' ? { t: val.t, v: new MemLV(val.v, 0, val.t) } : val, s.line);
          this.rec.note('抛出异常 ' + this.excText(sig.val), 'warn');
          throw sig;
        }
        case 'Try': return this.execTry(s);
        case 'Func': return null;
      }
      throw new RunError('暂不支持的语句类型：' + s.type, 'runtime');
    }
    execSub(s) {
      // body of if/loop: give non-block statements their own scope too
      if (s.type === 'Block') return this.execBlock(s);
      this.pushScope();
      const depth = this.frame.scopes.length;
      const r = this.exec(s);
      while (this.frame.scopes.length >= depth) this.popScope();
      return r;
    }
    execTry(s) {
      const frameDepth = this.frames.length;
      const scopeDepth = this.frame.scopes.length;
      this.step(s.line);
      let result = null, pendingThrow = null;
      try {
        if (s.resources) { this.pushScope(); for (const r of s.resources) this.exec(r); }
        result = this.execBlock(s.block);
        if (s.resources) this.popScope();
      } catch (e) {
        let exc = null;
        if (e instanceof ThrowSignal) exc = e;
        else if (e && e.isRun && e.kind !== 'limit') exc = this.runErrToThrow(e);
        if (!exc) throw e;
        // unwind
        while (this.frames.length > frameDepth) { const f = this.frames.pop(); for (const sc of f.scopes) for (const v of sc.values()) if (v.blk) v.blk.dead = true; }
        while (this.frame.scopes.length > scopeDepth) this.popScope();
        const h = s.handlers.find(h => this.catchMatches(h, exc.val));
        if (!h) { pendingThrow = e; }
        else {
          this.rec.note('异常被 catch 捕获：' + this.excText(exc.val), 'info');
          this.pushScope();
          if (h.name) {
            const ct = exc.val ? exc.val.t : T.any;
            const v = this.declareVar(h.name, ct.k === 'struct' ? ct : (ct.k === 'nullptr' ? T.any : ct), h.line);
            this.storeInit(this.varLV(v), exc.val);
          }
          this.lastCaught = exc.val;
          try {
            result = this.execBlock(h.body);
          } catch (e2) { this.popScope(); if (s.fin) { const fr = this.execBlock(s.fin); if (fr) return fr; } throw e2; }
          this.popScope();
        }
      }
      if (s.fin) { const fr = this.execBlock(s.fin); if (fr) return fr; }
      if (pendingThrow) throw pendingThrow;
      return result;
    }
    runErrToThrow(e) {
      if (!this.java && !this.cpp) return null;
      let name = null;
      const m = /^(\w+Exception)/.exec(e.message);
      if (this.java) {
        if (m) name = m[1];
        else if (e.kind === 'oob') name = 'ArrayIndexOutOfBoundsException';
        else if (e.kind === 'segfault') name = 'NullPointerException';
        else if (e.kind === 'div0') name = 'ArithmeticException';
        else return null;
      } else {
        if (e.cppExc) name = e.cppExc; else return null;
      }
      const st = this.classesByName.get(name) || this.classesByName.get(this.java ? 'RuntimeException' : 'exception');
      if (!st) return null;
      const obj = this.newObjectJava ? null : null;
      const val = this.java ? this.newJavaObject(st, [{ t: T.jstring, v: e.message.replace(/^\w+Exception：?/, '') }], this.curLine) : this.makeCppExc(st, e.message);
      return new ThrowSignal(val, this.curLine);
    }
    catchMatches(h, val) {
      if (h.types.includes('*')) return true;
      if (!val) return false;
      let st = null;
      if (val.t.k === 'ptr' && val.v && val.v.blk) st = val.v.blk.type;
      else if (val.t.k === 'struct') st = val.t;
      for (const tn of h.types) {
        if (tn === 'Exception' || tn === 'Throwable' || tn === 'exception' || tn === 'std::exception') { if (st) return true; }
        if (st) { for (let s = st; s; s = s.base) if (s.name === tn) return true; }
        else if (val.t.k === 'prim' && (tn === 'int' || tn === T.name(val.t))) return true;
        else if (val.t.k === 'ptr' && tn.includes('char')) return true;
        else if (val.t.k === 'string' && tn.includes('string')) return true;
      }
      return false;
    }

    execDecl(d) {
      let t = d.vtype;
      if (d.bind) return this.execBinding(d);
      if (t.k === 'arr' && t.len == null && d.init) t = this.inferArrLen(t, d.init);
      t = this.resolveVLA(t);
      if (t.k === 'auto') {
        if (!d.init) throw new RunError('auto 变量必须有初始值', 'runtime');
        const v0 = this.ev(d.init);
        let at = v0.t;
        if (at.k === 'nullptr') at = T.ptr(T.void);
        if (v0.arrDecay) at = v0.t;
        const v = this.declareVar(d.name, at, d.line);
        this.storeInit(this.varLV(v), v0);
        return;
      }
      if (t.k === 'ref') {
        if (!d.init) throw new RunError('引用必须在声明时初始化', 'runtime');
        let lv;
        if (this.isLvalueExpr(d.init)) lv = this.lv(d.init);
        else { const val = this.ev(d.init); if (val.lv) lv = val.lv; else { const vv = this.declareVar(d.name, t.to.k === 'auto' ? val.t : t.to, d.line); this.storeInit(this.varLV(vv), val); return; } }
        if (t.to.k === 'auto') t = T.ref(this.load(lv).t);
        this.declareVar(d.name, t, d.line, { lv });
        return;
      }
      if (d.isStatic && this.frame.fn) {
        // function-level static: keep across calls
        const key = (this.frame.fn.name) + '::' + d.name;
        let gv = this.globals.get(key);
        if (!gv) {
          const blk = this.newBlock('global', this.sizeOf(t), t, key); blk.zero = true; blk.typed = true;
          gv = { name: key, t, blk, line: d.line, isStaticLocal: true };
          this.globals.set(key, gv); this.globalOrder.push(gv);
          if (d.init) this.initVar(new MemLV(blk, 0, t), t, d.init, d.ctorArgs, d.line);
        }
        const sc = this.frame.scopes[this.frame.scopes.length - 1];
        sc.set(d.name, { name: d.name, t, blk: gv.blk, isStatic: true, seq: ++this.seq });
        return;
      }
      const v = this.declareVar(d.name, t, d.line);
      const lv = this.varLV(v);
      if (d.init || d.ctorArgs) this.initVar(lv, t, d.init, d.ctorArgs, d.line, d.braceInit);
      else this.defaultInit(lv, t);
    }
    execBinding(d) {
      const val = this.ev(d.init);
      const names = d.name;
      let parts;
      if (val.t.k === 'cont' && val.v) parts = this.pairParts(val.v);
      else if (val.t.k === 'struct') { this.layout(val.t); parts = val.t.allFields.map(f => this.load(new MemLV(val.v.blk, val.v.off + f.offset, f.type))); }
      else throw new RunError('结构化绑定只支持 pair / tuple / 结构体', 'runtime');
      names.forEach((n, i) => { const p = parts[i]; const v = this.declareVar(n, p.t, d.line); this.storeInit(this.varLV(v), p); });
    }
    resolveVLA(t) {
      if (t.k !== 'arr') return t;
      const inner = this.resolveVLA(t.of);
      if (t.lenExpr && t.len == null) {
        const n = this.convert(this.ev(t.lenExpr), T.long).v;
        if (n < 0) throw new RunError('数组长度不能是负数（' + n + '）', 'runtime');
        if (n > 1e6) throw new RunError('数组太大（' + n + ' 个元素），可视化器最多支持 100 万个元素', 'runtime');
        return T.arr(inner, n);
      }
      if (inner !== t.of) return T.arr(inner, t.len);
      return t;
    }
    inferArrLen(t, init) {
      if (init.type === 'InitList') {
        let n = init.items.length;
        let idx = 0, mx = 0;
        for (const it of init.items) { if (it.type === 'Designated' && it.des.index) idx = this.convert(this.ev(it.des.index), T.int).v; mx = Math.max(mx, idx + 1); idx++; }
        n = Math.max(n, mx);
        if (init.items.length === 1 && init.items[0].type === 'Str' && t.of.k === 'prim' && t.of.size === 1) n = init.items[0].v.length + 1;
        return T.arr(t.of, n);
      }
      if (init.type === 'Str') return T.arr(t.of, init.v.length + 1);
      return t;
    }
    isLvalueExpr(e) { return ['Ident', 'Index', 'Member', 'Deref', 'This'].includes(e.type) || (e.type === 'Call' && false); }

    // initialise a freshly declared object
    initVar(lv, t, init, ctorArgs, line, braceInit) {
      if (ctorArgs) {
        if (t.k === 'struct') return this.constructAt(lv, ctorArgs.map(a => this.evArg(a)), false);
        if (t.k === 'cont') return this.store(lv, { t, v: this.constructCont(t, ctorArgs.map(a => this.ev(a))) }, true);
        if (t.k === 'string') return this.store(lv, { t, v: this.constructString(ctorArgs.map(a => this.ev(a))) });
        if (ctorArgs.length) return this.store(lv, this.ev(ctorArgs[0]));
        return this.store(lv, { t, v: this.zeroOf(t) });
      }
      if (init.type === 'InitList') return this.initList(lv, t, init, line);
      if (t.k === 'arr' && init.type === 'Str') {
        const s = init.v;
        if (s.length + 1 > t.len) { if (s.length > t.len) throw new RunError('字符串 "' + s + '" 太长，放不进 char[' + t.len + ']（还需要 1 个字节存放 \\0）', 'oob'); }
        for (let i = 0; i < t.len; i++) this.writeCell(lv.blk, lv.off + i, T.char, i < s.length ? s.charCodeAt(i) : 0);
        return;
      }
      if (t.k === 'struct' && this.cpp) {
        const v = this.ev(init);
        if (v.t.k !== 'struct') return this.constructAt(lv, [v], false);
        if (t.ctors && t.ctors.length && v.t !== t) return this.constructAt(lv, [v], false);
        this.store(lv, v, true);
        return;
      }
      const v = this.ev(init);
      this.storeInit(lv, v);
    }
    storeInit(lv, v) {
      if (lv.t && lv.t.k === 'cont' && this.cpp && v.v && (v.fresh || v.t.k !== 'cont')) { this.store(lv, v, true); return; }
      this.store(lv, v);
    }
    defaultInit(lv, t) {
      if (t.k === 'struct') { if (this.cpp) this.constructAt(lv, [], false, true); return; }
      if (t.k === 'cont') { if (this.cpp) this.store(lv, { t, v: this.constructCont(t, []) }, true); return; }
      if (t.k === 'string' && !t.java) { this.store(lv, { t, v: '' }); return; }
      if (t.k === 'arr' && (t.of.k === 'struct' || t.of.k === 'cont' || t.of.k === 'string') && this.cpp) {
        const es = this.sizeOf(t.of);
        for (let i = 0; i < t.len; i++) this.defaultInit(new MemLV(lv.blk, lv.off + i * es, t.of), t.of);
      }
    }
    zeroFill(lv, t) {
      if (t.k === 'arr') { const es = this.sizeOf(t.of); for (let i = 0; i < t.len; i++) this.zeroFill(new MemLV(lv.blk, lv.off + i * es, t.of), t.of); return; }
      if (t.k === 'struct') { this.layout(t); for (const f of t.allFields) this.zeroFill(new MemLV(lv.blk, lv.off + f.offset, f.type), f.type); return; }
      if (t.k === 'cont' && this.cpp) { this.writeCell(lv.blk, lv.off, t, this.constructCont(t, [])); return; }
      this.writeCell(lv.blk, lv.off, t, this.zeroOf(t));
    }
    initList(lv, t, init, line) {
      const items = init.items;
      if (t.k === 'arr') {
        const es = this.sizeOf(t.of);
        if (items.length === 1 && items[0].type === 'Str' && t.of.k === 'prim' && t.of.size === 1) return this.initVar(lv, t, items[0], null, line);
        const done = new Set();
        let idx = 0;
        for (const it of items) {
          let e = it;
          if (it.type === 'Designated') { idx = this.convert(this.ev(it.des.index), T.int).v; e = it.value; }
          if (idx >= t.len) throw new RunError('初始化列表的元素太多：数组只有 ' + t.len + ' 个元素', 'oob');
          const elv = new MemLV(lv.blk, lv.off + idx * es, t.of);
          if (e.type === 'InitList') this.initList(elv, t.of, e, line);
          else this.initVar(elv, t.of, e, null, line);
          done.add(idx); idx++;
        }
        for (let i = 0; i < t.len; i++) if (!done.has(i)) this.zeroFill(new MemLV(lv.blk, lv.off + i * es, t.of), t.of);
        return;
      }
      if (t.k === 'struct') {
        this.layout(t);
        if (this.cpp && t.ctors.length) return this.constructAt(lv, items.map(a => this.evArg(a)), true);
        const done = new Set();
        let fi = 0;
        const fields = t.allFields;
        for (const it of items) {
          let e = it, f;
          if (it.type === 'Designated') { f = this.findField(t, it.des.field); if (!f) throw new RunError('结构体 ' + T.name(t) + ' 没有成员 ' + it.des.field, 'runtime'); fi = fields.indexOf(f); e = it.value; }
          else f = fields[fi];
          if (!f) throw new RunError('初始化列表的元素比结构体成员还多', 'runtime');
          const flv = new MemLV(lv.blk, lv.off + f.offset, f.type);
          if (e.type === 'InitList') this.initList(flv, f.type, e, line);
          else this.initVar(flv, f.type, e, null, line);
          done.add(f); fi++;
        }
        for (const f of fields) if (!done.has(f)) { if (f.init && this.cpp) this.initVar(new MemLV(lv.blk, lv.off + f.offset, f.type), f.type, f.init, null, line); else this.zeroFill(new MemLV(lv.blk, lv.off + f.offset, f.type), f.type); }
        return;
      }
      if (t.k === 'cont') { this.store(lv, { t, v: this.constructCont(t, [], items) }, true); return; }
      if (t.k === 'ptr' && t.jarr) { this.store(lv, { t, v: this.javaArrayFromInit(t.to, init) }); return; }
      if (t.k === 'string') { this.store(lv, items.length ? this.ev(items[0]) : { t, v: '' }); return; }
      // scalar
      if (items.length === 0) this.store(lv, { t, v: this.zeroOf(t) });
      else this.store(lv, this.ev(items[0]));
    }

    // ================= truthiness & equality =================
    truthy(val) {
      const t = val.t;
      if (t.k === 'prim') return val.v !== 0;
      if (t.k === 'ptr' || t.k === 'nullptr') return !!(val.v && (val.v.blk || val.v.wild));
      if (t.k === 'stream') return !val.v.fail;
      if (t.k === 'any') { if (val.v == null) return false; return this.truthy(val.v); }
      if (t.k === 'string') return val.v != null;
      if (t.k === 'cont') return val.v != null;
      return !!val.v;
    }
    eqVals(a, b) {
      const r = this.binop('==', a, b, 0);
      return r.v !== 0;
    }
  }

  DSV.ClikeInterp = Interp;
  DSV.clikeRT = { rel: () => REL, epoch: () => EPOCH, bump: () => { REL++; }, VMap, Block, Ptr, NULLP, MObj, Lambda, FnRef, ThrowSignal, StreamObj, MemLV, ElemLV, MapLV, StrCharLV, SbCharLV, TmpLV, BREAK, CONTINUE, Ret, isInt, isFlt, isArith, isPtrT };
})(typeof window !== 'undefined' ? window : globalThis);
