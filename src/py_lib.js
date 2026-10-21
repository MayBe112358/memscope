// ===== Python builtins, modules, snapshot =====
(function (G) {
  const DSV = G.DSV;
  const { RunError } = DSV;
  const R = DSV.pyRT;
  const { PyList, PyTuple, PyDict, PySet, PyDeque, PyObj, PyClass, PyFunc, PyBuiltin, PyBound, PyModule, PyRange, PyIter, PyProperty, PyStatic, PyClassMethod, PySuper, PyExc, floatRepr, strRepr } = R;
  const P = DSV.PyInterp.prototype;
  const NONE = null;

  P.mergeSort = function (arr, cmp) {
    if (arr.length < 2) return arr;
    const mid = arr.length >> 1;
    const a = this.mergeSort(arr.slice(0, mid), cmp), b = this.mergeSort(arr.slice(mid), cmp);
    let i = 0, j = 0, k = 0;
    while (i < a.length && j < b.length) arr[k++] = cmp(b[j], a[i]) < 0 ? b[j++] : a[i++];
    while (i < a.length) arr[k++] = a[i++];
    while (j < b.length) arr[k++] = b[j++];
    return arr;
  };
  P.sortValues = function (vals, keyFn, reverse) {
    const keys = keyFn && keyFn !== null ? vals.map(v => this.callValue(keyFn, [v], new Map())) : vals;
    const idx = vals.map((_, i) => i);
    this.mergeSort(idx, (a, b) => { const c = this.order(keys[a], keys[b], '<'); return reverse ? -c : c; });
    return idx.map(i => vals[i]);
  };
  P.lt = function (a, b) { return this.order(a, b, '<') < 0; };
  P.pyLen = function (v) {
    if (typeof v === 'string') return v.length;
    if (v instanceof PyList || v instanceof PyTuple || v instanceof PyDeque) return v.items.length;
    if (v instanceof PyDict || v instanceof PySet) return v.map.size;
    if (v instanceof PyRange) return this.rangeLen(v);
    if (v instanceof PyIter) return v.items.length - v.i;
    if (v instanceof PyObj) { const m = v.cls.lookup('__len__'); if (m) return Number(this.toInt(this.callValue(this.bind(v, m), [], new Map()))); }
    this.raise('TypeError', "object of type '" + this.typeName(v) + "' has no len()", v === null ? '你在对 None 求长度。检查变量是否被正确赋值。' : (typeof v === 'bigint' ? '整数没有长度。如果想知道数字有几位，可以用 len(str(n))。' : undefined));
  };

  // ================= builtins =================
  P.setupBuiltins = function () {
    const B = this.builtins;
    const self = this;
    const fn = (name, f) => B.set(name, new PyBuiltin(name, f));
    const type = (name, native, methods) => { const c = new PyClass(name, [], new Map()); c.builtin = true; c.native = native; c.methods = methods; B.set(name, c); return c; };
    const kw = (k, name, def) => k && k.has(name) ? k.get(name) : def;
    this.NotImplemented = { notImpl: true };
    B.set('NotImplemented', this.NotImplemented);
    B.set('Ellipsis', null);
    // exception hierarchy
    const exc = (name, base) => { const c = new PyClass(name, base ? [base] : [], new Map()); c.builtin = true; B.set(name, c); return c; };
    const BaseException = exc('BaseException');
    const Exception = exc('Exception', BaseException);
    exc('SystemExit', BaseException); exc('KeyboardInterrupt', BaseException);
    const Arith = exc('ArithmeticError', Exception); exc('ZeroDivisionError', Arith); exc('OverflowError', Arith);
    const Lookup = exc('LookupError', Exception); exc('IndexError', Lookup); exc('KeyError', Lookup);
    const VE = exc('ValueError', Exception); exc('UnicodeError', VE);
    exc('TypeError', Exception); exc('AttributeError', Exception);
    const NE = exc('NameError', Exception); exc('UnboundLocalError', NE);
    const RE = exc('RuntimeError', Exception); exc('RecursionError', RE); exc('NotImplementedError', RE);
    exc('StopIteration', Exception); exc('AssertionError', Exception); exc('ImportError', Exception); exc('ModuleNotFoundError', B.get('ImportError'));
    exc('EOFError', Exception); exc('MemoryError', Exception); exc('SyntaxError', Exception); exc('OSError', Exception); exc('FileNotFoundError', B.get('OSError'));
    exc('IndentationError', B.get('SyntaxError'));
    const objectCls = type('object', (a) => new PyObj(B.get('object')));
    // object base so super().__init__() works
    objectCls.attrs.set('__init__', new PyBuiltin('object.__init__', () => NONE));

    fn('print', (args, k) => {
      const sep = kw(k, 'sep', ' '), end = kw(k, 'end', '\n');
      const s = args.map(a => this.str(a)).join(sep === NONE ? ' ' : sep) + (end === NONE ? '\n' : end);
      this.rec.write(s);
      return NONE;
    });
    fn('input', (args) => {
      if (args.length) this.rec.write(this.str(args[0]));
      const ln = this.stdin.line();
      if (ln === null) this.raise('EOFError', 'EOF when reading a line', '程序调用了 input()，但“输入 (stdin)”框里的内容已经读完了。请在输入框里每行写一个值。');
      this.rec.write(ln + '\n');
      return ln;
    });
    fn('len', (a) => BigInt(this.pyLen(a[0])));
    type('int', (a, k) => {
      if (!a.length) return 0n;
      const v = a[0];
      if (a.length > 1 || k.has('base')) {
        const base = Number(this.toInt(a[1] !== undefined ? a[1] : k.get('base')));
        const s = this.str(v).trim().replace(/_/g, '').toLowerCase();
        const body = s.replace(/^[-+]/, '').replace(base === 16 ? /^0x/ : base === 2 ? /^0b/ : base === 8 ? /^0o/ : /^$/, '');
        const ok = body.length && [...body].every(c => { const d = parseInt(c, 36); return !isNaN(d) && d < base; });
        if (!ok) this.raise('ValueError', "invalid literal for int() with base " + base + ": " + strRepr(this.str(v)));
        let r = 0n; for (const c of body) r = r * BigInt(base) + BigInt(parseInt(c, 36));
        return s[0] === '-' ? -r : r;
      }
      if (typeof v === 'bigint') return v;
      if (typeof v === 'boolean') return v ? 1n : 0n;
      if (typeof v === 'number') { if (!isFinite(v)) this.raise(isNaN(v) ? 'ValueError' : 'OverflowError', 'cannot convert float ' + floatRepr(v) + ' to integer'); return BigInt(Math.trunc(v)); }
      if (typeof v === 'string') {
        const s = v.trim().replace(/_/g, '');
        if (!/^[-+]?\d+$/.test(s)) this.raise('ValueError', "invalid literal for int() with base 10: " + strRepr(v), /^[-+]?\d*\.\d+$/.test(s) ? '字符串里是小数，int() 不能直接转换带小数点的字符串。可以先 float() 再 int()。' : '字符串里只能包含数字（可以带正负号）。');
        return BigInt(s);
      }
      if (v instanceof PyObj) { const m = v.cls.lookup('__int__') || v.cls.lookup('__index__'); if (m) return this.callValue(this.bind(v, m), [], new Map()); }
      this.raise('TypeError', "int() argument must be a string, a bytes-like object or a real number, not '" + this.typeName(v) + "'");
    });
    type('float', (a) => {
      if (!a.length) return 0;
      const v = a[0];
      if (typeof v === 'string') {
        const s = v.trim().toLowerCase();
        if (s === 'inf' || s === '+inf' || s === 'infinity') return Infinity;
        if (s === '-inf' || s === '-infinity') return -Infinity;
        if (s === 'nan') return NaN;
        if (!/^[-+]?(\d+\.?\d*|\.\d+)(e[-+]?\d+)?$/.test(s.replace(/_/g, ''))) this.raise('ValueError', 'could not convert string to float: ' + strRepr(v));
        return parseFloat(s.replace(/_/g, ''));
      }
      if (v instanceof PyObj) { const m = v.cls.lookup('__float__'); if (m) return this.callValue(this.bind(v, m), [], new Map()); }
      return this.toNum(v);
    });
    type('str', (a) => a.length ? this.str(a[0]) : '');
    type('bool', (a) => a.length ? this.truthy(a[0]) : false);
    type('list', (a) => new PyList(a.length ? this.toArray(a[0]) : []));
    type('tuple', (a) => a.length && a[0] instanceof PyTuple && !a[0].cls ? a[0] : new PyTuple(a.length ? this.toArray(a[0]) : []));
    const dictCls = type('dict', (a, k) => {
      const d = new PyDict();
      if (a.length) this.dictUpdate(d, a[0]);
      for (const [kk, v] of k) this.dictSet(d, kk, v);
      return d;
    });
    dictCls.methods = { fromkeys: (it, rest) => { const d = new PyDict(); for (const x of this.toArray(it)) this.dictSet(d, x, rest.length ? rest[0] : NONE); return d; } };
    dictCls.attrs.set('fromkeys', new PyBuiltin('dict.fromkeys', (a) => { const d = new PyDict(); for (const x of this.toArray(a[0])) this.dictSet(d, x, a.length > 1 ? a[1] : NONE); return d; }));
    type('set', (a) => { const s = new PySet(); if (a.length) for (const v of this.toArray(a[0])) this.setAdd(s, v); return s; });
    type('frozenset', (a) => { const s = new PySet(); s.frozen = true; if (a.length) for (const v of this.toArray(a[0])) this.setAdd(s, v); return s; });
    type('range', (a) => {
      const ints = a.map(x => this.toInt(x));
      if (ints.length === 1) return new PyRange(0n, ints[0], 1n);
      if (ints.length === 2) return new PyRange(ints[0], ints[1], 1n);
      if (ints.length === 3) { if (ints[2] === 0n) this.raise('ValueError', 'range() arg 3 must not be zero'); return new PyRange(ints[0], ints[1], ints[2]); }
      this.raise('TypeError', 'range expected at least 1 argument, got 0');
    });
    type('type', (a) => this.typeOf(a[0]));
    type('slice', (a) => { const o = new PyObj(B.get('slice')); o.attrs.set('start', a.length > 1 ? a[0] : NONE); o.attrs.set('stop', a.length > 1 ? a[1] : a[0]); o.attrs.set('step', a[2] !== undefined ? a[2] : NONE); return o; });
    fn('abs', (a) => { const v = a[0]; if (typeof v === 'bigint') return v < 0n ? -v : v; if (typeof v === 'boolean') return v ? 1n : 0n; if (typeof v === 'number') return Math.abs(v); if (v instanceof PyObj) { const m = v.cls.lookup('__abs__'); if (m) return this.callValue(this.bind(v, m), [], new Map()); } this.raise('TypeError', "bad operand type for abs(): '" + this.typeName(v) + "'"); });
    const minmax = (which) => (a, k) => {
      const keyFn = kw(k, 'key', NONE);
      let vals = a.length === 1 ? this.toArray(a[0]) : a;
      if (!vals.length) { if (k.has('default')) return k.get('default'); this.raise('ValueError', which + '() arg is an empty sequence', '不能对空的列表/序列求最大值或最小值。可以先检查是否为空，或者传入 default= 参数。'); }
      let best = vals[0], bk = keyFn !== NONE ? this.callValue(keyFn, [best], new Map()) : best;
      for (let i = 1; i < vals.length; i++) {
        const v = vals[i], vk = keyFn !== NONE ? this.callValue(keyFn, [v], new Map()) : v;
        const c = this.order(vk, bk, which === 'max' ? '>' : '<');
        if (which === 'max' ? c > 0 : c < 0) { best = v; bk = vk; }
      }
      return best;
    };
    fn('min', minmax('min')); fn('max', minmax('max'));
    fn('sum', (a, k) => { let acc = a.length > 1 ? a[1] : kw(k, 'start', 0n); for (const v of this.toArray(a[0])) acc = this.binop('+', acc, v); return acc; });
    fn('sorted', (a, k) => new PyList(this.sortValues(this.toArray(a[0]), kw(k, 'key', NONE), this.truthy(kw(k, 'reverse', false)))));
    fn('reversed', (a) => { const v = a[0]; if (v instanceof PyObj) { const m = v.cls.lookup('__reversed__'); if (m) return this.callValue(this.bind(v, m), [], new Map()); } if (v instanceof PyDict || v instanceof PySet) { if (v instanceof PySet) this.raise('TypeError', "'set' object is not reversible"); } return new PyIter(this.toArray(v).reverse(), 'reversed'); });
    fn('enumerate', (a, k) => { let i = this.toInt(a.length > 1 ? a[1] : kw(k, 'start', 0n)); return new PyIter(this.toArray(a[0]).map(v => new PyTuple([i++, v])), 'enumerate'); });
    fn('zip', (a, k) => { const arrs = a.map(x => this.toArray(x)); const n = arrs.length ? Math.min(...arrs.map(x => x.length)) : 0; const out = []; for (let i = 0; i < n; i++) out.push(new PyTuple(arrs.map(x => x[i]))); return new PyIter(out, 'zip'); });
    fn('map', (a) => { const f = a[0]; const arrs = a.slice(1).map(x => this.toArray(x)); const n = Math.min(...arrs.map(x => x.length)); const out = []; for (let i = 0; i < n; i++) out.push(this.callValue(f, arrs.map(x => x[i]), new Map())); return new PyIter(out, 'map'); });
    fn('filter', (a) => new PyIter(this.toArray(a[1]).filter(v => this.truthy(a[0] === NONE ? v : this.callValue(a[0], [v], new Map()))), 'filter'));
    fn('any', (a) => { for (const v of this.toArray(a[0])) if (this.truthy(v)) return true; return false; });
    fn('all', (a) => { for (const v of this.toArray(a[0])) if (!this.truthy(v)) return false; return true; });
    fn('isinstance', (a) => this.isInstance(a[0], a[1]));
    fn('issubclass', (a) => { const chk = (c) => c instanceof PyTuple ? c.items.some(chk) : a[0].mro.includes(c); return chk(a[1]); });
    fn('ord', (a) => { if (typeof a[0] !== 'string' || [...a[0]].length !== 1) this.raise('TypeError', 'ord() expected a character, but string of length ' + (typeof a[0] === 'string' ? a[0].length : '?') + ' found'); return BigInt(a[0].codePointAt(0)); });
    fn('chr', (a) => String.fromCodePoint(Number(this.toInt(a[0]))));
    fn('round', (a) => {
      const v = a[0];
      if (a.length < 2 || a[1] === NONE) {
        if (typeof v === 'bigint') return v;
        const x = this.toNum(v); const f = Math.floor(x); const d = x - f;
        let r = d > 0.5 ? f + 1 : d < 0.5 ? f : (f % 2 === 0 ? f : f + 1);
        return BigInt(r);
      }
      const n = Number(this.toInt(a[1]));
      if (typeof v === 'bigint') { if (n >= 0) return v; const m = 10n ** BigInt(-n); return ((v + m / 2n) / m) * m; }
      return parseFloat(this.toNum(v).toFixed(Math.max(0, Math.min(n, 100))));
    });
    fn('pow', (a) => { if (a.length === 3) { let b = this.toInt(a[0]) % this.toInt(a[2]), e = this.toInt(a[1]), m = this.toInt(a[2]), r = 1n; while (e > 0n) { if (e & 1n) r = r * b % m; b = b * b % m; e >>= 1n; } return r; } return this.binop('**', a[0], a[1]); });
    fn('divmod', (a) => new PyTuple([this.binop('//', a[0], a[1]), this.binop('%', a[0], a[1])]));
    fn('hash', (a) => { const v = a[0]; if (typeof v === 'bigint') return v; const k = this.keyOf(v); let h = 0; for (let i = 0; i < k.length; i++) h = (Math.imul(31, h) + k.charCodeAt(i)) | 0; return BigInt(h); });
    fn('id', (a) => { const v = a[0]; if (v && typeof v === 'object' && v.id) return 140000000000000n + BigInt(parseInt(String(v.id).slice(1)) * 48); if (typeof v === 'bigint') return 9780000n + v * 32n; return 94000000000000n; });
    fn('repr', (a) => this.repr(a[0]));
    fn('ascii', (a) => this.repr(a[0]));
    fn('format', (a) => this.format(a[0], a.length > 1 ? a[1] : ''));
    fn('iter', (a) => { const v = a[0]; if (v instanceof PyIter) return v; if (v instanceof PyObj) { const m = v.cls.lookup('__iter__'); if (m) return this.callValue(this.bind(v, m), [], new Map()); } return new PyIter(this.toArray(v), this.typeName(v) + '_iterator'); });
    fn('next', (a) => {
      const it = a[0];
      if (it instanceof PyIter) { if (it.i < it.items.length) return it.items[it.i++]; if (a.length > 1) return a[1]; this.raise('StopIteration', null, '迭代器已经没有更多元素了。'); }
      if (it instanceof PyObj) { const m = it.cls.lookup('__next__'); if (m) return this.callValue(this.bind(it, m), [], new Map()); }
      this.raise('TypeError', "'" + this.typeName(it) + "' object is not an iterator");
    });
    fn('hex', (a) => { const n = this.toInt(a[0]); return (n < 0n ? '-0x' : '0x') + (n < 0n ? -n : n).toString(16); });
    fn('bin', (a) => { const n = this.toInt(a[0]); return (n < 0n ? '-0b' : '0b') + (n < 0n ? -n : n).toString(2); });
    fn('oct', (a) => { const n = this.toInt(a[0]); return (n < 0n ? '-0o' : '0o') + (n < 0n ? -n : n).toString(8); });
    fn('callable', (a) => a[0] instanceof PyFunc || a[0] instanceof PyBuiltin || a[0] instanceof PyBound || a[0] instanceof PyClass || (a[0] instanceof PyObj && !!a[0].cls.lookup('__call__')));
    fn('getattr', (a) => { try { return this.getattr(a[0], a[1]); } catch (e) { if (a.length > 2 && e instanceof PyExc && e.obj.cls.name === 'AttributeError') return a[2]; throw e; } });
    fn('setattr', (a) => { this.setattr(a[0], a[1], a[2]); return NONE; });
    fn('hasattr', (a) => { try { this.getattr(a[0], a[1]); return true; } catch (e) { if (e instanceof PyExc) return false; throw e; } });
    fn('delattr', (a) => { if (a[0] instanceof PyObj) a[0].attrs.delete(a[1]); return NONE; });
    fn('vars', (a) => { const d = new PyDict(); if (a[0] instanceof PyObj) for (const [k, v] of a[0].attrs) this.dictSet(d, k, v); return d; });
    fn('open', () => this.raise('OSError', '可视化器不支持文件操作', '可以把文件内容粘贴到“输入 (stdin)”框里，用 input() 逐行读取。'));
    fn('exit', () => { const o = new PyObj(B.get('SystemExit')); throw new PyExc(o); });
    fn('quit', () => { const o = new PyObj(B.get('SystemExit')); throw new PyExc(o); });
    fn('globals', () => { const d = new PyDict(); for (const [k, v] of this.globalEnv.vars) this.dictSet(d, k, v); return d; });
    fn('super', (a) => {
      if (a.length === 2) return new PySuper(a[0], a[1]);
      for (let i = this.frames.length - 1; i >= 0; i--) {
        const f = this.frames[i];
        if (f.fn && f.fn.cls) {
          const first = f.fn.def.params[0];
          return new PySuper(f.fn.cls, f.env.vars.get(first.name));
        }
      }
      this.raise('RuntimeError', 'super(): no arguments');
    });
    fn('staticmethod', (a) => new PyStatic(a[0]));
    fn('classmethod', (a) => new PyClassMethod(a[0]));
    const propCls = type('property', (a) => new PyProperty(a[0]));
    // property.setter support via attribute on PyProperty handled in builtinMethod
  };
  P.typeOf = function (v) {
    const B = this.builtins;
    if (v === null) return B.get('NoneType') || (() => { const c = new PyClass('NoneType', [], new Map()); c.builtin = true; B.set('NoneType', c); return c; })();
    if (v instanceof PyObj) return v.cls;
    const n = this.typeName(v);
    if (B.has(n) && B.get(n) instanceof PyClass) return B.get(n);
    const c = new PyClass(n, [], new Map()); c.builtin = true; B.set(n, c);
    return c;
  };
  P.isInstance = function (v, t) {
    if (t instanceof PyTuple) return t.items.some(x => this.isInstance(v, x));
    if (!(t instanceof PyClass)) this.raise('TypeError', 'isinstance() arg 2 must be a type or tuple of types');
    if (t.name === 'object' && t.builtin) return true;
    if (v instanceof PyObj) return v.cls.mro.includes(t);
    if (!t.builtin) return false;
    switch (t.name) {
      case 'int': return typeof v === 'bigint' || typeof v === 'boolean';
      case 'float': return typeof v === 'number';
      case 'str': return typeof v === 'string';
      case 'bool': return typeof v === 'boolean';
      case 'list': return v instanceof PyList;
      case 'tuple': return v instanceof PyTuple;
      case 'dict': return v instanceof PyDict;
      case 'set': return v instanceof PySet && !v.frozen;
      case 'frozenset': return v instanceof PySet && v.frozen;
      case 'deque': return v instanceof PyDeque;
      case 'defaultdict': return v instanceof PyDict && v.kind === 'defaultdict';
      case 'Counter': return v instanceof PyDict && v.kind === 'Counter';
      case 'range': return v instanceof PyRange;
      case 'NoneType': return v === null;
    }
    return this.typeName(v) === t.name;
  };
  P.dictUpdate = function (d, src) {
    if (src instanceof PyDict) { for (const [, en] of src.map) this.dictSet(d, en[0], en[1]); return; }
    for (const pair of this.toArray(src)) {
      const kv = this.toArray(pair);
      if (kv.length !== 2) this.raise('ValueError', 'dictionary update sequence element has length ' + kv.length + '; 2 is required');
      this.dictSet(d, kv[0], kv[1]);
    }
  };

  // ================= methods of builtin types =================
  P.builtinMethod = function (o, name) {
    const self = this;
    const mk = (f) => new PyBuiltin(name, (args, kw) => f(args, kw || new Map()));
    const kw = (k, n, d) => k.has(n) ? k.get(n) : d;
    if (o instanceof PyList || (o instanceof PyDeque)) {
      const it = o.items;
      const isDeque = o instanceof PyDeque;
      switch (name) {
        case 'append': return mk((a) => { if (a.length !== 1) this.raise('TypeError', 'append() takes exactly one argument (' + a.length + ' given)', '一次只能 append 一个元素；要添加多个元素请用 extend()。'); it.push(a[0]); if (isDeque && o.maxlen !== null && it.length > o.maxlen) it.shift(); return NONE; });
        case 'extend': return mk((a) => { it.push(...this.toArray(a[0])); if (isDeque && o.maxlen !== null) while (it.length > o.maxlen) it.shift(); return NONE; });
        case 'insert': return mk((a) => { let i = Number(this.toInt(a[0])); if (i < 0) i = Math.max(0, it.length + i); it.splice(Math.min(i, it.length), 0, a[1]); return NONE; });
        case 'pop': return mk((a) => {
          if (!it.length) this.raise('IndexError', 'pop from empty ' + (isDeque ? 'deque' : 'list'), '列表/队列已经是空的了。pop 之前先检查是否为空，例如 if stack: 或 while queue:。');
          if (!a.length) return it.pop();
          if (isDeque) this.raise('TypeError', 'deque.pop() takes no arguments', '要从左边弹出请用 popleft()。');
          const i = this.normIndex(a[0], it.length, 'pop'); return it.splice(i, 1)[0];
        });
        case 'remove': return mk((a) => { const i = it.findIndex(x => this.eq(x, a[0])); if (i < 0) this.raise('ValueError', (isDeque ? 'deque' : 'list') + '.remove(x): x not in ' + (isDeque ? 'deque' : 'list'), this.repr(a[0]) + ' 不在列表里。删除前可以先用 in 判断。'); it.splice(i, 1); return NONE; });
        case 'index': return mk((a) => { const start = a.length > 1 ? Number(this.toInt(a[1])) : 0; const i = it.findIndex((x, k) => k >= start && this.eq(x, a[0])); if (i < 0) this.raise('ValueError', this.repr(a[0]) + ' is not in list'); return BigInt(i); });
        case 'count': return mk((a) => BigInt(it.filter(x => this.eq(x, a[0])).length));
        case 'sort': return mk((a, k) => { if (a.length) this.raise('TypeError', 'sort() takes no positional arguments', '排序时指定规则要写成 sort(key=..., reverse=True)。'); const r = this.sortValues(it.slice(), kw(k, 'key', NONE), this.truthy(kw(k, 'reverse', false))); it.length = 0; it.push(...r); return NONE; });
        case 'reverse': return mk(() => { it.reverse(); return NONE; });
        case 'copy': return mk(() => isDeque ? Object.assign(new PyDeque(it.slice()), { maxlen: o.maxlen }) : new PyList(it.slice()));
        case 'clear': return mk(() => { it.length = 0; return NONE; });
      }
      if (isDeque) switch (name) {
        case 'appendleft': return mk((a) => { it.unshift(a[0]); if (o.maxlen !== null && it.length > o.maxlen) it.pop(); return NONE; });
        case 'popleft': return mk(() => { if (!it.length) this.raise('IndexError', 'pop from an empty deque', '队列已经是空的了。popleft 之前先检查队列是否为空，例如 while queue:。'); return it.shift(); });
        case 'extendleft': return mk((a) => { for (const x of this.toArray(a[0])) it.unshift(x); return NONE; });
        case 'rotate': return mk((a) => { const n = a.length ? Number(this.toInt(a[0])) : 1; if (!it.length) return NONE; const k = ((n % it.length) + it.length) % it.length; const moved = it.splice(it.length - k, k); it.unshift(...moved); return NONE; });
        case 'maxlen': return o.maxlen === null ? NONE : BigInt(o.maxlen);
        // queue.Queue API
        case 'put': case 'put_nowait': return mk((a) => { if (o.qkind === 'lifo') it.push(a[0]); else if (o.qkind === 'prio') this.heapPush(o, a[0]); else it.push(a[0]); return NONE; });
        case 'get': case 'get_nowait': return mk(() => { if (!it.length) this.raise('IndexError', 'get from empty queue（真实的 Queue.get 会一直阻塞等待）'); if (o.qkind === 'lifo') return it.pop(); if (o.qkind === 'prio') return this.heapPop(o); return it.shift(); });
        case 'empty': return mk(() => it.length === 0);
        case 'qsize': return mk(() => BigInt(it.length));
        case 'full': return mk(() => false);
      }
    }
    if (o instanceof PyTuple) {
      if (o.cls && o.cls.fields) { const i = o.cls.fields.indexOf(name); if (i >= 0) return o.items[i]; if (name === '_asdict') return mk(() => { const d = new PyDict(); o.cls.fields.forEach((f, k) => this.dictSet(d, f, o.items[k])); return d; }); if (name === '_replace') return mk((a, k) => new PyTuple(o.cls.fields.map((f, i2) => k.has(f) ? k.get(f) : o.items[i2]))); }
      if (name === 'count') return mk((a) => BigInt(o.items.filter(x => this.eq(x, a[0])).length));
      if (name === 'index') return mk((a) => { const i = o.items.findIndex(x => this.eq(x, a[0])); if (i < 0) this.raise('ValueError', 'tuple.index(x): x not in tuple'); return BigInt(i); });
    }
    if (o instanceof PyDict) {
      const d = o;
      switch (name) {
        case 'get': return mk((a) => { const en = d.map.get(this.keyOf(a[0])); return en ? en[1] : (a.length > 1 ? a[1] : NONE); });
        case 'keys': return mk(() => { const l = new PyList([...d.map.values()].map(en => en[0])); l.view = 'dict_keys'; return l; });
        case 'values': return mk(() => { const l = new PyList([...d.map.values()].map(en => en[1])); l.view = 'dict_values'; return l; });
        case 'items': return mk(() => { const l = new PyList([...d.map.values()].map(en => new PyTuple([en[0], en[1]]))); l.view = 'dict_items'; return l; });
        case 'pop': return mk((a) => { const k = this.keyOf(a[0]); const en = d.map.get(k); if (!en) { if (a.length > 1) return a[1]; this.raise('KeyError', this.repr(a[0])); } d.map.delete(k); return en[1]; });
        case 'popitem': return mk(() => { if (!d.map.size) this.raise('KeyError', 'popitem(): dictionary is empty'); const k = [...d.map.keys()].pop(); const en = d.map.get(k); d.map.delete(k); return new PyTuple([en[0], en[1]]); });
        case 'setdefault': return mk((a) => { const k = this.keyOf(a[0]); if (!d.map.has(k)) d.map.set(k, [a[0], a.length > 1 ? a[1] : NONE]); return d.map.get(k)[1]; });
        case 'update': return mk((a, k) => { if (a.length) { if (d.kind === 'Counter' && !(a[0] instanceof PyDict)) { for (const x of this.toArray(a[0])) this.dictSet(d, x, (d.map.has(this.keyOf(x)) ? d.map.get(this.keyOf(x))[1] : 0n) + 1n); } else this.dictUpdate(d, a[0]); } for (const [kk, v] of k) this.dictSet(d, kk, v); return NONE; });
        case 'copy': return mk(() => { const n = new PyDict(); n.kind = d.kind; n.defaultFactory = d.defaultFactory; for (const [k, en] of d.map) n.map.set(k, [en[0], en[1]]); return n; });
        case 'clear': return mk(() => { d.map.clear(); return NONE; });
        case 'most_common': return mk((a) => { let ents = [...d.map.values()]; ents = this.mergeSort(ents, (x, y) => Number(y[1] - x[1])); if (a.length && a[0] !== NONE) ents = ents.slice(0, Number(this.toInt(a[0]))); return new PyList(ents.map(en => new PyTuple([en[0], en[1]]))); });
        case 'elements': return mk(() => { const out = []; for (const en of d.map.values()) for (let i = 0n; i < en[1]; i++) out.push(en[0]); return new PyIter(out, 'itertools.chain'); });
        case 'subtract': return mk((a) => { const src = a[0] instanceof PyDict ? [...a[0].map.values()] : this.toArray(a[0]).map(x => [x, 1n]); for (const [k, c] of src) { const cur = d.map.get(this.keyOf(k)); this.dictSet(d, k, (cur ? cur[1] : 0n) - c); } return NONE; });
        case 'total': return mk(() => [...d.map.values()].reduce((s, en) => s + en[1], 0n));
        case 'move_to_end': return mk((a, k) => { const key = this.keyOf(a[0]); const en = d.map.get(key); if (!en) this.raise('KeyError', this.repr(a[0])); d.map.delete(key); if (this.truthy(kw(k, 'last', true))) d.map.set(key, en); else { const all = [...d.map]; d.map.clear(); d.map.set(key, en); for (const [kk, vv] of all) d.map.set(kk, vv); } return NONE; });
      }
    }
    if (o instanceof PySet) {
      const s = o;
      switch (name) {
        case 'add': return mk((a) => { if (s.frozen) this.raise('AttributeError', "'frozenset' object has no attribute 'add'"); this.setAdd(s, a[0]); return NONE; });
        case 'remove': return mk((a) => { const k = this.keyOf(a[0]); if (!s.map.has(k)) this.raise('KeyError', this.repr(a[0]), '集合里没有这个元素。如果不确定是否存在，可以用 discard()。'); s.map.delete(k); return NONE; });
        case 'discard': return mk((a) => { s.map.delete(this.keyOf(a[0])); return NONE; });
        case 'pop': return mk(() => { if (!s.map.size) this.raise('KeyError', "'pop from an empty set'"); const v = this.setOrder(s)[0]; s.map.delete(this.keyOf(v)); return v; });
        case 'clear': return mk(() => { s.map.clear(); return NONE; });
        case 'copy': return mk(() => { const n = new PySet(); for (const [k, v] of s.map) n.map.set(k, v); n.tsize = s.tsize; return n; });
        case 'union': return mk((a) => { let r = s; for (const x of a) r = this.binop('|', r, this.asSet(x)); return r === s ? this.binop('|', s, new PySet()) : r; });
        case 'intersection': return mk((a) => { let r = s; for (const x of a) r = this.binop('&', r, this.asSet(x)); return r; });
        case 'difference': return mk((a) => { let r = s; for (const x of a) r = this.binop('-', r, this.asSet(x)); return r; });
        case 'symmetric_difference': return mk((a) => this.binop('^', s, this.asSet(a[0])));
        case 'update': return mk((a) => { for (const x of a) for (const v of this.toArray(x)) this.setAdd(s, v); return NONE; });
        case 'intersection_update': return mk((a) => { const r = this.binop('&', s, this.asSet(a[0])); s.map = r.map; return NONE; });
        case 'difference_update': return mk((a) => { const r = this.binop('-', s, this.asSet(a[0])); s.map = r.map; return NONE; });
        case 'issubset': return mk((a) => { const t = this.asSet(a[0]); return [...s.map.keys()].every(k => t.map.has(k)); });
        case 'issuperset': return mk((a) => { const t = this.asSet(a[0]); return [...t.map.keys()].every(k => s.map.has(k)); });
        case 'isdisjoint': return mk((a) => { const t = this.asSet(a[0]); return ![...s.map.keys()].some(k => t.map.has(k)); });
      }
    }
    if (typeof o === 'string') return this.strMethod(o, name, mk, kw);
    if (typeof o === 'bigint' || typeof o === 'boolean') {
      if (name === 'bit_length') return mk(() => { const n = this.toInt(o); return BigInt((n < 0n ? -n : n).toString(2).replace(/^0$/, '').length); });
      if (name === 'is_integer') return mk(() => true);
      if (name === 'real') return o; if (name === 'imag') return 0n;
    }
    if (typeof o === 'number') {
      if (name === 'is_integer') return mk(() => Number.isInteger(o));
      if (name === 'real') return o;
    }
    if (o instanceof PyProperty) {
      if (name === 'setter') return mk((a) => { o.fset = a[0]; return o; });
      if (name === 'getter') return mk((a) => { o.fget = a[0]; return o; });
    }
    if (o instanceof PyIter && name === '__next__') return mk(() => { if (o.i < o.items.length) return o.items[o.i++]; this.raise('StopIteration'); });
    if (o instanceof PyFunc && name === 'cache_clear') return mk(() => NONE);
    if (o instanceof PyBuiltin && o.cache && name === 'cache_clear') return mk(() => { o.cache.clear(); return NONE; });
    if (o instanceof PyObj && o.cls.isEnum) { if (name === 'name') return o.attrs.get('name'); if (name === 'value') return o.attrs.get('value'); }
    return null;
  };
  P.asSet = function (x) { if (x instanceof PySet) return x; const s = new PySet(); for (const v of this.toArray(x)) this.setAdd(s, v); return s; };
  P.strMethod = function (s, name, mk, kw) {
    const B = (b) => b;
    switch (name) {
      case 'split': return mk((a, k) => {
        const sep = a.length ? a[0] : kw(k, 'sep', NONE);
        const max = a.length > 1 ? Number(this.toInt(a[1])) : Number(this.toInt(kw(k, 'maxsplit', -1n)));
        let parts;
        if (sep === NONE) { parts = s.trim().split(/\s+/).filter(x => x !== ''); if (max >= 0 && parts.length > max + 1) { let rest = s.trim(); const out = []; for (let i = 0; i < max; i++) { const m = /^(\S+)\s+/.exec(rest); out.push(m[1]); rest = rest.slice(m[0].length); } out.push(rest); parts = out; } }
        else { if (sep === '') this.raise('ValueError', 'empty separator'); parts = s.split(sep); if (max >= 0 && parts.length > max + 1) parts = parts.slice(0, max).concat([parts.slice(max).join(sep)]); }
        return new PyList(parts);
      });
      case 'rsplit': return mk((a) => { const sep = a.length ? a[0] : NONE; return new PyList(sep === NONE ? s.trim().split(/\s+/) : s.split(sep)); });
      case 'join': return mk((a) => {
        const items = this.toArray(a[0]);
        items.forEach((x, i) => { if (typeof x !== 'string') this.raise('TypeError', 'sequence item ' + i + ': expected str instance, ' + this.typeName(x) + ' found', 'join 只能拼接字符串。如果列表里是数字，可以写成 " ".join(map(str, 列表))。'); });
        return items.join(s);
      });
      case 'strip': return mk((a) => a.length && a[0] !== NONE ? trimChars(s, a[0], 3) : s.trim());
      case 'lstrip': return mk((a) => a.length && a[0] !== NONE ? trimChars(s, a[0], 1) : s.replace(/^\s+/, ''));
      case 'rstrip': return mk((a) => a.length && a[0] !== NONE ? trimChars(s, a[0], 2) : s.replace(/\s+$/, ''));
      case 'upper': return mk(() => s.toUpperCase());
      case 'lower': return mk(() => s.toLowerCase());
      case 'casefold': return mk(() => s.toLowerCase());
      case 'capitalize': return mk(() => s ? s[0].toUpperCase() + s.slice(1).toLowerCase() : s);
      case 'title': return mk(() => s.toLowerCase().replace(/(^|[^A-Za-z])([a-z])/g, (m, p, c) => p + c.toUpperCase()));
      case 'swapcase': return mk(() => [...s].map(c => c === c.toUpperCase() ? c.toLowerCase() : c.toUpperCase()).join(''));
      case 'replace': return mk((a) => { let n = a.length > 2 ? Number(this.toInt(a[2])) : -1; if (n < 0) return s.split(a[0]).join(a[1]); let r = s, out = ''; while (n-- > 0) { const i = r.indexOf(a[0]); if (i < 0) break; out += r.slice(0, i) + a[1]; r = r.slice(i + a[0].length); } return out + r; });
      case 'find': return mk((a) => BigInt(s.indexOf(a[0], a.length > 1 ? Number(this.toInt(a[1])) : 0)));
      case 'rfind': return mk((a) => BigInt(s.lastIndexOf(a[0])));
      case 'index': return mk((a) => { const i = s.indexOf(a[0], a.length > 1 ? Number(this.toInt(a[1])) : 0); if (i < 0) this.raise('ValueError', 'substring not found'); return BigInt(i); });
      case 'rindex': return mk((a) => { const i = s.lastIndexOf(a[0]); if (i < 0) this.raise('ValueError', 'substring not found'); return BigInt(i); });
      case 'count': return mk((a) => { if (a[0] === '') return BigInt(s.length + 1); let c = 0, i = 0; for (;;) { const j = s.indexOf(a[0], i); if (j < 0) break; c++; i = j + a[0].length; } return BigInt(c); });
      case 'startswith': return mk((a) => a[0] instanceof PyTuple ? a[0].items.some(p => s.startsWith(p)) : s.startsWith(a[0], a.length > 1 ? Number(this.toInt(a[1])) : 0));
      case 'endswith': return mk((a) => a[0] instanceof PyTuple ? a[0].items.some(p => s.endsWith(p)) : s.endsWith(a[0]));
      case 'isdigit': case 'isnumeric': case 'isdecimal': return mk(() => s.length > 0 && /^[0-9]+$/.test(s));
      case 'isalpha': return mk(() => s.length > 0 && /^\p{L}+$/u.test(s));
      case 'isalnum': return mk(() => s.length > 0 && /^[\p{L}0-9]+$/u.test(s));
      case 'isspace': return mk(() => s.length > 0 && /^\s+$/.test(s));
      case 'isupper': return mk(() => /[A-Z]/.test(s) && s === s.toUpperCase());
      case 'islower': return mk(() => /[a-z]/.test(s) && s === s.toLowerCase());
      case 'isidentifier': return mk(() => /^[A-Za-z_]\w*$/.test(s));
      case 'zfill': return mk((a) => { const w = Number(this.toInt(a[0])); const neg = /^[-+]/.test(s); return neg ? s[0] + s.slice(1).padStart(w - 1, '0') : s.padStart(w, '0'); });
      case 'center': return mk((a) => { const w = Number(this.toInt(a[0])), f = a.length > 1 ? a[1] : ' '; const pad = Math.max(0, w - s.length); const l = Math.floor(pad / 2) + (pad % 2 && w % 2 ? 1 : 0); return f.repeat(l) + s + f.repeat(pad - l); });
      case 'ljust': return mk((a) => s.padEnd(Number(this.toInt(a[0])), a.length > 1 ? a[1] : ' '));
      case 'rjust': return mk((a) => s.padStart(Number(this.toInt(a[0])), a.length > 1 ? a[1] : ' '));
      case 'splitlines': return mk(() => new PyList(s.split(/\r?\n/).filter((x, i, arr) => !(i === arr.length - 1 && x === ''))));
      case 'partition': return mk((a) => { const i = s.indexOf(a[0]); return i < 0 ? new PyTuple([s, '', '']) : new PyTuple([s.slice(0, i), a[0], s.slice(i + a[0].length)]); });
      case 'rpartition': return mk((a) => { const i = s.lastIndexOf(a[0]); return i < 0 ? new PyTuple(['', '', s]) : new PyTuple([s.slice(0, i), a[0], s.slice(i + a[0].length)]); });
      case 'format': return mk((a, k) => this.strFormat(s, a, k));
      case 'encode': return mk(() => s);
      case 'removeprefix': return mk((a) => s.startsWith(a[0]) ? s.slice(a[0].length) : s);
      case 'removesuffix': return mk((a) => a[0] && s.endsWith(a[0]) ? s.slice(0, -a[0].length) : s);
      case 'expandtabs': return mk(() => s.replace(/\t/g, '        '));
      case 'maketrans': return mk((a) => { const d = new PyDict(); for (let i = 0; i < a[0].length; i++) this.dictSet(d, BigInt(a[0].charCodeAt(i)), a[1][i]); return d; });
      case 'translate': return mk((a) => [...s].map(c => { const en = a[0].map.get('i' + c.charCodeAt(0)); return en ? (en[1] === NONE ? '' : this.str(en[1])) : c; }).join(''));
    }
    return null;
  };
  function trimChars(s, chars, mode) {
    let a = 0, b = s.length;
    if (mode & 1) while (a < b && chars.includes(s[a])) a++;
    if (mode & 2) while (b > a && chars.includes(s[b - 1])) b--;
    return s.slice(a, b);
  }
  P.strFormat = function (s, args, kwargs) {
    let auto = 0;
    return s.replace(/\{\{|\}\}|\{([^{}]*)\}/g, (m, body) => {
      if (m === '{{') return '{'; if (m === '}}') return '}';
      let [field, spec] = body.split(':');
      let conv = null;
      if (field.includes('!')) [field, conv] = field.split('!');
      let v;
      const mm = /^([^.\[]*)(.*)$/.exec(field);
      const head = mm[1];
      if (head === '') v = args[auto++];
      else if (/^\d+$/.test(head)) v = args[+head];
      else v = kwargs.get(head);
      let rest = mm[2];
      while (rest) {
        const a = /^\.(\w+)/.exec(rest);
        if (a) { v = this.getattr(v, a[1]); rest = rest.slice(a[0].length); continue; }
        const b = /^\[([^\]]+)\]/.exec(rest);
        if (b) { v = this.getitem(v, /^\d+$/.test(b[1]) ? BigInt(b[1]) : b[1]); rest = rest.slice(b[0].length); continue; }
        break;
      }
      if (v === undefined) this.raise('IndexError', 'Replacement index ' + (auto - 1) + ' out of range for positional args tuple');
      if (conv === 'r') v = this.repr(v); else if (conv === 's') v = this.str(v);
      return this.format(v, spec || '');
    });
  };

  // ================= heapq helpers =================
  P.heapPush = function (h, v) {
    const a = h.items;
    a.push(v);
    let i = a.length - 1;
    while (i > 0) { const p = (i - 1) >> 1; if (this.lt(a[i], a[p])) { [a[i], a[p]] = [a[p], a[i]]; i = p; } else break; }
  };
  P.heapSiftDown = function (a, i, n) {
    for (;;) {
      const l = 2 * i + 1, r = l + 1;
      let s = i;
      if (l < n && this.lt(a[l], a[s])) s = l;
      if (r < n && this.lt(a[r], a[s])) s = r;
      if (s === i) break;
      [a[i], a[s]] = [a[s], a[i]]; i = s;
    }
  };
  P.heapPop = function (h) {
    const a = h.items;
    if (!a.length) this.raise('IndexError', 'index out of range', '堆是空的，不能再 heappop。先检查堆是否为空，例如 while heap:。');
    const last = a.pop();
    if (!a.length) return last;
    const top = a[0]; a[0] = last;
    this.heapSiftDown(a, 0, a.length);
    return top;
  };

  // ================= modules =================
  P.getModule = function (name) {
    this.modules = this.modules || new Map();
    if (this.modules.has(name)) return this.modules.get(name);
    const attrs = new Map();
    const fn = (n, f) => attrs.set(n, new PyBuiltin(name + '.' + n, f));
    const B = this.builtins;
    const kw = (k, n, d) => k && k.has(n) ? k.get(n) : d;
    switch (name) {
      case 'math': {
        attrs.set('pi', Math.PI); attrs.set('e', Math.E); attrs.set('inf', Infinity); attrs.set('nan', NaN); attrs.set('tau', 2 * Math.PI);
        const f1 = (n, f) => fn(n, (a) => f(this.toNum(a[0]), a));
        f1('sqrt', (x) => { if (x < 0) this.raise('ValueError', 'math domain error', 'sqrt 的参数不能是负数。'); return Math.sqrt(x); });
        fn('floor', (a) => typeof a[0] === 'bigint' ? a[0] : BigInt(Math.floor(this.toNum(a[0]))));
        fn('ceil', (a) => typeof a[0] === 'bigint' ? a[0] : BigInt(Math.ceil(this.toNum(a[0]))));
        fn('trunc', (a) => BigInt(Math.trunc(this.toNum(a[0]))));
        f1('fabs', Math.abs); f1('exp', Math.exp); f1('sin', Math.sin); f1('cos', Math.cos); f1('tan', Math.tan); f1('atan', Math.atan); f1('asin', Math.asin); f1('acos', Math.acos);
        f1('log2', Math.log2); f1('log10', Math.log10); f1('degrees', x => x * 180 / Math.PI); f1('radians', x => x * Math.PI / 180);
        fn('log', (a) => { const x = this.toNum(a[0]); if (x <= 0) this.raise('ValueError', 'math domain error'); return a.length > 1 ? Math.log(x) / Math.log(this.toNum(a[1])) : Math.log(x); });
        fn('pow', (a) => Math.pow(this.toNum(a[0]), this.toNum(a[1])));
        fn('atan2', (a) => Math.atan2(this.toNum(a[0]), this.toNum(a[1])));
        fn('hypot', (a) => Math.hypot(...a.map(x => this.toNum(x))));
        fn('gcd', (a) => { let r = 0n; for (const x of a) { let p = this.toInt(x); p = p < 0n ? -p : p; let q = r; while (p) [q, p] = [p, q % p]; r = q; } return r; });
        fn('lcm', (a) => { let r = 1n; for (const x of a) { const p = this.toInt(x); let g = r, q = p; while (q) [g, q] = [q, g % q]; r = r * p / g; } return r < 0n ? -r : r; });
        fn('factorial', (a) => { const n = this.toInt(a[0]); if (n < 0n) this.raise('ValueError', 'factorial() not defined for negative values'); let r = 1n; for (let i = 2n; i <= n; i++) r *= i; return r; });
        fn('isqrt', (a) => { const n = this.toInt(a[0]); if (n < 0n) this.raise('ValueError', 'isqrt() argument must be nonnegative'); let x = BigInt(Math.floor(Math.sqrt(Number(n)))); while (x * x > n) x--; while ((x + 1n) * (x + 1n) <= n) x++; return x; });
        fn('comb', (a) => { const n = this.toInt(a[0]), k = this.toInt(a[1]); if (k > n) return 0n; let r = 1n; for (let i = 0n; i < k; i++) r = r * (n - i) / (i + 1n); return r; });
        fn('perm', (a) => { const n = this.toInt(a[0]), k = a.length > 1 ? this.toInt(a[1]) : n; let r = 1n; for (let i = 0n; i < k; i++) r *= (n - i); return r; });
        fn('isinf', (a) => !isFinite(this.toNum(a[0])) && !isNaN(this.toNum(a[0])));
        fn('isnan', (a) => isNaN(this.toNum(a[0])));
        fn('isclose', (a) => Math.abs(this.toNum(a[0]) - this.toNum(a[1])) <= 1e-9 * Math.max(Math.abs(this.toNum(a[0])), Math.abs(this.toNum(a[1]))));
        fn('prod', (a) => { let r = 1n; for (const x of this.toArray(a[0])) r = this.binop('*', r, x); return r; });
        fn('dist', (a) => Math.hypot(...this.toArray(a[0]).map((x, i) => this.toNum(x) - this.toNum(this.toArray(a[1])[i]))));
        break;
      }
      case 'random': {
        const rnd = () => this.rng() / 2147483648;
        fn('seed', (a) => { this.rng = DSV.makeRng(a.length ? Number(this.toInt(a[0])) : 42); return NONE; });
        fn('random', () => rnd());
        fn('randint', (a) => { const lo = this.toInt(a[0]), hi = this.toInt(a[1]); return lo + BigInt(Math.floor(rnd() * Number(hi - lo + 1n))); });
        fn('randrange', (a) => { const lo = a.length > 1 ? this.toInt(a[0]) : 0n, hi = this.toInt(a.length > 1 ? a[1] : a[0]); return lo + BigInt(Math.floor(rnd() * Number(hi - lo))); });
        fn('uniform', (a) => this.toNum(a[0]) + rnd() * (this.toNum(a[1]) - this.toNum(a[0])));
        fn('choice', (a) => { const arr = this.toArray(a[0]); if (!arr.length) this.raise('IndexError', 'Cannot choose from an empty sequence'); return arr[Math.floor(rnd() * arr.length)]; });
        fn('shuffle', (a) => { const it = a[0].items; for (let i = it.length - 1; i > 0; i--) { const j = Math.floor(rnd() * (i + 1)); [it[i], it[j]] = [it[j], it[i]]; } return NONE; });
        fn('sample', (a) => { const arr = this.toArray(a[0]); const k = Number(this.toInt(a[1])); const c = arr.slice(); for (let i = c.length - 1; i > 0; i--) { const j = Math.floor(rnd() * (i + 1)); [c[i], c[j]] = [c[j], c[i]]; } return new PyList(c.slice(0, k)); });
        fn('choices', (a, k) => { const arr = this.toArray(a[0]); const n = Number(this.toInt(kw(k, 'k', 1n))); const out = []; for (let i = 0; i < n; i++) out.push(arr[Math.floor(rnd() * arr.length)]); return new PyList(out); });
        break;
      }
      case 'collections': {
        const deque = new PyClass('deque', [], new Map()); deque.builtin = true;
        deque.native = (a, k) => { const d = new PyDeque(a.length ? this.toArray(a[0]) : []); const ml = a.length > 1 ? a[1] : kw(k, 'maxlen', NONE); d.maxlen = ml === NONE ? null : Number(this.toInt(ml)); if (d.maxlen !== null) while (d.items.length > d.maxlen) d.items.shift(); return d; };
        attrs.set('deque', deque); B.set('deque', deque);
        const dd = new PyClass('defaultdict', [B.get('dict')], new Map()); dd.builtin = true;
        dd.native = (a, k) => { const d = new PyDict(); d.kind = 'defaultdict'; d.defaultFactory = a.length ? a[0] : NONE; if (a.length > 1) this.dictUpdate(d, a[1]); return d; };
        attrs.set('defaultdict', dd); B.set('defaultdict', dd);
        const ct = new PyClass('Counter', [B.get('dict')], new Map()); ct.builtin = true;
        ct.native = (a, k) => { const d = this.newCounter(); if (a.length) { if (a[0] instanceof PyDict) this.dictUpdate(d, a[0]); else for (const x of this.toArray(a[0])) { const en = d.map.get(this.keyOf(x)); this.dictSet(d, x, (en ? en[1] : 0n) + 1n); } } for (const [kk, v] of k) this.dictSet(d, kk, v); return d; };
        attrs.set('Counter', ct); B.set('Counter', ct);
        const od = new PyClass('OrderedDict', [B.get('dict')], new Map()); od.builtin = true;
        od.native = (a) => { const d = new PyDict(); d.kind = 'OrderedDict'; if (a.length) this.dictUpdate(d, a[0]); return d; };
        attrs.set('OrderedDict', od);
        fn('namedtuple', (a) => {
          const nm = a[0];
          let fields = a[1];
          fields = typeof fields === 'string' ? fields.replace(/,/g, ' ').split(/\s+/).filter(Boolean) : this.toArray(fields);
          const c = new PyClass(nm, [B.get('tuple')], new Map());
          c.fields = fields;
          c.native = (args, k) => { const t = new PyTuple(fields.map((f, i) => i < args.length ? args[i] : (k.has(f) ? k.get(f) : this.raise('TypeError', nm + "() missing required argument: '" + f + "'")))); t.cls = c; return t; };
          return c;
        });
        break;
      }
      case 'heapq': {
        const chk = (h) => { if (!(h instanceof PyList)) this.raise('TypeError', 'heap argument must be a list'); return h; };
        fn('heappush', (a) => { this.heapPush(chk(a[0]), a[1]); return NONE; });
        fn('heappop', (a) => this.heapPop(chk(a[0])));
        fn('heapify', (a) => { const it = chk(a[0]).items; for (let i = (it.length >> 1) - 1; i >= 0; i--) this.heapSiftDown(it, i, it.length); return NONE; });
        fn('heappushpop', (a) => { const h = chk(a[0]); if (h.items.length && this.lt(h.items[0], a[1])) { const top = h.items[0]; h.items[0] = a[1]; this.heapSiftDown(h.items, 0, h.items.length); return top; } return a[1]; });
        fn('heapreplace', (a) => { const h = chk(a[0]); if (!h.items.length) this.raise('IndexError', 'index out of range'); const top = h.items[0]; h.items[0] = a[1]; this.heapSiftDown(h.items, 0, h.items.length); return top; });
        fn('nsmallest', (a, k) => new PyList(this.sortValues(this.toArray(a[1]), kw(k, 'key', NONE), false).slice(0, Number(this.toInt(a[0])))));
        fn('nlargest', (a, k) => new PyList(this.sortValues(this.toArray(a[1]), kw(k, 'key', NONE), true).slice(0, Number(this.toInt(a[0])))));
        break;
      }
      case 'sys': {
        attrs.set('maxsize', 9223372036854775807n);
        attrs.set('argv', new PyList(['main.py', ...(this.opts.args || [])]));
        fn('setrecursionlimit', (a) => { this.rec.note('sys.setrecursionlimit 在可视化器里不起作用（上限固定为 ' + this.depthLimit + ' 层）', 'info'); return NONE; });
        fn('getrecursionlimit', () => BigInt(this.depthLimit));
        fn('exit', () => { const o = new PyObj(B.get('SystemExit')); throw new PyExc(o); });
        const stdin = new PyModule('stdin', new Map());
        stdin.attrs.set('readline', new PyBuiltin('readline', () => { const l = this.stdin.line(); return l === null ? '' : l + '\n'; }));
        stdin.attrs.set('read', new PyBuiltin('read', () => { const s = this.stdin.text.slice(this.stdin.pos); this.stdin.pos = this.stdin.text.length; return s; }));
        stdin.attrs.set('readlines', new PyBuiltin('readlines', () => { const out = []; let l; while ((l = this.stdin.line()) !== null) out.push(l + '\n'); return new PyList(out); }));
        attrs.set('stdin', stdin);
        const stdout = new PyModule('stdout', new Map());
        stdout.attrs.set('write', new PyBuiltin('write', (a) => { this.rec.write(this.str(a[0])); return BigInt(this.str(a[0]).length); }));
        stdout.attrs.set('flush', new PyBuiltin('flush', () => NONE));
        attrs.set('stdout', stdout); attrs.set('stderr', stdout);
        break;
      }
      case 'copy': {
        fn('copy', (a) => this.shallowCopy(a[0]));
        fn('deepcopy', (a) => this.deepCopy(a[0], new Map()));
        break;
      }
      case 'functools': {
        const lru = (f) => {
          const cache = new Map();
          const w = new PyBuiltin(f.name, (args, k) => {
            const key = args.map(x => this.keyOf(x)).join('|');
            if (cache.has(key)) { this.rec.note('缓存命中：' + f.name + '(' + args.map(x => this.shortRepr(x)).join(', ') + ') 直接返回之前算好的结果', 'info'); return cache.get(key); }
            const r = this.callValue(f, args, k);
            cache.set(key, r);
            return r;
          });
          w.wrapped = f; w.cache = cache;
          return w;
        };
        fn('lru_cache', (a, k) => { if (a.length && (a[0] instanceof PyFunc)) return lru(a[0]); return new PyBuiltin('lru_cache', (b) => lru(b[0])); });
        fn('cache', (a) => lru(a[0]));
        fn('reduce', (a) => { const arr = this.toArray(a[1]); let acc = a.length > 2 ? a[2] : arr.shift(); if (acc === undefined) this.raise('TypeError', 'reduce() of empty iterable with no initial value'); for (const v of arr) acc = this.callValue(a[0], [acc, v], new Map()); return acc; });
        fn('cmp_to_key', (a) => { const cmpf = a[0]; const K = new PyClass('K', [], new Map()); K.attrs.set('__init__', new PyBuiltin('K.__init__', (b) => { b[0].attrs.set('obj', b[1]); return NONE; })); K.attrs.set('__lt__', new PyBuiltin('K.__lt__', (b) => this.toNum(this.callValue(cmpf, [b[0].attrs.get('obj'), b[1].attrs.get('obj')], new Map())) < 0)); return K; });
        fn('total_ordering', (a) => a[0]);
        fn('wraps', () => new PyBuiltin('wraps', (b) => b[0]));
        fn('partial', (a, k) => { const f = a[0], pre = a.slice(1); return new PyBuiltin('partial', (b, k2) => this.callValue(f, pre.concat(b), new Map([...k, ...k2]))); });
        break;
      }
      case 'itertools': {
        const tup = (arr) => new PyTuple(arr);
        fn('permutations', (a) => { const arr = this.toArray(a[0]); const r = a.length > 1 && a[1] !== NONE ? Number(this.toInt(a[1])) : arr.length; const out = []; const used = new Array(arr.length).fill(false); const cur = []; const rec = () => { if (cur.length === r) { out.push(tup(cur.slice())); return; } for (let i = 0; i < arr.length; i++) { if (used[i]) continue; used[i] = true; cur.push(arr[i]); rec(); cur.pop(); used[i] = false; } }; rec(); return new PyIter(out, 'itertools.permutations'); });
        fn('combinations', (a) => { const arr = this.toArray(a[0]); const r = Number(this.toInt(a[1])); const out = []; const cur = []; const rec = (s) => { if (cur.length === r) { out.push(tup(cur.slice())); return; } for (let i = s; i < arr.length; i++) { cur.push(arr[i]); rec(i + 1); cur.pop(); } }; rec(0); return new PyIter(out, 'itertools.combinations'); });
        fn('combinations_with_replacement', (a) => { const arr = this.toArray(a[0]); const r = Number(this.toInt(a[1])); const out = []; const cur = []; const rec = (s) => { if (cur.length === r) { out.push(tup(cur.slice())); return; } for (let i = s; i < arr.length; i++) { cur.push(arr[i]); rec(i); cur.pop(); } }; rec(0); return new PyIter(out, 'itertools.combinations_with_replacement'); });
        fn('product', (a, k) => { let pools = a.map(x => this.toArray(x)); const rep = Number(this.toInt(kw(k, 'repeat', 1n))); let all = []; for (let i = 0; i < rep; i++) all = all.concat(pools); let res = [[]]; for (const p of all) { const n = []; for (const r of res) for (const x of p) n.push(r.concat([x])); res = n; } return new PyIter(res.map(tup), 'itertools.product'); });
        fn('accumulate', (a, k) => { const arr = this.toArray(a[0]); const f = a.length > 1 ? a[1] : kw(k, 'func', NONE); const out = []; let acc; arr.forEach((v, i) => { acc = i === 0 ? (k && k.has('initial') ? this.binop('+', k.get('initial'), v) : v) : (f !== NONE ? this.callValue(f, [acc, v], new Map()) : this.binop('+', acc, v)); out.push(acc); }); if (k && k.has('initial')) out.unshift(k.get('initial')); return new PyIter(out, 'itertools.accumulate'); });
        fn('chain', (a) => new PyIter([].concat(...a.map(x => this.toArray(x))), 'itertools.chain'));
        fn('zip_longest', (a, k) => { const arrs = a.map(x => this.toArray(x)); const n = Math.max(...arrs.map(x => x.length)); const fv = kw(k, 'fillvalue', NONE); const out = []; for (let i = 0; i < n; i++) out.push(tup(arrs.map(x => i < x.length ? x[i] : fv))); return new PyIter(out, 'itertools.zip_longest'); });
        fn('islice', (a) => { const arr = this.toArray(a[0]); const [s, e] = a.length > 2 ? [Number(this.toInt(a[1])), a[2] === NONE ? arr.length : Number(this.toInt(a[2]))] : [0, Number(this.toInt(a[1]))]; return new PyIter(arr.slice(s, e), 'itertools.islice'); });
        fn('groupby', (a, k) => { const arr = this.toArray(a[0]); const kf = a.length > 1 ? a[1] : kw(k, 'key', NONE); const out = []; let cur = null, curK; for (const v of arr) { const kv = kf !== NONE ? this.callValue(kf, [v], new Map()) : v; if (cur && this.eq(kv, curK)) cur.push(v); else { cur = [v]; curK = kv; out.push([kv, cur]); } } return new PyIter(out.map(([kv, g]) => tup([kv, new PyIter(g, 'itertools._grouper')])), 'itertools.groupby'); });
        fn('repeat', (a) => new PyIter(new Array(a.length > 1 ? Number(this.toInt(a[1])) : 1000).fill(a[0]), 'itertools.repeat'));
        fn('count', (a) => { const st = a.length ? this.toInt(a[0]) : 0n; const out = []; for (let i = 0n; i < 10000n; i++) out.push(st + i); return new PyIter(out, 'itertools.count'); });
        break;
      }
      case 'bisect': {
        const bl = (arr, x, lo, hi, key) => { while (lo < hi) { const mid = (lo + hi) >> 1; const v = key ? this.callValue(key, [arr[mid]], new Map()) : arr[mid]; if (this.lt(v, x)) lo = mid + 1; else hi = mid; } return lo; };
        const br = (arr, x, lo, hi, key) => { while (lo < hi) { const mid = (lo + hi) >> 1; const v = key ? this.callValue(key, [arr[mid]], new Map()) : arr[mid]; if (this.lt(x, v)) hi = mid; else lo = mid + 1; } return lo; };
        const args = (a, k) => [a[0].items, a[1], a.length > 2 ? Number(this.toInt(a[2])) : Number(this.toInt(kw(k, 'lo', 0n))), a.length > 3 ? Number(this.toInt(a[3])) : (k && k.has('hi') ? Number(this.toInt(k.get('hi'))) : a[0].items.length), kw(k, 'key', NONE) === NONE ? null : k.get('key')];
        fn('bisect_left', (a, k) => BigInt(bl(...args(a, k))));
        fn('bisect_right', (a, k) => BigInt(br(...args(a, k))));
        fn('bisect', (a, k) => BigInt(br(...args(a, k))));
        fn('insort_left', (a, k) => { const ar = args(a, k); a[0].items.splice(bl(...ar), 0, a[1]); return NONE; });
        fn('insort', (a, k) => { const ar = args(a, k); a[0].items.splice(br(...ar), 0, a[1]); return NONE; });
        fn('insort_right', (a, k) => { const ar = args(a, k); a[0].items.splice(br(...ar), 0, a[1]); return NONE; });
        break;
      }
      case 'dataclasses': {
        const fieldMarker = (k) => { const o = { dcField: true, def: kw(k, 'default', undefined), factory: kw(k, 'default_factory', undefined) }; return o; };
        fn('field', (a, k) => fieldMarker(k));
        fn('dataclass', (a, k) => {
          const deco = (cls) => this.makeDataclass(cls, k || new Map());
          if (a.length && a[0] instanceof PyClass) return deco(a[0]);
          return new PyBuiltin('dataclass', (b) => deco(b[0]));
        });
        fn('asdict', (a) => { const d = new PyDict(); for (const f of a[0].cls.dataclassFields) this.dictSet(d, f.name, a[0].attrs.get(f.name)); return d; });
        break;
      }
      case 'typing': case 'typing_extensions': case 'collections.abc': {
        for (const n of ['List', 'Dict', 'Set', 'Tuple', 'Optional', 'Union', 'Any', 'Callable', 'Iterable', 'Iterator', 'Generator', 'Deque', 'DefaultDict', 'Sequence', 'Mapping', 'TypeVar', 'Generic', 'FrozenSet', 'Type', 'NamedTuple', 'Protocol', 'Hashable']) {
          const b = new PyBuiltin(n, (a) => a.length ? a[0] : NONE); b.typing = true; attrs.set(n, b);
        }
        const gen = new PyClass('Generic', [], new Map()); gen.builtin = true; attrs.set('Generic', gen);
        attrs.set('TypeVar', new PyBuiltin('TypeVar', (a) => { const b = new PyBuiltin(a[0], () => NONE); b.typing = true; return b; }));
        attrs.set('Protocol', gen);
        break;
      }
      case 'abc': {
        const abc = new PyClass('ABC', [], new Map()); abc.builtin = true; attrs.set('ABC', abc);
        fn('abstractmethod', (a) => { a[0].isAbstract = true; return a[0]; });
        break;
      }
      case 'enum': {
        const en = new PyClass('Enum', [], new Map()); en.builtin = true; en.isEnumBase = true; attrs.set('Enum', en); attrs.set('IntEnum', en);
        let autoN = 0n; fn('auto', () => ++autoN);
        break;
      }
      case 'string': {
        attrs.set('ascii_lowercase', 'abcdefghijklmnopqrstuvwxyz'); attrs.set('ascii_uppercase', 'ABCDEFGHIJKLMNOPQRSTUVWXYZ');
        attrs.set('ascii_letters', 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'); attrs.set('digits', '0123456789');
        attrs.set('punctuation', '!"#$%&\'()*+,-./:;<=>?@[\\]^_`{|}~'); attrs.set('whitespace', ' \t\n\r\x0b\x0c');
        break;
      }
      case 'time': { fn('time', () => 1700000000 + this.rec.steps.length / 1000); fn('perf_counter', () => this.rec.steps.length / 1000); fn('sleep', () => NONE); break; }
      case 'queue': {
        const mkq = (nm, kind) => { const c = new PyClass(nm, [], new Map()); c.builtin = true; c.native = () => { if (kind === 'prio') { const l = new PyDeque([]); l.qkind = 'prio'; return l; } const d = new PyDeque([]); d.qkind = kind; return d; }; attrs.set(nm, c); };
        mkq('Queue', 'fifo'); mkq('LifoQueue', 'lifo'); mkq('PriorityQueue', 'prio'); mkq('SimpleQueue', 'fifo');
        break;
      }
      case 'operator': {
        fn('itemgetter', (a) => new PyBuiltin('itemgetter', (b) => a.length === 1 ? this.getitem(b[0], a[0]) : new PyTuple(a.map(k => this.getitem(b[0], k)))));
        fn('attrgetter', (a) => new PyBuiltin('attrgetter', (b) => this.getattr(b[0], a[0])));
        fn('add', (a) => this.binop('+', a[0], a[1])); fn('mul', (a) => this.binop('*', a[0], a[1])); fn('sub', (a) => this.binop('-', a[0], a[1]));
        break;
      }
      case '__future__': attrs.set('annotations', true); break;
      case 'os': case 'array': case 'json': case 're':
        if (name === 're') {
          fn('findall', (a) => new PyList([...this.str(a[1]).matchAll(new RegExp(a[0], 'g'))].map(m => m.length > 2 ? new PyTuple(m.slice(1)) : (m[1] !== undefined ? m[1] : m[0]))));
          fn('sub', (a) => this.str(a[2]).replace(new RegExp(a[0], 'g'), this.str(a[1]).replace(/\\(\d)/g, '$$$1')));
          fn('split', (a) => new PyList(this.str(a[1]).split(new RegExp(a[0]))));
          fn('match', (a) => { const m = new RegExp('^(?:' + a[0] + ')').exec(this.str(a[1])); return m ? m[0] : NONE; });
          fn('fullmatch', (a) => new RegExp('^(?:' + a[0] + ')$').test(this.str(a[1])) ? a[1] : NONE);
          fn('search', (a) => { const m = new RegExp(a[0]).exec(this.str(a[1])); return m ? m[0] : NONE; });
          break;
        }
        if (name === 'json') { fn('dumps', (a) => this.repr(a[0]).replace(/'/g, '"').replace(/True/g, 'true').replace(/False/g, 'false').replace(/None/g, 'null')); break; }
        break;
      default:
        this.raise('ModuleNotFoundError', "No module named '" + name + "'", '可视化器只内置了常用的标准库模块（math、random、collections、heapq、sys、copy、functools、itertools、bisect、dataclasses、typing、string、queue、abc、enum、operator），不支持第三方库。');
    }
    const m = new PyModule(name, attrs);
    this.modules.set(name, m);
    return m;
  };
  P.makeDataclass = function (cls, k) {
    const fields = [];
    for (const name of cls.annotations || []) {
      if (fields.some(f => f.name === name)) continue;
      const dv = cls.attrs.get(name);
      const f = { name };
      if (dv && dv.dcField) { if (dv.def !== undefined) f.def = dv.def; if (dv.factory !== undefined) f.factory = dv.factory; cls.attrs.delete(name); }
      else if (dv !== undefined) f.def = dv;
      fields.push(f);
    }
    for (const b of cls.bases) if (b.dataclassFields) fields.unshift(...b.dataclassFields.filter(bf => !fields.some(f => f.name === bf.name)));
    cls.dataclassFields = fields;
    if (!cls.attrs.has('__init__')) {
      cls.attrs.set('__init__', new PyBuiltin(cls.name + '.__init__', (a, kw) => {
        const self = a[0];
        fields.forEach((f, i) => {
          let v;
          if (i + 1 < a.length) v = a[i + 1];
          else if (kw.has(f.name)) v = kw.get(f.name);
          else if (f.factory !== undefined) v = this.callValue(f.factory, [], new Map());
          else if (f.def !== undefined) v = f.def;
          else this.raise('TypeError', cls.name + ".__init__() missing required argument: '" + f.name + "'");
          self.attrs.set(f.name, v);
        });
        const post = cls.lookup('__post_init__');
        if (post) this.callValue(this.bind(self, post), [], new Map());
        return NONE;
      }));
    }
    if (!cls.attrs.has('__eq__')) cls.attrs.set('__eq__', new PyBuiltin('__eq__', (a) => a[1] instanceof PyObj && a[1].cls === a[0].cls && fields.every(f => this.eq(a[0].attrs.get(f.name), a[1].attrs.get(f.name)))));
    if (k.has('order') && this.truthy(k.get('order'))) {
      const key = (o) => new PyTuple(fields.map(f => o.attrs.get(f.name)));
      cls.attrs.set('__lt__', new PyBuiltin('__lt__', (a) => this.lt(key(a[0]), key(a[1]))));
      cls.attrs.set('__gt__', new PyBuiltin('__gt__', (a) => this.lt(key(a[1]), key(a[0]))));
      cls.attrs.set('__le__', new PyBuiltin('__le__', (a) => !this.lt(key(a[1]), key(a[0]))));
      cls.attrs.set('__ge__', new PyBuiltin('__ge__', (a) => !this.lt(key(a[0]), key(a[1]))));
    }
    if (k.has('frozen') && this.truthy(k.get('frozen'))) { cls.dataclassFrozen = true; cls.attrs.set('__hash__', new PyBuiltin('__hash__', (a) => this.keyOf(new PyTuple(fields.map(f => a[0].attrs.get(f.name)))))); }
    return cls;
  };
  P.shallowCopy = function (v) {
    if (v instanceof PyList) return new PyList(v.items.slice());
    if (v instanceof PyDeque) return new PyDeque(v.items.slice());
    if (v instanceof PyDict) { const d = new PyDict(); d.kind = v.kind; d.defaultFactory = v.defaultFactory; for (const [k, en] of v.map) d.map.set(k, [en[0], en[1]]); return d; }
    if (v instanceof PySet) { const s = new PySet(); for (const [k, x] of v.map) s.map.set(k, x); return s; }
    if (v instanceof PyObj) { const o = new PyObj(v.cls); for (const [k, x] of v.attrs) o.attrs.set(k, x); return o; }
    return v;
  };
  P.deepCopy = function (v, memo) {
    if (v === null || typeof v !== 'object') return v;
    if (memo.has(v)) return memo.get(v);
    if (v instanceof PyList) { const n = new PyList([]); memo.set(v, n); n.items = v.items.map(x => this.deepCopy(x, memo)); return n; }
    if (v instanceof PyDeque) { const n = new PyDeque([]); memo.set(v, n); n.items = v.items.map(x => this.deepCopy(x, memo)); return n; }
    if (v instanceof PyTuple) { const n = new PyTuple(v.items.map(x => this.deepCopy(x, memo))); n.cls = v.cls; memo.set(v, n); return n; }
    if (v instanceof PyDict) { const d = new PyDict(); d.kind = v.kind; d.defaultFactory = v.defaultFactory; memo.set(v, d); for (const [k, en] of v.map) d.map.set(k, [this.deepCopy(en[0], memo), this.deepCopy(en[1], memo)]); return d; }
    if (v instanceof PySet) { const s = new PySet(); memo.set(v, s); for (const [k, x] of v.map) s.map.set(k, this.deepCopy(x, memo)); return s; }
    if (v instanceof PyObj) { const o = new PyObj(v.cls); memo.set(v, o); for (const [k, x] of v.attrs) o.attrs.set(k, this.deepCopy(x, memo)); return o; }
    return v;
  };

  // enum + abstract support: hook class creation
  const _execClass = P.execClass;
  P.execClass = function (s) {
    const r = _execClass.call(this, s);
    const cls = this.lookup(s.name);
    if (cls instanceof PyClass) {
      if (cls.mro.some(c => c.isEnumBase)) {
        cls.isEnum = true;
        cls.members = [];
        for (const [k, v] of [...cls.attrs]) {
          if (k.startsWith('_') || v instanceof PyFunc || v instanceof PyStatic || v instanceof PyClassMethod || v instanceof PyProperty) continue;
          const o = new PyObj(cls); o.attrs.set('name', k); o.attrs.set('value', v); o.isEnumMember = true;
          cls.attrs.set(k, o); cls.members.push(o);
        }
        if (!cls.lookup('__repr__')) cls.attrs.set('__repr__', new PyBuiltin('__repr__', (a) => '<' + cls.name + '.' + a[0].attrs.get('name') + ': ' + this.repr(a[0].attrs.get('value')) + '>'));
        if (!cls.lookup('__str__')) cls.attrs.set('__str__', new PyBuiltin('__str__', (a) => cls.name + '.' + a[0].attrs.get('name')));
        cls.attrs.set('__iter__', null); cls.attrs.delete('__iter__');
      }
      const abstract = [];
      for (const c of cls.mro) for (const [k, v] of c.attrs) if (v instanceof PyFunc && v.isAbstract && cls.lookup(k) === v) abstract.push(k);
      if (abstract.length) cls.isAbstract = true;
    }
    return r;
  };
  const _toArray = P.toArray;
  P.toArray = function (v) { if (v instanceof PyClass && v.isEnum) return v.members.slice(); return _toArray.call(this, v); };
  const _repr = P.repr;
  P.repr = function (v, seen) { if (v instanceof PyList && v.view) return v.view + '(' + _repr.call(this, new PyList(v.items), seen) + ')'; return _repr.call(this, v, seen); };

  // ================= snapshot =================
  P.snapshot = function () {
    const ver = R.ver();
    const reuse = this._lastHeap && this._lastVer === ver;
    const snap = this.snapshotInner(reuse ? this._lastHeap : null);
    if (!reuse) { this._lastHeap = snap.heap; this._lastVer = R.ver(); }
    return snap;
  };
  P.snapshotInner = function (reuseHeap) {
    const stepNo = this.rec.steps.length;
    const heapMap = new Map();
    const order = [];
    const desc = (v) => {
      if (v === null || v === undefined) return { k: 'null', text: 'None' };
      switch (typeof v) {
        case 'boolean': return V2('prim', v ? 'True' : 'False', 'bool');
        case 'bigint': { const s = v.toString(); return V2('prim', s.length > 40 ? s.slice(0, 18) + '…' + s.slice(-18) : s, 'int'); }
        case 'number': return V2('prim', floatRepr(v), 'float');
        case 'string': { const r = strRepr(v.length > 300 ? v.slice(0, 300) + '…' : v); return { k: 'str', text: r }; }
      }
      if (envMode && (v instanceof PyFunc || (v instanceof PyBuiltin && !v.wrapped))) { if (!heapMap.has(v)) { heapMap.set(v, null); order.push(v); } return { k: 'ref', id: v.id }; }
      if (v instanceof PyFunc) return { k: 'func', text: (v.def.isLambda ? 'λ ' : 'function ') + v.name + '(' + v.def.params.map(p => (p.kind === 'varargs' ? '*' : p.kind === 'kwargs' ? '**' : '') + p.name).join(', ') + ')' };
      if (v instanceof PyClass) return { k: 'func', text: 'class ' + v.name };
      if (v instanceof PyBuiltin) return { k: 'func', text: v.wrapped ? 'function ' + v.wrapped.name + ' (带缓存)' : 'built-in ' + v.name };
      if (v instanceof PyBound) return { k: 'func', text: 'method ' + (v.fn.name || '') };
      if (v instanceof PyModule) return { k: 'func', text: 'module ' + v.name };
      if (v instanceof PyRange) return V2('prim', this.repr(v), 'range');
      if (v instanceof PyStatic || v instanceof PyClassMethod) return { k: 'func', text: 'function ' + v.fn.name };
      if (v instanceof PyProperty) return { k: 'func', text: 'property' };
      if (v instanceof PySuper) return { k: 'func', text: 'super' };
      if (v.notImpl) return V2('prim', 'NotImplemented');
      if (v.id) { if (!heapMap.has(v)) { heapMap.set(v, null); order.push(v); } return { k: 'ref', id: v.id }; }
      return V2('prim', String(v));
    };
    const V2 = (k, text, type) => ({ k, text, type });
    const envMode = this.envMode;
    const descFrame = (f) => {
      const env = f.isGlobal ? this.globalEnv : f.env;
      const vars = [];
      for (const [k, v] of env.vars) {
        if (f.isGlobal && (this.hidden.has(k) || k.startsWith('__'))) continue;
        vars.push({ name: k, val: desc(v), type: this.typeName(v) });
      }
      const fr = { id: f.id, name: f.name, vars, line: f.line };
      if (f.returning) fr.ret = desc(f.retVal);
      if (envMode) {
        if (f.isGlobal) { fr.label = 'Global'; fr.seq = 0; }
        else { fr.label = f.label; fr.parent = f.parent; fr.seq = f.seq; if (f.fn && f.fn.def.isLambda) fr.lambdaLine = f.fn.def.line; }
        if (f.exited) fr.exited = true;
      }
      return fr;
    };
    const frames = this.frames.map(descFrame);
    const extraFrames = envMode ? this.exitedFrames.map(descFrame) : null;
    const tail = { lang: 'python', showAddr: false };
    if (envMode) { tail.envMode = true; tail.extraFrames = extraFrames; }
    if (reuseHeap) return Object.assign({ frames, globals: null, heap: reuseHeap }, tail);
    const heap = [];
    for (let i = 0; i < order.length && heap.length < 600; i++) {
      const o = order[i];
      let ent;
      const flags = {};
      if (o instanceof PyObj && !o.isEnumMember && !this.isExcClass(o.cls) && o._dcVer === o.attrs.ver && o._dcVal) {
        for (const k of o._dcKids) if (!heapMap.has(k)) { heapMap.set(k, null); order.push(k); }
        heap.push({ id: o.id, label: o.cls.name, val: o._dcVal, flags, kind: 'py', born: o.born });
        continue;
      }
      if (o instanceof PyList) ent = { label: o.view || 'list', val: { k: 'list', kind: 'list', items: o.items.slice(0, 150).map(desc), total: o.items.length } };
      else if (o instanceof PyTuple) {
        if (o.cls) ent = { label: o.cls.name, val: { k: 'struct', name: o.cls.name, fields: o.cls.fields.map((f, j) => ({ name: f, val: desc(o.items[j]) })) } };
        else ent = { label: 'tuple', val: { k: 'list', kind: 'tuple', items: o.items.slice(0, 150).map(desc), total: o.items.length } };
      }
      else if (o instanceof PyDeque) ent = { label: o.qkind ? 'Queue' : 'deque', val: { k: 'list', kind: o.qkind === 'lifo' ? 'stack' : (o.qkind === 'prio' ? 'heap' : 'deque'), items: o.items.slice(0, 150).map(desc), total: o.items.length } };
      else if (o instanceof PySet) ent = { label: o.frozen ? 'frozenset' : 'set', val: { k: 'list', kind: 'set', items: this.setOrder(o).slice(0, 150).map(desc), total: o.map.size } };
      else if (o instanceof PyDict) ent = { label: o.kind || 'dict', val: { k: 'map', entries: [...o.map.values()].slice(0, 150).map(en => ({ key: desc(en[0]), val: desc(en[1]) })), total: o.map.size } };
      else if (o instanceof PyObj) {
        if (o.isEnumMember) ent = { label: o.cls.name, val: { k: 'struct', name: o.cls.name + '.' + o.attrs.get('name'), fields: [{ name: 'value', val: desc(o.attrs.get('value')) }] } };
        else {
          ent = { label: o.cls.name, val: { k: 'struct', name: o.cls.name, fields: [...o.attrs].map(([k, v]) => ({ name: k, val: desc(v) })) } };
          o._dcVer = o.attrs.ver; o._dcVal = ent.val; o._dcKids = [...o.attrs.values()].filter(v => v && typeof v === 'object' && v.id && !((!envMode && (v instanceof PyFunc || v instanceof PyBuiltin)) || v instanceof PyClass || v instanceof PyBound || v instanceof PyModule || v instanceof PyRange || v instanceof PyStatic || v instanceof PyClassMethod || v instanceof PyProperty || v instanceof PySuper));
        }
        if (this.isExcClass(o.cls)) flags.exc = true;
      }
      else if (o instanceof PyFunc) {
        const d = o.def;
        const ps = d.params.map(p => (p.kind === 'varargs' ? '*' : p.kind === 'kwargs' ? '**' : '') + p.name).join(', ');
        ent = { label: '函数', val: { k: 'fnobj', name: d.isLambda ? 'λ' : o.name, params: ps, line: d.isLambda ? d.line : null, parent: o.parentLabel || 'Global', cls: o.cls ? o.cls.name : null } };
      }
      else if (o instanceof PyBuiltin) ent = { label: '内置函数', val: { k: 'fnobj', name: o.name, params: '...', builtin: true } };
      else if (o instanceof PyIter) ent = { label: o.label, val: { k: 'list', kind: 'iter', items: o.items.slice(o.i, o.i + 100).map(desc), total: o.items.length - o.i } };
      else continue;
      ent.id = o.id; ent.flags = flags; ent.kind = 'py'; ent.born = o.born;
      heap.push(ent);
    }
    return Object.assign({ frames, globals: null, heap }, tail);
  };

  DSV.langs.python = {
    name: 'Python',
    run(code, opts) {
      opts = opts || {};
      let mod;
      try { mod = DSV.pyParse(code); }
      catch (e) { return DSV.finishRun(new DSV.Recorder(opts), e); }
      R.setCurStep(0);
      const it = new DSV.PyInterp(mod, opts);
      return it.run();
    }
  };
})(typeof window !== 'undefined' ? window : globalThis);
