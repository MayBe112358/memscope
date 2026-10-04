// ===== C / C++ / Java runtime library =====
(function (G) {
  const DSV = G.DSV;
  const { RunError, ExitSignal } = DSV;
  const T = DSV.CT;
  const { Block, Ptr, NULLP, MObj, Lambda, FnRef, ThrowSignal, StreamObj, MemLV, ElemLV, MapLV, StrCharLV, SbCharLV, TmpLV, isInt, isFlt, isArith } = DSV.clikeRT;
  const P = DSV.ClikeInterp.prototype;

  const C_FUNCS = new Set(('printf puts putchar fputs fprintf sprintf snprintf scanf getchar fgets gets get_int get_float get_double get_long get_long_long get_char get_string malloc calloc realloc free ' +
    'strlen strcpy strncpy strcat strncat strcmp strncmp strcasecmp strchr strrchr strstr strdup toupper tolower isalpha isdigit isalnum isspace isupper islower ispunct isprint isxdigit ' +
    'atoi atol atoll atof strtol strtoul strtod abs labs llabs fabs sqrt pow floor ceil round fmax fmin fmod exp log log2 log10 sin cos tan asin acos atan atan2 hypot trunc cbrt rand srand time exit abort assert ' +
    'memset memcpy memmove memcmp qsort fflush fopen fclose perror sleep usleep clock').split(' '));
  const CPP_FUNCS = new Set(('max min swap sort stable_sort reverse to_string stoi stol stoll stod stof getline make_pair find count fill accumulate min_element max_element lower_bound upper_bound binary_search iota ' +
    'gcd __gcd lcm setw setprecision next_permutation prev_permutation unique distance advance make_heap push_heap pop_heap all_of any_of none_of count_if find_if remove isnan isinf to_upper move').split(' '));

  P.isBuiltinFunc = function (name) { return C_FUNCS.has(name) || (this.cpp && CPP_FUNCS.has(name)); };

  P.callBuiltin = function (name, e, discard) {
    if (!this.isBuiltinFunc(name) && !(this.java && name === '__jassert')) {
      throw new RunError('调用了未定义的函数 “' + name + '()”。', 'runtime', '检查函数名是否拼写正确、是否在使用前定义，或者是否包含了对应的头文件（可视化器只支持常用的标准库函数）。');
    }
    if (name === 'swap' && this.cpp) {
      const a = this.lv(e.args[0]), b = this.lv(e.args[1]);
      const va = this.load(a), vb = this.load(b);
      if (va.t.k === 'struct') {
        const tmp = this.newBlock('temp', this.sizeOf(va.t), va.t, '');
        const tl = new MemLV(tmp, 0, va.t);
        this.copyStruct(tl, va); this.copyStruct(a, vb); this.copyStruct(b, { t: va.t, v: tl });
      } else if (va.t.k === 'cont') { this.store(a, vb, true); this.store(b, va, true); }
      else { this.store(a, vb); this.store(b, va); }
      return { t: T.void, v: 0 };
    }
    if (name === 'getline' && this.cpp) {
      const lv = this.lv(e.args[1]);
      const line = this.stdin.line();
      if (line === null) { this.cin.fail = true; this.store(lv, { t: T.string, v: '' }); }
      else this.store(lv, { t: T.string, v: line });
      return { t: T.stream('istream'), v: this.cin };
    }
    if (name === '__jassert') {
      const c = this.ev(e.args[0]);
      if (!this.truthy(c)) throw new RunError('AssertionError' + (e.args[1] ? '：' + this.javaStr(this.ev(e.args[1])) : ''), 'exception');
      return { t: T.void, v: 0 };
    }
    const args = e.args.map(a => this.ev(a));
    return this.callBuiltinVals(name, args, e.line, e);
  };

  P.argStr = function (v) {
    if (v.t.k === 'string') return v.v;
    if (v.t.k === 'ptr' || v.t.k === 'nullptr') return this.readCString(v.v);
    throw new RunError('这里需要一个字符串参数，但给的是 ' + T.name(v.t), 'runtime');
  };
  P.argNum = function (v) {
    if (v.t.k === 'any') v = this.unboxAny(v);
    if (v.t.k !== 'prim') throw new RunError('这里需要一个数字参数，但给的是 ' + T.name(v.t), 'runtime');
    return v.v;
  };
  P.cFormat = function (fmt, args, fname) {
    let i = 0;
    const self = this;
    const out = DSV.formatPrintf(fmt, (kind) => {
      const a = args[i++];
      if (!a) {
        if (!self.warnedFmt) { self.warnedFmt = true; self.rec.note('⚠ ' + fname + ' 格式字符串里的 % 说明符比后面给的参数多。', 'warn'); }
        return kind === 'str' ? '(null)' : 0;
      }
      let v = a;
      if (v.t.k === 'any') v = v.v || { t: T.nullptr, v: NULLP };
      switch (kind) {
        case 'int': case 'char':
          if (v.t.k === 'prim') { if (v.t.fl && !self.warnedFmtF) { self.warnedFmtF = true; self.rec.note('⚠ 用 %d 打印了浮点数，结果是错误的。打印 float/double 应该用 %f。', 'warn'); } return v.t.fl ? 0 : v.v; }
          if (v.t.k === 'ptr') { if (!self.warnedFmtP) { self.warnedFmtP = true; self.rec.note('⚠ 用整数格式打印了指针。打印指针应该用 %p，打印指向的值要先解引用 *p。', 'warn'); } return v.v.blk ? v.v.blk.addr + v.v.off : 0; }
          return 0;
        case 'float':
          if (v.t.k === 'prim') { if (!v.t.fl && !self.warnedFmtI) { self.warnedFmtI = true; self.rec.note('⚠ 用 %f 打印了整数，真实的 C 程序会打印出错误的值（这里显示的是转换后的结果）。可以写成 (float) x。', 'warn'); } return v.v; }
          return 0;
        case 'str':
          if (v.t.k === 'string') return self.java ? self.javaStr(v) : v.v;
          if (self.java) return self.javaStr(v);
          if (v.t.k === 'ptr' || v.t.k === 'nullptr') { if (!v.v.blk && !v.v.wild) return '(null)'; return self.readCString(v.v); }
          if (v.t.k === 'prim') throw new RunError('printf 的 %s 需要字符串（char *），但传入的是 ' + T.name(v.t) + '。', 'segfault', '打印整数用 %d，打印字符用 %c。');
          return String(v.v);
        case 'ptr':
          if (v.t.k === 'ptr' || v.t.k === 'nullptr') return v.v.blk ? self.hex(v.v.blk.addr + v.v.off) : (v.v.wild ? self.hex(v.v.off) : '(nil)');
          return self.hex(v.v);
        case 'bool': return self.javaStr(v);
      }
      return v.v;
    });
    return out;
  };

  // ---------- heap ----------
  P.cMalloc = function (n, zero, how) {
    if (n < 0 || n > 64 * 1024 * 1024) throw new RunError(how + ' 的大小不合法：' + n, 'runtime');
    const blk = this.newBlock('heap', Math.max(n, 1), null, '');
    blk.zero = !!zero;
    blk.realSize = n;
    this.mallocCount++;
    this.rec.note(how + ' 在堆上分配了 ' + n + ' 字节，地址 ' + this.hex(blk.addr) + (zero ? '（全部清零）' : '（内容未初始化）'), 'alloc');
    return new Ptr(blk, 0);
  };

  P.callBuiltinVals = function (name, args, line, e) {
    const r = (t, v) => ({ t, v });
    const I = (v) => ({ t: T.int, v });
    const D = (v) => ({ t: T.double, v });
    const num = (i) => this.argNum(args[i]);
    switch (name) {
      // ---------- output ----------
      case 'printf': {
        const fmt = this.argStr(args[0]);
        const s = this.cFormat(fmt, args.slice(1), 'printf');
        this.rec.write(s);
        return I(s.length);
      }
      case 'fprintf': { const s = this.cFormat(this.argStr(args[1]), args.slice(2), 'fprintf'); this.rec.write(s); return I(s.length); }
      case 'sprintf': case 'snprintf': {
        const off = name === 'snprintf' ? 2 : 1;
        let s = this.cFormat(this.argStr(args[off]), args.slice(off + 1), name);
        if (name === 'snprintf') { const n = num(1); if (s.length >= n) s = s.slice(0, Math.max(0, n - 1)); }
        this.writeCString(args[0].v, s);
        return I(s.length);
      }
      case 'puts': { const s = this.argStr(args[0]); this.rec.write(s + '\n'); return I(1); }
      case 'fputs': { this.rec.write(this.argStr(args[0])); return I(1); }
      case 'putchar': { this.rec.write(String.fromCharCode(num(0) & 0xff)); return I(num(0)); }
      case 'fflush': return I(0);
      case 'perror': this.rec.write(this.argStr(args[0]) + ': error\n'); return r(T.void, 0);
      // ---------- input ----------
      case 'get_int': case 'get_long': case 'get_long_long': case 'get_float': case 'get_double': case 'get_char': case 'get_string': {
        if (args.length) { const p = this.cFormat(this.argStr(args[0]), args.slice(1), name); this.rec.write(p); }
        for (;;) {
          const ln = this.stdin.line();
          if (ln === null) {
            if (name === 'get_string') { this.rec.note('标准输入已经读完，get_string 返回 NULL', 'warn'); return r(T.ptr(T.char), NULLP); }
            throw new RunError(name + '() 需要从键盘读取输入，但“标准输入”框里的内容已经读完了。', 'runtime', '在页面上方的“输入 (stdin)”框里，每行写一个程序要读取的值。');
          }
          this.rec.write(ln + '\n');
          if (name === 'get_string') {
            const blk = this.newBlock('heap', ln.length + 1, T.arr(T.char, ln.length + 1), '');
            blk.typed = true; blk.cs50 = true;
            for (let i = 0; i < ln.length; i++) blk.cells.set(i, { t: T.char, v: ln.charCodeAt(i) & 0xff });
            blk.cells.set(ln.length, { t: T.char, v: 0 });
            this.rec.note('get_string 读入 "' + ln + '"，并在堆上为它分配了 ' + (ln.length + 1) + ' 字节（CS50 库会在程序结束时自动释放）', 'alloc');
            return r(T.ptr(T.char), new Ptr(blk, 0));
          }
          if (name === 'get_char') { if (ln.length === 1) return r(T.char, ln.charCodeAt(0)); }
          else if (name === 'get_float' || name === 'get_double') { if (/^\s*[-+]?(\d+\.?\d*|\.\d+)([eE][-+]?\d+)?\s*$/.test(ln)) return r(name === 'get_float' ? T.float : T.double, parseFloat(ln)); }
          else if (/^\s*[-+]?\d+\s*$/.test(ln)) return r(name === 'get_int' ? T.int : T.long, parseInt(ln, 10));
          if (args.length) this.rec.write(this.cFormat(this.argStr(args[0]), args.slice(1), name));
          this.rec.note('输入 "' + ln + '" 格式不对，' + name + ' 会重新提示输入', 'warn');
        }
      }
      case 'scanf': {
        const fmt = this.argStr(args[0]);
        let ai = 1, count = 0;
        for (let i = 0; i < fmt.length; i++) {
          const c = fmt[i];
          if (c === '%') {
            i++;
            let width = '';
            while (/[0-9]/.test(fmt[i])) width += fmt[i++];
            let lmod = '';
            while (/[hlLz]/.test(fmt[i])) lmod += fmt[i++];
            const conv = fmt[i];
            const target = args[ai++];
            if (conv === 'c') { const ch = this.stdin.char(); if (ch === null) return I(count || -1); this.storeTo(target, r(T.char, ch.charCodeAt(0))); count++; continue; }
            const tok = this.stdin.token();
            if (tok === null) return I(count === 0 ? -1 : count);
            if (!target || target.t.k !== 'ptr') throw new RunError('scanf 的参数必须是地址（指针）。读入到变量 x 时应该写 &x。', 'segfault', '例如 scanf("%d", &x);  读字符串到 char 数组时不需要 &。');
            if (conv === 'd' || conv === 'i' || conv === 'u') { if (!/^[-+]?\d+/.test(tok)) return I(count); this.storeTo(target, r(lmod ? T.long : T.int, parseInt(tok, 10))); }
            else if (conv === 'f' || conv === 'g' || conv === 'e') { this.storeTo(target, r(lmod ? T.double : T.float, parseFloat(tok))); }
            else if (conv === 's') this.writeCString(target.v, width ? tok.slice(0, +width) : tok);
            else if (conv === 'x') this.storeTo(target, I(parseInt(tok, 16)));
            count++;
            this.rec.write(tok + ' ');
          }
        }
        return I(count);
      }
      case 'getchar': { const ch = this.stdin.char(); return I(ch === null ? -1 : ch.charCodeAt(0)); }
      case 'fgets': case 'gets': {
        const ln = this.stdin.line();
        if (ln === null) return r(T.ptr(T.char), NULLP);
        let s = name === 'fgets' ? ln + '\n' : ln;
        if (name === 'fgets') { const n = num(1); if (s.length > n - 1) s = s.slice(0, n - 1); }
        else this.rec.note('⚠ gets 不检查缓冲区大小，非常危险，已经被 C 标准移除。请使用 fgets。', 'warn');
        this.writeCString(args[0].v, s);
        return args[0];
      }
      // ---------- memory ----------
      case 'malloc': return r(T.ptr(T.void), this.cMalloc(num(0), false, 'malloc'));
      case 'calloc': return r(T.ptr(T.void), this.cMalloc(num(0) * num(1), true, 'calloc'));
      case 'realloc': {
        const p = args[0].v, n = num(1);
        if (!p.blk) return r(T.ptr(T.void), this.cMalloc(n, false, 'realloc'));
        if (p.blk.freed) throw new RunError('realloc 了一块已经释放的内存', 'uaf');
        const np = this.cMalloc(n, false, 'realloc');
        for (const [o, c] of p.blk.cells) if (o < n) np.blk.cells.set(o, c);
        if (p.blk.zero) np.blk.zero = false;
        const vt = p.blk.type;
        if (vt) { np.blk.type = vt.k === 'arr' ? T.arr(vt.of, Math.floor(n / this.sizeOf(vt.of))) : vt; np.blk.typed = true; }
        this.rec.note('realloc 把原来 ' + p.blk.size + ' 字节的内容复制到新地址，并释放了旧内存', 'info');
        p.blk.freed = true; p.blk.freedStep = this.rec.steps.length;
        return r(T.ptr(T.void), np);
      }
      case 'free': {
        const p = args[0].v;
        if (!p || !p.blk) { if (p && p.wild) throw new RunError('free 了一个未初始化的指针', 'segfault', '只能 free 由 malloc 返回的指针。'); this.rec.note('free(NULL) 什么也不做', 'info'); return r(T.void, 0); }
        if (p.blk.viaNew && this.cpp) this.rec.note('⚠ 用 new 分配的内存应该用 delete 释放，而不是 free', 'warn');
        this.freeBlock(p, 'free', e);
        return r(T.void, 0);
      }
      case 'memset': {
        const p = args[0].v, val = num(1) & 0xff, n = num(2);
        this.checkAccess(new MemLV(p.blk, p.off, T.arr(T.char, n), true, 'memset'), true);
        for (let i = 0; i < n; i++) this.writeCell(p.blk, p.off + i, T.uchar, val);
        if (val === 0) { // keep typed zeros nicer: rewrite as typed zero cells if block typed
          const vt = p.blk.type;
          if (vt && p.off === 0 && n >= p.blk.size) { for (const k of [...p.blk.cells.keys()]) if (k < n) p.blk.cells.delete(k); this.zeroFill(new MemLV(p.blk, 0, vt), vt); }
        }
        return args[0];
      }
      case 'memcpy': case 'memmove': {
        const d = args[0].v, s = args[1].v, n = num(2);
        this.checkAccess(new MemLV(d.blk, d.off, T.arr(T.char, n), true, name + ' 的目标'), true);
        this.checkAccess(new MemLV(s.blk, s.off, T.arr(T.char, n), true, name + ' 的源'), false);
        const tmp = [];
        for (const [o, c] of s.blk.cells) if (o >= s.off && o < s.off + n) tmp.push([o - s.off, c]);
        for (const k of [...d.blk.cells.keys()]) if (k >= d.off && k < d.off + n) d.blk.cells.delete(k);
        for (const [o, c] of tmp) d.blk.cells.set(d.off + o, c);
        if (!d.blk.typed && s.blk.type) { const st = s.blk.type; this.inferViewType(d.blk, st.k === 'arr' ? st.of : st); }
        return args[0];
      }
      case 'memcmp': { const a = args[0].v, b = args[1].v, n = num(2); for (let i = 0; i < n; i++) { const x = this.peekCell(a.blk, a.off + i, T.uchar) || 0, y = this.peekCell(b.blk, b.off + i, T.uchar) || 0; if (x !== y) return I(x - y); } return I(0); }
      // ---------- strings ----------
      case 'strlen': return r(T.size_t, this.argStr(args[0]).length);
      case 'strcpy': case 'strncpy': { let s = this.argStr(args[1]); if (name === 'strncpy') { const n = num(2); s = s.slice(0, n); if (s.length < n) this.writeCString(args[0].v, s); else for (let i = 0; i < n; i++) this.writeCell(args[0].v.blk, args[0].v.off + i, T.char, s.charCodeAt(i)); return args[0]; } this.writeCString(args[0].v, s); return args[0]; }
      case 'strcat': case 'strncat': { const a = this.argStr(args[0]); let b = this.argStr(args[1]); if (name === 'strncat') b = b.slice(0, num(2)); this.writeCString(args[0].v, a + b); return args[0]; }
      case 'strcmp': case 'strncmp': case 'strcasecmp': {
        let a = this.argStr(args[0]), b = this.argStr(args[1]);
        if (name === 'strncmp') { a = a.slice(0, num(2)); b = b.slice(0, num(2)); }
        if (name === 'strcasecmp') { a = a.toLowerCase(); b = b.toLowerCase(); }
        for (let i = 0; i < Math.max(a.length, b.length); i++) { const x = i < a.length ? a.charCodeAt(i) : 0, y = i < b.length ? b.charCodeAt(i) : 0; if (x !== y) return I(x - y); }
        return I(0);
      }
      case 'strchr': case 'strrchr': { const s = this.argStr(args[0]); const ch = String.fromCharCode(num(1)); const i = name === 'strchr' ? (num(1) === 0 ? s.length : s.indexOf(ch)) : s.lastIndexOf(ch); return r(T.ptr(T.char), i < 0 ? NULLP : new Ptr(args[0].v.blk, args[0].v.off + i)); }
      case 'strstr': { const s = this.argStr(args[0]); const i = s.indexOf(this.argStr(args[1])); return r(T.ptr(T.char), i < 0 ? NULLP : new Ptr(args[0].v.blk, args[0].v.off + i)); }
      case 'strdup': { const s = this.argStr(args[0]); const p = this.cMalloc(s.length + 1, false, 'strdup'); this.writeCString(p, s); return r(T.ptr(T.char), p); }
      case 'toupper': { const c = num(0); return I(c >= 97 && c <= 122 ? c - 32 : c); }
      case 'tolower': { const c = num(0); return I(c >= 65 && c <= 90 ? c + 32 : c); }
      case 'isalpha': return I(/[A-Za-z]/.test(String.fromCharCode(num(0))) ? 1024 : 0);
      case 'isdigit': return I(/[0-9]/.test(String.fromCharCode(num(0))) ? 2048 : 0);
      case 'isalnum': return I(/[A-Za-z0-9]/.test(String.fromCharCode(num(0))) ? 8 : 0);
      case 'isspace': return I(/[ \t\n\r\f\v]/.test(String.fromCharCode(num(0))) ? 8192 : 0);
      case 'isupper': return I(/[A-Z]/.test(String.fromCharCode(num(0))) ? 256 : 0);
      case 'islower': return I(/[a-z]/.test(String.fromCharCode(num(0))) ? 512 : 0);
      case 'ispunct': return I(/[!-\/:-@\[-`{-~]/.test(String.fromCharCode(num(0))) ? 4 : 0);
      case 'isprint': { const c = num(0); return I(c >= 32 && c < 127 ? 16384 : 0); }
      case 'isxdigit': return I(/[0-9a-fA-F]/.test(String.fromCharCode(num(0))) ? 4096 : 0);
      case 'atoi': { const m = /^\s*[-+]?\d+/.exec(this.argStr(args[0])); return I(m ? this.wrapInt(parseInt(m[0], 10), T.int) : 0); }
      case 'atol': case 'atoll': case 'strtol': case 'strtoul': { const m = /^\s*[-+]?\d+/.exec(this.argStr(args[0])); return r(T.long, m ? parseInt(m[0], name === 'strtol' && args[2] ? num(2) : 10) : 0); }
      case 'atof': case 'strtod': return D(parseFloat(this.argStr(args[0])) || 0);
      // ---------- math ----------
      case 'abs': case 'labs': case 'llabs': { const v = args[0]; if (v.t.fl) return D(Math.abs(v.v)); return r(this.promote(v.t), Math.abs(num(0))); }
      case 'fabs': return D(Math.abs(num(0)));
      case 'sqrt': if (num(0) < 0) this.rec.note('⚠ sqrt 的参数是负数，结果是 nan', 'warn'); return D(Math.sqrt(num(0)));
      case 'pow': return D(Math.pow(num(0), num(1)));
      case 'floor': return D(Math.floor(num(0)));
      case 'ceil': return D(Math.ceil(num(0)));
      case 'round': return D(Math.sign(num(0)) * Math.round(Math.abs(num(0))));
      case 'trunc': return D(Math.trunc(num(0)));
      case 'fmax': return D(Math.max(num(0), num(1)));
      case 'fmin': return D(Math.min(num(0), num(1)));
      case 'fmod': return D(num(0) % num(1));
      case 'exp': return D(Math.exp(num(0)));
      case 'log': return D(Math.log(num(0)));
      case 'log2': return D(Math.log2(num(0)));
      case 'log10': return D(Math.log10(num(0)));
      case 'sin': return D(Math.sin(num(0))); case 'cos': return D(Math.cos(num(0))); case 'tan': return D(Math.tan(num(0)));
      case 'asin': return D(Math.asin(num(0))); case 'acos': return D(Math.acos(num(0))); case 'atan': return D(Math.atan(num(0)));
      case 'atan2': return D(Math.atan2(num(0), num(1))); case 'hypot': return D(Math.hypot(num(0), num(1))); case 'cbrt': return D(Math.cbrt(num(0)));
      case 'isnan': return this.mkBool(isNaN(num(0))); case 'isinf': return this.mkBool(!isFinite(num(0)) && !isNaN(num(0)));
      case 'rand': return I(this.rng() % 2147483648);
      case 'srand': this.rng = DSV.makeRng(num(0)); return r(T.void, 0);
      case 'time': return r(T.long, 1700000000);
      case 'clock': return r(T.long, this.rec.steps.length * 10);
      case 'sleep': case 'usleep': return I(0);
      case 'exit': throw new ExitSignal(num(0));
      case 'abort': throw new RunError('程序调用了 abort() 异常终止', 'runtime');
      case 'assert': if (!this.truthy(args[0])) throw new RunError('断言失败（assertion failed）：assert 的条件为假。', 'runtime', 'assert 用来检查“一定应该成立”的条件；它失败说明程序的状态和你预期的不一样。'); return r(T.void, 0);
      case 'fopen': throw new RunError('可视化器不支持文件操作（fopen）。', 'runtime', '可以改为从标准输入读取数据，把文件内容粘贴到“输入”框里。');
      case 'fclose': return I(0);
      case 'qsort': {
        const base = args[0].v, n = num(1), sz = num(2), cmp = args[3];
        const items = [];
        for (let i = 0; i < n; i++) { const cells = []; for (const [o, c] of base.blk.cells) if (o >= base.off + i * sz && o < base.off + (i + 1) * sz) cells.push([o - base.off - i * sz, c]); items.push(cells); }
        // sort using temp blocks so comparator can read through pointers
        const tmps = items.map(cells => { const b = this.newBlock('temp', sz, base.blk.type && base.blk.type.k === 'arr' ? base.blk.type.of : null, ''); for (const [o, c] of cells) b.cells.set(o, c); return b; });
        const order = tmps.map((b, i) => i);
        this.mergeSort(order, (x, y) => this.convert(this.callValue(cmp, [{ t: T.ptr(T.void), v: new Ptr(tmps[x], 0) }, { t: T.ptr(T.void), v: new Ptr(tmps[y], 0) }], line), T.int).v);
        for (const k of [...base.blk.cells.keys()]) if (k >= base.off && k < base.off + n * sz) base.blk.cells.delete(k);
        order.forEach((src, i) => { for (const [o, c] of items[src]) base.blk.cells.set(base.off + i * sz + o, c); });
        return r(T.void, 0);
      }
    }
    if (this.cpp) return this.cppBuiltin(name, args, line, e);
    throw new RunError('调用了未定义的函数 “' + name + '()”', 'runtime');
  };
  P.storeTo = function (ptrV, val) {
    if (ptrV.t.k !== 'ptr') throw new RunError('需要一个指针参数', 'runtime');
    this.store(new MemLV(ptrV.v.blk, ptrV.v.off, ptrV.t.to, true, '*ptr'), val);
  };
  P.mergeSort = function (arr, cmp) {
    // stable merge sort calling cmp(a,b) -> number
    if (arr.length < 2) return arr;
    const mid = arr.length >> 1;
    const a = this.mergeSort(arr.slice(0, mid), cmp), b = this.mergeSort(arr.slice(mid), cmp);
    let i = 0, j = 0, k = 0;
    while (i < a.length && j < b.length) arr[k++] = cmp(b[j], a[i]) < 0 ? b[j++] : a[i++];
    while (i < a.length) arr[k++] = a[i++];
    while (j < b.length) arr[k++] = b[j++];
    return arr;
  };

  // ======================= comparisons =======================
  P.compareVals = function (a, b) {
    if (a.t.k === 'any') a = a.v || { t: T.nullptr, v: NULLP };
    if (b.t.k === 'any') b = b.v || { t: T.nullptr, v: NULLP };
    if (a.t.k === 'prim' && b.t.k === 'prim') return a.v < b.v ? -1 : a.v > b.v ? 1 : 0;
    if (a.t.k === 'string' && b.t.k === 'string') return a.v < b.v ? -1 : a.v > b.v ? 1 : 0;
    if (a.t.k === 'cont' && b.t.k === 'cont') {
      const ia = this.contItems(a.v), ib = this.contItems(b.v);
      for (let i = 0; i < Math.min(ia.length, ib.length); i++) { const c = this.compareVals(ia[i], ib[i]); if (c) return c; }
      return ia.length - ib.length;
    }
    if (a.t.k === 'ptr' && this.java && a.v.blk && a.v.blk.type && a.v.blk.type.k === 'struct') {
      const ms = this.findMethods(a.v.blk.type, 'compareTo');
      if (ms) return this.convert(this.callMethod(ms, [b], a.v, this.curLine), T.int).v;
      if (a.v.blk.isEnum) return a.v.blk.enumIdx - b.v.blk.enumIdx;
      throw new RunError('ClassCastException：类 ' + a.v.blk.type.name + ' 没有实现 Comparable（compareTo 方法），不能排序或放进 TreeMap/PriorityQueue。', 'runtime', '让类实现 Comparable<T> 接口，或者传入一个比较器（Comparator）。');
    }
    if (a.t.k === 'struct' && b.t.k === 'struct') {
      const ms = this.findMethods(a.t, 'operator<');
      throw new RunError('结构体之间不能直接比较大小，需要提供比较函数（例如 sort 的第三个参数）。', 'runtime');
    }
    if ((a.t.k === 'ptr' || a.t.k === 'nullptr') && (b.t.k === 'ptr' || b.t.k === 'nullptr')) {
      const x = a.v.blk ? a.v.blk.addr + a.v.off : 0, y = b.v.blk ? b.v.blk.addr + b.v.off : 0;
      return x - y;
    }
    if (a.t.k === 'prim' && b.t.k === 'string' || a.t.k === 'string' && b.t.k === 'prim') return a.t.k === 'prim' ? -1 : 1;
    throw new RunError('无法比较 ' + T.name(a.t) + ' 和 ' + T.name(b.t), 'runtime');
  };
  P.makeComparator = function (cmpV, reverse) {
    if (!cmpV) return reverse ? (a, b) => this.compareVals(b, a) : (a, b) => this.compareVals(a, b);
    if (cmpV.t.k === 'cmpT') return cmpV.v === 'greater' ? (a, b) => this.compareVals(b, a) : (a, b) => this.compareVals(a, b);
    return (a, b) => {
      const r = this.callValue(cmpV, [a, b], this.curLine);
      if (this.cpp || r.t.isBool) {
        // C++ comparator returns bool "a<b"
        if (this.truthy(r)) return -1;
        const r2 = this.callValue(cmpV, [b, a], this.curLine);
        return this.truthy(r2) ? 1 : 0;
      }
      return this.convert(r, T.int).v;
    };
  };

  // ======================= stream I/O (C++) =======================
  P.cppDouble = function (v, st) {
    if (!isFinite(v)) return isNaN(v) ? 'nan' : (v > 0 ? 'inf' : '-inf');
    const prec = st && st.prec != null ? st.prec : 6;
    if (st && st.fixed) return v.toFixed(prec);
    if (v === 0) return '0';
    const p = Math.max(prec, 1);
    const exp = Math.floor(Math.log10(Math.abs(v)));
    if (exp < -5 || exp >= p) {
      let s = v.toExponential(p - 1);
      let [m, ex] = s.split('e');
      if (m.includes('.')) m = m.replace(/0+$/, '').replace(/\.$/, '');
      const sign = ex[0] === '-' ? '-' : '+';
      ex = ex.replace(/^[-+]/, '');
      if (ex.length < 2) ex = '0' + ex;
      return m + 'e' + sign + ex;
    }
    let s = v.toPrecision(p);
    if (s.includes('e')) s = String(Number(s));
    if (s.includes('.')) s = s.replace(/0+$/, '').replace(/\.$/, '');
    return s;
  };
  P.cppStr = function (v, st) {
    const t = v.t;
    switch (t.k) {
      case 'string': return v.v;
      case 'prim':
        if (t.isBool) return st && st.boolalpha ? (v.v ? 'true' : 'false') : String(v.v ? 1 : 0);
        if (t.isChar && t.size === 1 || v.isCharLit) return String.fromCharCode(v.v & 0xff);
        if (t.fl) return this.cppDouble(v.v, st);
        return String(v.v);
      case 'ptr': case 'nullptr':
        if (t.k === 'ptr' && t.to.k === 'prim' && t.to.size === 1 && v.v.blk) return this.readCString(v.v);
        return v.v.blk ? this.hex(v.v.blk.addr + v.v.off) : (t.k === 'ptr' && t.to.k === 'prim' && t.to.size === 1 ? '' : '0');
      case 'any': return v.v ? this.cppStr(v.v, st) : '0';
      case 'manip': return v.v === 'endl' ? '\n' : '';
      case 'struct': throw new RunError('不能直接用 cout 输出结构体/对象 ' + T.name(t) + '，需要逐个输出它的成员。', 'runtime');
      case 'cont': throw new RunError('不能直接用 cout 输出 ' + T.name(t) + '，需要用循环逐个输出元素。', 'runtime');
    }
    return String(v.v);
  };
  P.streamOut = function (st, val) {
    if (val.t.k === 'manip') {
      const m = val.v;
      if (m === 'endl') { this.rec.write('\n'); return; }
      if (m === 'fixed') { st.fixed = true; return; }
      if (m === 'scientific') { st.fixed = false; return; }
      if (m === 'boolalpha') { st.boolalpha = true; return; }
      if (m === 'noboolalpha') { st.boolalpha = false; return; }
      if (m && m.setw != null) { st.width = m.setw; return; }
      if (m && m.prec != null) { st.prec = m.prec; return; }
      if (m && m.fill != null) { st.fill = m.fill; return; }
      return;
    }
    let s = this.cppStr(val, st);
    if (st.width) { s = s.padStart(st.width, st.fill || ' '); st.width = 0; }
    this.rec.write(s);
  };
  P.streamIn = function (st, target) {
    const lv = this.lv(target);
    const t = lv.t;
    if (st.fail) return;
    if (t.k === 'prim' && t.isChar && t.size === 1) {
      this.stdin.skipWs();
      const ch = this.stdin.char();
      if (ch === null) { st.fail = true; return; }
      this.store(lv, { t, v: ch.charCodeAt(0) });
      return;
    }
    const tok = this.stdin.token();
    if (tok === null) { st.fail = true; return; }
    if (t.k === 'string') this.store(lv, { t, v: tok });
    else if (t.k === 'prim') {
      if (t.fl) { const v = parseFloat(tok); if (isNaN(v)) { st.fail = true; return; } this.store(lv, { t, v }); }
      else { if (!/^[-+]?\d+/.test(tok)) { st.fail = true; this.store(lv, { t, v: 0 }); return; } this.store(lv, { t, v: parseInt(tok, 10) }); }
    } else throw new RunError('cin 不能读入 ' + T.name(t) + ' 类型', 'runtime');
  };
  P.streamMethod = function (st, name, argEs, e) {
    if (this.java) {
      if (st === this.cout) return this.javaPrint(name, argEs.map(a => this.ev(a)), e);
    }
    switch (name) {
      case 'get': { const ch = this.stdin.char(); if (argEs.length) { this.store(this.lv(argEs[0]), { t: T.char, v: ch === null ? 0 : ch.charCodeAt(0) }); return { t: T.stream('istream'), v: st }; } return { t: T.int, v: ch === null ? -1 : ch.charCodeAt(0) }; }
      case 'ignore': if (this.stdin.text[this.stdin.pos] === '\n') this.stdin.pos++; else this.stdin.line(); return { t: T.stream('istream'), v: st };
      case 'eof': return this.mkBool(this.stdin.eof());
      case 'fail': return this.mkBool(st.fail);
      case 'good': return this.mkBool(!st.fail);
      case 'clear': st.fail = false; return { t: T.void, v: 0 };
      case 'flush': return { t: T.stream('ostream'), v: st };
      case 'precision': st.prec = this.argNum(this.ev(argEs[0])); return { t: T.void, v: 0 };
      case 'tie': case 'sync_with_stdio': return { t: T.void, v: 0 };
      case 'peek': { const ch = this.stdin.text[this.stdin.pos]; return { t: T.int, v: ch === undefined ? -1 : ch.charCodeAt(0) }; }
    }
    throw new RunError('不支持的流方法：' + name, 'runtime');
  };

  // ======================= C++ std functions =======================
  P.cppBuiltin = function (name, args, line, e) {
    const num = (i) => this.argNum(args[i]);
    switch (name) {
      case 'max': case 'min': {
        if (args.length === 1 && args[0].t.k === 'initlist') { const l = args[0].v; let best = l[0]; for (const x of l) if (name === 'max' ? this.compareVals(x, best) > 0 : this.compareVals(x, best) < 0) best = x; return best; }
        const a = args[0], b = args[1];
        if (args[2]) { const lt = this.truthy(this.callValue(args[2], [a, b], line)); return name === 'max' ? (lt ? b : a) : (this.truthy(this.callValue(args[2], [b, a], line)) ? b : a); }
        const c = this.compareVals(a, b);
        if (a.t.k === 'prim' && b.t.k === 'prim' && a.t !== b.t && (a.t.fl !== b.t.fl || a.t.size !== b.t.size) && !this.warnedMinMax) { this.warnedMinMax = true; }
        return name === 'max' ? (c < 0 ? b : a) : (c > 0 ? b : a);
      }
      case 'to_string': { const v = args[0]; return { t: T.string, v: v.t.fl ? v.v.toFixed(6) : String(v.v) }; }
      case 'stoi': case 'stol': case 'stoll': {
        const s = this.argStr(args[0]);
        const m = /^\s*[-+]?\d+/.exec(s);
        if (!m) { const err = new RunError('invalid_argument：stoi 无法把 "' + s + '" 转换为整数', 'exception'); err.cppExc = 'invalid_argument'; throw err; }
        return { t: name === 'stoi' ? T.int : T.long, v: parseInt(m[0], 10) };
      }
      case 'stod': case 'stof': return { t: T.double, v: parseFloat(this.argStr(args[0])) };
      case 'make_pair': return { t: T.cont('pair', [args[0].t, args[1].t]), v: this.makePair(args[0], args[1]), fresh: true };
      case 'setw': return { t: { k: 'manip' }, v: { setw: num(0) } };
      case 'setprecision': return { t: { k: 'manip' }, v: { prec: num(0) } };
      case 'gcd': case '__gcd': { let a = Math.abs(num(0)), b = Math.abs(num(1)); while (b) [a, b] = [b, a % b]; return { t: args[0].t, v: a }; }
      case 'lcm': { let a = Math.abs(num(0)), b = Math.abs(num(1)), x = a, y = b; while (y) [x, y] = [y, x % y]; return { t: args[0].t, v: x ? a / x * b : 0 }; }
      case 'distance': return { t: T.long, v: this.iterIndex(args[1]) - this.iterIndex(args[0]) };
      case 'move': return args[0];
    }
    // range algorithms: (first, last, ...)
    const R = this.rangeOf(args[0], args[1], name);
    switch (name) {
      case 'sort': case 'stable_sort': {
        const vals = R.get();
        const cmp = this.makeComparator(args[2]);
        const order = vals.map((v, i) => i);
        this.mergeSort(order, (x, y) => cmp(vals[x], vals[y]));
        R.set(order.map(i => vals[i]));
        this.rec.note('sort 排序了 ' + vals.length + ' 个元素', 'info');
        return { t: T.void, v: 0 };
      }
      case 'reverse': { R.set(R.get().reverse()); return { t: T.void, v: 0 }; }
      case 'fill': { const vals = R.get(); R.set(vals.map(() => args[2])); return { t: T.void, v: 0 }; }
      case 'iota': { let x = num(2); R.set(R.get().map(v => ({ t: v.t, v: x++ }))); return { t: T.void, v: 0 }; }
      case 'accumulate': { let acc = args[2]; for (const v of R.get()) acc = args[3] ? this.callValue(args[3], [acc, v], line) : this.binop('+', acc, v, line); return acc; }
      case 'count': { let c = 0; for (const v of R.get()) if (this.compareVals(v, args[2]) === 0) c++; return { t: T.long, v: c }; }
      case 'count_if': { let c = 0; for (const v of R.get()) if (this.truthy(this.callValue(args[2], [v], line))) c++; return { t: T.long, v: c }; }
      case 'find': { const vals = R.get(); const i = vals.findIndex(v => this.compareVals(v, args[2]) === 0); return R.at(i < 0 ? vals.length : i); }
      case 'find_if': { const vals = R.get(); const i = vals.findIndex(v => this.truthy(this.callValue(args[2], [v], line))); return R.at(i < 0 ? vals.length : i); }
      case 'all_of': return this.mkBool(R.get().every(v => this.truthy(this.callValue(args[2], [v], line))));
      case 'any_of': return this.mkBool(R.get().some(v => this.truthy(this.callValue(args[2], [v], line))));
      case 'none_of': return this.mkBool(!R.get().some(v => this.truthy(this.callValue(args[2], [v], line))));
      case 'min_element': case 'max_element': {
        const vals = R.get(); if (!vals.length) return R.at(0);
        let bi = 0; for (let i = 1; i < vals.length; i++) { const c = this.compareVals(vals[i], vals[bi]); if (name === 'min_element' ? c < 0 : c > 0) bi = i; }
        return R.at(bi);
      }
      case 'lower_bound': case 'upper_bound': {
        const vals = R.get(); let lo = 0, hi = vals.length;
        while (lo < hi) { const mid = (lo + hi) >> 1; const c = this.compareVals(vals[mid], args[2]); if (name === 'lower_bound' ? c < 0 : c <= 0) lo = mid + 1; else hi = mid; }
        return R.at(lo);
      }
      case 'binary_search': return this.mkBool(R.get().some(v => this.compareVals(v, args[2]) === 0));
      case 'next_permutation': case 'prev_permutation': {
        const a = R.get(); const cmp = name === 'next_permutation' ? (x, y) => this.compareVals(x, y) : (x, y) => this.compareVals(y, x);
        let i = a.length - 2; while (i >= 0 && cmp(a[i], a[i + 1]) >= 0) i--;
        if (i < 0) { R.set(a.reverse()); return this.mkBool(false); }
        let j = a.length - 1; while (cmp(a[j], a[i]) <= 0) j--;
        [a[i], a[j]] = [a[j], a[i]];
        const tail = a.splice(i + 1).reverse();
        R.set(a.concat(tail)); return this.mkBool(true);
      }
      case 'unique': {
        const vals = R.get(); const out = [];
        for (const v of vals) if (!out.length || this.compareVals(out[out.length - 1], v) !== 0) out.push(v);
        const all = out.concat(vals.slice(out.length));
        R.set(all); return R.at(out.length);
      }
      case 'remove': {
        const vals = R.get(); const keep = vals.filter(v => this.compareVals(v, args[2]) !== 0);
        R.set(keep.concat(vals.slice(keep.length))); return R.at(keep.length);
      }
      case 'make_heap': case 'push_heap': case 'pop_heap': {
        const vals = R.get(); const cmp = this.makeComparator(args[2]);
        if (name === 'pop_heap') { const top = vals.shift(); const rest = vals; this.heapify(rest, (a, b) => cmp(b, a)); R.set(rest.concat([top])); }
        else { this.heapify(vals, (a, b) => cmp(b, a)); R.set(vals); }
        return { t: T.void, v: 0 };
      }
    }
    throw new RunError('不支持的函数 ' + name + '()', 'runtime');
  };
  P.heapify = function (arr, cmp) { // max-heap per cmp (cmp(a,b)<0 means a should be higher)
    const n = arr.length;
    const down = (i) => { for (;;) { let l = 2 * i + 1, r = l + 1, m = i; if (l < n && cmp(arr[l], arr[m]) < 0) m = l; if (r < n && cmp(arr[r], arr[m]) < 0) m = r; if (m === i) break; [arr[i], arr[m]] = [arr[m], arr[i]]; i = m; } };
    for (let i = (n >> 1) - 1; i >= 0; i--) down(i);
  };
  // abstract range over iterator pair / pointer pair
  P.rangeOf = function (a, b, fname) {
    if (!a || !b) throw new RunError(fname + ' 需要一个范围参数 (first, last)', 'runtime');
    if (a.t.k === 'iter' && b.t.k === 'iter') {
      const it = a.v;
      if (it.slv) {
        const lv = it.slv; const i0 = it.idx, i1 = b.v.idx;
        return {
          get: () => [...this.load(lv).v.slice(i0, i1)].map(c => ({ t: T.char, v: c.charCodeAt(0) })),
          set: (vals) => { const s = this.load(lv).v; this.store(lv, { t: T.string, v: s.slice(0, i0) + vals.map(v => String.fromCharCode(v.v)).join('') + s.slice(i1) }); },
          at: (i) => ({ t: { k: 'iter' }, v: { slv: lv, idx: i0 + i } }),
        };
      }
      const obj = it.obj; const i0 = it.idx, i1 = b.v.idx;
      return {
        get: () => obj.items.slice(i0, i1).map(x => x.t.k === 'struct' ? { t: x.t, v: new MemLV(x.v, 0, x.t) } : x),
        set: (vals) => { const nv = vals.map(v => this.elemVal(v, obj.t.args[0] || v.t)); obj.items.splice(i0, i1 - i0, ...nv); },
        at: (i) => ({ t: { k: 'iter' }, v: { obj, idx: i0 + i } }),
      };
    }
    if (a.t.k === 'ptr' && b.t.k === 'ptr') {
      const blk = a.v.blk, et = a.t.to, es = this.sizeOf(et);
      if (blk !== b.v.blk) throw new RunError(fname + ' 的两个指针必须指向同一个数组', 'runtime');
      const n = (b.v.off - a.v.off) / es;
      const lvs = []; for (let i = 0; i < n; i++) lvs.push(new MemLV(blk, a.v.off + i * es, et, true, 'arr'));
      return {
        get: () => lvs.map(lv => { const v = this.load(lv); return v.t.k === 'struct' ? this.structToElemVal(v) : v; }),
        set: (vals) => vals.forEach((v, i) => this.store(lvs[i], v)),
        at: (i) => ({ t: a.t, v: new Ptr(blk, a.v.off + i * es) }),
      };
    }
    throw new RunError(fname + ' 的参数需要是迭代器（如 v.begin(), v.end()）或指针（如 arr, arr + n）', 'runtime');
  };
  P.structToElemVal = function (v) { const e = this.structToElem(v); return { t: e.t, v: new MemLV(e.v, 0, e.t) }; };

  // ======================= strings =======================
  P.constructString = function (args) {
    if (!args.length) return '';
    if (args.length === 2 && args[0].t.k === 'prim') return String.fromCharCode(args[1].v).repeat(args[0].v);
    if (args[0].t.k === 'iter' && args[1]) { const R = this.rangeOf(args[0], args[1], 'string'); return R.get().map(v => String.fromCharCode(v.v)).join(''); }
    return this.convert(args[0], T.string).v;
  };
  P.javaStringCtor = function (args) {
    const a = args[0];
    if (a.t.k === 'ptr' && a.t.jarr) { const blk = a.v.blk; let s = ''; for (let i = 0; i < blk.type.len; i++) s += String.fromCharCode(this.peekCell(blk, i * 2, T.jchar) || 0); return s; }
    return this.javaStr(a);
  };
  P.stringMethod = function (sv, slv, name, args, e) {
    const s = sv.v;
    if (s == null) throw new RunError('NullPointerException：在 null 字符串上调用 ' + name + '()', 'segfault', '字符串变量可能还没有被赋值。');
    const ST = this.java ? T.jstring : T.string;
    const B = (b) => this.mkBool(b);
    const I = (v) => ({ t: T.int, v });
    const num = (i) => this.argNum(args[i]);
    const str = (i) => this.java ? this.javaStr(args[i]) : (args[i].t.k === 'prim' ? String.fromCharCode(args[i].v) : this.argStr(args[i]));
    const mutate = (ns) => { if (!slv) throw new RunError('不能修改临时字符串', 'runtime'); this.store(slv, { t: ST, v: ns }); };
    switch (name) {
      case 'length': case 'size': return this.java ? I(s.length) : { t: T.size_t, v: s.length };
      case 'charAt': { const i = num(0); if (i < 0 || i >= s.length) throw new RunError('StringIndexOutOfBoundsException：下标 ' + i + ' 超出了字符串 ' + DSV.quoteStr(s) + ' 的范围（长度 ' + s.length + '）', 'oob', '字符串下标的范围是 0 ~ length()-1。'); return { t: T.jchar, v: s.charCodeAt(i) }; }
      case 'at': { const i = num(0); if (i < 0 || i >= s.length) { const er = new RunError('out_of_range：string::at 的下标 ' + i + ' 超出范围（长度 ' + s.length + '）', 'oob'); er.cppExc = 'out_of_range'; throw er; } return { t: T.char, v: s.charCodeAt(i) }; }
      case 'isEmpty': case 'empty': return B(s.length === 0);
      case 'isBlank': return B(s.trim().length === 0);
      case 'substring': { const a = num(0), b = args[1] ? num(1) : s.length; if (a < 0 || b > s.length || a > b) throw new RunError('StringIndexOutOfBoundsException：substring(' + a + ', ' + b + ') 超出范围，字符串长度是 ' + s.length, 'oob'); return { t: ST, v: s.slice(a, b) }; }
      case 'substr': { const a = num(0); if (a > s.length) { const er = new RunError('out_of_range：substr 的起点 ' + a + ' 超过了字符串长度 ' + s.length, 'oob'); er.cppExc = 'out_of_range'; throw er; } const n = args[1] ? num(1) : s.length; return { t: ST, v: s.substr(a, n) }; }
      case 'indexOf': case 'find': { const r = s.indexOf(str(0), args[1] ? num(1) : 0); return this.java ? I(r) : { t: T.long, v: r }; }
      case 'lastIndexOf': case 'rfind': { const r = s.lastIndexOf(str(0)); return this.java ? I(r) : { t: T.long, v: r }; }
      case 'contains': return B(s.includes(str(0)));
      case 'startsWith': case 'starts_with': return B(s.startsWith(str(0)));
      case 'endsWith': case 'ends_with': return B(s.endsWith(str(0)));
      case 'equals': return B(args[0].t.k === 'string' && args[0].v === s);
      case 'equalsIgnoreCase': return B(args[0].v != null && args[0].v.toLowerCase() === s.toLowerCase());
      case 'compareTo': case 'compare': { const o = str(0); if (this.java) { for (let i = 0; i < Math.min(s.length, o.length); i++) if (s[i] !== o[i]) return I(s.charCodeAt(i) - o.charCodeAt(i)); return I(s.length - o.length); } return I(s < o ? -1 : s > o ? 1 : 0); }
      case 'compareToIgnoreCase': { const a = s.toLowerCase(), b = str(0).toLowerCase(); return I(a < b ? -1 : a > b ? 1 : 0); }
      case 'toUpperCase': return { t: ST, v: s.toUpperCase() };
      case 'toLowerCase': return { t: ST, v: s.toLowerCase() };
      case 'trim': case 'strip': return { t: ST, v: s.trim() };
      case 'replace': if (this.java) return { t: ST, v: s.split(str(0)).join(str(1)) };
        { const pos = num(0), n = num(1); mutate(s.slice(0, pos) + str(2) + s.slice(pos + n)); return { t: ST, v: this.load(slv).v }; }
      case 'replaceAll': return { t: ST, v: s.replace(new RegExp(str(0), 'g'), str(1)) };
      case 'split': {
        let parts = s.split(new RegExp(str(0)));
        if (s === '') parts = [''];
        while (parts.length > 1 && parts[parts.length - 1] === '') parts.pop();
        return { t: T.ptr(T.jstring, { jarr: true }), v: this.makeJavaArray(T.jstring, parts.map(p => ({ t: T.jstring, v: p }))) };
      }
      case 'toCharArray': return { t: T.ptr(T.jchar, { jarr: true }), v: this.makeJavaArray(T.jchar, [...s].map(c => ({ t: T.jchar, v: c.charCodeAt(0) }))) };
      case 'chars': return { t: T.cont('ArrayList', [T.int]), v: this.newListOf('ArrayList', [...s].map(c => ({ t: T.int, v: c.charCodeAt(0) }))) };
      case 'hashCode': return I(this.javaHash({ t: ST, v: s }));
      case 'repeat': return { t: ST, v: s.repeat(num(0)) };
      case 'concat': return { t: ST, v: s + str(0) };
      case 'matches': return B(new RegExp('^(?:' + str(0) + ')$').test(s));
      case 'intern': case 'toString': return { t: ST, v: s };
      case 'c_str': case 'data': { // make a char* view
        const blk = this.newBlock('temp', s.length + 1, T.arr(T.char, s.length + 1), 'c_str');
        for (let i = 0; i < s.length; i++) blk.cells.set(i, { t: T.char, v: s.charCodeAt(i) }); blk.cells.set(s.length, { t: T.char, v: 0 });
        return { t: T.ptr(T.char), v: new Ptr(blk, 0) };
      }
      case 'push_back': case 'append': case '+=': mutate(s + str(0)); return { t: T.void, v: 0 };
      case 'pop_back': mutate(s.slice(0, -1)); return { t: T.void, v: 0 };
      case 'back': return { t: T.char, v: s.charCodeAt(s.length - 1) };
      case 'front': return { t: T.char, v: s.charCodeAt(0) };
      case 'clear': mutate(''); return { t: T.void, v: 0 };
      case 'insert': mutate(s.slice(0, num(0)) + str(1) + s.slice(num(0))); return { t: T.void, v: 0 };
      case 'erase': { const p = args.length ? (args[0].t.k === 'iter' ? args[0].v.idx : num(0)) : 0; const n = args[1] ? (args[1].t.k === 'iter' ? args[1].v.idx - p : num(1)) : (args[0] && args[0].t.k === 'iter' ? 1 : s.length); mutate(s.slice(0, p) + s.slice(p + n)); return { t: T.void, v: 0 }; }
      case 'begin': return { t: { k: 'iter' }, v: { slv: slv || new TmpLV(sv), idx: 0 } };
      case 'end': return { t: { k: 'iter' }, v: { slv: slv || new TmpLV(sv), idx: s.length } };
      case 'resize': { const n = num(0); mutate(n <= s.length ? s.slice(0, n) : s + String.fromCharCode(args[1] ? num(1) : 0).repeat(n - s.length)); return { t: T.void, v: 0 }; }
      case 'reverse': return { t: ST, v: [...s].reverse().join('') };
      case 'count': return I(s.split(str(0)).length - 1);
    }
    throw new RunError('字符串没有方法 ' + name + '()（或可视化器暂不支持）', 'runtime');
  };

  // ======================= containers =======================
  const SEQ = new Set(['vector', 'deque', 'list', 'stack', 'queue', 'ArrayList', 'LinkedList', 'Stack', 'ArrayDeque', 'Vector', 'List', 'Deque', 'Queue', 'Collection']);
  const HEAPC = new Set(['priority_queue', 'PriorityQueue']);
  const MAPC = new Set(['map', 'unordered_map', 'multimap', 'HashMap', 'TreeMap', 'LinkedHashMap', 'Map']);
  const SETC = new Set(['set', 'unordered_set', 'multiset', 'HashSet', 'TreeSet', 'LinkedHashSet', 'Set']);
  P.contKind = function (m) {
    const c = m.ctype;
    if (SEQ.has(c)) return 'seq';
    if (HEAPC.has(c)) return 'heap';
    if (MAPC.has(c)) return 'map';
    if (SETC.has(c)) return 'set';
    return c;
  };
  P.newMObj = function (ctype, t) {
    DSV.clikeRT.bump();
    const m = new MObj(ctype, t);
    m.born = this.rec.steps.length;
    if (MAPC.has(ctype) || SETC.has(ctype)) { m.map = new Map(); m.seq = 0; }
    this.mobjs.add(m);
    return m;
  };
  P.constructCont = function (t, args, initItems) {
    const m = this.newMObj(t.name, t);
    const et = t.args[0];
    const kind = this.contKind(m);
    if (t.name === 'pair') {
      if (initItems) args = initItems.map(x => this.ev(x));
      m.items = [args[0] ? this.elemVal(args[0], t.args[0]) : this.defaultElem(t.args[0]), args[1] ? this.elemVal(args[1], t.args[1]) : this.defaultElem(t.args[1])];
      return m;
    }
    if (kind === 'heap') {
      const cmpT = t.args[2];
      m.cmp = cmpT && cmpT.k === 'cmp' && cmpT.name === 'greater' ? 'min' : 'max';
      if (args.length && args[0].t.k === 'lambda') { m.cmpFn = args[0]; }
    }
    if (initItems) {
      for (const it of initItems) {
        const v = it.type === 'InitList' ? (kind === 'map' ? { t: T.cont('pair', [t.args[0], t.args[1]]), v: this.constructCont(T.cont('pair', [t.args[0], t.args[1]]), [], it.items), fresh: true } : { t: et, v: this.constructCont(et, [], it.items), fresh: true }) : this.ev(it);
        this.contAdd(m, v);
      }
      return m;
    }
    if (args.length) {
      const a0 = args[0];
      if (a0.t.k === 'initlist') { for (const v of a0.v) this.contAdd(m, v); return m; }
      if (a0.t.k === 'cont' && a0.v) { for (const v of this.contItems(a0.v)) this.contAdd(m, v); return m; }
      if (a0.t.k === 'iter' && args[1]) { for (const v of this.rangeOf(a0, args[1], 'construct').get()) this.contAdd(m, v); return m; }
      if (a0.t.k === 'ptr' && args[1] && args[1].t.k === 'ptr') { for (const v of this.rangeOf(a0, args[1], 'construct').get()) this.contAdd(m, v); return m; }
      if (a0.t.k === 'prim' && kind === 'seq') {
        const n = a0.v;
        if (n > 1e6) throw new RunError('vector 太大', 'runtime');
        for (let i = 0; i < n; i++) m.items.push(args[1] ? this.elemVal(args[1], et) : this.defaultElem(et));
        m.cap = n;
        return m;
      }
    }
    return m;
  };
  P.defaultElem = function (et) {
    if (!et) return { t: T.int, v: 0 };
    if (et.k === 'cont') return { t: et, v: this.constructCont(et, []) };
    if (et.k === 'struct') { const blk = this.newBlock('temp', this.sizeOf(et), et, ''); blk.elem = true; const lv = new MemLV(blk, 0, et); if (this.cpp) this.constructAt(lv, [], true); else this.zeroFill(lv, et); return { t: et, v: blk }; }
    if (et.k === 'string') return { t: et, v: et.java ? null : '' };
    if (et.k === 'any') return { t: T.any, v: null, isNull: true };
    return { t: et, v: this.zeroOf(et) };
  };
  P.cloneCont = function (m) {
    if (!m) return m;
    const n = this.newMObj(m.ctype, m.t);
    n.cap = m.cap; n.cmp = m.cmp; n.cmpFn = m.cmpFn;
    n.items = m.items.map(it => this.cloneItem(it));
    if (m.map) { n.map = new Map(); for (const [k, e] of m.map) n.map.set(k, { k: this.cloneItem(e.k), v: this.cloneItem(e.v), seq: e.seq }); n.seq = m.seq; }
    n.str = m.str;
    return n;
  };
  P.cloneItem = function (it) {
    if (!it) return it;
    if (it.t.k === 'cont' && it.v) return { t: it.t, v: this.cloneCont(it.v) };
    if (it.t.k === 'struct' && it.v instanceof Block) { const b = this.newBlock('temp', it.v.size, it.t, ''); b.elem = true; for (const [o, c] of it.v.cells) b.cells.set(o, c.t.k === 'cont' && c.v ? { t: c.t, v: this.cloneCont(c.v) } : c); return { t: it.t, v: b }; }
    return it;
  };
  P.makePair = function (a, b) {
    const m = this.newMObj('pair', T.cont('pair', [a.t, b.t]));
    m.items = [this.elemVal(a, a.t), this.elemVal(b, b.t)];
    return m;
  };
  P.pairParts = function (m) {
    if (m.ctype === 'pair' || m.ctype === 'Entry') return m.items.map(x => x.t.k === 'struct' ? { t: x.t, v: new MemLV(x.v, 0, x.t) } : x);
    if (m.ctype === 'mapentry') return [m.entry.k, m.entry.v];
    throw new RunError('不是 pair', 'runtime');
  };
  // ordered list of typed values (for iteration / printing)
  P.contItems = function (m) {
    const kind = this.contKind(m);
    if (kind === 'map') return this.mapEntries(m).map(en => ({ t: { k: 'cont', name: 'mapentry', args: [] }, v: this.entryObj(m, en) }));
    if (kind === 'set') return this.mapEntries(m).map(en => en.k);
    if (kind === 'heap' && this.java) return m.items.slice();
    if (m.ctype === 'pair') return m.items.slice();
    return m.items.map(x => x.t.k === 'struct' ? { t: x.t, v: new MemLV(x.v, 0, x.t) } : x);
  };
  P.entryObj = function (m, en) {
    // lightweight entry view object
    const o = { ctype: 'mapentry', map: m, entry: en, id: 'e' + en.seq, isView: true, items: [] };
    return o;
  };
  P.keyOf = function (v) {
    if (!v) return 'null';
    if (v.t.k === 'any') return v.v ? this.keyOf(v.v) : 'null';
    switch (v.t.k) {
      case 'prim': return 'n' + v.v;
      case 'string': return v.v == null ? 'null' : 's' + v.v;
      case 'ptr': case 'nullptr': return v.v.blk ? (this.java && v.v.blk.type && v.v.blk.type.k === 'struct' && this.findMethods(v.v.blk.type, 'equals') ? this.objKeyViaHash(v) : 'p' + v.v.blk.id + ':' + v.v.off) : 'null';
      case 'cont': return v.v ? 'c[' + this.contItems(v.v).map(x => this.keyOf(x)).join(',') + ']' : 'null';
      case 'struct': return 'S' + this.sizeOf(v.t);
    }
    return String(v.v);
  };
  P.objKeyViaHash = function (v) {
    const h = this.findMethods(v.v.blk.type, 'hashCode');
    if (!h) return 'p' + v.v.blk.id;
    // objects with equals/hashCode: use hash + fields signature
    const hv = this.convert(this.callMethod(h, [], v.v, this.curLine), T.int).v;
    return 'h' + hv;
  };
  P.javaHash = function (v) {
    if (!v || v.v == null) return 0;
    if (v.t.k === 'any') return this.javaHash(v.v);
    switch (v.t.k) {
      case 'prim':
        if (v.t.isBool) return v.v ? 1231 : 1237;
        if (v.t.fl) { const buf = new DataView(new ArrayBuffer(8)); buf.setFloat64(0, v.v); return (buf.getInt32(0) ^ buf.getInt32(4)) | 0; }
        if (v.t.size === 8) { const b = BigInt.asUintN(64, BigInt(v.v)); return Number(BigInt.asIntN(32, b ^ (b >> 32n))); }
        return v.v | 0;
      case 'string': { let h = 0; for (let i = 0; i < v.v.length; i++) h = (Math.imul(31, h) + v.v.charCodeAt(i)) | 0; return h; }
      case 'ptr': {
        if (v.v.blk && v.v.blk.type && v.v.blk.type.k === 'struct') { const hm = this.findMethods(v.v.blk.type, 'hashCode'); if (hm) return this.convert(this.callMethod(hm, [], v.v, this.curLine), T.int).v; }
        return this.objHash(v.v);
      }
      case 'cont': { let h = 1; for (const x of this.contItems(v.v)) h = (Math.imul(31, h) + this.javaHash(x)) | 0; return h; }
    }
    return 0;
  };
  P.mapEntries = function (m) {
    const ents = [...m.map.values()];
    const c = m.ctype;
    if (c === 'map' || c === 'TreeMap' || c === 'set' || c === 'TreeSet' || c === 'multiset' || c === 'multimap') {
      const cmp = this.makeComparator(m.cmpFn);
      return this.mergeSort(ents, (a, b) => cmp(a.k, b.k));
    }
    if (c === 'HashMap' || c === 'HashSet') {
      const cap = m.cap || 16;
      const bucket = (e) => { if (e.h === undefined) { const h = this.javaHash(e.k); e.h = (h ^ (h >>> 16)); } return e.h & (cap - 1); };
      return ents.sort((a, b) => (bucket(a) - bucket(b)) || (a.seq - b.seq));
    }
    if (c === 'unordered_map' || c === 'unordered_set') return ents.sort((a, b) => b.seq - a.seq);
    return ents.sort((a, b) => a.seq - b.seq);
  };
  P.mapSet = function (m, kv, vv) {
    DSV.clikeRT.bump();
    const key = this.keyOf(kv);
    const ex = m.map.get(key);
    if (ex) { ex.v = vv; return ex; }
    const en = { k: this.elemVal(kv, m.t.args[0]), v: vv, seq: ++m.seq };
    m.map.set(key, en);
    if (m.ctype === 'HashMap' || m.ctype === 'HashSet') { if (!m.cap) m.cap = 16; while (m.map.size > m.cap * 0.75) m.cap *= 2; }
    return en;
  };
  P.mapGetLV = function (lv) {
    const en = lv.obj.map.get(this.keyOf(lv.key));
    if (!en) return this.defaultElem(lv.t);
    if (en.v.t.k === 'struct') return { t: en.v.t, v: new MemLV(en.v.v, 0, en.v.t) };
    return en.v;
  };
  P.contAdd = function (m, v) {
    const kind = this.contKind(m);
    const et = m.t.args[0];
    if (kind === 'seq') { m.items.push(this.elemVal(v, et)); this.grow(m); return; }
    if (kind === 'heap') { this.heapPush(m, this.elemVal(v, et)); return; }
    if (kind === 'set') { const key = this.keyOf(v); if (!m.map.has(key) || m.ctype === 'multiset') this.mapSet(m, v, null); return; }
    if (kind === 'map') {
      const parts = v.t.k === 'cont' && v.v ? this.pairParts(v.v) : null;
      if (!parts) throw new RunError('map 的元素需要是键值对 {key, value}', 'runtime');
      if (!m.map.has(this.keyOf(parts[0]))) this.mapSet(m, parts[0], this.elemVal(parts[1], m.t.args[1]));
      return;
    }
    m.items.push(this.elemVal(v, et));
  };
  P.grow = function (m) {
    if (m.ctype !== 'vector') return;
    if (m.items.length > m.cap) {
      const old = m.cap;
      m.cap = Math.max(1, m.cap * 2);
      while (m.cap < m.items.length) m.cap *= 2;
      if (old) this.rec.note('vector 容量不够了：重新分配了一块 ' + m.cap + ' 个元素的内存，并把旧元素复制过去（容量 ' + old + ' → ' + m.cap + '）', 'alloc');
    }
  };
  // binary heap (min or max)
  P.heapCmp = function (m) {
    if (m.cmpFn) { const c = this.makeComparator(m.cmpFn); return this.cpp ? (a, b) => -c(a, b) : c; }
    if (this.java) return (a, b) => this.compareVals(a, b);
    return m.cmp === 'min' ? (a, b) => this.compareVals(a, b) : (a, b) => this.compareVals(b, a);
  };
  P.heapPush = function (m, v) {
    const a = m.items; const cmp = this.heapCmp(m);
    a.push(v);
    let i = a.length - 1;
    while (i > 0) { const p = (i - 1) >> 1; if (cmp(a[i], a[p]) >= 0) break; [a[i], a[p]] = [a[p], a[i]]; i = p; }
  };
  P.heapPop = function (m) {
    const a = m.items; const cmp = this.heapCmp(m);
    const top = a[0];
    const last = a.pop();
    if (a.length) {
      a[0] = last;
      let i = 0;
      for (;;) { const l = 2 * i + 1, r = l + 1; let s = i; if (l < a.length && cmp(a[l], a[s]) < 0) s = l; if (r < a.length && cmp(a[r], a[s]) < 0) s = r; if (s === i) break; [a[i], a[s]] = [a[s], a[i]]; i = s; }
    }
    return top;
  };

  P.contIndexLV = function (base, idxV, e) {
    const m = base.v;
    if (!m) throw new RunError('容器还没有被创建', 'segfault');
    const kind = this.contKind(m);
    if (kind === 'map') {
      const key = idxV;
      if (!m.map.has(this.keyOf(key))) this.mapSet(m, key, this.defaultElem(m.t.args[1]));
      return new MapLV(m, key, m.t.args[1]);
    }
    if (kind !== 'seq') throw new RunError(m.ctype + ' 不支持 [] 下标访问', 'runtime');
    const i = this.convert(idxV, T.long).v;
    return new ElemLV(m, i, m.t.args[0]);
  };
  P.contMemberLV = function (objV, e) {
    const m = objV.v;
    if (objV.t.k === 'iter') {
      const tgt = this.iterLV(m);
      const v = this.load(tgt);
      return this.memberLV({ type: 'Member', obj: { type: '__val', val: v }, name: e.name, arrow: v.t.k === 'ptr', line: e.line });
    }
    if (m.ctype === 'pair' || m.ctype === 'Entry') {
      if (e.name === 'first') return new ElemLV(m, 0, m.items[0].t);
      if (e.name === 'second') return new ElemLV(m, 1, m.items[1].t);
    }
    if (m.ctype === 'mapentry') {
      if (e.name === 'first') return new TmpLV(m.entry.k);
      if (e.name === 'second') return new MapLV(m.map, m.entry.k, m.map.t.args[1]);
    }
    throw new RunError(m.ctype + ' 没有成员 ' + e.name, 'runtime');
  };
  P.iterLV = function (it) {
    if (it.slv) return new StrCharLV(it.slv, it.idx, T.char);
    if (it.mapIt) {
      const ents = this.mapEntries(it.obj);
      const en = ents[it.idx];
      if (!en) throw new RunError('解引用了 end() 迭代器（越界）', 'oob');
      if (this.contKind(it.obj) === 'set') return new TmpLV(en.k);
      return new TmpLV({ t: { k: 'cont', name: 'mapentry', args: [] }, v: this.entryObj(it.obj, en) });
    }
    if (it.idx < 0 || it.idx >= it.obj.items.length) throw new RunError('解引用了越界的迭代器（例如 end()）', 'oob', 'end() 指向最后一个元素的“下一个位置”，不能解引用。');
    return new ElemLV(it.obj, it.idx, it.obj.t.args[0]);
  };
  P.iterAdvance = function (it, d) { return Object.assign({}, it, { idx: it.idx + d }); };
  P.iterIndex = function (v) { if (v.t.k === 'iter') return v.v.idx; if (v.t.k === 'ptr') return v.v.off / this.sizeOf(v.t.to); return v.v; };
  P.iterBinop = function (op, a, b) {
    if (a.t.k === 'iter' && b.t.k === 'prim') {
      if (op === '+') return { t: a.t, v: this.iterAdvance(a.v, b.v) };
      if (op === '-') return { t: a.t, v: this.iterAdvance(a.v, -b.v) };
    }
    if (a.t.k === 'iter' && b.t.k === 'iter') {
      const x = a.v.idx, y = b.v.idx;
      if (op === '-') return { t: T.long, v: x - y };
      return this.mkBool(this.cmpOp(op, x - y));
    }
    throw new RunError('不支持对迭代器使用 ' + op, 'runtime');
  };

  P.newListOf = function (ctype, vals) {
    const m = this.newMObj(ctype, T.cont(ctype, [T.any]));
    m.items = vals.map(v => this.elemVal(v, T.any));
    return m;
  };
  P.newJavaCont = function (t, args) {
    const m = this.newMObj(t.name, t);
    if (t.name === 'Scanner' || t.name === 'Random') { m.hidden = true; if (t.name === 'Random') m.rng = DSV.makeRng(args[0] ? args[0].v : 42); return m; }
    if (t.name === 'StringBuilder') { m.str = args[0] && args[0].t.k === 'string' ? args[0].v : ''; return m; }
    const kind = this.contKind(m);
    for (const a of args) {
      if (a.t.k === 'lambda') m.cmpFn = a;
      else if (a.t.k === 'cont' && a.v) {
        if (kind === 'map' && this.contKind(a.v) === 'map') { for (const en of this.mapEntries(a.v)) this.mapSet(m, en.k, en.v); }
        else for (const v of this.contItems(a.v)) this.contAdd(m, v);
      }
    }
    return m;
  };

  // ---------- container methods ----------
  P.contMethod = function (objV, name, argEs, e, discard) {
    DSV.clikeRT.bump();
    const m = objV.v;
    if (objV.t.k === 'iter') {
      if (name === 'first' || name === 'second') { }
      throw new RunError('迭代器不支持方法 ' + name, 'runtime');
    }
    if (m.ctype === 'mapentry') {
      if (name === 'getKey') return m.entry.k;
      if (name === 'getValue') return m.entry.v.t.k === 'struct' ? { t: m.entry.v.t, v: new MemLV(m.entry.v.v, 0, m.entry.v.t) } : m.entry.v;
      if (name === 'setValue') { const v = this.ev(argEs[0]); m.entry.v = this.elemVal(v, m.map.t.args[1]); return v; }
    }
    // lambdas need evaluated args; for removeIf etc
    const args = argEs.map(a => a.type ? this.ev(a) : a);
    if (m.ctype === 'StringBuilder') return this.sbMethod(m, name, args);
    if (m.ctype === 'Scanner') return this.scannerMethod(m, name, args);
    if (m.ctype === 'Random') { if (name === 'nextInt') return { t: T.int, v: args.length ? m.rng() % args[0].v : m.rng() }; if (name === 'nextDouble') return { t: T.double, v: m.rng() / 2147483648 }; if (name === 'nextBoolean') return this.mkBool(m.rng() & 1); }
    if (m.ctype === 'pair' || m.ctype === 'Entry') {
      if (name === 'getKey') return m.items[0]; if (name === 'getValue') return m.items[1];
    }
    const kind = this.contKind(m);
    const et = m.t.args[0];
    const items = m.items;
    const I = (v) => ({ t: T.int, v });
    const SZ = (v) => this.java ? I(v) : { t: T.size_t, v };
    const B = (b) => this.mkBool(b);
    const V = { t: T.void, v: 0 };
    const getItem = (i) => { const it = items[i]; return it.t.k === 'struct' ? { t: it.t, v: new MemLV(it.v, 0, it.t) } : it; };
    const emptyErr = (what) => {
      if (this.java) {
        if (['pop', 'peek', 'firstElement', 'lastElement'].includes(what) && m.ctype === 'Stack') throw new RunError('EmptyStackException：栈是空的，不能 ' + what + '()', 'runtime', '调用前先用 isEmpty() 检查。');
        throw new RunError('NoSuchElementException：' + m.ctype + ' 是空的，不能调用 ' + what + '()', 'runtime', '调用前先用 isEmpty() 检查。');
      }
      throw new RunError('对空的 ' + m.ctype + ' 调用了 ' + what + '()——这在 C++ 里是未定义行为，通常会导致程序崩溃。', 'oob', '调用前先用 empty() 检查容器是否为空。');
    };
    const name2 = name;
    // common
    switch (name2) {
      case 'size': return SZ(kind === 'map' || kind === 'set' ? m.map.size : items.length);
      case 'length': return SZ(items.length);
      case 'empty': return B((kind === 'map' || kind === 'set' ? m.map.size : items.length) === 0);
      case 'isEmpty': return B((kind === 'map' || kind === 'set' ? m.map.size : items.length) === 0);
      case 'clear': if (m.map) m.map.clear(); m.items = []; return V;
      case 'toString': return { t: T.jstring, v: this.javaStr(objV) };
      case 'hashCode': return I(this.javaHash(objV));
      case 'equals': return B(args[0].t.k === 'cont' && this.keyOf(objV) === this.keyOf(args[0]));
      case 'forEach': {
        for (const it of this.contItems(m)) {
          if (it.t.name === 'mapentry') this.callValue(args[0], [it.v.entry.k, it.v.entry.v], e.line);
          else this.callValue(args[0], [it], e.line);
        }
        return V;
      }
      case 'stream': return { t: m.t, v: m };
      case 'iterator': { const it = this.newMObj('Iterator', T.cont('Iterator', [])); it.hidden = true; it.src = this.contItems(m); it.pos = 0; it.owner = m; return { t: it.t, v: it }; }
      case 'hasNext': return B(m.pos < m.src.length);
      case 'next': if (m.ctype === 'Iterator') { if (m.pos >= m.src.length) emptyErr('next'); return m.src[m.pos++]; } break;
    }
    if (kind === 'seq') {
      switch (name2) {
        case 'push_back': case 'emplace_back': case 'add': case 'addLast': case 'offer': case 'offerLast': case 'addElement': {
          if (name2 === 'add' && args.length === 2) { const i = this.argNum(args[0]); if (i < 0 || i > items.length) this.boundsErr(m, i); items.splice(i, 0, this.elemVal(args[1], et)); return V; }
          if (m.ctype === 'stack' || m.ctype === 'queue') break;
          const v = name2 === 'emplace_back' && et && et.k === 'struct' ? this.evConstruct({ ty: et, args: argEs, brace: false }) : (name2 === 'emplace_back' && et && et.k === 'cont' && args.length !== 1 ? { t: et, v: this.constructCont(et, args), fresh: true } : args[0]);
          items.push(this.elemVal(v, et)); this.grow(m);
          return this.java ? B(true) : V;
        }
        case 'push_front': case 'emplace_front': case 'addFirst': case 'offerFirst': items.unshift(this.elemVal(args[0], et)); return V;
        case 'push': case 'emplace':
          if (m.ctype === 'Stack') { items.push(this.elemVal(args[0], et)); return args[0]; }
          if (m.ctype === 'ArrayDeque' || m.ctype === 'Deque' || m.ctype === 'LinkedList') { items.unshift(this.elemVal(args[0], et)); return V; }
          items.push(this.elemVal(name2 === 'emplace' && et && et.k === 'struct' ? this.evConstruct({ ty: et, args: argEs }) : args[0], et)); return V;
        case 'pop_back': case 'removeLast': case 'pollLast': {
          if (!items.length) { if (name2 === 'pollLast') return { t: T.any, v: null }; emptyErr(name2); }
          const v = items.pop(); return this.java ? v : V;
        }
        case 'pop_front': case 'removeFirst': case 'pollFirst': case 'poll': case 'remove': {
          if (name2 === 'remove' && args.length) {
            const a = args[0];
            if (a.t.k === 'prim' && !a.t.isChar && (m.ctype === 'ArrayList' || m.ctype === 'LinkedList' || m.ctype === 'List' || m.ctype === 'Vector')) { const i = a.v; if (i < 0 || i >= items.length) this.boundsErr(m, i); return items.splice(i, 1)[0]; }
            const idx = items.findIndex(x => this.keyOf(x) === this.keyOf(a));
            if (idx >= 0) items.splice(idx, 1);
            return B(idx >= 0);
          }
          if (!items.length) { if (name2 === 'poll' || name2 === 'pollFirst') return { t: T.any, v: null, isNull: true }; emptyErr(name2); }
          const v = items.shift(); return this.java ? v : V;
        }
        case 'pop': {
          if (!items.length) emptyErr('pop');
          if (m.ctype === 'queue' || m.ctype === 'ArrayDeque' || m.ctype === 'Deque' || m.ctype === 'LinkedList') { const v = items.shift(); return this.java ? v : V; }
          const v = items.pop(); return this.java ? v : V;
        }
        case 'top': if (!items.length) emptyErr('top'); return Object.assign(getItem(items.length - 1), { lv: new ElemLV(m, items.length - 1, et) });
        case 'back': case 'getLast': case 'peekLast': case 'lastElement': if (!items.length) { if (name2 === 'peekLast') return { t: T.any, v: null }; emptyErr(name2); } return Object.assign(getItem(items.length - 1), { lv: new ElemLV(m, items.length - 1, et) });
        case 'front': case 'getFirst': case 'peekFirst': case 'element': case 'firstElement': if (!items.length) { if (name2 === 'peekFirst') return { t: T.any, v: null }; emptyErr(name2); } return Object.assign(getItem(0), { lv: new ElemLV(m, 0, et) });
        case 'peek': {
          if (!items.length) { if (m.ctype === 'Stack') emptyErr('peek'); return { t: T.any, v: null, isNull: true }; }
          if (m.ctype === 'Stack') return getItem(items.length - 1);
          return getItem(0);
        }
        case 'search': { const i = items.map(x => this.keyOf(x)).lastIndexOf(this.keyOf(args[0])); return I(i < 0 ? -1 : items.length - i); }
        case 'get': case 'at': case 'elementAt': {
          const i = this.argNum(args[0]);
          if (i < 0 || i >= items.length) { if (this.cpp) { const er = new RunError('out_of_range：vector::at 的下标 ' + i + ' 超出范围（size = ' + items.length + '）', 'oob', '下标范围是 0 ~ size()-1。'); er.cppExc = 'out_of_range'; throw er; } this.boundsErr(m, i); }
          return Object.assign(getItem(i), { lv: new ElemLV(m, i, et) });
        }
        case 'set': { const i = this.argNum(args[0]); if (i < 0 || i >= items.length) this.boundsErr(m, i); const old = items[i]; items[i] = this.elemVal(args[1], et); return old; }
        case 'contains': return B(items.some(x => this.keyOf(x) === this.keyOf(args[0])));
        case 'indexOf': return I(items.findIndex(x => this.keyOf(x) === this.keyOf(args[0])));
        case 'lastIndexOf': return I(items.map(x => this.keyOf(x)).lastIndexOf(this.keyOf(args[0])));
        case 'addAll': { const src = args[args.length - 1]; const vals = this.contItems(src.v); if (args.length === 2) items.splice(this.argNum(args[0]), 0, ...vals.map(v => this.elemVal(v, et))); else for (const v of vals) items.push(this.elemVal(v, et)); return B(true); }
        case 'removeIf': { const before = items.length; m.items = items.filter(x => !this.truthy(this.callValue(args[0], [x], e.line))); return B(m.items.length !== before); }
        case 'sort': { const cmp = this.makeComparator(args[0] && args[0].v ? args[0] : null); const order = items.map((_, i) => i); this.mergeSort(order, (a, b) => cmp(getItem(a), getItem(b))); m.items = order.map(i => items[i]); return V; }
        case 'reversed': return { t: m.t, v: Object.assign(this.cloneCont(m), { items: items.slice().reverse() }) };
        case 'subList': { const n = this.newMObj('ArrayList', m.t); n.items = items.slice(this.argNum(args[0]), this.argNum(args[1])); return { t: m.t, v: n }; }
        case 'toArray': return { t: T.ptr(T.any, { jarr: true }), v: this.makeJavaArray(T.any, items) };
        case 'resize': { const n = this.argNum(args[0]); while (items.length > n) items.pop(); while (items.length < n) items.push(args[1] ? this.elemVal(args[1], et) : this.defaultElem(et)); if (n > m.cap) m.cap = n; return V; }
        case 'reserve': { const n = this.argNum(args[0]); if (n > m.cap) m.cap = n; return V; }
        case 'capacity': return SZ(Math.max(m.cap, items.length));
        case 'shrink_to_fit': m.cap = items.length; return V;
        case 'assign': { const n = this.argNum(args[0]); m.items = []; for (let i = 0; i < n; i++) m.items.push(this.elemVal(args[1], et)); return V; }
        case 'begin': case 'cbegin': return { t: { k: 'iter' }, v: { obj: m, idx: 0 } };
        case 'end': case 'cend': return { t: { k: 'iter' }, v: { obj: m, idx: items.length } };
        case 'rbegin': return { t: { k: 'iter' }, v: { obj: m, idx: items.length - 1, rev: true } };
        case 'insert': case 'emplace': {
          const it = args[0];
          if (it.t.k !== 'iter') throw new RunError('insert 的第一个参数需要是迭代器，例如 v.begin() + i', 'runtime');
          if (it.v.idx < 0 || it.v.idx > items.length) throw new RunError('insert 的位置越界', 'oob');
          if (args.length === 3) { const n = this.argNum(args[1]); for (let k = 0; k < n; k++) items.splice(it.v.idx, 0, this.elemVal(args[2], et)); }
          else items.splice(it.v.idx, 0, this.elemVal(args[1], et));
          this.grow(m);
          return { t: { k: 'iter' }, v: { obj: m, idx: it.v.idx } };
        }
        case 'erase': {
          const it = args[0];
          if (it.t.k !== 'iter') throw new RunError('erase 的参数需要是迭代器，例如 v.begin() + i', 'runtime');
          const i0 = it.v.idx, i1 = args[1] ? args[1].v.idx : i0 + 1;
          if (i0 < 0 || i1 > items.length) throw new RunError('erase 的位置越界（size = ' + items.length + '）', 'oob');
          items.splice(i0, i1 - i0);
          return { t: { k: 'iter' }, v: { obj: m, idx: i0 } };
        }
        case 'swap': { const o = args[0].v; [m.items, o.items] = [o.items, m.items]; return V; }
        case 'descendingIterator': { const it = this.newMObj('Iterator', T.cont('Iterator', [])); it.hidden = true; it.src = items.slice().reverse(); it.pos = 0; return { t: it.t, v: it }; }
      }
    }
    if (kind === 'heap') {
      switch (name2) {
        case 'push': case 'emplace': case 'add': case 'offer': this.heapPush(m, this.elemVal(args[0], et)); return this.java ? B(true) : V;
        case 'pop': if (!items.length) emptyErr('pop'); this.heapPop(m); return V;
        case 'poll': case 'remove': if (!items.length) { if (name2 === 'poll') return { t: T.any, v: null, isNull: true }; emptyErr('remove'); } if (name2 === 'remove' && args.length) { const i = items.findIndex(x => this.keyOf(x) === this.keyOf(args[0])); if (i < 0) return B(false); const rest = items.filter((_, k) => k !== i); m.items = []; for (const x of rest) this.heapPush(m, x); return B(true); } return this.heapPop(m);
        case 'top': case 'peek': case 'element': if (!items.length) { if (name2 === 'peek') return { t: T.any, v: null, isNull: true }; emptyErr(name2); } return getItem(0);
        case 'contains': return B(items.some(x => this.keyOf(x) === this.keyOf(args[0])));
        case 'addAll': for (const v of this.contItems(args[0].v)) this.heapPush(m, this.elemVal(v, et)); return B(true);
      }
    }
    if (kind === 'map') {
      const vt = m.t.args[1];
      const get = (k) => m.map.get(this.keyOf(k));
      const outV = (en) => en ? (en.v.t.k === 'struct' ? { t: en.v.t, v: new MemLV(en.v.v, 0, en.v.t) } : en.v) : { t: T.any, v: null, isNull: true };
      switch (name2) {
        case 'put': { const en = get(args[0]); const old = en ? en.v : null; this.mapSet(m, args[0], this.elemVal(args[1], vt)); return old || { t: T.any, v: null, isNull: true }; }
        case 'get': return outV(get(args[0]));
        case 'getOrDefault': { const en = get(args[0]); return en ? outV(en) : args[1]; }
        case 'containsKey': return B(!!get(args[0]));
        case 'containsValue': return B([...m.map.values()].some(en => this.keyOf(en.v) === this.keyOf(args[0])));
        case 'count': return SZ(get(args[0]) ? 1 : 0);
        case 'contains': return B(!!get(args[0]));
        case 'remove': case 'erase': {
          let k = args[0];
          if (k.t.k === 'iter' && k.v.mapIt) { const en = this.mapEntries(m)[k.v.idx]; if (en) k = en.k; }
          const key = this.keyOf(k); const en = m.map.get(key); m.map.delete(key);
          return this.java ? outV(en) : SZ(en ? 1 : 0);
        }
        case 'putIfAbsent': { const en = get(args[0]); if (!en) this.mapSet(m, args[0], this.elemVal(args[1], vt)); return outV(en); }
        case 'computeIfAbsent': { let en = get(args[0]); if (!en) { const v = this.callValue(args[1], [args[0]], e.line); en = this.mapSet(m, args[0], this.elemVal(v, vt)); } return outV(en); }
        case 'computeIfPresent': case 'compute': { const en = get(args[0]); if (name2 === 'computeIfPresent' && !en) return { t: T.any, v: null }; const v = this.callValue(args[1], [args[0], en ? en.v : { t: T.any, v: null, isNull: true }], e.line); if (v.v == null || v.isNull) { m.map.delete(this.keyOf(args[0])); return v; } this.mapSet(m, args[0], this.elemVal(v, vt)); return v; }
        case 'merge': { const en = get(args[0]); const v = en ? this.callValue(args[2], [en.v, args[1]], e.line) : args[1]; this.mapSet(m, args[0], this.elemVal(v, vt)); return v; }
        case 'keySet': { const s = this.newMObj('LinkedHashSet', T.cont('Set', [m.t.args[0]])); for (const en of this.mapEntries(m)) this.mapSet(s, en.k, null); s.view = true; return { t: s.t, v: s }; }
        case 'values': { const l = this.newMObj('ArrayList', T.cont('Collection', [vt])); l.items = this.mapEntries(m).map(en => en.v); l.view = true; return { t: l.t, v: l }; }
        case 'entrySet': { const l = this.newMObj('ArrayList', T.cont('Set', [])); l.items = this.mapEntries(m).map(en => ({ t: { k: 'cont', name: 'mapentry', args: [] }, v: this.entryObj(m, en) })); l.view = true; return { t: l.t, v: l }; }
        case 'insert': case 'emplace': {
          const kv = args.length === 2 ? [args[0], args[1]] : this.pairParts(args[0].v);
          const had = !!get(kv[0]);
          if (!had) this.mapSet(m, kv[0], this.elemVal(kv[1], vt));
          return { t: T.cont('pair', []), v: this.makePair({ t: { k: 'iter' }, v: { obj: m, mapIt: true, idx: this.mapEntries(m).findIndex(en => this.keyOf(en.k) === this.keyOf(kv[0])) } }, this.mkBool(!had)) };
        }
        case 'find': { const ents = this.mapEntries(m); const i = ents.findIndex(en => this.keyOf(en.k) === this.keyOf(args[0])); return { t: { k: 'iter' }, v: { obj: m, mapIt: true, idx: i < 0 ? ents.length : i } }; }
        case 'begin': return { t: { k: 'iter' }, v: { obj: m, mapIt: true, idx: 0 } };
        case 'end': return { t: { k: 'iter' }, v: { obj: m, mapIt: true, idx: m.map.size } };
        case 'at': { const en = get(args[0]); if (!en) { const er = new RunError('out_of_range：map::at 找不到键 ' + this.toDisplay(args[0]), 'oob'); er.cppExc = 'out_of_range'; throw er; } return Object.assign(outV(en), { lv: new MapLV(m, args[0], vt) }); }
        case 'firstKey': case 'lastKey': { const ents = this.mapEntries(m); if (!ents.length) emptyErr(name2); return ents[name2 === 'firstKey' ? 0 : ents.length - 1].k; }
        case 'floorKey': case 'ceilingKey': case 'lowerKey': case 'higherKey': { const ents = this.mapEntries(m); const k = args[0]; let best = null; for (const en of ents) { const c = this.compareVals(en.k, k); if (name2 === 'floorKey' && c <= 0 || name2 === 'lowerKey' && c < 0) best = en.k; if ((name2 === 'ceilingKey' && c >= 0 || name2 === 'higherKey' && c > 0) && !best) best = en.k; } return best || { t: T.any, v: null, isNull: true }; }
        case 'putAll': for (const en of this.mapEntries(args[0].v)) this.mapSet(m, en.k, en.v); return V;
      }
    }
    if (kind === 'set') {
      switch (name2) {
        case 'add': case 'insert': case 'emplace': { const had = m.map.has(this.keyOf(args[0])); if (!had || m.ctype === 'multiset') { if (m.ctype === 'multiset' && had) { const en = { k: this.elemVal(args[0], et), v: null, seq: ++m.seq }; m.map.set(this.keyOf(args[0]) + '#' + en.seq, en); } else this.mapSet(m, args[0], null); } return B(!had); }
        case 'contains': return B(m.map.has(this.keyOf(args[0])));
        case 'count': return SZ([...m.map.values()].filter(en => this.keyOf(en.k) === this.keyOf(args[0])).length);
        case 'remove': case 'erase': {
          let k = args[0];
          if (k.t.k === 'iter') { const en = this.mapEntries(m)[k.v.idx]; if (en) k = en.k; }
          const key = this.keyOf(k); const had = m.map.has(key); m.map.delete(key); return this.java ? B(had) : SZ(had ? 1 : 0);
        }
        case 'find': { const ents = this.mapEntries(m); const i = ents.findIndex(en => this.keyOf(en.k) === this.keyOf(args[0])); return { t: { k: 'iter' }, v: { obj: m, mapIt: true, idx: i < 0 ? ents.length : i } }; }
        case 'begin': return { t: { k: 'iter' }, v: { obj: m, mapIt: true, idx: 0 } };
        case 'end': return { t: { k: 'iter' }, v: { obj: m, mapIt: true, idx: m.map.size } };
        case 'addAll': { let ch = false; for (const v of this.contItems(args[0].v)) if (!m.map.has(this.keyOf(v))) { this.mapSet(m, v, null); ch = true; } return B(ch); }
        case 'retainAll': { const keep = new Set(this.contItems(args[0].v).map(v => this.keyOf(v))); for (const k of [...m.map.keys()]) if (!keep.has(k)) m.map.delete(k); return B(true); }
        case 'removeAll': { for (const v of this.contItems(args[0].v)) m.map.delete(this.keyOf(v)); return B(true); }
        case 'first': case 'last': { const ents = this.mapEntries(m); if (!ents.length) emptyErr(name2); return ents[name2 === 'first' ? 0 : ents.length - 1].k; }
        case 'pollFirst': { const ents = this.mapEntries(m); if (!ents.length) return { t: T.any, v: null }; m.map.delete(this.keyOf(ents[0].k)); return ents[0].k; }
      }
    }
    throw new RunError(m.ctype + ' 没有方法 ' + name + '()（或可视化器暂不支持）', 'runtime');
  };
  P.sbMethod = function (m, name, args) {
    const SB = { t: T.cont('StringBuilder', []), v: m };
    switch (name) {
      case 'append': m.str += this.javaStr(args[0]); return SB;
      case 'toString': return { t: T.jstring, v: m.str };
      case 'length': return { t: T.int, v: m.str.length };
      case 'charAt': { const i = args[0].v; if (i < 0 || i >= m.str.length) throw new RunError('StringIndexOutOfBoundsException：下标 ' + i + '，长度 ' + m.str.length, 'oob'); return { t: T.jchar, v: m.str.charCodeAt(i) }; }
      case 'reverse': m.str = [...m.str].reverse().join(''); return SB;
      case 'insert': m.str = m.str.slice(0, args[0].v) + this.javaStr(args[1]) + m.str.slice(args[0].v); return SB;
      case 'deleteCharAt': m.str = m.str.slice(0, args[0].v) + m.str.slice(args[0].v + 1); return SB;
      case 'delete': m.str = m.str.slice(0, args[0].v) + m.str.slice(args[1].v); return SB;
      case 'setCharAt': m.str = m.str.slice(0, args[0].v) + String.fromCharCode(args[1].v) + m.str.slice(args[0].v + 1); return { t: T.void, v: 0 };
      case 'setLength': m.str = m.str.slice(0, args[0].v).padEnd(args[0].v, '\0'); return { t: T.void, v: 0 };
      case 'indexOf': return { t: T.int, v: m.str.indexOf(args[0].v) };
      case 'isEmpty': return this.mkBool(!m.str.length);
    }
    throw new RunError('StringBuilder 没有方法 ' + name, 'runtime');
  };
  P.scannerMethod = function (m, name, args) {
    const need = () => { throw new RunError('NoSuchElementException：Scanner 需要读取输入，但“标准输入”框里的内容已经读完了。', 'runtime', '在页面上的“输入 (stdin)”框里写上程序要读取的数据。'); };
    switch (name) {
      case 'nextInt': case 'nextLong': case 'nextShort': { const t = this.stdin.token(); if (t === null) need(); if (!/^[-+]?\d+$/.test(t)) throw new RunError('InputMismatchException：输入 "' + t + '" 不是整数', 'runtime'); this.rec.write(''); return { t: name === 'nextLong' ? T.long : T.int, v: parseInt(t, 10) }; }
      case 'nextDouble': case 'nextFloat': { const t = this.stdin.token(); if (t === null) need(); return { t: T.double, v: parseFloat(t) }; }
      case 'next': { const t = this.stdin.token(); if (t === null) need(); return { t: T.jstring, v: t }; }
      case 'nextBoolean': { const t = this.stdin.token(); if (t === null) need(); return this.mkBool(t.toLowerCase() === 'true'); }
      case 'nextLine': { const l = this.stdin.line(); if (l === null) need(); return { t: T.jstring, v: l }; }
      case 'hasNext': case 'hasNextInt': case 'hasNextLine': { const save = this.stdin.pos; this.stdin.skipWs(); const ok = !this.stdin.eof(); let r = ok; if (ok && name === 'hasNextInt') { const t = this.stdin.token(); r = /^[-+]?\d+$/.test(t); } this.stdin.pos = save; if (name === 'hasNextLine') r = save < this.stdin.text.length; return this.mkBool(r); }
      case 'close': return { t: T.void, v: 0 };
    }
    throw new RunError('Scanner 没有方法 ' + name, 'runtime');
  };

  // ---------- for-each ----------
  P.execForEach = function (s) {
    this.pushScope();
    const depth = this.frame.scopes.length;
    this.step(s.line);
    const iv = this.ev(s.iter);
    let src = iv.t.k === 'any' ? iv.v : iv;
    let getters;
    if (src.t.k === 'cont') {
      const m = src.v;
      if (!m) throw new RunError((this.java ? 'NullPointerException：' : '') + '遍历的集合是 null', 'segfault');
      const kind = this.contKind(m);
      if (kind === 'seq' || m.ctype === 'pair') getters = m.items.map((_, i) => () => ({ lv: new ElemLV(m, i, m.t.args[0]) }));
      else getters = this.contItems(m).map(v => () => ({ val: v }));
    } else if (src.t.k === 'ptr' && (src.t.jarr || src.arrDecay) || src.t.k === 'ptr' && src.v.blk && src.v.blk.type && src.v.blk.type.k === 'arr') {
      const blk = src.v.blk;
      if (!blk) throw new RunError((this.java ? 'NullPointerException：' : '') + '遍历的数组是 null', 'segfault');
      const at = src.arrDecay || blk.type;
      const et = src.t.to, es = this.sizeOf(et);
      const n = src.arrDecay ? src.arrDecay.len : at.len;
      getters = []; for (let i = 0; i < n; i++) getters.push(() => ({ lv: new MemLV(blk, src.v.off + i * es, et, true) }));
    } else if (src.t.k === 'string') {
      const str = src.v;
      getters = [...str].map((c, i) => () => ({ val: { t: this.java ? T.jchar : T.char, v: c.charCodeAt(0) } }));
    } else if (src.t.k === 'initlist') {
      getters = src.v.map(v => () => ({ val: v }));
    } else throw new RunError('这个值不能用于 for-each 遍历：' + T.name(src.t), 'runtime');
    let result = null;
    let first = true;
    for (const g of getters) {
      if (!first) this.step(s.line);
      first = false;
      this.pushScope();
      const it = g();
      if (Array.isArray(s.name)) {
        const val = it.val || this.load(it.lv);
        const parts = val.t.k === 'cont' ? (val.v.ctype === 'mapentry' ? [val.v.entry.k, val.v.entry.v] : this.pairParts(val.v)) : [];
        s.name.forEach((n, i) => {
          if (s.isRef && val.t.k === 'cont' && val.v.ctype === 'mapentry' && i === 1) this.declareVar(n, T.ref(val.v.map.t.args[1] || parts[1].t), s.line, { lv: new MapLV(val.v.map, val.v.entry.k, val.v.map.t.args[1]) });
          else { const v = this.declareVar(n, parts[i].t, s.line); this.storeInit(this.varLV(v), parts[i]); }
        });
      } else if (s.isRef && it.lv) {
        let t = s.vtype;
        if (t.k === 'auto') t = this.load(it.lv).t;
        this.declareVar(s.name, T.ref(t), s.line, { lv: it.lv });
      } else if (s.isRef && it.val && it.val.t.k === 'cont' && it.val.v && it.val.v.ctype === 'mapentry') {
        const v = this.declareVar(s.name, it.val.t, s.line); this.writeCell(v.blk, 0, it.val.t, it.val.v);
      } else {
        const val = it.val || this.load(it.lv);
        let t = s.vtype.k === 'auto' ? val.t : s.vtype;
        if (val.t.k === 'cont' && val.v && val.v.ctype === 'mapentry') t = val.t;
        if (t.k === 'nullptr') t = T.any;
        const v = this.declareVar(s.name, t, s.line);
        if (t.k === 'cont' && val.v && val.v.ctype === 'mapentry') this.writeCell(v.blk, 0, t, val.v);
        else this.storeInit(this.varLV(v), val);
      }
      const r = this.execSub(s.body);
      this.popScope();
      if (r === BREAK) break;
      if (r && r !== CONTINUE) { result = r; break; }
    }
    while (this.frame.scopes.length >= depth) this.popScope();
    return result;
  };
  const { BREAK, CONTINUE } = DSV.clikeRT;

  // ======================= Java library =======================
  P.javaDouble = function (v, isFloat) {
    if (isNaN(v)) return 'NaN';
    if (!isFinite(v)) return v > 0 ? 'Infinity' : '-Infinity';
    if (v === 0) return Object.is(v, -0) ? '-0.0' : '0.0';
    let s;
    if (isFloat) { for (let p = 1; p <= 9; p++) { const c = parseFloat(v.toPrecision(p)); if (Math.fround(c) === v) { s = String(c); break; } } if (!s) s = String(v); }
    else s = String(v);
    const a = Math.abs(v);
    if (a >= 1e-3 && a < 1e7) {
      if (s.includes('e')) s = Number(s).toFixed(20).replace(/0+$/, '');
      if (!s.includes('.')) s += '.0';
      return s;
    }
    let [mant, ex] = Number(s).toExponential().split('e');
    if (!mant.includes('.')) mant += '.0';
    return mant + 'E' + ex.replace('+', '');
  };
  P.javaStr = function (v) {
    if (v == null) return 'null';
    const t = v.t;
    switch (t.k) {
      case 'string': return v.v == null ? 'null' : v.v;
      case 'prim':
        if (t.isBool) return v.v ? 'true' : 'false';
        if (t.isChar) return String.fromCharCode(v.v);
        if (t.fl) return this.javaDouble(v.v, t.size === 4);
        return String(v.v);
      case 'any': return v.v == null ? 'null' : this.javaStr(v.v);
      case 'nullptr': return 'null';
      case 'ptr': {
        const p = v.v;
        if (!p || !p.blk) return 'null';
        const blk = p.blk;
        if (blk.type && blk.type.k === 'arr') {
          const et = blk.type.of;
          const code = et.k === 'prim' ? ({ int: 'I', double: 'D', char: 'C', boolean: 'Z', long: 'J', float: 'F', short: 'S', byte: 'B' })[et.name] : 'L' + (et.k === 'string' ? 'java.lang.String' : (et.to ? et.to.name : 'Object')) + ';';
          return '[' + code + '@' + this.objHash(p).toString(16);
        }
        const st = blk.type;
        if (st && st.k === 'struct') {
          if (blk.isEnum) return st.enumConsts[blk.enumIdx];
          const ms = this.findMethods(st, 'toString');
          if (ms) return this.javaStr(this.callMethod(ms, [], p, this.curLine));
          if (st.isRecord) return st.name + '[' + st.fields.map(f => f.name + '=' + this.javaStr(this.load(new MemLV(blk, f.offset, f.type)))).join(', ') + ']';
          if (st.builtin) { const f = this.findField(st, 'message'); const m = this.peekCell(blk, f.offset, f.type); return 'java.lang.' + st.name + (m != null ? ': ' + m : ''); }
          return st.name + '@' + this.objHash(p).toString(16);
        }
        return 'Object@' + this.objHash(p).toString(16);
      }
      case 'cont': {
        const m = v.v;
        if (!m) return 'null';
        if (m.ctype === 'StringBuilder') return m.str;
        if (m.ctype === 'mapentry') return this.javaStr(m.entry.k) + '=' + this.javaStr(m.entry.v);
        const kind = this.contKind(m);
        if (kind === 'map') return '{' + this.mapEntries(m).map(en => this.javaStr(en.k) + '=' + this.javaStr(en.v)).join(', ') + '}';
        return '[' + this.contItems(m).map(x => this.javaStr(x)).join(', ') + ']';
      }
      case 'lambda': return 'Lambda@' + (Math.random() * 1e6 | 0).toString(16);
      case 'class': return 'class ' + t.st.name;
    }
    return String(v.v);
  };
  P.javaPrint = function (name, args, e) {
    switch (name) {
      case 'println': this.rec.write((args.length ? this.javaPrintArg(args[0]) : '') + '\n'); return { t: T.void, v: 0 };
      case 'print': this.rec.write(this.javaPrintArg(args[0])); return { t: T.void, v: 0 };
      case 'printf': case 'format': this.rec.write(this.javaFormat(args)); return { t: T.void, v: 0 };
      case 'flush': return { t: T.void, v: 0 };
    }
    throw new RunError('System.out 没有方法 ' + name, 'runtime');
  };
  P.javaPrintArg = function (v) {
    if (v.t.k === 'ptr' && v.t.jarr && v.t.to.k === 'prim' && v.t.to.isChar && v.v.blk) { let s = ''; const blk = v.v.blk; for (let i = 0; i < blk.type.len; i++) s += String.fromCharCode(this.peekCell(blk, i * 2, T.jchar) || 0); return s; }
    return this.javaStr(v);
  };
  P.javaFormat = function (args) {
    const fmt = this.javaStr(args[0]);
    let rest = args.slice(1);
    if (rest.length === 1 && rest[0].t.k === 'ptr' && rest[0].t.jarr && rest[0].t.to.k !== 'prim') { const blk = rest[0].v.blk; rest = []; for (let i = 0; i < blk.type.len; i++) rest.push(this.load(new MemLV(blk, i * 8, blk.type.of))); }
    let i = 0;
    return DSV.formatPrintf(fmt, (kind) => {
      let a = rest[i++];
      if (!a) throw new RunError('MissingFormatArgumentException：格式字符串需要的参数比给的多', 'runtime');
      if (a.t.k === 'any') a = a.v || { t: T.nullptr, v: NULLP };
      if (kind === 'str' || kind === 'bool') return this.javaStr(a);
      if (kind === 'char') return a.t.k === 'prim' ? String.fromCharCode(a.v) : this.javaStr(a);
      if (kind === 'float' && a.t.k === 'prim' && !a.t.fl) throw new RunError('IllegalFormatConversionException：%f 不能用于整数 ' + a.v + '（Java 不会自动转换）', 'runtime', '整数用 %d，小数用 %f；或者写成 (double) x。');
      if (kind === 'int' && a.t.k === 'prim' && a.t.fl) throw new RunError('IllegalFormatConversionException：%d 不能用于小数 ' + a.v, 'runtime', '小数用 %f 或 %.2f。');
      return a.v;
    });
  };
  P.javaPrimMethod = function (v, name, args) {
    switch (name) {
      case 'equals': { const o = args[0].t.k === 'any' ? args[0].v : args[0]; return this.mkBool(o && o.t.k === 'prim' && o.v === v.v && !!o.t.fl === !!v.t.fl); }
      case 'compareTo': case 'compare': { const o = this.unboxAny(args[0]); return { t: T.int, v: v.v < o.v ? -1 : v.v > o.v ? 1 : 0 }; }
      case 'intValue': return { t: T.int, v: this.wrapInt(Math.trunc(v.v), T.int) };
      case 'longValue': return { t: T.long, v: Math.trunc(v.v) };
      case 'doubleValue': return { t: T.double, v: v.v };
      case 'toString': return { t: T.jstring, v: this.javaStr(v) };
      case 'hashCode': return { t: T.int, v: this.javaHash(v) };
      case 'charValue': return { t: T.jchar, v: v.v };
      case 'booleanValue': return this.mkBool(v.v);
    }
    throw new RunError(T.name(v.t) + ' 没有方法 ' + name + '()', 'runtime');
  };
  P.javaArrayMethod = function (objV, name, args) {
    if (name === 'clone') {
      const blk = objV.v.blk;
      const nb = this.newBlock('heap', blk.size, blk.type, ''); nb.zero = true; nb.typed = true; nb.jarr = true;
      for (const [o, c] of blk.cells) nb.cells.set(o, c);
      return { t: objV.t, v: new Ptr(nb, 0) };
    }
    if (name === 'equals') return this.mkBool(args[0].v && args[0].v.blk === objV.v.blk);
    if (name === 'length') throw new RunError('数组的长度是属性 arr.length，不是方法 arr.length()', 'runtime', '去掉括号：arr.length。字符串的长度才是方法 s.length()。');
    throw new RunError('数组没有方法 ' + name + '()', 'runtime');
  };
  P.arrValues = function (av) {
    const blk = av.v.blk;
    if (!blk) throw new RunError('NullPointerException：数组是 null', 'segfault');
    const et = blk.type.of, es = this.sizeOf(et);
    const out = [];
    for (let i = 0; i < blk.type.len; i++) out.push(this.load(new MemLV(blk, i * es, et)));
    return { vals: out, set: (vals, from) => vals.forEach((v, i) => this.store(new MemLV(blk, ((from || 0) + i) * es, et), v)), et, blk };
  };
  P.javaStaticCall = function (cls, name, argEs, e) {
    const args = argEs.map(a => this.ev(a));
    const num = (i) => this.argNum(args[i]);
    const I = (v) => ({ t: T.int, v });
    const D = (v) => ({ t: T.double, v });
    const S = (v) => ({ t: T.jstring, v });
    const B = (b) => this.mkBool(b);
    const key = cls + '.' + name;
    switch (key) {
      case 'Math.max': case 'Math.min': { const a = this.unboxAny(args[0]), b = this.unboxAny(args[1]); const rt = this.arithType(a.t, b.t); const r = name === 'max' ? Math.max(a.v, b.v) : Math.min(a.v, b.v); return { t: rt, v: r }; }
      case 'Math.abs': { const a = this.unboxAny(args[0]); return { t: a.t.fl ? a.t : this.promote(a.t), v: a.t.fl ? Math.abs(a.v) : this.wrapInt(Math.abs(a.v), this.promote(a.t)) }; }
      case 'Math.sqrt': return D(Math.sqrt(num(0))); case 'Math.pow': return D(Math.pow(num(0), num(1)));
      case 'Math.floor': return D(Math.floor(num(0))); case 'Math.ceil': return D(Math.ceil(num(0)));
      case 'Math.round': return { t: T.long, v: Math.floor(num(0) + 0.5) };
      case 'Math.random': return D(this.rng() / 2147483648);
      case 'Math.log': return D(Math.log(num(0))); case 'Math.log10': return D(Math.log10(num(0))); case 'Math.exp': return D(Math.exp(num(0)));
      case 'Math.sin': return D(Math.sin(num(0))); case 'Math.cos': return D(Math.cos(num(0))); case 'Math.hypot': return D(Math.hypot(num(0), num(1)));
      case 'Math.floorMod': return I(((num(0) % num(1)) + num(1)) % num(1));
      case 'Math.floorDiv': return I(Math.floor(num(0) / num(1)));
      case 'Math.signum': return D(Math.sign(num(0)));
      case 'Math.cbrt': return D(Math.cbrt(num(0)));
      case 'Integer.parseInt': case 'Integer.valueOf': case 'Long.parseLong': case 'Long.valueOf': {
        if (args[0].t.k === 'prim') return { t: cls === 'Long' ? T.long : T.int, v: args[0].v };
        const s = this.javaStr(args[0]);
        if (!/^[-+]?\d+$/.test(s.trim()) || s !== s.trim()) throw new RunError('NumberFormatException：For input string: "' + s + '"', 'runtime', '字符串里只能包含数字（可以带正负号）。');
        return { t: cls === 'Long' ? T.long : T.int, v: parseInt(s, args[1] ? num(1) : 10) };
      }
      case 'Double.parseDouble': case 'Double.valueOf': case 'Float.parseFloat': { const s = this.javaStr(args[0]); const v = parseFloat(s); if (isNaN(v) && s.trim() !== 'NaN') throw new RunError('NumberFormatException：For input string: "' + s + '"', 'runtime'); return D(v); }
      case 'Integer.toString': case 'Long.toString': case 'Double.toString': case 'String.valueOf': case 'Character.toString': case 'Boolean.toString': case 'Objects.toString':
        if (args.length === 2 && cls === 'Integer') return S(num(0).toString(num(1)));
        if (key === 'String.valueOf' && args[0].t.k === 'ptr' && args[0].t.jarr) return S(this.javaPrintArg(args[0]));
        return S(this.javaStr(args[0]));
      case 'Integer.toBinaryString': return S((num(0) >>> 0).toString(2));
      case 'Integer.toHexString': return S((num(0) >>> 0).toString(16));
      case 'Integer.compare': case 'Long.compare': case 'Double.compare': case 'Character.compare': case 'Boolean.compare': { const a = this.unboxAny(args[0]).v, b = this.unboxAny(args[1]).v; return I(a < b ? -1 : a > b ? 1 : 0); }
      case 'Integer.max': case 'Integer.min': return I(name === 'max' ? Math.max(num(0), num(1)) : Math.min(num(0), num(1)));
      case 'Integer.sum': case 'Long.sum': return this.binop('+', this.unboxAny(args[0]), this.unboxAny(args[1]));
      case 'Integer.bitCount': { let x = num(0) >>> 0, c = 0; while (x) { c += x & 1; x >>>= 1; } return I(c); }
      case 'Character.isDigit': return B(/[0-9]/.test(String.fromCharCode(num(0))));
      case 'Character.isLetter': case 'Character.isAlphabetic': return B(/\p{L}/u.test(String.fromCharCode(num(0))));
      case 'Character.isLetterOrDigit': return B(/[\p{L}0-9]/u.test(String.fromCharCode(num(0))));
      case 'Character.isUpperCase': return B(/\p{Lu}/u.test(String.fromCharCode(num(0))));
      case 'Character.isLowerCase': return B(/\p{Ll}/u.test(String.fromCharCode(num(0))));
      case 'Character.isWhitespace': case 'Character.isSpaceChar': return B(/\s/.test(String.fromCharCode(num(0))));
      case 'Character.toUpperCase': return { t: T.jchar, v: String.fromCharCode(num(0)).toUpperCase().charCodeAt(0) };
      case 'Character.toLowerCase': return { t: T.jchar, v: String.fromCharCode(num(0)).toLowerCase().charCodeAt(0) };
      case 'Character.getNumericValue': return I(parseInt(String.fromCharCode(num(0)), 36));
      case 'Character.valueOf': return { t: T.jchar, v: num(0) };
      case 'Boolean.parseBoolean': return B(this.javaStr(args[0]).toLowerCase() === 'true');
      case 'String.format': return S(this.javaFormat(args));
      case 'String.join': {
        const sep = this.javaStr(args[0]);
        let parts;
        if (args.length === 2 && args[1].t.k === 'cont') parts = this.contItems(args[1].v).map(x => this.javaStr(x));
        else if (args.length === 2 && args[1].t.k === 'ptr' && args[1].t.jarr) parts = this.arrValues(args[1]).vals.map(x => this.javaStr(x));
        else parts = args.slice(1).map(x => this.javaStr(x));
        return S(parts.join(sep));
      }
      case 'Objects.equals': { const a = args[0], b = args[1]; if (a.v == null || b.v == null || a.isNull || b.isNull) return B((a.v == null || a.isNull || a.v instanceof Ptr && !a.v.blk) && (b.v == null || b.isNull || b.v instanceof Ptr && !b.v.blk)); return B(this.keyOf(a) === this.keyOf(b)); }
      case 'Objects.hash': { let h = 1; for (const a of args) h = (Math.imul(31, h) + this.javaHash(a)) | 0; return I(h); }
      case 'Objects.isNull': return B(args[0].v == null || args[0].isNull || args[0].v instanceof Ptr && !args[0].v.blk);
      case 'Objects.nonNull': return B(!(args[0].v == null || args[0].isNull || args[0].v instanceof Ptr && !args[0].v.blk));
      case 'Objects.requireNonNull': if (args[0].v == null || args[0].v instanceof Ptr && !args[0].v.blk) throw new RunError('NullPointerException' + (args[1] ? '：' + this.javaStr(args[1]) : ''), 'segfault'); return args[0];
      case 'System.currentTimeMillis': case 'System.nanoTime': return { t: T.long, v: 1700000000000 + this.rec.steps.length };
      case 'System.exit': throw new ExitSignal(num(0));
      case 'System.arraycopy': {
        const src = this.arrValues(args[0]), dst = this.arrValues(args[2]);
        const sp = num(1), dp = num(3), n = num(4);
        if (sp < 0 || dp < 0 || sp + n > src.vals.length || dp + n > dst.vals.length) throw new RunError('ArrayIndexOutOfBoundsException：arraycopy 越界', 'oob');
        dst.set(src.vals.slice(sp, sp + n), dp);
        return { t: T.void, v: 0 };
      }
      case 'Arrays.toString': {
        if (args[0].v == null || !args[0].v.blk) return S('null');
        return S('[' + this.arrValues(args[0]).vals.map(v => this.javaStr(v)).join(', ') + ']');
      }
      case 'Arrays.deepToString': {
        const rec = (av) => '[' + this.arrValues(av).vals.map(v => v.t.k === 'ptr' && v.t.jarr ? rec(v) : this.javaStr(v)).join(', ') + ']';
        return S(rec(args[0]));
      }
      case 'Arrays.sort': {
        const A = this.arrValues(args[0]);
        let from = 0, to = A.vals.length, cmpV = null;
        if (args.length >= 3 && args[1].t.k === 'prim') { from = num(1); to = num(2); cmpV = args[3] || null; }
        else cmpV = args[1] || null;
        const seg = A.vals.slice(from, to);
        const cmp = this.makeComparator(cmpV);
        const order = seg.map((_, i) => i);
        this.mergeSort(order, (a, b) => cmp(seg[a], seg[b]));
        A.set(order.map(i => seg[i]), from);
        return { t: T.void, v: 0 };
      }
      case 'Arrays.fill': { const A = this.arrValues(args[0]); if (args.length === 4) { const vals = A.vals.slice(num(1), num(2)).map(() => args[3]); A.set(vals, num(1)); } else A.set(A.vals.map(() => args[1])); return { t: T.void, v: 0 }; }
      case 'Arrays.asList': case 'List.of': case 'Set.of': {
        let vals = args;
        if (args.length === 1 && args[0].t.k === 'ptr' && args[0].t.jarr && args[0].t.to.k !== 'prim') vals = this.arrValues(args[0]).vals;
        if (cls === 'Set') { const m = this.newMObj('LinkedHashSet', T.cont('Set', [T.any])); for (const v of vals) this.mapSet(m, v, null); return { t: m.t, v: m }; }
        const m = this.newListOf('ArrayList', vals); m.immutable = cls === 'List';
        return { t: m.t, v: m };
      }
      case 'Map.of': { const m = this.newMObj('LinkedHashMap', T.cont('Map', [T.any, T.any])); for (let i = 0; i + 1 < args.length; i += 2) this.mapSet(m, args[i], this.elemVal(args[i + 1], T.any)); return { t: m.t, v: m }; }
      case 'Arrays.copyOf': case 'Arrays.copyOfRange': {
        const A = this.arrValues(args[0]);
        const from = name === 'copyOfRange' ? num(1) : 0, to = name === 'copyOfRange' ? num(2) : num(1);
        const vals = []; for (let i = from; i < to; i++) vals.push(i < A.vals.length ? A.vals[i] : { t: A.et, v: this.zeroOf(A.et) });
        return { t: args[0].t, v: this.makeJavaArray(A.et, vals) };
      }
      case 'Arrays.equals': { const a = this.arrValues(args[0]).vals, b = this.arrValues(args[1]).vals; return B(a.length === b.length && a.every((x, i) => this.keyOf(x) === this.keyOf(b[i]))); }
      case 'Arrays.stream': { const m = this.newListOf('ArrayList', this.arrValues(args[0]).vals); return { t: m.t, v: m }; }
      case 'Arrays.binarySearch': { const vals = this.arrValues(args[0]).vals; let lo = 0, hi = vals.length - 1; while (lo <= hi) { const mid = (lo + hi) >>> 1; const c = this.compareVals(vals[mid], args[1]); if (c < 0) lo = mid + 1; else if (c > 0) hi = mid - 1; else return I(mid); } return I(-(lo + 1)); }
      case 'Collections.sort': {
        const m = args[0].v; const cmp = this.makeComparator(args[1] || null);
        const its = m.items; const order = its.map((_, i) => i);
        this.mergeSort(order, (a, b) => cmp(its[a], its[b]));
        m.items = order.map(i => its[i]);
        return { t: T.void, v: 0 };
      }
      case 'Collections.reverse': args[0].v.items.reverse(); return { t: T.void, v: 0 };
      case 'Collections.swap': { const it = args[0].v.items; const i = num(1), j = num(2); [it[i], it[j]] = [it[j], it[i]]; return { t: T.void, v: 0 }; }
      case 'Collections.max': case 'Collections.min': { const vals = this.contItems(args[0].v); if (!vals.length) throw new RunError('NoSuchElementException：集合是空的', 'runtime'); const cmp = this.makeComparator(args[1] || null); let b = vals[0]; for (const v of vals) if (name === 'max' ? cmp(v, b) > 0 : cmp(v, b) < 0) b = v; return b; }
      case 'Collections.reverseOrder': return { t: { k: 'lambda' }, v: { native: (a) => I(this.compareVals(a[1], a[0])) } };
      case 'Collections.emptyList': case 'List.copyOf': { const m = this.newListOf('ArrayList', args.length ? this.contItems(args[0].v) : []); return { t: m.t, v: m }; }
      case 'Collections.unmodifiableList': return args[0];
      case 'Collections.frequency': { let c = 0; for (const x of this.contItems(args[0].v)) if (this.keyOf(x) === this.keyOf(args[1])) c++; return I(c); }
      case 'Thread.sleep': return { t: T.void, v: 0 };
    }
    throw new RunError(key + '() 暂不支持', 'runtime', '可视化器支持常用的 Java 标准库方法，但不是全部。');
  };

  // ======================= Java program start =======================
  P.runJava = function () {
    // static fields
    this.frames.push({ name: '<static>', scopes: [new Map()], hidden: true, id: 0 });
    for (const st of this.prog.classes) {
      for (const f of st.staticFields) {
        const key = st.name + '.' + f.name;
        const blk = this.newBlock('global', this.sizeOf(f.type), f.type, key);
        blk.zero = true; blk.typed = true;
        const gv = { name: key, t: f.type, blk, line: f.line, cls: st };
        this.globals.set(key, gv); this.globalOrder.push(gv);
      }
    }
    for (const st of this.prog.classes) {
      this.frame.cls = st;
      for (const f of st.staticFields) {
        if (!f.init) continue;
        const gv = this.globals.get(st.name + '.' + f.name);
        const lv = new MemLV(gv.blk, 0, gv.t);
        if (f.init.type === 'InitList') this.store(lv, { t: f.type, v: this.javaArrayFromInit(f.type.to, f.init) });
        else this.store(lv, this.ev(f.init));
      }
      for (const b of st.staticInit) this.execBlock(b);
    }
    this.frames.pop();
    let main = null;
    for (const st of this.prog.classes) {
      const ms = st.methods.get('main');
      if (ms) { const m = ms.find(x => x.isStatic) || ms[0]; if (m && !st.builtin) { main = m; break; } }
    }
    if (!main) throw new DSV.CompileError('找不到 main 方法。Java 程序需要一个 public static void main(String[] args) 作为入口。', 1);
    const args = [];
    if (main.params.length) {
      const strs = (this.opts.args || []).map(s => ({ t: T.jstring, v: s }));
      args.push({ t: T.ptr(T.jstring, { jarr: true }), v: this.makeJavaArray(T.jstring, strs) });
    }
    this.callFunction(main, args, null, main.line);
    this.finalStep(main.endLine || this.curLine);
  };

  // short display text for messages
  P.toDisplay = function (v) {
    if (!v) return '';
    const t = v.t;
    try {
      switch (t.k) {
        case 'prim':
          if (t.isBool) return this.java || this.cpp ? (v.v ? 'true' : 'false') : String(v.v);
          if (t.isChar && t.size <= 2 && (this.java || this.cpp || v.isCharLit)) return "'" + DSV.escChar(String.fromCharCode(v.v)) + "'";
          if (t.fl) return this.java ? this.javaDouble(v.v, t.size === 4) : DSV.fmtNum(v.v, true);
          return String(v.v);
        case 'ptr': case 'nullptr':
          if (!v.v || !v.v.blk) return v.v && v.v.wild ? '野指针' : (this.java ? 'null' : (this.cpp ? 'nullptr' : 'NULL'));
          if (this.java) { const st = v.v.blk.type; if (v.v.blk.isEnum) return st.enumConsts[v.v.blk.enumIdx]; return st && st.k === 'struct' ? st.name + ' 对象' : '数组'; }
          if (t.k === 'ptr' && t.to.k === 'prim' && t.to.size === 1 && v.v.blk.kind === 'str') return DSV.quoteStr(this.cstrOf(v.v.blk));
          return this.hex(v.v.blk.addr + v.v.off);
        case 'string': return v.v == null ? 'null' : DSV.quoteStr(v.v);
        case 'any': return v.v == null ? 'null' : this.toDisplay(v.v);
        case 'struct': return T.name(t) + ' {…}';
        case 'cont': return v.v ? (v.v.ctype === 'mapentry' ? this.toDisplay(v.v.entry.k) + '=' + this.toDisplay(v.v.entry.v) : v.v.ctype + '(' + (v.v.map ? v.v.map.size : v.v.items.length) + ')') : 'null';
        case 'lambda': return 'lambda';
        case 'func': return t.name || 'function';
        case 'iter': return 'iterator';
      }
    } catch (e) { }
    return String(v.v);
  };
})(typeof window !== 'undefined' ? window : globalThis);
