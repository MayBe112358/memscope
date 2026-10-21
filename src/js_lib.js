// ===== JavaScript builtins, console.log formatting, snapshot =====
(function (G) {
  const DSV = G.DSV;
  const { RunError } = DSV;
  const R = DSV.jsRT;
  const { JSO, JSArr, JSFunc, JSMap, JSSet, JSGen, JSRegExp, Slot, Acc, Throw, Scope, HOLE, isObj, isIndex, numStr, ITER } = R;
  const P = DSV.JSInterp.prototype;

  P.setupGlobals = function () {
    const self = this;
    const OP = this.ObjectProto = new JSO(null);
    const FP = this.FunctionProto = new JSFunc(OP);
    const nf = (name, fn, len) => { const f = new JSFunc(FP); f.fname = name; f.native = fn; f.nlen = len || 0; return f; };
    const def = (o, name, fn, len) => { o.props.set(name, new Slot(nf(name, fn, len), false)); };
    const val = (o, name, v) => o.props.set(name, new Slot(v, false));
    const ctor = (name, fn, proto, statics) => {
      const F = nf(name, fn);
      F.isCtorNative = true;
      if (proto) { val(F, 'prototype', proto); val(proto, 'constructor', F); }
      return F;
    };
    this.nf = nf;
    const AP = this.ArrayProto = new JSO(OP);
    const SP = this.StringProto = new JSO(OP);
    const NP = this.NumberProto = new JSO(OP);
    const BP = this.BooleanProto = new JSO(OP);
    const BIP = this.BigIntProto = new JSO(OP);
    const MP = this.MapProto = new JSO(OP);
    const SetP = this.SetProto = new JSO(OP);
    const EP = this.ErrorProto = new JSO(OP);
    const RP = this.RegExpProto = new JSO(OP);
    const GP = this.GenProto = new JSO(OP);
    const builtin = new Scope(null, 'builtin');
    this.globalScope = new Scope(builtin, 'global');
    const g = (name, v) => builtin.vars.set(name, { v, kind: 'const', builtin: true });
    const num = (v) => this.toNum(v);
    const int = (v, d) => { if (v === undefined) return d; const n = Math.trunc(this.toNum(v)); return Number.isNaN(n) ? 0 : n; };
    const relIdx = (v, len, d) => { let n = int(v, d); if (n < 0) n = Math.max(0, len + n); return Math.min(n, len); };
    const arr = (t) => { if (!(t instanceof JSArr)) this.throwErr('TypeError', 'not an array'); return t; };
    const cb = (f, what) => { if (!(f instanceof JSFunc)) this.throwErr('TypeError', this.shortInspect(f) + ' is not a function', what ? what + ' 的参数需要是一个函数，例如 x => x * 2。' : undefined); return f; };
    const call = (f, thisV, args) => this.callFunction(f, thisV, args);
    const elems = (a) => a.items.map(x => x === HOLE ? undefined : x);
    const sameZero = (a, b) => a === b || (Number.isNaN(a) && Number.isNaN(b));

    // ---------- Object.prototype ----------
    def(OP, 'hasOwnProperty', (t, a) => { const k = this.toKey(a[0]); if (t instanceof JSArr && (k === 'length' || isIndex(k) && Number(k) < t.items.length && t.items[Number(k)] !== HOLE)) return true; return isObj(t) && t.props.has(k); });
    def(OP, 'toString', (t) => t instanceof JSArr ? this.arrJoin(t, ',') : (t === null || t === undefined ? '[object Undefined]' : '[object ' + (t instanceof JSMap ? 'Map' : t instanceof JSSet ? 'Set' : 'Object') + ']'));
    def(OP, 'valueOf', (t) => t);
    def(OP, 'isPrototypeOf', (t, a) => { for (let p = isObj(a[0]) ? a[0].proto : null; p; p = p.proto) if (p === t) return true; return false; });
    def(OP, 'toLocaleString', (t) => this.toStr(t));
    // ---------- Function.prototype ----------
    def(FP, 'call', (t, a) => call(t, a[0], a.slice(1)));
    def(FP, 'apply', (t, a) => call(t, a[0], a[1] ? this.toArray(a[1]) : []));
    def(FP, 'bind', (t, a) => { const f = new JSFunc(FP); f.fname = 'bound ' + t.fname; f.bound = { target: t, thisV: a[0], args: a.slice(1) }; return f; });
    def(FP, 'toString', (t) => t.isClass ? 'class ' + t.fname + ' { ... }' : 'function ' + t.fname + '() { ... }');

    // ---------- Array ----------
    def(AP, 'push', (t, a) => { arr(t).items.push(...a); return t.items.length; }, 1);
    def(AP, 'pop', (t) => { const v = arr(t).items.pop(); return v === HOLE ? undefined : v; });
    def(AP, 'shift', (t) => { const v = arr(t).items.shift(); return v === HOLE ? undefined : v; });
    def(AP, 'unshift', (t, a) => { arr(t).items.unshift(...a); return t.items.length; }, 1);
    def(AP, 'slice', (t, a) => { const n = t.items.length; return this.newArray(t.items.slice(relIdx(a[0], n, 0), relIdx(a[1], n, n))); }, 2);
    def(AP, 'splice', (t, a) => { const n = t.items.length; const s = relIdx(a[0], n, 0); const dc = a.length < 2 ? n - s : Math.max(0, Math.min(int(a[1], 0), n - s)); return this.newArray(t.items.splice(s, dc, ...a.slice(2))); }, 2);
    def(AP, 'concat', (t, a) => { const out = t.items.slice(); for (const x of a) { if (x instanceof JSArr) out.push(...x.items); else out.push(x); } return this.newArray(out); }, 1);
    def(AP, 'join', (t, a) => this.arrJoin(t, a[0] === undefined ? ',' : this.toStr(a[0])), 1);
    def(AP, 'toString', (t) => this.arrJoin(t, ','));
    def(AP, 'reverse', (t) => { arr(t).items.reverse(); return t; });
    def(AP, 'sort', (t, a) => {
      const items = arr(t).items;
      const und = items.filter(x => x === undefined || x === HOLE);
      const vals = items.filter(x => x !== undefined && x !== HOLE);
      let cmp;
      if (a[0] !== undefined) { const f = cb(a[0], 'sort'); cmp = (x, y) => { const r = this.toNum(call(f, undefined, [x, y])); return Number.isNaN(r) ? 0 : r; }; }
      else {
        if (vals.length > 1 && vals.every(v => typeof v === 'number') && !this.warned.has('sortnum')) { const s2 = vals.map(String).sort(); const numeric = vals.slice().sort((x, y) => x - y); if (s2.join() !== numeric.map(String).join()) { this.warned.add('sortnum'); this.rec.note('⚠ sort() 默认按“字符串”顺序排序，所以 10 会排在 9 前面。对数字排序请写 arr.sort((a, b) => a - b)。', 'warn'); } }
        cmp = (x, y) => { const sx = this.toStr(x), sy = this.toStr(y); return sx < sy ? -1 : sx > sy ? 1 : 0; };
      }
      const sorted = this.mergeSort(vals, cmp);
      items.length = 0; items.push(...sorted, ...und);
      return t;
    }, 1);
    const finder = (name, fromEnd, wantIndex) => def(AP, name, (t, a) => {
      const f = cb(a[0], name); const it = arr(t).items;
      if (!fromEnd) { for (let i = 0; i < it.length; i++) { const v = it[i] === HOLE ? undefined : it[i]; if (this.truthy(call(f, a[1], [v, i, t]))) return wantIndex ? i : v; } }
      else for (let i = it.length - 1; i >= 0; i--) { const v = it[i] === HOLE ? undefined : it[i]; if (this.truthy(call(f, a[1], [v, i, t]))) return wantIndex ? i : v; }
      return wantIndex ? -1 : undefined;
    }, 1);
    finder('find', false, false); finder('findIndex', false, true); finder('findLast', true, false); finder('findLastIndex', true, true);
    def(AP, 'indexOf', (t, a) => { const it = arr(t).items; for (let i = relIdx(a[1], it.length, 0); i < it.length; i++) if (it[i] === a[0]) return i; return -1; }, 1);
    def(AP, 'lastIndexOf', (t, a) => { const it = arr(t).items; for (let i = it.length - 1; i >= 0; i--) if (it[i] === a[0]) return i; return -1; }, 1);
    def(AP, 'includes', (t, a) => arr(t).items.some(x => sameZero(x === HOLE ? undefined : x, a[0])), 1);
    def(AP, 'filter', (t, a) => { const f = cb(a[0], 'filter'); const out = []; arr(t).items.forEach((v, i) => { if (v !== HOLE && this.truthy(call(f, a[1], [v, i, t]))) out.push(v); }); return this.newArray(out); }, 1);
    def(AP, 'map', (t, a) => { const f = cb(a[0], 'map'); return this.newArray(arr(t).items.map((v, i) => v === HOLE ? HOLE : call(f, a[1], [v, i, t]))); }, 1);
    def(AP, 'forEach', (t, a) => { const f = cb(a[0], 'forEach'); const it = arr(t).items; for (let i = 0; i < it.length; i++) if (it[i] !== HOLE) call(f, a[1], [it[i], i, t]); return undefined; }, 1);
    def(AP, 'reduce', (t, a) => { const f = cb(a[0], 'reduce'); const it = arr(t).items.map((v, i) => [v, i]).filter(x => x[0] !== HOLE); let acc, k = 0; if (a.length > 1) acc = a[1]; else { if (!it.length) this.throwErr('TypeError', 'Reduce of empty array with no initial value', '对空数组调用 reduce 时需要提供初始值，例如 arr.reduce((s, x) => s + x, 0)。'); acc = it[0][0]; k = 1; } for (; k < it.length; k++) acc = call(f, undefined, [acc, it[k][0], it[k][1], t]); return acc; }, 1);
    def(AP, 'reduceRight', (t, a) => { const f = cb(a[0]); const it = arr(t).items; let i = it.length - 1, acc; if (a.length > 1) acc = a[1]; else { if (i < 0) this.throwErr('TypeError', 'Reduce of empty array with no initial value'); acc = it[i--]; } for (; i >= 0; i--) acc = call(f, undefined, [acc, it[i], i, t]); return acc; }, 1);
    def(AP, 'some', (t, a) => { const f = cb(a[0]); return arr(t).items.some((v, i) => v !== HOLE && this.truthy(call(f, a[1], [v, i, t]))); }, 1);
    def(AP, 'every', (t, a) => { const f = cb(a[0]); return arr(t).items.every((v, i) => v === HOLE || this.truthy(call(f, a[1], [v, i, t]))); }, 1);
    def(AP, 'fill', (t, a) => { const it = arr(t).items; const n = it.length; for (let i = relIdx(a[1], n, 0); i < relIdx(a[2], n, n); i++) it[i] = a[0]; return t; }, 1);
    def(AP, 'flat', (t, a) => { const depth = a[0] === undefined ? 1 : int(a[0]); const flat = (items, d) => { const out = []; for (const v of items) { if (v === HOLE) continue; if (v instanceof JSArr && d > 0) out.push(...flat(v.items, d - 1)); else out.push(v); } return out; }; return this.newArray(flat(arr(t).items, depth)); });
    def(AP, 'flatMap', (t, a) => { const f = cb(a[0]); const out = []; arr(t).items.forEach((v, i) => { const r = call(f, a[1], [v, i, t]); if (r instanceof JSArr) out.push(...r.items); else out.push(r); }); return this.newArray(out); }, 1);
    def(AP, 'at', (t, a) => { const it = arr(t).items; let i = int(a[0], 0); if (i < 0) i += it.length; const v = it[i]; return v === HOLE ? undefined : v; }, 1);
    def(AP, 'keys', (t) => new JSGen(GP, t.items.map((_, i) => i)));
    def(AP, 'values', (t) => new JSGen(GP, elems(t)));
    def(AP, 'entries', (t) => new JSGen(GP, elems(t).map((v, i) => this.newArray([i, v]))));
    def(AP, ITER, (t) => new JSGen(GP, elems(t)));
    def(AP, 'toReversed', (t) => this.newArray(t.items.slice().reverse()));
    def(AP, 'toSorted', (t, a) => { const c = this.newArray(t.items.slice()); return call(this.get(AP, 'sort'), c, a); });
    def(AP, 'with', (t, a) => { const c = t.items.slice(); let i = int(a[0]); if (i < 0) i += c.length; c[i] = a[1]; return this.newArray(c); });
    const ArrayCtor = this.ArrayCtor = ctor('Array', (t, a, nt) => {
      if (a.length === 1 && typeof a[0] === 'number') { if (!Number.isInteger(a[0]) || a[0] < 0) this.throwErr('RangeError', 'Invalid array length'); if (a[0] > 1e6) this.throwErr('RangeError', '数组太大（可视化器最多支持 100 万个元素）'); return this.newArray(new Array(a[0]).fill(HOLE)); }
      return this.newArray(a.slice());
    }, AP);
    def(ArrayCtor, 'isArray', (t, a) => a[0] instanceof JSArr);
    def(ArrayCtor, 'of', (t, a) => this.newArray(a.slice()));
    def(ArrayCtor, 'from', (t, a) => {
      let items;
      const src = a[0];
      if (isObj(src) && !(src instanceof JSArr) && !(src instanceof JSMap) && !(src instanceof JSSet) && !(src instanceof JSGen) && !this.get(src, ITER)) { const n = int(this.get(src, 'length'), 0); items = []; for (let i = 0; i < n; i++) items.push(this.get(src, String(i))); }
      else items = this.toArray(src);
      if (a[1]) { const f = cb(a[1]); items = items.map((v, i) => call(f, undefined, [v, i])); }
      return this.newArray(items);
    });
    g('Array', ArrayCtor);

    // ---------- String ----------
    const str = (t) => typeof t === 'string' ? t : this.toStr(t);
    def(SP, 'charAt', (t, a) => str(t).charAt(int(a[0], 0)));
    def(SP, 'charCodeAt', (t, a) => str(t).charCodeAt(int(a[0], 0)));
    def(SP, 'codePointAt', (t, a) => str(t).codePointAt(int(a[0], 0)));
    def(SP, 'at', (t, a) => str(t).at(int(a[0], 0)));
    def(SP, 'indexOf', (t, a) => str(t).indexOf(this.toStr(a[0]), int(a[1], 0)));
    def(SP, 'lastIndexOf', (t, a) => str(t).lastIndexOf(this.toStr(a[0])));
    def(SP, 'includes', (t, a) => str(t).includes(this.toStr(a[0]), int(a[1], 0)));
    def(SP, 'startsWith', (t, a) => str(t).startsWith(this.toStr(a[0]), int(a[1], 0)));
    def(SP, 'endsWith', (t, a) => str(t).endsWith(this.toStr(a[0])));
    def(SP, 'slice', (t, a) => str(t).slice(a[0] === undefined ? 0 : int(a[0]), a[1] === undefined ? undefined : int(a[1])));
    def(SP, 'substring', (t, a) => str(t).substring(int(a[0], 0), a[1] === undefined ? undefined : int(a[1])));
    def(SP, 'substr', (t, a) => str(t).substr(int(a[0], 0), a[1] === undefined ? undefined : int(a[1])));
    def(SP, 'toUpperCase', (t) => str(t).toUpperCase());
    def(SP, 'toLowerCase', (t) => str(t).toLowerCase());
    def(SP, 'toLocaleUpperCase', (t) => str(t).toUpperCase());
    def(SP, 'toLocaleLowerCase', (t) => str(t).toLowerCase());
    def(SP, 'trim', (t) => str(t).trim());
    def(SP, 'trimStart', (t) => str(t).trimStart());
    def(SP, 'trimEnd', (t) => str(t).trimEnd());
    def(SP, 'split', (t, a) => { const s = str(t); if (a[0] === undefined) return this.newArray([s]); const sep = a[0] instanceof JSRegExp ? a[0].re : this.toStr(a[0]); let parts = s.split(sep); if (a[1] !== undefined) parts = parts.slice(0, int(a[1])); return this.newArray(parts.map(p => p === undefined ? undefined : p)); });
    const replaceImpl = (all) => (t, a) => {
      const s = str(t);
      const pat = a[0], rep = a[1];
      const fnRep = rep instanceof JSFunc ? (...m) => this.toStr(call(rep, undefined, m.slice(0, -2).concat([m[m.length - 2], m[m.length - 1]]))) : this.toStr(rep);
      if (pat instanceof JSRegExp) { if (all && !pat.re.global) this.throwErr('TypeError', 'replaceAll must be called with a global RegExp'); return s.replace(pat.re, fnRep); }
      const p = this.toStr(pat);
      if (all) return s.split(p).join(typeof fnRep === 'string' ? fnRep : '');
      return s.replace(p, fnRep);
    };
    def(SP, 'replace', replaceImpl(false));
    def(SP, 'replaceAll', replaceImpl(true));
    def(SP, 'repeat', (t, a) => { const n = int(a[0], 0); if (n < 0) this.throwErr('RangeError', 'Invalid count value: ' + n); return str(t).repeat(n); });
    def(SP, 'padStart', (t, a) => str(t).padStart(int(a[0], 0), a[1] === undefined ? ' ' : this.toStr(a[1])));
    def(SP, 'padEnd', (t, a) => str(t).padEnd(int(a[0], 0), a[1] === undefined ? ' ' : this.toStr(a[1])));
    def(SP, 'concat', (t, a) => str(t) + a.map(x => this.toStr(x)).join(''));
    def(SP, 'localeCompare', (t, a) => { const x = str(t), y = this.toStr(a[0]); return x.localeCompare(y); });
    def(SP, 'normalize', (t) => str(t));
    def(SP, 'toString', (t) => str(t));
    def(SP, 'valueOf', (t) => str(t));
    def(SP, 'search', (t, a) => str(t).search(a[0] instanceof JSRegExp ? a[0].re : this.toStr(a[0])));
    def(SP, 'match', (t, a) => { const m = str(t).match(a[0] instanceof JSRegExp ? a[0].re : this.toStr(a[0])); if (!m) return null; const r = this.newArray([...m]); if (m.index !== undefined) r.props.set('index', new Slot(m.index)); return r; });
    def(SP, 'matchAll', (t, a) => new JSGen(GP, [...str(t).matchAll(a[0].re)].map(m => this.newArray([...m]))));
    def(SP, ITER, (t) => new JSGen(GP, [...str(t)]));
    const StringCtor = ctor('String', (t, a) => a.length ? (isObj(a[0]) ? this.toStr(a[0]) : String(a[0] === undefined ? 'undefined' : a[0] === null ? 'null' : typeof a[0] === 'number' ? numStr(a[0]) : a[0])) : '', SP);
    def(StringCtor, 'fromCharCode', (t, a) => String.fromCharCode(...a.map(x => num(x))));
    def(StringCtor, 'fromCodePoint', (t, a) => String.fromCodePoint(...a.map(x => num(x))));
    g('String', StringCtor);

    // ---------- Number / Boolean / BigInt ----------
    const numv = (t) => typeof t === 'number' ? t : this.toNum(t);
    def(NP, 'toFixed', (t, a) => { const d = int(a[0], 0); if (d < 0 || d > 100) this.throwErr('RangeError', 'toFixed() digits argument must be between 0 and 100'); return numv(t).toFixed(d); });
    def(NP, 'toString', (t, a) => { const r = a[0] === undefined ? 10 : int(a[0]); if (r < 2 || r > 36) this.throwErr('RangeError', 'toString() radix must be between 2 and 36'); return r === 10 ? numStr(numv(t)) : numv(t).toString(r); });
    def(NP, 'toPrecision', (t, a) => a[0] === undefined ? numStr(numv(t)) : numv(t).toPrecision(int(a[0])));
    def(NP, 'valueOf', (t) => numv(t));
    def(NP, 'toLocaleString', (t) => numv(t).toLocaleString('en-US'));
    def(BP, 'toString', (t) => String(t));
    def(BIP, 'toString', (t) => String(t));
    const NumberCtor = ctor('Number', (t, a) => a.length ? (typeof a[0] === 'bigint' ? Number(a[0]) : this.toNum(a[0])) : 0, NP);
    def(NumberCtor, 'isInteger', (t, a) => Number.isInteger(a[0]));
    def(NumberCtor, 'isSafeInteger', (t, a) => Number.isSafeInteger(a[0]));
    def(NumberCtor, 'isFinite', (t, a) => Number.isFinite(a[0]));
    def(NumberCtor, 'isNaN', (t, a) => Number.isNaN(a[0]));
    const parseIntF = nf('parseInt', (t, a) => parseInt(this.toStr(a[0]), a[1] === undefined ? undefined : int(a[1])));
    const parseFloatF = nf('parseFloat', (t, a) => parseFloat(this.toStr(a[0])));
    val(NumberCtor, 'parseInt', parseIntF); val(NumberCtor, 'parseFloat', parseFloatF);
    for (const k of ['MAX_SAFE_INTEGER', 'MIN_SAFE_INTEGER', 'MAX_VALUE', 'MIN_VALUE', 'EPSILON', 'POSITIVE_INFINITY', 'NEGATIVE_INFINITY', 'NaN']) val(NumberCtor, k, Number[k]);
    g('Number', NumberCtor);
    g('Boolean', ctor('Boolean', (t, a) => this.truthy(a[0]), BP));
    const BigIntCtor = ctor('BigInt', (t, a, nt) => { if (nt) this.throwErr('TypeError', 'BigInt is not a constructor'); const v = a[0]; if (typeof v === 'number' && !Number.isInteger(v)) this.throwErr('RangeError', 'The number ' + v + ' cannot be converted to a BigInt because it is not an integer'); try { return BigInt(typeof v === 'string' ? v.trim() : v); } catch (e) { this.throwErr('SyntaxError', 'Cannot convert ' + this.toStr(v) + ' to a BigInt'); } }, BIP);
    g('BigInt', BigIntCtor);
    g('parseInt', parseIntF); g('parseFloat', parseFloatF);
    g('isNaN', nf('isNaN', (t, a) => Number.isNaN(this.toNum(a[0]))));
    g('isFinite', nf('isFinite', (t, a) => Number.isFinite(this.toNum(a[0]))));
    g('Infinity', Infinity); g('NaN', NaN); g('undefined', undefined);

    // ---------- Object ----------
    const ObjectCtor = ctor('Object', (t, a) => isObj(a[0]) ? a[0] : this.newObject(), OP);
    def(ObjectCtor, 'keys', (t, a) => { if (a[0] === null || a[0] === undefined) this.throwErr('TypeError', 'Cannot convert undefined or null to object'); if (typeof a[0] === 'string') return this.newArray([...a[0]].map((_, i) => String(i))); return this.newArray(isObj(a[0]) ? this.ownKeys(a[0]) : []); });
    def(ObjectCtor, 'values', (t, a) => this.newArray(isObj(a[0]) ? this.ownKeys(a[0]).map(k => this.get(a[0], k)) : []));
    def(ObjectCtor, 'entries', (t, a) => this.newArray(isObj(a[0]) ? this.ownKeys(a[0]).map(k => this.newArray([k, this.get(a[0], k)])) : []));
    def(ObjectCtor, 'assign', (t, a) => { const tgt = a[0]; for (const src of a.slice(1)) if (isObj(src)) for (const k of this.ownKeys(src)) this.put(tgt, k, this.get(src, k)); return tgt; });
    def(ObjectCtor, 'freeze', (t, a) => { if (isObj(a[0])) { a[0].frozen = true; a[0].sealed = true; } return a[0]; });
    def(ObjectCtor, 'isFrozen', (t, a) => !isObj(a[0]) || !!a[0].frozen);
    def(ObjectCtor, 'seal', (t, a) => { if (isObj(a[0])) a[0].sealed = true; return a[0]; });
    def(ObjectCtor, 'create', (t, a) => { const o = new JSO(a[0]); if (isObj(a[1])) for (const k of this.ownKeys(a[1])) { const d = this.get(a[1], k); o.props.set(k, new Slot(this.get(d, 'value'), this.truthy(this.get(d, 'enumerable')))); } return o; });
    def(ObjectCtor, 'fromEntries', (t, a) => { const o = this.newObject(); for (const e of this.toArray(a[0])) { const kv = this.toArray(e); o.props.set(this.toKey(kv[0]), new Slot(kv[1])); } return o; });
    def(ObjectCtor, 'getPrototypeOf', (t, a) => this.protoOf(a[0]));
    def(ObjectCtor, 'setPrototypeOf', (t, a) => { a[0].proto = a[1]; return a[0]; });
    def(ObjectCtor, 'getOwnPropertyNames', (t, a) => this.newArray(this.ownKeys(a[0], false)));
    def(ObjectCtor, 'defineProperty', (t, a) => { const [o, k, d] = a; const key = this.toKey(k); const g2 = this.get(d, 'get'), s2 = this.get(d, 'set'); if (g2 || s2) o.props.set(key, new Acc(g2, s2, this.truthy(this.get(d, 'enumerable')))); else o.props.set(key, new Slot(this.get(d, 'value'), this.truthy(this.get(d, 'enumerable')))); return o; });
    def(ObjectCtor, 'is', (t, a) => Object.is(a[0], a[1]));
    g('Object', ObjectCtor);

    // ---------- Function ----------
    g('Function', ctor('Function', () => this.throwErr('EvalError', '可视化器不支持 new Function（动态创建代码）'), FP));

    // ---------- Map / Set ----------
    const mapThis = (t, nm) => { if (!(t instanceof JSMap)) this.throwErr('TypeError', 'Method Map.prototype.' + nm + ' called on incompatible receiver'); return t; };
    def(MP, 'get', (t, a) => { const e = mapThis(t, 'get').m.get(this.mapKey(a[0])); return e ? e[1] : undefined; });
    def(MP, 'set', (t, a) => { const k = this.mapKey(a[0]); const e = mapThis(t, 'set').m.get(k); if (e) e[1] = a[1]; else t.m.set(k, [a[0], a[1]]); return t; });
    def(MP, 'has', (t, a) => mapThis(t, 'has').m.has(this.mapKey(a[0])));
    def(MP, 'delete', (t, a) => mapThis(t, 'delete').m.delete(this.mapKey(a[0])));
    def(MP, 'clear', (t) => { mapThis(t, 'clear').m.clear(); return undefined; });
    def(MP, 'forEach', (t, a) => { const f = cb(a[0]); for (const [, e] of [...mapThis(t, 'forEach').m]) call(f, a[1], [e[1], e[0], t]); return undefined; });
    def(MP, 'keys', (t) => new JSGen(GP, [...t.m.values()].map(e => e[0])));
    def(MP, 'values', (t) => new JSGen(GP, [...t.m.values()].map(e => e[1])));
    def(MP, 'entries', (t) => new JSGen(GP, [...t.m.values()].map(e => this.newArray([e[0], e[1]]))));
    def(MP, ITER, (t) => new JSGen(GP, [...t.m.values()].map(e => this.newArray([e[0], e[1]]))));
    const MapCtor = this.MapCtor = ctor('Map', (t, a, nt, existing) => {
      if (!nt) this.throwErr('TypeError', "Constructor Map requires 'new'");
      const m = existing ? t : new JSMap(MP);
      if (a[0] !== undefined && a[0] !== null) for (const e of this.toArray(a[0])) { const kv = this.toArray(e); m.m.set(this.mapKey(kv[0]), [kv[0], kv[1]]); }
      return m;
    }, MP);
    g('Map', MapCtor); g('WeakMap', MapCtor);
    const setThis = (t) => { if (!(t instanceof JSSet)) this.throwErr('TypeError', 'Set method called on incompatible receiver'); return t; };
    def(SetP, 'add', (t, a) => { const k = this.mapKey(a[0]); if (!setThis(t).m.has(k)) t.m.set(k, a[0]); return t; });
    def(SetP, 'has', (t, a) => setThis(t).m.has(this.mapKey(a[0])));
    def(SetP, 'delete', (t, a) => setThis(t).m.delete(this.mapKey(a[0])));
    def(SetP, 'clear', (t) => { setThis(t).m.clear(); return undefined; });
    def(SetP, 'forEach', (t, a) => { const f = cb(a[0]); for (const v of [...setThis(t).m.values()]) call(f, a[1], [v, v, t]); return undefined; });
    def(SetP, 'values', (t) => new JSGen(GP, [...t.m.values()]));
    def(SetP, 'keys', (t) => new JSGen(GP, [...t.m.values()]));
    def(SetP, 'entries', (t) => new JSGen(GP, [...t.m.values()].map(v => this.newArray([v, v]))));
    def(SetP, ITER, (t) => new JSGen(GP, [...t.m.values()]));
    const SetCtor = this.SetCtor = ctor('Set', (t, a, nt, existing) => {
      if (!nt) this.throwErr('TypeError', "Constructor Set requires 'new'");
      const s = existing ? t : new JSSet(SetP);
      if (a[0] !== undefined && a[0] !== null) for (const v of this.toArray(a[0])) { const k = this.mapKey(v); if (!s.m.has(k)) s.m.set(k, v); }
      return s;
    }, SetP);
    g('Set', SetCtor); g('WeakSet', SetCtor);

    // ---------- generators ----------
    def(GP, 'next', (t) => { const o = this.newObject(); if (t.i < t.items.length) { o.props.set('value', new Slot(t.items[t.i++])); o.props.set('done', new Slot(false)); } else { o.props.set('value', new Slot(undefined)); o.props.set('done', new Slot(true)); } return o; });
    def(GP, ITER, (t) => t);
    def(GP, 'toArray', (t) => this.newArray(t.items.slice(t.i)));

    // ---------- Errors ----------
    val(EP, 'name', 'Error'); val(EP, 'message', '');
    def(EP, 'toString', (t) => { const n = this.get(t, 'name'), m = this.get(t, 'message'); return m ? n + ': ' + m : String(n); });
    const mkErr = (name, proto) => {
      const F = ctor(name, (t, a, nt, existing) => {
        const target = existing ? t : new JSO(proto);
        if (a[0] !== undefined) target.props.set('message', new Slot(this.toStr(a[0]), false));
        target.props.set('stack', new Slot(name + ': ' + (a[0] !== undefined ? this.toStr(a[0]) : ''), false));
        return target;
      }, proto);
      g(name, F);
      return F;
    };
    const ErrorCtor = mkErr('Error', EP);
    for (const n of ['TypeError', 'RangeError', 'ReferenceError', 'SyntaxError', 'EvalError', 'URIError']) { const p = new JSO(EP); val(p, 'name', n); const F = mkErr(n, p); F.parentClass = ErrorCtor; F.proto = ErrorCtor; }

    // ---------- RegExp ----------
    def(RP, 'test', (t, a) => t.re.test(this.toStr(a[0])));
    def(RP, 'exec', (t, a) => { const m = t.re.exec(this.toStr(a[0])); if (!m) return null; const r = this.newArray([...m]); r.props.set('index', new Slot(m.index)); return r; });
    def(RP, 'toString', (t) => String(t.re));
    g('RegExp', ctor('RegExp', (t, a) => new JSRegExp(RP, new RegExp(a[0] instanceof JSRegExp ? a[0].re.source : this.toStr(a[0]), a[1] === undefined ? '' : this.toStr(a[1]))), RP));

    // ---------- Symbol ----------
    const SymbolF = nf('Symbol', (t, a) => { const o = new JSO(OP); o.isSymbol = true; o.key = '@@sym' + (++this.symSeq) + ':' + (a[0] !== undefined ? this.toStr(a[0]) : ''); return o; });
    this.symSeq = 0;
    val(SymbolF, 'iterator', ITER);
    g('Symbol', SymbolF);

    // ---------- Math ----------
    const MathO = new JSO(OP);
    const m1 = (n, f) => def(MathO, n, (t, a) => f(num(a[0])));
    for (const n of ['abs', 'floor', 'ceil', 'round', 'trunc', 'sqrt', 'cbrt', 'sign', 'log', 'log2', 'log10', 'exp', 'sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'fround']) m1(n, Math[n]);
    def(MathO, 'max', (t, a) => Math.max(...a.map(num)));
    def(MathO, 'min', (t, a) => Math.min(...a.map(num)));
    def(MathO, 'pow', (t, a) => Math.pow(num(a[0]), num(a[1])));
    def(MathO, 'atan2', (t, a) => Math.atan2(num(a[0]), num(a[1])));
    def(MathO, 'hypot', (t, a) => Math.hypot(...a.map(num)));
    def(MathO, 'random', () => this.rng() / 2147483648);
    for (const k of ['PI', 'E', 'LN2', 'LN10', 'SQRT2', 'LOG2E', 'LOG10E']) val(MathO, k, Math[k]);
    g('Math', MathO);

    // ---------- JSON ----------
    const JSONO = new JSO(OP);
    def(JSONO, 'stringify', (t, a) => this.jsonStringify(a[0], a[2]));
    def(JSONO, 'parse', (t, a) => { let v; try { v = JSON.parse(this.toStr(a[0])); } catch (e) { this.throwErr('SyntaxError', e.message); } return this.fromHost(v); });
    g('JSON', JSONO);

    // ---------- console ----------
    const consoleO = new JSO(OP);
    const log = (t, a) => { this.rec.write(this.formatLog(a) + '\n'); return undefined; };
    for (const n of ['log', 'info', 'debug', 'warn', 'error', 'trace']) def(consoleO, n, log);
    def(consoleO, 'assert', (t, a) => { if (!this.truthy(a[0])) this.rec.write('Assertion failed' + (a.length > 1 ? ': ' + this.formatLog(a.slice(1)) : '') + '\n'); return undefined; });
    def(consoleO, 'table', (t, a) => { this.rec.write(this.formatLog(a) + '\n'); return undefined; });
    this.counts = new Map();
    def(consoleO, 'count', (t, a) => { const k = a[0] === undefined ? 'default' : this.toStr(a[0]); this.counts.set(k, (this.counts.get(k) || 0) + 1); this.rec.write(k + ': ' + this.counts.get(k) + '\n'); return undefined; });
    def(consoleO, 'group', (t, a) => { if (a.length) this.rec.write(this.formatLog(a) + '\n'); return undefined; });
    def(consoleO, 'groupEnd', () => undefined);
    def(consoleO, 'time', () => undefined); def(consoleO, 'timeEnd', (t, a) => { this.rec.write((a[0] || 'default') + ': 0.1ms\n'); return undefined; });
    g('console', consoleO);

    // ---------- misc ----------
    const DateCtor = ctor('Date', (t, a, nt) => { const o = new JSO(OP); o.props.set('__time', new Slot(1700000000000 + this.rec.steps.length, false)); return nt ? o : 'Tue Nov 14 2023'; }, new JSO(OP));
    def(DateCtor, 'now', () => 1700000000000 + this.rec.steps.length);
    def(this.get(DateCtor, 'prototype'), 'getTime', (t) => this.get(t, '__time'));
    g('Date', DateCtor);
    this.timers = []; this.timerSeq = 0;
    g('setTimeout', nf('setTimeout', (t, a) => { const id = ++this.timerSeq; this.timers.push({ fn: cb(a[0]), t: a[1] ? num(a[1]) : 0, args: a.slice(2), seq: id }); this.rec.note('setTimeout：回调函数被放进了任务队列，会在当前代码全部执行完之后才运行', 'info'); return id; }));
    g('clearTimeout', nf('clearTimeout', (t, a) => { this.timers = this.timers.filter(x => x.seq !== a[0]); return undefined; }));
    g('setInterval', nf('setInterval', () => this.throwErr('Error', '可视化器不支持 setInterval（会无限执行）')));
    g('queueMicrotask', nf('queueMicrotask', (t, a) => { this.timers.push({ fn: a[0], t: -1, args: [], seq: ++this.timerSeq }); return undefined; }));
    g('prompt', nf('prompt', (t, a) => { if (a.length) this.rec.write(this.toStr(a[0])); const l = this.stdin.line(); if (l === null) return null; this.rec.write(l + '\n'); return l; }));
    g('readline', nf('readline', () => { const l = this.stdin.line(); return l === null ? undefined : l; }));
    g('structuredClone', nf('structuredClone', (t, a) => this.deepClone(a[0], new Map())));
    g('require', nf('require', (t, a) => { const m = this.toStr(a[0]); if (m === 'readline' || m === 'fs') this.throwErr('Error', '可视化器不支持 require("' + m + '")。读取输入可以使用 prompt() 或 readline()，它们会从“输入 (stdin)”框里逐行读取。'); this.throwErr('Error', "Cannot find module '" + m + "'（可视化器不支持模块）"); }));
    const globalThisO = new JSO(OP);
    g('globalThis', globalThisO);
    g('Promise', ctor('Promise', () => this.throwErr('Error', '可视化器暂不支持 Promise / async（只模拟同步代码的执行）'), new JSO(OP)));
  };

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
  P.arrJoin = function (t, sep) {
    if (!this._joining) this._joining = new Set();
    if (this._joining.has(t)) return '';
    this._joining.add(t);
    try { return t.items.map(x => x === HOLE || x === undefined || x === null ? '' : this.toStr(x)).join(sep); }
    finally { this._joining.delete(t); }
  };
  P.fromHost = function (v) {
    if (Array.isArray(v)) return this.newArray(v.map(x => this.fromHost(x)));
    if (v && typeof v === 'object') { const o = this.newObject(); for (const k of Object.keys(v)) o.props.set(k, new Slot(this.fromHost(v[k]))); return o; }
    return v;
  };
  P.deepClone = function (v, memo) {
    if (!isObj(v)) return v;
    if (memo.has(v)) return memo.get(v);
    if (v instanceof JSFunc) this.throwErr('DataCloneError' === 'x' ? '' : 'TypeError', 'function could not be cloned');
    let c;
    if (v instanceof JSArr) { c = this.newArray([]); memo.set(v, c); c.items = v.items.map(x => this.deepClone(x, memo)); return c; }
    if (v instanceof JSMap) { c = new JSMap(this.MapProto); memo.set(v, c); for (const [k, e] of v.m) c.m.set(k, [this.deepClone(e[0], memo), this.deepClone(e[1], memo)]); return c; }
    if (v instanceof JSSet) { c = new JSSet(this.SetProto); memo.set(v, c); for (const [k, x] of v.m) c.m.set(k, this.deepClone(x, memo)); return c; }
    c = this.newObject(); memo.set(v, c);
    for (const k of this.ownKeys(v)) c.props.set(k, new Slot(this.deepClone(this.get(v, k), memo)));
    return c;
  };
  P.jsonStringify = function (v, indent) {
    const gap = typeof indent === 'number' ? ' '.repeat(Math.min(10, indent)) : (typeof indent === 'string' ? indent.slice(0, 10) : '');
    const stack = [];
    const ser = (v, ind) => {
      if (isObj(v)) { const tj = this.get(v, 'toJSON'); if (tj instanceof JSFunc) v = this.callFunction(tj, v, []); }
      if (v === null) return 'null';
      if (v === undefined || v instanceof JSFunc) return undefined;
      if (typeof v === 'string') return JSON.stringify(v);
      if (typeof v === 'number') return isFinite(v) ? numStr(v) : 'null';
      if (typeof v === 'boolean') return String(v);
      if (typeof v === 'bigint') this.throwErr('TypeError', 'Do not know how to serialize a BigInt');
      if (stack.includes(v)) this.throwErr('TypeError', 'Converting circular structure to JSON', '对象里有循环引用（例如双向链表的 prev/next），不能直接转成 JSON。');
      stack.push(v);
      const ni = ind + gap;
      let out;
      if (v instanceof JSArr) {
        const parts = v.items.map(x => { const s = ser(x === HOLE ? undefined : x, ni); return s === undefined ? 'null' : s; });
        out = !parts.length ? '[]' : gap ? '[\n' + ni + parts.join(',\n' + ni) + '\n' + ind + ']' : '[' + parts.join(',') + ']';
      } else {
        const parts = [];
        if (!(v instanceof JSMap) && !(v instanceof JSSet)) for (const k of this.ownKeys(v)) { const s = ser(this.get(v, k), ni); if (s !== undefined) parts.push(JSON.stringify(k) + (gap ? ': ' : ':') + s); }
        out = !parts.length ? '{}' : gap ? '{\n' + ni + parts.join(',\n' + ni) + '\n' + ind + '}' : '{' + parts.join(',') + '}';
      }
      stack.pop();
      return out;
    };
    return ser(v, '');
  };

  // ======================= Node-style inspect =======================
  const IDENT = /^[a-zA-Z_][a-zA-Z_0-9]*$/;
  function strEscape(s) {
    let q = "'";
    if (s.includes("'")) { if (!s.includes('"')) q = '"'; else if (!s.includes('`') && !s.includes('${')) q = '`'; }
    let r = '';
    for (const c of s) {
      if (c === q || c === '\\') r += '\\' + c;
      else if (c === '\n') r += '\\n'; else if (c === '\t') r += '\\t'; else if (c === '\r') r += '\\r'; else if (c === '\b') r += '\\b'; else if (c === '\f') r += '\\f'; else if (c === '\v') r += '\\v';
      else if (c.charCodeAt(0) < 32) r += '\\x' + c.charCodeAt(0).toString(16).padStart(2, '0').toUpperCase();
      else r += c;
    }
    return q + r + q;
  }
  P.ctorName = function (o) {
    for (let p = o.proto; p; p = p.proto) {
      const c = p.props.get('constructor');
      if (c && !c.acc && c.v instanceof JSFunc) return c.v.fname || '';
    }
    return null;
  };
  P.inspect = function (v, depth) {
    const ctx = { seen: [], indentationLvl: 0, currentDepth: 0, depth: depth === undefined ? 2 : depth, circular: new Map(), breakLength: 80, compact: 3 };
    return this.fmtValue(ctx, v, 0, true);
  };
  P.shortInspect = function (v) {
    try {
      if (isObj(v) && !(v instanceof JSFunc)) {
        const name = v instanceof JSArr ? 'Array(' + v.items.length + ')' : v instanceof JSMap ? 'Map(' + v.m.size + ')' : v instanceof JSSet ? 'Set(' + v.m.size + ')' : (this.ctorName(v) || 'Object');
        const s = this.inspect(v, 0);
        return s.length > 30 ? name : s;
      }
      const s = typeof v === 'string' ? strEscape(v) : this.inspect(v, 1);
      return s.length > 40 ? s.slice(0, 37) + '…' : s;
    } catch (e) { return '…'; }
  };
  P.fmtValue = function (ctx, v, recurseTimes, typed) {
    if (!isObj(v)) {
      if (typeof v === 'string') return strEscape(v);
      if (typeof v === 'number') return Object.is(v, -0) ? '-0' : String(v);
      if (typeof v === 'bigint') return v + 'n';
      if (v === undefined) return 'undefined';
      return String(v);
    }
    if (v.isSymbol) return 'Symbol(' + v.key.replace(/^@@sym\d+:/, '') + ')';
    if (ctx.seen.includes(v)) {
      let idx = ctx.circular.get(v);
      if (!idx) { idx = ctx.circular.size + 1; ctx.circular.set(v, idx); }
      return '[Circular *' + idx + ']';
    }
    return this.fmtRaw(ctx, v, recurseTimes);
  };
  P.fmtRaw = function (ctx, v, recurseTimes) {
    let ctorN = this.ctorName(v);
    let braces, base = '', output = [], extrasArray = false;
    const keys = (v instanceof JSFunc) ? this.ownKeys(v).filter(k => k !== 'prototype') : this.ownKeys(v).filter(k => !(v instanceof JSArr && isIndex(k)));
    if (v instanceof JSFunc) {
      base = v.isClass ? '[class ' + (v.fname || '(anonymous)') + (v.parentClass ? ' extends ' + v.parentClass.fname : '') + ']' : (v.native ? '[Function: ' + v.fname + ']' : '[Function: ' + (v.fname || '(anonymous)') + ']');
      if (!v.fname && !v.isClass) base = '[Function (anonymous)]';
      if (!keys.length) return base;
      braces = ['{', '}'];
    } else if (v instanceof JSArr) {
      const prefix = ctorN !== 'Array' && ctorN ? ctorN + '(' + v.items.length + ') ' : '';
      braces = [prefix + '[', ']'];
      extrasArray = true;
      if (!v.items.length && !keys.length) return braces[0] + ']';
    } else if (v instanceof JSMap) {
      braces = [(ctorN || 'Map') + '(' + v.m.size + ') {', '}'];
      if (!v.m.size && !keys.length) return braces[0] + '}';
    } else if (v instanceof JSSet) {
      braces = [(ctorN || 'Set') + '(' + v.m.size + ') {', '}'];
      if (!v.m.size && !keys.length) return braces[0] + '}';
    } else if (v instanceof JSGen) {
      return 'Object [Generator] {}';
    } else if (v instanceof JSRegExp) {
      return String(v.re);
    } else if (this.isError(v)) {
      const n = this.get(v, 'name'), m = this.get(v, 'message');
      base = (ctorN && ctorN !== n ? ctorN + ' [' + n + ']' : n) + (m ? ': ' + m : '') + '\n    at <anonymous>';
      const k2 = keys.filter(k => k !== 'message' && k !== 'stack');
      if (!k2.length) return base;
      braces = ['{', '}'];
    } else {
      const prefix = ctorN === null ? '[Object: null prototype] ' : (ctorN && ctorN !== 'Object' ? ctorN + ' ' : '');
      braces = [prefix + '{', '}'];
      if (!keys.length) return prefix + '{}';
    }
    if (recurseTimes > ctx.depth) {
      if (v instanceof JSArr) return '[Array]';
      return '[' + (ctorN && ctorN !== 'Object' ? ctorN : (v instanceof JSMap ? 'Map' : v instanceof JSSet ? 'Set' : 'Object')) + ']';
    }
    ctx.seen.push(v);
    ctx.currentDepth = recurseTimes;
    const child = (x) => { ctx.indentationLvl += 2; const s = this.fmtValue(ctx, x, recurseTimes + 1); ctx.indentationLvl -= 2; return s; };
    if (v instanceof JSArr) {
      let holes = 0;
      const flush = () => { if (holes) { output.push('<' + holes + ' empty item' + (holes > 1 ? 's' : '') + '>'); holes = 0; } };
      const lim = Math.min(v.items.length, 100);
      for (let i = 0; i < lim; i++) { const x = v.items[i]; if (x === HOLE) { holes++; continue; } flush(); output.push(child(x)); }
      flush();
      if (v.items.length > 100) output.push('... ' + (v.items.length - 100) + ' more item' + (v.items.length - 100 > 1 ? 's' : ''));
    } else if (v instanceof JSMap) {
      for (const e of v.m.values()) output.push(child(e[0]) + ' => ' + child(e[1]));
    } else if (v instanceof JSSet) {
      for (const x of v.m.values()) output.push(child(x));
    }
    for (const k of keys) {
      if (this.isError(v) && (k === 'message' || k === 'stack')) continue;
      const slot = v.props.get(k);
      const kname = IDENT.test(k) ? k : strEscape(k);
      if (slot && slot.acc) { output.push(kname + ': ' + (slot.get && slot.set ? '[Getter/Setter]' : slot.get ? '[Getter]' : '[Setter]')); continue; }
      output.push(kname + ': ' + child(this.get(v, k)));
    }
    ctx.seen.pop();
    const idx = ctx.circular.get(v);
    if (idx) { const ref = '<ref *' + idx + '> '; if (base) base = ref + base; else braces[0] = ref + braces[0]; }
    return this.reduceToSingle(ctx, output, base, braces, extrasArray, recurseTimes, v);
  };
  P.reduceToSingle = function (ctx, output, base, braces, extrasArray, recurseTimes, value) {
    const entries = output.length;
    if (extrasArray && entries > 6) output = this.groupArrayElements(ctx, output, value);
    if (ctx.currentDepth - recurseTimes < ctx.compact && entries === output.length) {
      const start = output.length + ctx.indentationLvl + braces[0].length + base.length + 10;
      let total = output.length + start;
      let ok = total + output.length <= ctx.breakLength;
      if (ok) for (const o of output) { total += o.length; if (total > ctx.breakLength) { ok = false; break; } }
      if (ok && !base.includes('\n')) {
        const joined = output.join(', ');
        if (!joined.includes('\n')) return (base ? base + ' ' : '') + braces[0] + ' ' + joined + ' ' + braces[1];
      }
    }
    const ind = '\n' + ' '.repeat(ctx.indentationLvl);
    return (base ? base + ' ' : '') + braces[0] + ind + '  ' + output.join(',' + ind + '  ') + ind + braces[1];
  };
  P.groupArrayElements = function (ctx, output, value) {
    let totalLength = 0, maxLength = 0, i = 0;
    let outputLength = output.length;
    if (value && value.items && value.items.length > 100) outputLength--;
    const separatorSpace = 2;
    const dataLen = new Array(outputLength);
    for (; i < outputLength; i++) { const len = output[i].length; dataLen[i] = len; totalLength += len + separatorSpace; if (maxLength < len) maxLength = len; }
    const actualMax = maxLength + separatorSpace;
    if (actualMax * 3 + ctx.indentationLvl < ctx.breakLength && (totalLength / actualMax > 5 || maxLength <= 6)) {
      const averageBias = Math.sqrt(actualMax - totalLength / output.length);
      const biasedMax = Math.max(actualMax - 3 - averageBias, 1);
      const columns = Math.min(Math.round(Math.sqrt(2.5 * biasedMax * outputLength) / biasedMax), Math.floor((ctx.breakLength - ctx.indentationLvl) / actualMax), ctx.compact * 4, 15);
      if (columns <= 1) return output;
      const tmp = [], maxLineLength = [];
      for (let c = 0; c < columns; c++) { let lineLength = 0; for (let j = c; j < output.length; j += columns) if (dataLen[j] > lineLength) lineLength = dataLen[j]; maxLineLength.push(lineLength + separatorSpace); }
      let padStart = true;
      if (value && value.items) for (let k = 0; k < output.length; k++) { const x = value.items[k]; if (typeof x !== 'number' && typeof x !== 'bigint') { padStart = false; break; } }
      for (let k = 0; k < outputLength; k += columns) {
        const max = Math.min(k + columns, outputLength);
        let s = '', j = k;
        for (; j < max - 1; j++) { const padding = maxLineLength[j - k]; s += padStart ? (output[j] + ', ').padStart(padding, ' ') : (output[j] + ', ').padEnd(padding, ' '); }
        if (padStart) { const padding = maxLineLength[j - k] - separatorSpace; s += output[j].padStart(padding, ' '); }
        else s += output[j];
        tmp.push(s);
      }
      if (outputLength < output.length) tmp.push(output[outputLength]);
      return tmp;
    }
    return output;
  };
  P.formatLog = function (args) {
    if (!args.length) return '';
    let first = args[0];
    let rest = args.slice(1);
    let out = '';
    if (typeof first === 'string' && /%[sdifoOjc%]/.test(first) && rest.length) {
      let i = 0;
      first = first.replace(/%([sdifoOjc%])/g, (m, c) => {
        if (c === '%') return '%';
        if (i >= rest.length) return m;
        const v = rest[i++];
        switch (c) {
          case 's': return typeof v === 'string' ? v : this.inspect(v, 1);
          case 'd': case 'i': return isObj(v) ? 'NaN' : String(c === 'i' ? Math.trunc(this.toNum(v)) : this.toNum(v));
          case 'f': return String(this.toNum(v));
          case 'o': case 'O': case 'j': return this.inspect(v, 4);
          case 'c': return '';
        }
      });
      rest = rest.slice(i);
    }
    const parts = [typeof first === 'string' ? first : this.inspect(first)];
    for (const v of rest) parts.push(typeof v === 'string' ? v : this.inspect(v));
    return parts.join(' ');
  };

  // ======================= snapshot =======================
  P.snapshot = function () {
    const ver = R.ver();
    const reuse = this._lastHeap && this._lastVer === ver;
    const snap = this.snapshotInner(reuse ? this._lastHeap : null);
    if (!reuse) { this._lastHeap = snap.heap; this._lastVer = R.ver(); }
    return snap;
  };
  P.snapshotInner = function (reuseHeap) {
    const stepNo = this.rec.steps.length;
    const heapSeen = new Set();
    const order = [];
    const funcText = (f) => {
      if (f.isClass) return 'class ' + (f.fname || '(匿名)');
      if (f.native) return 'built-in ' + f.fname;
      if (f.bound) return 'bound ' + f.bound.target.fname;
      const params = f.node ? f.node.params.map(p => p.type === 'Id' ? p.name : p.type === 'Rest' ? '...' + (p.arg.name || '') : p.type === 'Default' ? (p.target.name || '?') + '=' : '{…}') : [];
      return (f.isArrow || (f.node && f.node.arrow) ? '' : 'function ') + (f.fname || '') + '(' + params.join(', ') + ')' + (f.node && f.node.arrow ? ' =>' : '');
    };
    const desc = (v) => {
      if (v === undefined) return { k: 'null', text: 'undefined' };
      if (v === null) return { k: 'null', text: 'null' };
      if (v === HOLE) return { k: 'prim', text: 'empty', type: 'hole' };
      switch (typeof v) {
        case 'number': return { k: 'prim', text: Object.is(v, -0) ? '-0' : String(v), type: 'number' };
        case 'boolean': return { k: 'prim', text: String(v), type: 'boolean' };
        case 'bigint': return { k: 'prim', text: v + 'n', type: 'bigint' };
        case 'string': return { k: 'str', text: strEscape(v.length > 300 ? v.slice(0, 300) + '…' : v) };
      }
      if (envMode && v instanceof JSFunc && !v.isClass) { if (!heapSeen.has(v)) { heapSeen.add(v); order.push(v); } return { k: 'ref', id: v.id }; }
      if (v instanceof JSFunc) return { k: 'func', text: funcText(v) };
      if (v.isSymbol) return { k: 'prim', text: 'Symbol()' };
      if (v instanceof JSRegExp) return { k: 'prim', text: String(v.re) };
      if (!heapSeen.has(v)) { heapSeen.add(v); order.push(v); }
      return { k: 'ref', id: v.id };
    };
    const envMode = this.envMode;
    const frames = [];
    const extraFrames = envMode ? [] : null;
    for (const f of this.frames.concat(envMode ? this.exitedFrames : [])) {
      const scopes = [];
      const stop = f.isGlobal ? this.globalScope : f.fnScope;
      for (let s = f.scope; s; s = s.parent) { scopes.push(s); if (s === stop) break; }
      scopes.reverse();
      const vars = [];
      if (!f.isGlobal && isObj(f.thisV) && !(f.thisV instanceof JSFunc && !f.fn.isClass && false)) vars.push({ name: 'this', val: desc(f.thisV), isThis: true });
      for (const s of scopes) for (const [k, r] of s.vars) {
        if (r.hidden || r.tdz || k === 'arguments') continue;
        vars.push({ name: k, val: desc(r.v), type: this.typeOf(r.v), kind: r.kind });
      }
      const fr = { id: f.id, name: f.name, vars, line: f.line };
      if (f.returning) fr.ret = desc(f.retVal);
      if (envMode) {
        if (f.isGlobal) { fr.label = 'Global'; fr.seq = 0; }
        else { fr.label = f.label; fr.parent = f.parent; fr.seq = f.seq; if (f.fn && !f.fn.fname && f.fn.node) fr.lambdaLine = f.fn.node.line; }
        if (f.exited) { fr.exited = true; extraFrames.push(fr); continue; }
      }
      frames.push(fr);
    }
    const tail = { lang: this.ts ? 'ts' : 'js', showAddr: false };
    if (envMode) { tail.envMode = true; tail.extraFrames = extraFrames; }
    if (reuseHeap) return Object.assign({ frames, globals: null, heap: reuseHeap }, tail);
    const heap = [];
    for (let i = 0; i < order.length && heap.length < 600; i++) {
      const o = order[i];
      const flags = {};
      let ent;
      const plain = !(o instanceof JSArr || o instanceof JSMap || o instanceof JSSet || o instanceof JSGen) && !this.isError(o);
      if (plain && o._dcVer === o.props.ver && o._dcVal) {
        for (const k of o._dcKids) if (!heapSeen.has(k)) { heapSeen.add(k); order.push(k); }
        heap.push({ id: o.id, label: o._dcLabel, val: o._dcVal, flags, kind: 'js', born: o.born });
        continue;
      }
      if (o instanceof JSFunc) {
        if (o.native || o.bound) ent = { label: '内置函数', val: { k: 'fnobj', name: o.bound ? 'bound ' + (o.bound.target.fname || '') : o.fname, params: '...', builtin: true } };
        else {
          const ps = o.node ? o.node.params.map(p => p.type === 'Id' ? p.name : p.type === 'Rest' ? '...' + (p.arg.name || '') : p.type === 'Default' ? (p.target.name || '?') + '=…' : '{…}').join(', ') : '';
          ent = { label: '函数', val: { k: 'fnobj', name: o.fname || '', arrow: !!(o.node && o.node.arrow), params: ps, line: o.fname ? null : (o.node ? o.node.line : null), parent: o.parentLabel || 'Global' } };
        }
      }
      else if (o instanceof JSArr) ent = { label: 'Array', val: { k: 'list', kind: 'array', items: o.items.slice(0, 150).map(desc), total: o.items.length } };
      else if (o instanceof JSMap) ent = { label: 'Map', val: { k: 'map', entries: [...o.m.values()].slice(0, 150).map(e => ({ key: desc(e[0]), val: desc(e[1]) })), total: o.m.size } };
      else if (o instanceof JSSet) ent = { label: 'Set', val: { k: 'list', kind: 'set', items: [...o.m.values()].slice(0, 150).map(desc), total: o.m.size } };
      else if (o instanceof JSGen) ent = { label: 'Generator', val: { k: 'list', kind: 'iter', items: o.items.slice(o.i, o.i + 100).map(desc), total: o.items.length - o.i } };
      else {
        const cn = this.ctorName(o);
        const fields = [];
        if (this.isError(o)) fields.push({ name: 'message', val: desc(this.get(o, 'message')) });
        for (const k of this.ownKeys(o)) {
          if (this.isError(o) && (k === 'message' || k === 'stack')) continue;
          const s = o.props.get(k);
          if (s && s.acc) { fields.push({ name: k, val: { k: 'prim', text: '[getter]' } }); continue; }
          fields.push({ name: k, val: desc(s ? s.v : this.get(o, k)) });
        }
        const label = cn && cn !== 'Object' ? cn : (cn === null ? 'Object' : 'Object');
        ent = { label, val: { k: 'struct', name: label, fields } };
        if (this.isError(o)) flags.exc = true;
        else if (plain) { o._dcVer = o.props.ver; o._dcVal = ent.val; o._dcLabel = label; o._dcKids = []; for (const s of o.props.values()) if (s && !s.acc && isObj(s.v) && !(s.v instanceof JSFunc && (!envMode || s.v.isClass)) && !s.v.isSymbol && !(s.v instanceof JSRegExp)) o._dcKids.push(s.v); }
      }
      ent.id = o.id; ent.flags = flags; ent.kind = 'js'; ent.born = o.born;
      heap.push(ent);
    }
    return Object.assign({ frames, globals: null, heap }, tail);
  };

  function runJS(ts) {
    return function (code, opts) {
      opts = opts || {};
      let prog;
      try { prog = DSV.jsParse(code, ts); }
      catch (e) { return DSV.finishRun(new DSV.Recorder(opts), e); }
      R.setCurStep(0);
      const it = new DSV.JSInterp(prog, opts, ts);
      return it.run();
    };
  }
  DSV.langs.js = { name: 'JavaScript', run: runJS(false) };
  DSV.langs.ts = { name: 'TypeScript', run: runJS(true) };
})(typeof window !== 'undefined' ? window : globalThis);
