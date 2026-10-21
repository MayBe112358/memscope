// ===== Visualization renderer: stack + heap + arrows =====
(function (G) {
  const DSV = G.DSV;
  const esc = (s) => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
  const IDX_NAMES = /^(i|j|k|l|r|lo|hi|low|high|mid|left|right|start|end|idx|index|pos|p|q|top|front|rear|head|tail|cur|curr|pivot|min_?idx|max_?idx|minIndex|maxIndex|minIdx|maxIdx|smallest|largest|parent|child|slow|fast|ii|jj|row|col)$/i;
  const BACK_NAMES = /^(prev|previous|parent|up|back|father|pre|predecessor|pred|before|last)$/i;
  const GX = 46, GY = 34;

  class Viz {
    constructor(root, opts) {
      this.root = root;
      this.opts = opts || {};
      root.innerHTML =
        '<div class="viz-sizer"><div class="viz-canvas">' +
        '<svg class="viz-arrows" aria-hidden="true"><defs>' +
        '<marker id="ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="ah"></path></marker>' +
        '<marker id="ah-hot" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="ah-hot"></path></marker>' +
        '<marker id="ah-bad" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="ah-bad"></path></marker>' +
        '</defs><g class="arrows"></g></svg>' +
        '<div class="viz-stack"></div><div class="viz-heap"></div>' +
        '</div></div>';
      this.sizer = root.querySelector('.viz-sizer');
      this.canvas = root.querySelector('.viz-canvas');
      this.stackEl = root.querySelector('.viz-stack');
      this.heapEl = root.querySelector('.viz-heap');
      this.svg = root.querySelector('.viz-arrows');
      this.arrowG = root.querySelector('.arrows');
      this.heapEls = new Map();
      this.pos = new Map();
      this.scale = 1;
      this.heapY = 46;
      this.autoFit = true;
      this.anim = null;
    }

    // ---------- signatures (for change detection) ----------
    sigMap(snap) {
      if (snap._sig) return snap._sig;
      const m = new Map();
      const leaf = (d) => {
        switch (d.k) {
          case 'prim': return 'p' + d.text; case 'str': return 's' + d.text; case 'null': return 'n'; case 'uninit': return 'u';
          case 'ref': return 'r' + d.id + ':' + (d.sub || '') + (d.dangling ? '!' : ''); case 'func': return 'f' + d.text; case 'raw': return 'w' + d.text;
        }
        return '?';
      };
      const walk = (base, path, d) => {
        if (!d) return;
        if (d.k === 'arr') { d.elems.forEach((e, i) => walk(base, path ? path + '.' + i : String(i), e)); m.set(base + '#' + path + '#len', String(d.total)); return; }
        if (d.k === 'struct') { d.fields.forEach(f => walk(base, path ? path + '.' + f.name : f.name, f.val)); return; }
        if (d.k === 'list') { d.items.forEach((e, i) => walk(base, (path ? path + '.' : '') + i, e)); m.set(base + '#' + path + '#len', String(d.total)); return; }
        if (d.k === 'map') { d.entries.forEach((en, i) => { const kk = leaf(en.key); walk(base, (path ? path + '.' : '') + 'k:' + kk, en.val); }); return; }
        m.set(base + '#' + path, leaf(d));
      };
      const frames = (snap.globals ? [snap.globals].concat(snap.frames) : snap.frames).concat(snap.extraFrames || []);
      for (const f of frames) for (const v of f.vars) walk('F' + f.id + '/' + v.name, '', v.val);
      for (const h of snap.heap) walk('H' + h.id, '', h.val);
      snap._sig = m;
      return m;
    }

    // ---------- value rendering ----------
    valHTML(d, base, path, ctx, depth) {
      depth = depth || 0;
      const a = base + (path ? ':' + path : '');
      const sigKey = ctx.sigBase + '#' + (path || '');
      let chg = '';
      if (ctx.prevSig && ctx.changedKeys.has(sigKey)) chg = ' chg';
      switch (d.k) {
        case 'prim': return '<span class="v prim' + (d.type === 'hole' ? ' hole' : '') + chg + '" data-a="' + a + '">' + esc(d.text) + '</span>';
        case 'str': return '<span class="v str' + chg + '" data-a="' + a + '">' + esc(d.text) + '</span>';
        case 'null': return '<span class="v nul' + (d.wild ? ' wild' : '') + chg + '" data-a="' + a + '"' + (d.wild ? ' title="未初始化的指针：指向一个随机地址"' : '') + '>' + esc(d.wild ? '野指针' : d.text) + '</span>';
        case 'uninit': return '<span class="v uninit' + chg + '" data-a="' + a + '" title="未初始化：值是随机的“垃圾值”">?</span>';
        case 'func': return '<span class="v fn' + chg + '" data-a="' + a + '" title="' + esc(d.text) + '">' + esc(d.text.length > 34 ? d.text.slice(0, 32) + '…' : d.text) + '</span>';
        case 'raw': return '<span class="v raw" data-a="' + a + '">' + esc(d.text) + '</span>';
        case 'ref': {
          if (d.lit && !ctx.showLiterals) return '<span class="v ptr lit' + chg + '" data-a="' + a + '" title="指向只读区里的字符串字面量（在设置里可以把它单独画出来）"><span class="litarrow">→</span>' + esc(d.lit.length > 24 ? d.lit.slice(0, 22) + '…"' : d.lit) + '</span>';
          let addr = '';
          if (ctx.showAddr && ctx.addrOf) { const ad = ctx.addrOf(d.id, d.sub); if (ad) addr = '<span class="paddr">' + ad + '</span>'; }
          const dg = d.dangling ? ' dangling' : '';
          const ttl = d.dangling === 'freed' ? '悬空指针：指向的内存已经被释放' : (d.dangling === 'dead' ? '悬空指针：指向的局部变量已经销毁' : (d.isAlias ? '引用（别名）' : '指针 / 引用'));
          return '<span class="v ptr' + dg + (d.isAlias ? ' alias' : '') + chg + '" data-a="' + a + '" data-t="' + d.id + '" data-s="' + (d.sub || '') + '" title="' + ttl + '"><span class="dot"></span>' + addr + '</span>';
        }
        case 'arr': return this.arrHTML(d, base, path, ctx, depth, depth === 0 && this.isPtrArray(d));
        case 'struct': {
          if (d.name === 'pair' && d.fields.length === 2 && d.fields[0].name === 'first' && d.fields[1].name === 'second' && d.fields.every(f => this.isSimple(f.val))) {
            return '<span class="v st tup" data-a="' + a + '" title="pair：first, second">(' + this.valHTML(d.fields[0].val, base, (path ? path + '.' : '') + 'first', ctx, depth + 1) + '<span class="tsep">,</span>' + this.valHTML(d.fields[1].val, base, (path ? path + '.' : '') + 'second', ctx, depth + 1) + ')</span>';
          }
          let h = '<span class="v st" data-a="' + a + '">';
          for (const f of d.fields) {
            const p = path ? path + '.' + f.name : f.name;
            const sub = Object.assign({}, ctx);
            h += '<span class="sf"><span class="sk">' + esc(f.name) + '</span>' + this.valHTML(f.val, base, p, Object.assign(ctx, {}), depth + 1) + '</span>';
          }
          return h + '</span>';
        }
      }
      return '<span class="v">?</span>';
    }
    isMatrix(d) {
      if (!d.elems || d.elems.length < 2 || d.elems.length > 16 || d.total !== d.elems.length) return false;
      const w = d.elems[0].k === 'arr' ? d.elems[0].total : -1;
      if (w < 1 || w > 16) return false;
      return d.elems.every(r => r.k === 'arr' && !r.charArr && r.total === w && r.elems.length === w && r.elems.every(e => e.k === 'prim' || e.k === 'uninit'));
    }
    matrixHTML(d, base, path, ctx) {
      const a = base + (path ? ':' + path : '');
      const markers = ctx.markers && ctx.markers.get(a);
      const w = d.elems[0].total, n = d.elems.length;
      const isOn = (e) => e.k === 'prim' && (e.text === 'true' || e.text === '1' || e.text === 'True');
      const boolish = d.elems.every(r => r.elems.every(e => e.k === 'prim' && /^(true|false|True|False|0|1)$/.test(e.text)));
      const isBool = d.elems.every(r => r.elems.every(e => e.k === 'prim' && /^(true|false|True|False)$/.test(e.text)));
      let h = '<span class="v mat' + (isBool ? ' boolm' : '') + '" data-a="' + a + '"><table class="mtx"><thead><tr><th class="corner" title="行下标 \\ 列下标">i\\j</th>';
      for (let j = 0; j < w; j++) h += '<th>' + j + '</th>';
      h += '</tr></thead><tbody>';
      for (let i = 0; i < n; i++) {
        const row = d.elems[i];
        const rp = path ? path + '.' + i : String(i);
        const mk = markers ? markers.filter(m => m.idx === i).map(m => m.name) : null;
        h += '<tr data-a="' + base + ':' + rp + '"' + (mk && mk.length ? ' class="marked"' : '') + '><th>' + i + (mk && mk.length ? '<span class="mk">' + esc(mk.join(' ')) + '</span>' : '') + '</th>';
        for (let j = 0; j < w; j++) {
          const e = row.elems[j];
          h += '<td' + (boolish && isOn(e) ? ' class="on"' : '') + '>' + this.valHTML(e, base, rp + '.' + j, ctx, 2) + '</td>';
        }
        h += '</tr>';
      }
      h += '</tbody></table>';
      const vn = ctx.varName || ''; const nameHint = /adj|graph|edge|link|conn|locked|visit|mat/i.test(vn) || /^g$/i.test(vn);
      if ((isBool || (boolish && nameHint)) && n === w && n <= 10 && ctx.heapTree) h += this.adjGraphHTML(d, base, path, ctx, isOn);
      return h + '</span>';
    }
    adjGraphHTML(d, base, path, ctx, isOn) {
      const n = d.elems.length;
      const R = n <= 3 ? 34 : n <= 6 ? 46 : 60;
      const W = R * 2 + 40, H = R * 2 + 36, cx = W / 2, cy = H / 2 + 2, r = 12;
      const P = []; for (let i = 0; i < n; i++) { const t = -Math.PI / 2 + i * 2 * Math.PI / n; P.push({ x: cx + R * Math.cos(t), y: cy + R * Math.sin(t) }); }
      let edges = '', cnt = 0;
      let sym = true;
      for (let i = 0; i < n && sym; i++) for (let j = 0; j < n; j++) if (isOn(d.elems[i].elems[j]) !== isOn(d.elems[j].elems[i])) { sym = false; break; }
      const arrow = (x, y, ux, uy) => { const s = 6; return '<path class="ah" d="M' + x.toFixed(1) + ' ' + y.toFixed(1) + ' L' + (x - ux * s - uy * s * 0.55).toFixed(1) + ' ' + (y - uy * s + ux * s * 0.55).toFixed(1) + ' L' + (x - ux * s + uy * s * 0.55).toFixed(1) + ' ' + (y - uy * s - ux * s * 0.55).toFixed(1) + 'Z"/>'; };
      for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
        if (!isOn(d.elems[i].elems[j])) continue;
        cnt++;
        const p = path ? path + '.' + i + '.' + j : i + '.' + j;
        const hot = ctx.prevSig && ctx.changedKeys.has(ctx.sigBase + '#' + p) ? ' hot' : '';
        if (i === j) { const a = P[i]; const ox = (a.x - cx) / R, oy = (a.y - cy) / R; const lx = a.x + ox * (r + 7), ly = a.y + oy * (r + 7); edges += '<g class="e' + hot + '"><circle class="loop" cx="' + lx.toFixed(1) + '" cy="' + ly.toFixed(1) + '" r="7"/></g>'; continue; }
        const a = P[i], b = P[j];
        let dx = b.x - a.x, dy = b.y - a.y; const L = Math.hypot(dx, dy); const ux = dx / L, uy = dy / L;
        if (sym) {
          if (j < i) continue;
          const p2 = path ? path + '.' + j + '.' + i : j + '.' + i;
          const hot2 = hot || (ctx.prevSig && ctx.changedKeys.has(ctx.sigBase + '#' + p2)) ? ' hot' : '';
          edges += '<g class="e' + hot2 + '"><line x1="' + (a.x + ux * r).toFixed(1) + '" y1="' + (a.y + uy * r).toFixed(1) + '" x2="' + (b.x - ux * r).toFixed(1) + '" y2="' + (b.y - uy * r).toFixed(1) + '"/></g>';
          continue;
        }
        const both = isOn(d.elems[j].elems[i]);
        const off = both ? 5 : 0; const nx = -uy * off, ny = ux * off;
        const x1 = a.x + ux * r + nx, y1 = a.y + uy * r + ny, x2 = b.x - ux * (r + 1) + nx, y2 = b.y - uy * (r + 1) + ny;
        edges += '<g class="e' + hot + '"><line x1="' + x1.toFixed(1) + '" y1="' + y1.toFixed(1) + '" x2="' + x2.toFixed(1) + '" y2="' + y2.toFixed(1) + '"/>' + arrow(x2, y2, ux, uy) + '</g>';
      }
      let nodes = '';
      for (let i = 0; i < n; i++) {
        let indeg = 0; for (let k = 0; k < n; k++) if (k !== i && isOn(d.elems[k].elems[i])) indeg++;
        nodes += '<g class="n' + (indeg === 0 && cnt && !sym ? ' src' : '') + '" transform="translate(' + P[i].x.toFixed(1) + ',' + P[i].y.toFixed(1) + ')"><circle r="' + r + '"/><text dy="4">' + i + '</text></g>';
      }
      return '<div class="htree-wrap agraph"><div class="htree-cap">' + (!cnt ? '看成图（还没有边）' : sym ? '看成无向图' : '看成有向图：[i][j] 为真 = 边 i→j<br>实心 = 没有入边的点') + '</div><svg class="adjg" width="' + W + '" height="' + H + '" viewBox="0 0 ' + W + ' ' + H + '">' + edges + nodes + '</svg></div>';
    }
    arrHTML(d, base, path, ctx, depth, vertical) {
      if (this.isMatrix(d)) return this.matrixHTML(d, base, path, ctx);
      const a = base + (path ? ':' + path : '');
      const markers = ctx.markers && ctx.markers.get(a);
      const isPtrArr = d.elems.length && d.elems.every(e => e.k === 'ref' || e.k === 'null' || e.k === 'uninit');
      const letters = d.total === 26 && isPtrArr;
      let h = '<span class="v arr' + (d.charArr ? ' chars' : '') + (vertical ? ' vert' : '') + '" data-a="' + a + '">';
      let n = d.elems.length;
      if (!d.total) return '<span class="v arr empty-arr" data-a="' + a + '"><span class="empty">空数组</span></span>';
      const collapse = ctx.collapseNull;
      let tailFrom = -1;
      if (d.charArr) {
        const z = d.elems.findIndex(e => e.k === 'prim' && e.text === "'\\0'");
        if (z >= 0 && z < n - 2 && d.elems.slice(z + 1).every(e => e.k === 'uninit' || (e.k === 'prim' && e.text === "'\\0'"))) tailFrom = z + 1;
      }
      let i = 0;
      while (i < n) {
        const e = d.elems[i];
        if (i === tailFrom) {
          h += '<span class="cell run" title="\\0 之后的 ' + (n - i) + ' 个字节：没有用到（未初始化或为 0）"><span class="cv"><span class="v nul">… ×' + (n - i) + '</span></span><span class="ci">' + i + '–' + (n - 1) + '</span></span>';
          break;
        }
        if (collapse && e.k === 'null' && !(markers && markers.some(m => m.idx === i))) {
          let j = i;
          while (j < n && d.elems[j].k === 'null' && !(markers && markers.some(m => m.idx === j))) j++;
          if (j - i >= 4) {
            const lab = letters ? String.fromCharCode(97 + i) + '–' + String.fromCharCode(96 + j) : i + '–' + (j - 1);
            h += '<span class="cell run"><span class="cv"><span class="v nul">' + esc(e.text) + ' ×' + (j - i) + '</span></span><span class="ci">' + lab + '</span></span>';
            i = j; continue;
          }
        }
        const p = path ? path + '.' + i : String(i);
        let inner;
        if (d.charArr && e.k === 'prim') {
          const sigKey = ctx.sigBase + '#' + p;
          const chg = ctx.prevSig && ctx.changedKeys.has(sigKey) ? ' chg' : '';
          inner = '<span class="v prim ch' + chg + (e.text === "'\\0'" ? ' nulch' : '') + '" data-a="' + base + ':' + p + '">' + esc(e.text.replace(/^'(.*)'$/, '$1')) + '</span>';
        } else inner = this.valHTML(e, base, p, ctx, depth + 1);
        const mk = markers ? markers.filter(m => m.idx === i).map(m => m.name) : null;
        h += '<span class="cell' + (mk && mk.length ? ' marked' : '') + '"><span class="cv">' + inner + '</span><span class="ci">' + (letters ? String.fromCharCode(97 + i) : i) + '</span>' + (mk && mk.length ? '<span class="mk">' + esc(mk.join(' ')) + '</span>' : '') + '</span>';
        i++;
      }
      if (d.total > n) h += '<span class="cell more"><span class="cv">…</span><span class="ci">共 ' + d.total + '</span></span>';
      h += '</span>';
      if (d.charArr) {
        let s = '';
        for (const e of d.elems) { if (e.k !== 'prim') { s += '?'; continue; } const ch = e.text.replace(/^'(.*)'$/, '$1'); if (ch === '\\0') break; s += ch === '\\n' ? '\\n' : ch; }
        h = '<span class="arrwrap">' + h + '<span class="cstr">"' + esc(s) + '"</span></span>';
      }
      return h;
    }
    listHTML(d, id, ctx, vertical) {
      // managed containers: list/tuple/set/deque/stack/queue/heap/iter
      const base = id;
      const markers = ctx.markers && ctx.markers.get(base);
      const kind = d.kind;
      const items = d.items;
      let h = '';
      if (kind === 'stack' && !vertical) {
        // draw as a vertical pile, top first
        h += '<div class="lst stack">';
        if (!items.length) h += '<div class="empty">（空栈）</div>';
        for (let i = items.length - 1; i >= 0; i--) {
          h += '<div class="srow' + (i === items.length - 1 ? ' top' : '') + '"><span class="ci">' + i + '</span>' + this.valHTML(items[i], base, String(i), ctx, 1) + (i === items.length - 1 ? '<span class="tag">栈顶</span>' : '') + '</div>';
        }
        h += '</div>';
        return h;
      }
      const showIdx = kind !== 'set' && kind !== 'iter';
      h += '<div class="lst ' + kind + (vertical ? ' vert' : '') + '">';
      if (!items.length) h += '<div class="empty">' + ({ set: '空集合', queue: '空队列', deque: '空', heap: '空堆', iter: '已耗尽' }[kind] || '空') + '</div>';
      items.forEach((e, i) => {
        const mk = markers ? markers.filter(m => m.idx === i).map(m => m.name) : null;
        let tag = '';
        if ((kind === 'queue' || kind === 'deque') && items.length) { if (i === 0) tag = '<span class="tag">' + (kind === 'queue' ? '队首' : '左端') + '</span>'; else if (i === items.length - 1) tag = '<span class="tag r">' + (kind === 'queue' ? '队尾' : '右端') + '</span>'; }
        if (kind === 'heap' && i === 0) tag = '<span class="tag">堆顶</span>';
        h += '<span class="cell' + (mk && mk.length ? ' marked' : '') + '">' + tag + '<span class="cv">' + this.valHTML(e, base, String(i), ctx, 1) + '</span>' + (showIdx ? '<span class="ci">' + i + '</span>' : '') + (mk && mk.length ? '<span class="mk">' + esc(mk.join(' ')) + '</span>' : '') + '</span>';
      });
      if (d.total > items.length) h += '<span class="cell more"><span class="cv">…</span><span class="ci">共 ' + d.total + '</span></span>';
      h += '</div>';
      if (kind === 'heap' && items.length > 1 && ctx.heapTree) h += this.heapTreeHTML(items);
      return h;
    }
    heapTreeHTML(items) {
      const n = Math.min(items.length, 31);
      const levels = Math.floor(Math.log2(n)) + 1;
      const W = Math.max(160, Math.pow(2, levels - 1) * 34);
      const H = levels * 38;
      let lines = '', nodes = '';
      const posOf = (i) => { const lv = Math.floor(Math.log2(i + 1)); const k = i + 1 - Math.pow(2, lv); const cnt = Math.pow(2, lv); return { x: (k + 0.5) * W / cnt, y: 16 + lv * 38 }; };
      for (let i = 1; i < n; i++) { const p = posOf(i), q = posOf((i - 1) >> 1); lines += '<line x1="' + q.x + '" y1="' + q.y + '" x2="' + p.x + '" y2="' + p.y + '"></line>'; }
      for (let i = 0; i < n; i++) {
        const p = posOf(i);
        const it = items[i]; const t = it.k === 'prim' || it.k === 'str' ? it.text : it.k === 'ref' ? '•' : it.k === 'struct' && it.fields.length && it.fields.every(f => f.val.k === 'prim' || f.val.k === 'str') ? it.fields.map(f => f.val.text).join(',') : '?';
        nodes += '<g transform="translate(' + p.x + ',' + p.y + ')"><circle r="13"></circle><text dy="4">' + esc(t.length > 5 ? t.slice(0, 4) + '…' : t) + '</text></g>';
      }
      return '<div class="htree-wrap"><div class="htree-cap">按完全二叉树看：下标 i 的孩子是 2i+1 和 2i+2</div><svg class="htree" width="' + W + '" height="' + H + '" viewBox="0 0 ' + W + ' ' + H + '">' + lines + nodes + '</svg></div>';
    }
    mapHTML(d, id, ctx) {
      let h = '<table class="mapt"><tbody>';
      if (!d.entries.length) h += '<tr><td class="empty" colspan="2">空</td></tr>';
      d.entries.forEach((en, i) => {
        const kk = en.key.k === 'prim' ? 'p' + en.key.text : en.key.k === 'str' ? 's' + en.key.text : en.key.k === 'null' ? 'n' : en.key.k === 'ref' ? 'r' + en.key.id + ':' : '?';
        const p = 'k:' + kk;
        h += '<tr><td class="mk-k">' + this.valHTML(en.key, id, 'key' + i, Object.assign({}, ctx, { changedKeys: new Set() })) + '</td><td class="mk-v">' + this.valHTML(en.val, id, p, ctx, 1) + '</td></tr>';
      });
      if (d.total > d.entries.length) h += '<tr><td colspan="2" class="more">… 共 ' + d.total + ' 项</td></tr>';
      return h + '</tbody></table>';
    }
    structHTML(d, id, ctx, compact) {
      if (compact) {
        let h = '<div class="sth">';
        for (const f of d.fields) h += '<div class="fcell"><span class="fk">' + esc(f.name) + '</span><span class="fv">' + this.valHTML(f.val, id, f.name, ctx, 1) + '</span></div>';
        if (!d.fields.length) h += '<div class="empty">（没有字段）</div>';
        return h + '</div>';
      }
      let h = '<table class="stv"><tbody>';
      for (const f of d.fields) h += '<tr><td class="fk">' + esc(f.name) + '</td><td class="fv">' + this.valHTML(f.val, id, f.name, ctx, 1) + '</td></tr>';
      if (!d.fields.length) h += '<tr><td class="empty">（没有属性）</td></tr>';
      return h + '</tbody></table>';
    }
    isPtrArray(d) {
      if (!d.elems || d.elems.length < 2 || d.elems.length > 40) return false;
      const refs = d.elems.filter(e => e.k === 'ref').length;
      return refs >= 2 && d.elems.every(e => e.k === 'ref' || e.k === 'null');
    }
    isSimple(d) { return ['prim', 'str', 'null', 'ref', 'uninit', 'func'].includes(d.k) && !(d.k === 'str' && d.text.length > 18) && !(d.k === 'func'); }
    isVertical(ent) {
      const v = ent.val;
      const items = v.k === 'arr' ? v.elems : (v.k === 'list' && v.kind !== 'stack' && v.kind !== 'set' ? v.items : null);
      if (!items || items.length < 2) return false;
      const refs = items.filter(e => e.k === 'ref').length;
      const ptrish = items.filter(e => e.k === 'ref' || e.k === 'null').length;
      return refs >= 2 && ptrish === items.length && items.length <= 40;
    }

    // ---------- main render ----------
    render(step, prev, settings, extra) {
      let snap = step.snap;
      if (!settings.showLiterals) snap = Object.assign({}, snap, { heap: snap.heap.filter(h => !(h.flags && h.flags.rodata)) });
      const ctx0 = {
        showLiterals: settings.showLiterals,
        showAddr: settings.showAddr && snap.showAddr,
        collapseNull: settings.collapseNull,
        heapTree: settings.heapTree,
        prevSig: prev ? this.sigMap(prev.snap) : null,
      };
      const cur = this.sigMap(snap);
      const changed = new Set();
      if (ctx0.prevSig) {
        const prevHeapIds = new Set(prev.snap.heap.map(h => 'H' + h.id));
        const prevFrames = new Set((prev.snap.globals ? [prev.snap.globals] : []).concat(prev.snap.frames).map(f => 'F' + f.id));
        for (const [k, v] of cur) {
          const pv = ctx0.prevSig.get(k);
          if (pv === undefined) {
            const base = k.split('#')[0];
            const objKey = base.startsWith('H') ? base : base.split('/')[0];
            if (base.startsWith('H') ? prevHeapIds.has(base) : prevFrames.has(objKey)) changed.add(k);
          } else if (pv !== v) changed.add(k);
        }
      }
      ctx0.changedKeys = changed;
      // address lookup (C)
      const heapById = new Map(snap.heap.map(h => [h.id, h]));
      const varAnchors = new Map();
      for (const f of (snap.globals ? [snap.globals] : []).concat(snap.frames)) for (const v of f.vars) if (v.anchor) varAnchors.set(v.anchor, v);
      ctx0.addrOf = (id, sub) => {
        const h = heapById.get(id); const v = varAnchors.get(id);
        const base = h ? h.addr : v ? v.addr : null;
        if (!base) return null;
        if (!sub) return base;
        return base + '+…';
      };
      // index markers for the current frame
      const markers = new Map();
      if (settings.markers && snap.frames.length) {
        const fr = snap.frames[snap.frames.length - 1];
        const idxVars = fr.vars.filter(v => v.val.k === 'prim' && /^-?\d+$/.test(v.val.text) && IDX_NAMES.test(v.name));
        if (idxVars.length) {
          const arrays = [];
          const addArr = (anchor, len) => arrays.push({ anchor, len });
          const look = (d, anchorBase) => {
            if (!d) return;
            if (d.k === 'ref') { const h = heapById.get(d.id); if (h) { if (h.val.k === 'arr') { if (!d.sub) addArr(h.id, h.val.total); } else if (h.val.k === 'list') addArr(h.id, h.val.total); else if (h.val.k === 'struct') h.val.fields.forEach(f => { if (f.val.k === 'ref') { const h2 = heapById.get(f.val.id); if (h2 && (h2.val.k === 'list' || h2.val.k === 'arr')) addArr(h2.id, h2.val.total); } else if (f.val.k === 'arr') addArr(h.id + ':' + f.name, f.val.total); }); } else { const v = varAnchors.get(d.id); if (v && v.val.k === 'arr') addArr(d.id + (d.sub ? ':' + d.sub : ''), v.val.total); } }
            else if (d.k === 'arr') addArr(anchorBase, d.total);
          };
          for (const v of fr.vars) look(v.val, v.anchor || ('F' + fr.id + '/' + v.name));
          for (const ar of arrays) {
            const ms = [];
            for (const iv of idxVars) { const k = +iv.val.text; if (k >= 0 && k < ar.len) ms.push({ name: iv.name, idx: k }); }
            if (ms.length) markers.set(ar.anchor, (markers.get(ar.anchor) || []).concat(ms));
          }
        }
      }
      ctx0.markers = markers;

      // ----- stack -----
      let sh = '';
      let allFrames = (snap.globals ? [snap.globals] : []).concat(snap.frames);
      if (snap.envMode && snap.extraFrames && snap.extraFrames.length) allFrames = allFrames.concat(snap.extraFrames).sort((a, b) => (a.seq || 0) - (b.seq || 0));
      const topId = snap.frames.length ? snap.frames[snap.frames.length - 1].id : null;
      if (!allFrames.length) sh += '<div class="frame done"><div class="fh"><span class="fname">（程序已结束，栈已清空）</span></div></div>';
      for (const f of allFrames) {
        const isTop = f.id === topId;
        const isGlob = f.id === 'globals' || f.id === 'g';
        sh += '<div class="frame' + (isTop ? ' top' : '') + (isGlob ? ' glob' : '') + (f.ret ? ' returning' : '') + (f.exited ? ' exited' : '') + '" data-fid="' + f.id + '">';
        if (f.label) {
          const nm = f.label === 'Global' ? '<span class="fname">Global 全局帧</span>' : '<span class="fname"><span class="flab">' + esc(f.label) + '</span>: ' + esc(f.name) + (f.lambdaLine ? ' <span class="fpar">&lt;第 ' + f.lambdaLine + ' 行&gt;</span>' : '') + ' <span class="fpar">[parent=' + esc(f.parent || 'Global') + ']</span></span>';
          sh += '<div class="fh"' + (f.exited ? ' title="这个函数已经返回。帧仍然保留在环境图里：如果有函数的 parent 指向它（闭包），里面的变量之后还会被用到。"' : '') + '>' + nm + (!f.exited && f.line && !isGlob ? '<span class="fline">第 ' + f.line + ' 行</span>' : '') + '</div>';
        } else sh += '<div class="fh"><span class="fname">' + esc(f.name) + '</span>' + (f.line && !isGlob ? '<span class="fline">第 ' + f.line + ' 行</span>' : '') + '</div>';
        const vars = settings.showFuncs ? f.vars : f.vars.filter(v => !(v.val.k === 'func' && isGlob));
        if (!vars.length && !f.ret) sh += '<div class="fempty">（没有变量）</div>';
        sh += '<table class="vars"><tbody>';
        for (const v of vars) {
          const base = v.anchor || ('F' + f.id + '/' + v.name);
          const ctx = Object.assign({}, ctx0, { sigBase: 'F' + f.id + '/' + v.name });
          ctx.varName = v.name;
          const vh = this.valHTML(v.val, base, '', ctx);
          ctx.varName = '';
          const isNew = !!prev && this.hadFrame(prev, f.id) && !this.hadVar(prev, f.id, v.name);
          sh += '<tr class="' + (v.isThis ? 'this-row' : '') + (isNew ? ' newvar' : '') + '"><td class="vn" title="' + esc((v.type || '') + (v.addr ? '  地址 ' + v.addr : '')) + '">' + esc(v.name) + (ctx0.showAddr && v.addr ? '<span class="vaddr">' + v.addr + '</span>' : '') + '</td><td class="vv" data-a="' + base + '">' + vh + '</td></tr>';
        }
        if (f.ret) {
          const ctx = Object.assign({}, ctx0, { sigBase: 'R' + f.id });
          sh += '<tr class="ret"><td class="vn">' + (snap.envMode ? 'Return value' : '返回值') + '</td><td class="vv">' + this.valHTML(f.ret, 'R' + f.id, '', ctx) + '</td></tr>';
        }
        sh += '</tbody></table></div>';
      }
      this.stackEl.innerHTML = '<div class="col-label">栈<span>Stack · 函数调用</span></div>' + sh;

      // ----- heap -----
      const AN = this.an = this.analyze(snap, heapById);
      const seen = new Set();
      const prevPos = new Map(this.pos);
      for (const ent of snap.heap) {
        seen.add(ent.id);
        let el = this.heapEls.get(ent.id);
        if (!el) {
          el = document.createElement('div');
          el.className = 'hobj';
          el.dataset.id = ent.id;
          this.heapEl.appendChild(el);
          this.heapEls.set(ent.id, el);
          el.style.opacity = '0';
          el._new = true;
        }
        const ctx = Object.assign({}, ctx0, { sigBase: 'H' + ent.id });
        const vert = this.isVertical(ent);
        ent._vert = vert;
        let body;
        const v = ent.val;
        let kindCls = v.k;
        const lab = AN.label(ent.id);
        if (v.k === 'struct' && AN.treeLabels.has(lab) && AN.treeFields.get(lab) && AN.treeFields.get(lab).size) { body = this.treeNodeHTML(v, ent.id, ctx, AN.treeFields.get(lab)); kindCls += ' tree'; }
        else if (v.k === 'struct') { const compact = v.fields.length <= 5 && v.fields.length > 0 && v.fields.every(f => this.isSimple(f.val) || (f.val.k === 'arr' && (f.val.charArr ? f.val.total <= 40 : f.val.total <= 6))); body = this.structHTML(v, ent.id, ctx, compact); kindCls += compact ? ' compact' : ''; }
        else if (v.k === 'arr') body = this.arrHTML(v, ent.id, '', ctx, 0, vert);
        else if (v.k === 'list') body = this.listHTML(v, ent.id, ctx, vert);
        else if (v.k === 'map') body = this.mapHTML(v, ent.id, ctx);
        else if (v.k === 'fnobj') body = '<div class="fnobj"><span class="fkw">func</span> ' + (v.arrow ? (v.name ? esc(v.name) + ' = ' : '') + '(' + esc(v.params) + ') =>' : esc(v.name || '(匿名)') + '(' + esc(v.params) + ')') + (v.line ? ' <span class="fpar">&lt;第 ' + v.line + ' 行&gt;</span>' : '') + (v.builtin ? '' : ' <span class="fpar">[parent=' + esc(v.parent) + ']</span>') + '</div>';
        else body = '<div class="rawv">' + this.valHTML(v, ent.id, '', ctx) + '</div>';
        const f = Object.assign({}, ent.flags || {});
        if (ent.born !== undefined && extra && extra.idx !== undefined && ent.born === extra.idx) f.fresh = true;
        let badges = '';
        if (f.leak) badges += '<span class="badge leak" title="没有任何指针指向这块内存，再也无法释放它了">泄漏</span>';
        if (f.freed) badges += '<span class="badge freed">已释放</span>';
        if (f.fresh) badges += '<span class="badge fresh">新</span>';
        if (f.rodata) badges += '<span class="badge ro" title="字符串字面量存放在只读数据区">只读</span>';
        if (f.argv) badges += '<span class="badge ro">argv</span>';
        let label = ent.label;
        if (v.k === 'list' && v.cap !== undefined) label += '  size ' + v.total + ' · cap ' + v.cap;
        else if ((v.k === 'list' || v.k === 'map') && ent.kind !== 'cont') label += '  ' + v.total + ' 项';
        el.className = 'hobj k-' + kindCls + (vert ? ' vert' : '') + (f.leak ? ' leak' : '') + (f.freed ? ' freed' : '') + (f.fresh ? ' fresh' : '') + (f.rodata || f.argv ? ' rodata' : '') + (f.exc ? ' exc' : '');
        el.dataset.a = ent.id;
        const isTree = kindCls.indexOf('tree') >= 0;
        el.title = isTree ? label : '';
        el.innerHTML = '<div class="hh">' + (isTree ? '' : '<span class="ht">' + esc(label) + '</span>') + (ctx0.showAddr && ent.addr ? '<span class="haddr">' + ent.addr + '</span>' : '') + badges + '</div><div class="hb" data-a="' + ent.id + '">' + body + '</div>';
      }
      for (const [id, el] of [...this.heapEls]) if (!seen.has(id)) { el.remove(); this.heapEls.delete(id); }

      // ----- layout -----
      {
        const cr = this.canvas.getBoundingClientRect();
        const sc = this.scale;
        const ys = new Map();
        this.stackEl.querySelectorAll('.ptr[data-a]').forEach(n => { const r = n.getBoundingClientRect(); ys.set(n.dataset.a, (r.top + r.height / 2 - cr.top) / sc); });
        this.stackCellY = ys;
      }
      const stackW = this.stackEl.offsetWidth;
      const heapX = stackW + 72;
      const sizes = new Map();
      for (const ent of snap.heap) { const el = this.heapEls.get(ent.id); sizes.set(ent.id, { w: el.offsetWidth, h: el.offsetHeight }); }
      const pos = this.layout(snap, sizes, heapById);
      this.pos = pos;
      // heap label
      let maxX = heapX + 200, maxY = this.stackEl.offsetHeight + 20;
      for (const [id, p] of pos) { const s = sizes.get(id); maxX = Math.max(maxX, heapX + p.x + s.w + 40); maxY = Math.max(maxY, this.heapY + p.y + s.h + 60); }
      this.heapEl.style.left = heapX + 'px';
      this.heapEl.style.top = this.heapY + 'px';
      this.heapX = heapX;
      if (!this.heapLabel) { this.heapLabel = document.createElement('div'); this.heapLabel.className = 'col-label heap-label'; this.heapLabel.innerHTML = '堆<span>Heap · 动态分配的对象</span>'; this.heapEl.appendChild(this.heapLabel); }
      this.heapLabel.style.display = '';
      this.emptyHeap = !snap.heap.length;
      if (!this.emptyNote) { this.emptyNote = document.createElement('div'); this.emptyNote.className = 'heap-empty'; this.heapEl.appendChild(this.emptyNote); }
      this.emptyNote.hidden = !this.emptyHeap;
      this.emptyNote.textContent = snap.lang === 'python' || snap.lang === 'js' || snap.lang === 'ts' || snap.lang === 'java' ? '还没有对象。列表、字典、类的实例等都会出现在这里。' : '堆上还没有分配内存。malloc / new 分配的内存会出现在这里。';
      this.canvasW = maxX; this.canvasH = maxY;
      this.canvas.style.width = maxX + 'px';
      this.canvas.style.height = maxY + 'px';
      this.svg.setAttribute('width', maxX); this.svg.setAttribute('height', maxY);
      if (this.autoFit) {
        const avail = this.root.clientWidth - 6;
        if (avail > 200 && maxX * this.scale > avail) this.scale = Math.max(0.55, Math.min(this.scale, avail / maxX));
      }
      this.applyScale();
      // ----- keep the active stack frame in view -----
      const topEl = this.stackEl.querySelector('.frame.top');
      if (topEl && this.root.scrollHeight > this.root.clientHeight + 4) {
        const vr = this.root.getBoundingClientRect(), tr = topEl.getBoundingClientRect();
        const room = vr.height - 24;
        let dy = 0;
        if (tr.height > room || tr.top < vr.top + 8) dy = tr.top - vr.top - 12;
        else if (tr.bottom > vr.bottom - 8) dy = tr.bottom - vr.bottom + 16;
        if (dy) this.root.scrollTop += dy;
      }
      // ----- measure anchors -----
      this.measure(snap, sizes);
      // ----- animate -----
      const animate = settings.animate && !matchMedia('(prefers-reduced-motion: reduce)').matches && prev && extra && extra.adjacent;
      if (this.anim) cancelAnimationFrame(this.anim);
      const from = new Map();
      for (const [id, p] of pos) from.set(id, prevPos.get(id) || p);
      const changedArrows = changed;
      const frame = (t) => {
        for (const [id, p] of pos) {
          const el = this.heapEls.get(id);
          if (!el) continue;
          const f0 = from.get(id);
          const x = f0.x + (p.x - f0.x) * t, y = f0.y + (p.y - f0.y) * t;
          el.style.transform = 'translate(' + x + 'px,' + y + 'px)';
          el._cx = x; el._cy = y;
          if (el._new) { el.style.opacity = String(t); if (t >= 1) { el._new = false; el.style.opacity = ''; } }
        }
        this.drawArrows(changedArrows);
      };
      if (animate) {
        const t0 = performance.now(), dur = 260;
        const tick = (now) => {
          let t = Math.min(1, (now - t0) / dur);
          t = 1 - Math.pow(1 - t, 3);
          frame(t);
          if (t < 1) this.anim = requestAnimationFrame(tick); else this.anim = null;
        };
        frame(0);
        this.anim = requestAnimationFrame(tick);
      } else frame(1);
    }
    clear() {
      if (this.anim) { cancelAnimationFrame(this.anim); this.anim = null; }
      this.stackEl.innerHTML = '';
      this.arrowG.innerHTML = '';
      for (const el of this.heapEls.values()) el.remove();
      this.heapEls.clear();
      this.pos = new Map();
      if (this.emptyNote) this.emptyNote.hidden = true;
      if (this.heapLabel) this.heapLabel.style.display = 'none';
    }
    hadFrame(prev, fid) { return prev && (prev.snap.frames.some(f => f.id === fid) || (prev.snap.globals && prev.snap.globals.id === fid)); }
    hadVar(prev, fid, name) { const fr = prev.snap.frames.find(f => f.id === fid) || (prev.snap.globals && prev.snap.globals.id === fid ? prev.snap.globals : null); return fr && fr.vars.some(v => v.name === name); }

    applyScale() {
      this.canvas.style.transform = this.scale === 1 ? '' : 'scale(' + this.scale + ')';
      this.sizer.style.width = (this.canvasW * this.scale) + 'px';
      this.sizer.style.height = (this.canvasH * this.scale) + 'px';
    }
    setScale(s) { this.scale = Math.max(0.3, Math.min(2, s)); this.applyScale(); }
    fit() {
      const w = this.root.clientWidth - 8;
      if (!this.canvasW) return;
      this.setScale(Math.min(1, w / this.canvasW));
    }

    // ---------- measure anchors & pointer sources ----------
    measure(snap, sizes) {
      const cr = this.canvas.getBoundingClientRect();
      const sc = this.scale;
      const rel = (r) => ({ x: (r.left - cr.left) / sc, y: (r.top - cr.top) / sc, w: r.width / sc, h: r.height / sc });
      this.anchors = new Map();   // anchor -> {obj (id|null), x,y,w,h (relative to obj or canvas)}
      this.ptrs = [];
      // reset transforms to measure offsets relative to object origin
      for (const [id, el] of this.heapEls) el.style.transform = 'translate(0px,0px)';
      const heapOrigin = { x: this.heapX, y: 0 };
      for (const [id, el] of this.heapEls) {
        const er = rel(el.getBoundingClientRect());
        el.querySelectorAll('[data-a]').forEach(n => {
          const r = rel(n.getBoundingClientRect());
          const a = n.dataset.a;
          if (!this.anchors.has(a) || n.classList.contains('hb')) this.anchors.set(a, { obj: id, x: r.x - er.x, y: r.y - er.y, w: r.w, h: r.h, whole: n.classList.contains('hb') || n === el });
        });
        this.anchors.set(id, { obj: id, x: 0, y: 0, w: er.w, h: er.h, whole: true, hdr: el.querySelector('.hh') ? el.querySelector('.hh').offsetHeight : 0 });
        el.querySelectorAll('.ptr').forEach(n => {
          const d = n.querySelector('.dot');
          const r = rel((d || n).getBoundingClientRect());
          this.ptrs.push({ obj: id, x: r.x - er.x + r.w / 2, y: r.y - er.y + r.h / 2, t: n.dataset.t, s: n.dataset.s, dangling: n.classList.contains('dangling'), alias: n.classList.contains('alias'), hot: n.classList.contains('chg'), el: n });
        });
      }
      this.stackEl.querySelectorAll('[data-a]').forEach(n => {
        const r = rel(n.getBoundingClientRect());
        const a = n.dataset.a;
        if (!this.anchors.has(a) || n.classList.contains('vv')) this.anchors.set(a, { obj: null, x: r.x, y: r.y, w: r.w, h: r.h, whole: n.classList.contains('vv') });
      });
      this.stackEl.querySelectorAll('.ptr').forEach(n => {
        const d = n.querySelector('.dot');
        const r = rel((d || n).getBoundingClientRect());
        this.ptrs.push({ obj: null, x: r.x + r.w / 2, y: r.y + r.h / 2, t: n.dataset.t, s: n.dataset.s, dangling: n.classList.contains('dangling'), alias: n.classList.contains('alias'), hot: n.classList.contains('chg'), el: n });
      });
    }
    absOf(a) {
      if (!a) return null;
      if (a.obj === null) return { x: a.x, y: a.y, w: a.w, h: a.h, whole: a.whole };
      const el = this.heapEls.get(a.obj);
      if (!el) return null;
      return { x: this.heapX + (el._cx || 0) + a.x, y: this.heapY + (el._cy || 0) + a.y, w: a.w, h: a.h, whole: a.whole, hdr: a.hdr };
    }
    drawArrows() {
      let h = '';
      for (const p of this.ptrs) {
        let tgtA = this.anchors.get(p.t + (p.s ? ':' + p.s : '')) || this.anchors.get(p.t);
        if (!tgtA) continue;
        const src = p.obj === null ? { x: p.x, y: p.y } : (() => { const el = this.heapEls.get(p.obj); return { x: this.heapX + (el._cx || 0) + p.x, y: this.heapY + (el._cy || 0) + p.y }; })();
        const T = this.absOf(tgtA);
        if (!T) continue;
        // choose target point
        let tx, ty, side;
        const midY = T.whole && T.hdr !== undefined ? T.y + Math.min(T.h - 8, T.hdr + 14) : T.y + Math.min(T.h / 2, 14);
        const downish = tgtA.obj !== null && T.y > src.y + 16 && Math.abs((T.x + T.w / 2) - src.x) < Math.max(150, (T.y - src.y) * 2.2) && p.obj !== null;
        if (downish) { tx = T.x + Math.min(T.w / 2, 40); ty = T.y + (T.hdr || 0) - 2; side = 't'; }
        else if (T.x >= src.x + 12) { tx = T.x; ty = tgtA.obj === null ? T.y + Math.min(T.h / 2, 13) : midY; side = 'l'; }
        else if (T.x + T.w <= src.x - 12) { tx = T.x + T.w; ty = tgtA.obj === null ? T.y + Math.min(T.h / 2, 13) : midY; side = 'r'; }
        else if (T.y > src.y) { tx = T.x + Math.min(T.w / 2, 24); ty = T.y; side = 't'; }
        else { tx = T.x + Math.min(T.w / 2, 24); ty = T.y + T.h; side = 'b'; }
        const dx = tx - src.x, dy = ty - src.y;
        let path;
        if (side === 'l') {
          const c = Math.max(24, Math.min(140, Math.abs(dx) * 0.5));
          path = 'M' + src.x + ',' + src.y + ' C' + (src.x + c) + ',' + src.y + ' ' + (tx - c) + ',' + ty + ' ' + tx + ',' + ty;
        } else if (side === 'r') {
          // back edge: loop below
          const drop = 34 + Math.min(60, Math.abs(dx) * 0.15);
          path = 'M' + src.x + ',' + src.y + ' C' + (src.x + 40) + ',' + (src.y + drop) + ' ' + (tx + 40) + ',' + (ty + drop) + ' ' + tx + ',' + ty;
        } else if (side === 't') {
          const c = Math.max(18, Math.abs(dy) * 0.5);
          path = 'M' + src.x + ',' + src.y + ' C' + src.x + ',' + (src.y + c) + ' ' + tx + ',' + (ty - c) + ' ' + tx + ',' + ty;
        } else {
          const c = Math.max(20, Math.abs(dy) * 0.45);
          path = 'M' + src.x + ',' + src.y + ' C' + (src.x + (dx > 0 ? 20 : -20)) + ',' + (src.y + (side === 't' ? c : -c)) + ' ' + tx + ',' + (ty + (side === 't' ? -c : c)) + ' ' + tx + ',' + ty;
        }
        const cls = 'arr' + (p.dangling ? ' bad' : '') + (p.alias ? ' alias' : '') + (p.hot ? ' hot' : '');
        const marker = p.dangling ? 'ah-bad' : (p.hot ? 'ah-hot' : 'ah');
        h += '<path class="' + cls + '" d="' + path + '" marker-end="url(#' + marker + ')"></path>';
      }
      this.arrowG.innerHTML = h;
    }

    // ---------- structure analysis (shared by rendering and layout) ----------
    analyze(snap, byId) {
      const edges = new Map();
      const collect = (d, path, out) => {
        if (!d) return;
        if (d.k === 'ref') { if (byId.has(d.id)) out.push({ t: d.id, path }); return; }
        if (d.k === 'arr') d.elems.forEach((e, i) => collect(e, path ? path + '.' + i : String(i), out));
        else if (d.k === 'struct') d.fields.forEach(f => collect(f.val, path ? path + '.' + f.name : f.name, out));
        else if (d.k === 'list') d.items.forEach((e, i) => collect(e, String(i), out));
        else if (d.k === 'map') d.entries.forEach((en, i) => { collect(en.key, 'key' + i, out); collect(en.val, 'v' + i, out); });
      };
      for (const h of snap.heap) { const out = []; collect(h.val, '', out); edges.set(h.id, out); }
      const label = (id) => { const h = byId.get(id); return h ? (h.val.k === 'struct' ? 'S:' + h.val.name : h.val.k) : ''; };
      const isStruct = (id) => { const h = byId.get(id); return h && h.val.k === 'struct'; };
      const firstField = (path) => path.split('.')[0];
      const isContainerOf = (cid, lab) => { const h = byId.get(cid); if (!h || (h.val.k !== 'list' && h.val.k !== 'arr')) return false; const es = edges.get(cid); return es.length > 0 && es.every(e => label(e.t) === lab); };
      const treeKids = (id) => {
        const lab = label(id);
        if (!isStruct(id)) return [];
        const out = [];
        for (const e of edges.get(id)) {
          if (BACK_NAMES.test(firstField(e.path))) continue;
          if (label(e.t) === lab) out.push(e);
          else if (isContainerOf(e.t, lab)) out.push(Object.assign({ container: true }, e));
        }
        return out;
      };
      const treeLabels = new Set();
      const treeFields = new Map();
      for (const h of snap.heap) {
        if (!isStruct(h.id)) continue;
        const kids = treeKids(h.id);
        let n = 0;
        for (const k of kids) n += k.container ? edges.get(k.t).length : 1;
        const fields = h.val.fields.map(f => f.name.toLowerCase());
        const lab = label(h.id);
        if (n >= 2 || (fields.some(f => /left/.test(f)) && fields.some(f => /right/.test(f))) || kids.some(k => k.container)) treeLabels.add(lab);
        if (kids.some(k => /^(children|child|kids|next|son|sons)$/i.test(firstField(k.path)) && /\.\d+$/.test(k.path))) treeLabels.add(lab);
        if (!treeFields.has(lab)) treeFields.set(lab, new Set());
        for (const k of kids) treeFields.get(lab).add(firstField(k.path));
        for (const f of h.val.fields) if (/^(left|right|l|r|lchild|rchild|leftchild|rightchild)$/i.test(f.name)) treeFields.get(lab).add(f.name);
      }
      return { edges, label, isStruct, firstField, treeKids, treeLabels, treeFields, isContainerOf };
    }
    treeNodeHTML(d, id, ctx, ports) {
      const vals = d.fields.filter(f => !ports.has(f.name));
      const pf = d.fields.filter(f => ports.has(f.name));
      let h = '<div class="tn">';
      if (vals.length === 1 && this.isSimple(vals[0].val)) h += '<div class="tn-v one"><span class="tn-k">' + esc(vals[0].name) + '</span>' + this.valHTML(vals[0].val, id, vals[0].name, ctx, 1) + '</div>';
      else if (vals.length) h += '<div class="tn-v">' + vals.map(f => '<div class="tn-f"><span class="fk">' + esc(f.name) + '</span>' + this.valHTML(f.val, id, f.name, ctx, 1) + '</div>').join('') + '</div>';
      if (pf.length) {
        h += '<div class="tn-p">';
        for (const f of pf) {
          const inner = f.val.k === 'arr' ? this.arrHTML(f.val, id, f.name, ctx, 1, false) : this.valHTML(f.val, id, f.name, ctx, 1);
          h += '<div class="tp"><span class="tk">' + esc(f.name) + '</span>' + inner + '</div>';
        }
        h += '</div>';
      }
      return h + '</div>';
    }

    // ---------- layout ----------
    layout(snap, sizes, byId) {
      const pos = new Map();
      const rects = [];
      const AN = this.an || this.analyze(snap, byId);
      const edges = AN.edges;
      const { label, isStruct, firstField, treeKids, treeLabels } = AN;
      const overlaps = (x, y, w, h) => rects.some(r => x < r.x + r.w + 14 && x + w + 14 > r.x && y < r.y + r.h + 12 && y + h + 12 > r.y);
      const free = (x, y, w, h) => { let guard = 0; while (overlaps(x, y, w, h) && guard++ < 400) y += 18; return y; };
      const put = (id, x, y) => { const s = sizes.get(id); pos.set(id, { x, y }); rects.push({ x, y, w: s.w, h: s.h }); };
      const self = this;
      function layoutTree(rootId, x0, y0) {
        // collect tree nodes
        const lab = label(rootId);
        const kids = new Map();
        const nodes = [];
        const visit = (id, depth) => {
          if (kids.has(id) || pos.has(id)) return;
          nodes.push(id);
          const ks = [];
          kids.set(id, ks);
          if (isStruct(id)) {
            const tk = treeKids(id);
            const fieldsLower = byId.get(id).val.fields.map(f => f.name.toLowerCase());
            const binary = fieldsLower.some(f => /left/.test(f)) && fieldsLower.some(f => /right/.test(f));
            if (binary) {
              const L = tk.find(e => /left/i.test(firstField(e.path))), R = tk.find(e => /right/i.test(firstField(e.path)));
              ks.push(L && !kids.has(L.t) ? L.t : null, R && !kids.has(R.t) ? R.t : null);
              ks.binary = true;
            } else for (const e of tk) if (!kids.has(e.t)) ks.push(e.t);
          } else {
            for (const e of edges.get(id)) if (label(e.t) === lab && !kids.has(e.t)) ks.push(e.t);
          }
          for (const k of ks) if (k) visit(k, depth + 1);
        };
        visit(rootId, 0);
        // tidy layout: compute widths
        const W = new Map();
        const width = (id) => {
          if (W.has(id)) return W.get(id);
          const s = sizes.get(id);
          const ks = kids.get(id) || [];
          let sum = 0, cnt = 0;
          if (ks.binary) {
            const lw = ks[0] ? width(ks[0]) : s.w * 0.6, rw = ks[1] ? width(ks[1]) : s.w * 0.6;
            sum = lw + rw + 24; cnt = 2;
          } else for (const k of ks) { sum += width(k) + (cnt ? 22 : 0); cnt++; }
          const w = Math.max(s.w, sum);
          W.set(id, w);
          return w;
        };
        width(rootId);
        const levelH = new Map();
        const depthOf = new Map();
        const setDepth = (id, d) => { depthOf.set(id, d); const s = sizes.get(id); levelH.set(d, Math.max(levelH.get(d) || 0, s.h)); for (const k of (kids.get(id) || [])) if (k) setDepth(k, d + 1); };
        setDepth(rootId, 0);
        const yOf = (d) => { let y = 0; for (let i = 0; i < d; i++) y += (levelH.get(i) || 30) + 40; return y; };
        const local = new Map();
        const place = (id, left) => {
          const w = W.get(id), s = sizes.get(id);
          const ks = kids.get(id) || [];
          local.set(id, { x: left + (w - s.w) / 2, y: yOf(depthOf.get(id)) });
          if (ks.binary) {
            const lw = ks[0] ? W.get(ks[0]) : s.w * 0.6, rw = ks[1] ? W.get(ks[1]) : s.w * 0.6;
            const total = lw + rw + 24;
            let l = left + (w - total) / 2;
            if (ks[0]) place(ks[0], l);
            if (ks[1]) place(ks[1], l + lw + 24);
          } else {
            let sum = 0; ks.forEach((k, i) => sum += W.get(k) + (i ? 22 : 0));
            let l = left + (w - sum) / 2;
            for (const k of ks) { place(k, l); l += W.get(k) + 22; }
          }
        };
        place(rootId, 0);
        let bw = 0, bh = 0;
        for (const [id, p] of local) { const s = sizes.get(id); bw = Math.max(bw, p.x + s.w); bh = Math.max(bh, p.y + s.h); }
        let y = y0;
        let guard = 0;
        while (guard++ < 300) { let ok = true; for (const [id, p] of local) { const s = sizes.get(id); if (overlaps(x0 + p.x, y + p.y, s.w, s.h)) { ok = false; break; } } if (ok) break; y += 20; }
        for (const [id, p] of local) put(id, x0 + p.x, y + p.y);
        // non-tree children below the tree
        let by = y + bh + GY;
        for (const id of nodes) for (const e of edges.get(id)) if (!pos.has(e.t)) { const p = pos.get(id); placeObj(e.t, p.x, Math.max(by, p.y + sizes.get(id).h + GY)); }
        return { bottom: y + bh };
      }
      function placeObj(id, x, y) {
        if (pos.has(id) || !sizes.has(id)) return;
        if (treeLabels.has(label(id)) && isStruct(id)) { layoutTree(id, x, y); return; }
        const s = sizes.get(id);
        y = free(x, y, s.w, s.h);
        put(id, x, y);
        const ent = byId.get(id);
        const es = edges.get(id).filter(e => !pos.has(e.t));
        if (!es.length) return;
        if (ent._vert) {
          let cursor = y;
          for (const e of es) {
            if (pos.has(e.t)) continue;
            const a = self.anchors && null;
            const cellY = self.cellOffsetY(id, e.path);
            placeObj(e.t, x + s.w + GX, Math.max(cursor, y + cellY - 12));
            const p2 = pos.get(e.t);
            if (p2) cursor = p2.y + sizes.get(e.t).h + 8;
          }
          return;
        }
        // chain: same-type next pointer continues to the right
        const lab = label(id);
        const chain = es.find(e => label(e.t) === lab && !BACK_NAMES.test(firstField(e.path)));
        if (chain) placeObj(chain.t, x + s.w + GX, y);
        let bx = x;
        for (const e of es) {
          if (e === chain || pos.has(e.t)) continue;
          const cx = self.cellOffsetX(id, e.path);
          placeObj(e.t, Math.max(bx, x + cx - 8), y + s.h + GY);
          const p2 = pos.get(e.t);
          if (p2) bx = p2.x + sizes.get(e.t).w + 18;
        }
      }
      // roots in stack order; each root tries to sit level with the variable that points to it
      let rowY = 0;
      const roots = [];
      const want = new Map();
      const frames = (snap.globals ? [snap.globals] : []).concat(snap.frames);
      const cellY = this.stackCellY || new Map();
      const pushRefs = (d, base, path) => {
        if (!d) return;
        if (d.k === 'ref') {
          if (byId.has(d.id)) {
            roots.push(d.id);
            const cy = cellY.get(base + (path ? ':' + path : ''));
            if (cy !== undefined && !want.has(d.id)) want.set(d.id, cy - this.heapY - 30);
          }
          return;
        }
        if (d.k === 'arr') d.elems.forEach((e, i) => pushRefs(e, base, path ? path + '.' + i : String(i)));
        else if (d.k === 'struct') d.fields.forEach(f => pushRefs(f.val, base, path ? path + '.' + f.name : f.name));
      };
      for (const f of frames) { for (const v of f.vars) pushRefs(v.val, v.anchor || ('F' + f.id + '/' + v.name), ''); if (f.ret) pushRefs(f.ret, 'R' + f.id, ''); }
      // less interesting blocks (argv strings, string literals) go after everything else
      const late = (id) => { const h = byId.get(id); return h && h.flags && (h.flags.argv || h.flags.rodata); };
      const early = roots.filter(r => !late(r)), lateR = roots.filter(r => late(r));
      roots.length = 0; roots.push(...early, ...lateR);
      for (const h of snap.heap) if (!(h.flags && (h.flags.leak || h.flags.freed))) roots.push(h.id);
      for (const h of snap.heap) roots.push(h.id);
      // place each root on its own row
      this._sizes = sizes;
      for (const r of roots) {
        if (pos.has(r)) continue;
        const h = byId.get(r);
        let y = want.has(r) ? Math.max(0, want.get(r)) : rowY;
        if (h && h.flags && (h.flags.leak || h.flags.freed)) y = Math.max(rowY, this.maxBottom(rects) + 26);
        placeObj(r, 0, y);
        rowY = this.maxBottom(rects) + GY;
      }
      return pos;
    }
    maxBottom(rects) { let b = 0; for (const r of rects) b = Math.max(b, r.y + r.h); return rects.length ? b : 0; }
    cellOffsetY(id, path) {
      const el = this.heapEls.get(id);
      if (!el) return 0;
      const n = el.querySelector('[data-a="' + id + ':' + path + '"]');
      if (!n) return 0;
      let y = 0, cur = n;
      while (cur && cur !== el) { y += cur.offsetTop; cur = cur.offsetParent; if (cur === el) break; }
      return y;
    }
    cellOffsetX(id, path) {
      const el = this.heapEls.get(id);
      if (!el) return 0;
      const n = el.querySelector('[data-a="' + id + ':' + path + '"]');
      if (!n) return 0;
      let x = 0, cur = n;
      while (cur && cur !== el) { x += cur.offsetLeft; cur = cur.offsetParent; if (cur === el) break; }
      return x;
    }
  }
  DSV.Viz = Viz;
})(typeof window !== 'undefined' ? window : globalThis);
