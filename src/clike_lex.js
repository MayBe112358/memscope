// ===== C / C++ / Java lexer + tiny preprocessor =====
(function (G) {
  const DSV = G.DSV;
  const { CompileError } = DSV;

  const OPS = [
    '>>>=', '<<=', '>>=', '>>>', '...', '->*', '->', '++', '--', '<<', '>>', '<=', '>=', '==', '!=', '&&', '||',
    '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '::',
    '+', '-', '*', '/', '%', '<', '>', '=', '!', '~', '&', '|', '^', '?', ':', ';', ',', '.', '(', ')', '[', ']', '{', '}', '@'
  ];

  function unescape(s, i, line) {
    // returns [char, newIndex]
    const c = s[i];
    if (c !== '\\') return [c, i + 1];
    const n = s[i + 1];
    switch (n) {
      case 'n': return ['\n', i + 2];
      case 't': return ['\t', i + 2];
      case 'r': return ['\r', i + 2];
      case '0': {
        // octal
        let j = i + 1, v = '';
        while (j < s.length && v.length < 3 && /[0-7]/.test(s[j])) v += s[j++];
        return [String.fromCharCode(parseInt(v, 8)), j];
      }
      case 'a': return ['\x07', i + 2];
      case 'b': return ['\b', i + 2];
      case 'f': return ['\f', i + 2];
      case 'v': return ['\v', i + 2];
      case 'x': {
        let j = i + 2, v = '';
        while (j < s.length && /[0-9a-fA-F]/.test(s[j])) v += s[j++];
        return [String.fromCharCode(parseInt(v || '0', 16)), j];
      }
      case 'u': {
        const v = s.substr(i + 2, 4);
        return [String.fromCharCode(parseInt(v, 16)), i + 6];
      }
      case '\\': return ['\\', i + 2];
      case '\'': return ['\'', i + 2];
      case '"': return ['"', i + 2];
      case '?': return ['?', i + 2];
      default:
        if (/[1-7]/.test(n)) {
          let j = i + 1, v = '';
          while (j < s.length && v.length < 3 && /[0-7]/.test(s[j])) v += s[j++];
          return [String.fromCharCode(parseInt(v, 8)), j];
        }
        return [n, i + 2];
    }
  }

  function lex(src, dialect) {
    const toks = [];
    const macros = new Map();
    const includes = [];
    let i = 0, line = 1, lineStart = 0;
    const n = src.length;
    let atLineStart = true;
    while (i < n) {
      const c = src[i];
      if (c === '\n') { line++; i++; lineStart = i; atLineStart = true; continue; }
      if (c === ' ' || c === '\t' || c === '\r' || c === '\f' || c === '\v') { i++; continue; }
      // comments
      if (c === '/' && src[i + 1] === '/') { while (i < n && src[i] !== '\n') i++; continue; }
      if (c === '/' && src[i + 1] === '*') {
        i += 2;
        while (i < n && !(src[i] === '*' && src[i + 1] === '/')) { if (src[i] === '\n') line++; i++; }
        if (i >= n) throw new CompileError('注释 /* 没有闭合', line);
        i += 2; continue;
      }
      // preprocessor
      if (c === '#' && atLineStart && dialect !== 'java') {
        const startLine = line;
        let text = '';
        i++;
        while (i < n && src[i] !== '\n') {
          if (src[i] === '\\' && src[i + 1] === '\n') { i += 2; line++; text += ' '; continue; }
          if (src[i] === '\\' && src[i + 1] === '\r' && src[i + 2] === '\n') { i += 3; line++; text += ' '; continue; }
          // strip comments inside directives
          if (src[i] === '/' && src[i + 1] === '/') { while (i < n && src[i] !== '\n') i++; break; }
          if (src[i] === '/' && src[i + 1] === '*') { i += 2; while (i < n && !(src[i] === '*' && src[i + 1] === '/')) { if (src[i] === '\n') line++; i++; } i += 2; continue; }
          text += src[i++];
        }
        handleDirective(text.trim(), startLine);
        continue;
      }
      atLineStart = false;
      const col = i - lineStart + 1;
      // identifiers
      if (/[A-Za-z_$]/.test(c) || c.charCodeAt(0) > 127) {
        let j = i + 1;
        while (j < n && (/[A-Za-z0-9_$]/.test(src[j]) || src.charCodeAt(j) > 127)) j++;
        const word = src.slice(i, j);
        // C++ raw string / prefixes like u8"..", L".."
        if ((word === 'L' || word === 'u8' || word === 'u' || word === 'U') && (src[j] === '"' || src[j] === "'")) { i = j; continue; }
        toks.push({ t: 'id', v: word, line, col });
        i = j; continue;
      }
      // numbers
      if (/[0-9]/.test(c) || (c === '.' && /[0-9]/.test(src[i + 1] || ''))) {
        let j = i, isFloat = false, val;
        if (c === '0' && /[xX]/.test(src[i + 1])) {
          j = i + 2; while (j < n && /[0-9a-fA-F_']/.test(src[j])) j++;
          val = parseInt(src.slice(i + 2, j).replace(/[_']/g, ''), 16);
        } else if (c === '0' && /[bB]/.test(src[i + 1])) {
          j = i + 2; while (j < n && /[01_']/.test(src[j])) j++;
          val = parseInt(src.slice(i + 2, j).replace(/[_']/g, ''), 2);
        } else {
          while (j < n && /[0-9_']/.test(src[j])) j++;
          if (src[j] === '.' && /[0-9]/.test(src[j + 1] || '') || (src[j] === '.' && !/[A-Za-z_.]/.test(src[j + 1] || ''))) { isFloat = true; j++; while (j < n && /[0-9_]/.test(src[j])) j++; }
          if (/[eE]/.test(src[j] || '') && /[0-9+-]/.test(src[j + 1] || '')) { isFloat = true; j++; if (/[+-]/.test(src[j])) j++; while (j < n && /[0-9]/.test(src[j])) j++; }
          const txt = src.slice(i, j).replace(/[_']/g, '');
          if (!isFloat && txt.length > 1 && txt[0] === '0') val = parseInt(txt, 8);
          else val = isFloat ? parseFloat(txt) : parseInt(txt, 10);
        }
        let suffix = '';
        while (j < n && /[uUlLfFdD]/.test(src[j])) suffix += src[j++];
        if (/[fF]/.test(suffix) && !/0[xX]/.test(src.slice(i, i + 2))) isFloat = true;
        if (/[dD]/.test(suffix)) isFloat = true;
        toks.push({ t: 'num', v: val, isFloat, suffix: suffix.toLowerCase(), line, col, text: src.slice(i, j) });
        i = j; continue;
      }
      // char literal
      if (c === "'") {
        let j = i + 1;
        if (src[j] === "'") throw new CompileError('空的字符字面量 \'\'', line);
        const [ch, nj] = unescape(src, j, line);
        j = nj;
        if (src[j] !== "'") {
          // multi-char constant – take until closing quote
          while (j < n && src[j] !== "'" && src[j] !== '\n') j++;
        }
        if (src[j] !== "'") throw new CompileError('字符字面量缺少右引号 \'', line);
        toks.push({ t: 'chr', v: ch.charCodeAt(0), line, col });
        i = j + 1; continue;
      }
      // string literal
      if (c === '"') {
        // Java text block
        if (dialect === 'java' && src.startsWith('"""', i)) {
          let j = src.indexOf('\n', i) + 1; let s = '';
          const end = src.indexOf('"""', j);
          if (end < 0) throw new CompileError('文本块没有闭合', line);
          const raw = src.slice(j, end);
          for (const ch of raw) if (ch === '\n') line++;
          const lines = raw.split('\n');
          const ind = Math.min(...lines.filter(l => l.trim()).map(l => l.match(/^ */)[0].length));
          s = lines.map(l => l.slice(ind)).join('\n');
          toks.push({ t: 'str', v: s, line, col });
          i = end + 3; continue;
        }
        let j = i + 1, s = '';
        while (j < n && src[j] !== '"') {
          if (src[j] === '\n') throw new CompileError('字符串缺少右引号 "', line);
          const [ch, nj] = unescape(src, j, line);
          s += ch; j = nj;
        }
        if (j >= n) throw new CompileError('字符串缺少右引号 "', line);
        toks.push({ t: 'str', v: s, line, col });
        i = j + 1; continue;
      }
      // C++ raw string R"(...)"
      // operators
      let matched = null;
      for (const op of OPS) { if (src.startsWith(op, i)) { matched = op; break; } }
      if (!matched) throw new CompileError('无法识别的字符：' + c, line);
      if (dialect === 'java' && matched === '->*') matched = '->';
      if (dialect === 'java' && matched === '::') matched = '::';
      toks.push({ t: 'op', v: matched, line, col });
      i += matched.length;
    }
    toks.push({ t: 'eof', v: '<文件结尾>', line, col: 0 });

    function handleDirective(text, dline) {
      const m = /^(\w+)\s*(.*)$/s.exec(text);
      if (!m) return;
      const dir = m[1], rest = m[2];
      if (dir === 'include') { includes.push(rest.replace(/[<>"]/g, '').trim()); return; }
      if (dir === 'define') {
        const mm = /^([A-Za-z_]\w*)(\(([^)]*)\))?\s*(.*)$/s.exec(rest);
        if (!mm) return;
        const name = mm[1];
        const params = mm[2] !== undefined && rest[name.length] === '(' ? mm[3].split(',').map(s => s.trim()).filter(Boolean) : null;
        const body = params ? mm[4] : (mm[2] !== undefined ? mm[2] + ' ' + mm[4] : mm[4]);
        const bodyToks = body.trim() ? lex(body, dialect).toks.slice(0, -1) : [];
        macros.set(name, { params, body: bodyToks, line: dline });
        return;
      }
      if (dir === 'undef') { macros.delete(rest.trim()); return; }
      // ifdef/ifndef/endif/pragma etc. ignored
    }

    return { toks: expandMacros(toks, macros), includes, macros };
  }

  function expandMacros(toks, macros) {
    if (!macros.size) return toks;
    const out = [];
    const expand = (list, depth, hide) => {
      const res = [];
      for (let k = 0; k < list.length; k++) {
        const tk = list[k];
        if (tk.t === 'id' && macros.has(tk.v) && !hide.has(tk.v) && depth < 30) {
          const mac = macros.get(tk.v);
          if (mac.params) {
            if (!(list[k + 1] && list[k + 1].v === '(')) { res.push(tk); continue; }
            // collect args
            let j = k + 2, depthP = 0, cur = [], args = [];
            for (; j < list.length; j++) {
              const t = list[j];
              if (t.t === 'op' && (t.v === '(' || t.v === '[' || t.v === '{')) depthP++;
              if (t.t === 'op' && (t.v === ')' || t.v === ']' || t.v === '}')) { if (depthP === 0) break; depthP--; }
              if (t.t === 'op' && t.v === ',' && depthP === 0) { args.push(cur); cur = []; continue; }
              cur.push(t);
            }
            if (cur.length || args.length) args.push(cur);
            const body = [];
            for (const bt of mac.body) {
              const pi = bt.t === 'id' ? mac.params.indexOf(bt.v) : -1;
              if (pi >= 0) for (const at of (args[pi] || [])) body.push(Object.assign({}, at, { line: tk.line }));
              else body.push(Object.assign({}, bt, { line: tk.line }));
            }
            const nh = new Set(hide); nh.add(tk.v);
            res.push(...expand(body, depth + 1, nh));
            k = j;
          } else {
            const body = mac.body.map(bt => Object.assign({}, bt, { line: tk.line, col: tk.col }));
            const nh = new Set(hide); nh.add(tk.v);
            res.push(...expand(body, depth + 1, nh));
          }
        } else res.push(tk);
      }
      return res;
    };
    return expand(toks, 0, new Set());
  }

  DSV.clikeLex = lex;
})(typeof window !== 'undefined' ? window : globalThis);
