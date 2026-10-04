// ===== Python lexer + parser =====
(function (G) {
  const DSV = G.DSV;
  const { CompileError } = DSV;

  const OPS = ['**=', '//=', '>>=', '<<=', '...', '!=', '==', '<=', '>=', '->', ':=', '**', '//', '<<', '>>', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '@=',
    '+', '-', '*', '/', '%', '@', '&', '|', '^', '~', '<', '>', '(', ')', '[', ']', '{', '}', ',', ':', '.', ';', '='];
  const KEYWORDS = new Set(['False', 'None', 'True', 'and', 'as', 'assert', 'async', 'await', 'break', 'class', 'continue', 'def', 'del', 'elif', 'else', 'except', 'finally', 'for', 'from', 'global', 'if', 'import', 'in', 'is', 'lambda', 'nonlocal', 'not', 'or', 'pass', 'raise', 'return', 'try', 'while', 'with', 'yield']);

  function lex(src) {
    const toks = [];
    const indents = [0];
    let i = 0, line = 1, depth = 0;
    const n = src.length;
    let atLineStart = true;
    const push = (t, v, extra) => toks.push(Object.assign({ t, v, line }, extra || {}));
    while (i < n) {
      if (atLineStart && depth === 0) {
        // measure indentation
        let col = 0, j = i;
        while (j < n && (src[j] === ' ' || src[j] === '\t' || src[j] === '\f')) { col = src[j] === '\t' ? (Math.floor(col / 8) + 1) * 8 : col + 1; j++; }
        if (j >= n) { i = j; break; }
        if (src[j] === '\n' || src[j] === '#' || (src[j] === '\r' && src[j + 1] === '\n')) {
          // blank or comment line
          while (j < n && src[j] !== '\n') j++;
          i = j + 1; line++; continue;
        }
        atLineStart = false;
        i = j;
        const top = indents[indents.length - 1];
        if (col > top) { indents.push(col); push('INDENT', col); }
        else if (col < top) {
          while (indents.length && col < indents[indents.length - 1]) { indents.pop(); push('DEDENT', col); }
          if (indents[indents.length - 1] !== col) throw new CompileError('缩进错误（IndentationError）：这一行的缩进和前面任何一层都对不上。', line);
        }
      }
      const c = src[i];
      if (c === '\n') { if (depth === 0) { push('NEWLINE', ''); atLineStart = true; } line++; i++; continue; }
      if (c === ' ' || c === '\t' || c === '\r' || c === '\f') { i++; continue; }
      if (c === '#') { while (i < n && src[i] !== '\n') i++; continue; }
      if (c === '\\' && (src[i + 1] === '\n' || (src[i + 1] === '\r' && src[i + 2] === '\n'))) { i += src[i + 1] === '\n' ? 2 : 3; line++; continue; }
      // strings (with prefixes)
      const sm = /^([rRbBuUfF]{0,2})('''|"""|'|")/.exec(src.slice(i, i + 5));
      if (sm && (sm[1] === '' || /^(r|b|u|f|rb|br|fr|rf)$/i.test(sm[1]))) {
        const prefix = sm[1].toLowerCase();
        const q = sm[2];
        let j = i + sm[0].length;
        const startLine = line;
        let raw = '';
        for (;;) {
          if (j >= n) throw new CompileError('字符串没有闭合（缺少结尾的 ' + q + '）', startLine);
          if (src.startsWith(q, j)) { j += q.length; break; }
          const ch = src[j];
          if (ch === '\n') { if (q.length === 1) throw new CompileError('字符串没有闭合（缺少结尾的 ' + q + '）', startLine); line++; }
          if (ch === '\\' && j + 1 < n) { raw += ch + src[j + 1]; if (src[j + 1] === '\n') line++; j += 2; continue; }
          raw += ch; j++;
        }
        const isRaw = prefix.includes('r');
        const val = isRaw ? raw : unescape(raw, startLine);
        toks.push({ t: 'STRING', v: prefix.includes('f') ? raw : val, f: prefix.includes('f'), rawStr: isRaw, bytes: prefix.includes('b'), line: startLine });
        i = j; continue;
      }
      if (/[A-Za-z_]/.test(c) || c.charCodeAt(0) > 127) {
        let j = i + 1;
        while (j < n && (/[A-Za-z0-9_]/.test(src[j]) || src.charCodeAt(j) > 127)) j++;
        const w = src.slice(i, j);
        push(KEYWORDS.has(w) ? 'KW' : 'NAME', w);
        i = j; continue;
      }
      if (/[0-9]/.test(c) || (c === '.' && /[0-9]/.test(src[i + 1] || ''))) {
        let j = i, isFloat = false, val;
        if (c === '0' && /[xXoObB]/.test(src[i + 1] || '')) {
          const base = { x: 16, o: 8, b: 2 }[src[i + 1].toLowerCase()];
          j = i + 2; while (j < n && /[0-9a-fA-F_]/.test(src[j])) j++;
          val = BigInt((base === 16 ? '0x' : base === 8 ? '0o' : '0b') + src.slice(i + 2, j).replace(/_/g, ''));
        } else {
          while (j < n && /[0-9_]/.test(src[j])) j++;
          if (src[j] === '.' && !/[A-Za-z_]/.test(src[j + 1] || '') ) { isFloat = true; j++; while (j < n && /[0-9_]/.test(src[j])) j++; }
          if (/[eE]/.test(src[j] || '') && /[0-9+-]/.test(src[j + 1] || '')) { isFloat = true; j++; if (/[+-]/.test(src[j])) j++; while (j < n && /[0-9]/.test(src[j])) j++; }
          const txt = src.slice(i, j).replace(/_/g, '');
          val = isFloat ? parseFloat(txt) : BigInt(txt);
        }
        if (/[jJ]/.test(src[j] || '')) throw new CompileError('暂不支持复数', line);
        push('NUMBER', val);
        i = j; continue;
      }
      let op = null;
      for (const o of OPS) if (src.startsWith(o, i)) { op = o; break; }
      if (!op) {
        if (c === '!' ) throw new CompileError('Python 里没有 ! 运算符，逻辑非请用 not', line);
        if (c === '?' ) throw new CompileError('Python 没有 ?: 三目运算符，请写成 a if 条件 else b', line);
        throw new CompileError('无法识别的字符：' + c, line);
      }
      if (op === '(' || op === '[' || op === '{') depth++;
      if (op === ')' || op === ']' || op === '}') depth = Math.max(0, depth - 1);
      push('OP', op);
      i += op.length;
    }
    if (toks.length && toks[toks.length - 1].t !== 'NEWLINE') push('NEWLINE', '');
    while (indents.length > 1) { indents.pop(); push('DEDENT', 0); }
    push('EOF', '');
    return toks;
  }

  function unescape(raw, line) {
    let s = '';
    for (let i = 0; i < raw.length; i++) {
      const c = raw[i];
      if (c !== '\\') { s += c; continue; }
      const nx = raw[++i];
      switch (nx) {
        case 'n': s += '\n'; break; case 't': s += '\t'; break; case 'r': s += '\r'; break;
        case '\\': s += '\\'; break; case "'": s += "'"; break; case '"': s += '"'; break;
        case '0': s += '\0'; break; case 'a': s += '\x07'; break; case 'b': s += '\b'; break; case 'f': s += '\f'; break; case 'v': s += '\v'; break;
        case '\n': break;
        case 'x': s += String.fromCharCode(parseInt(raw.substr(i + 1, 2), 16)); i += 2; break;
        case 'u': s += String.fromCharCode(parseInt(raw.substr(i + 1, 4), 16)); i += 4; break;
        default: s += '\\' + nx;
      }
    }
    return s;
  }

  class Parser {
    constructor(toks) { this.toks = toks; this.p = 0; }
    peek(o) { return this.toks[Math.min(this.p + (o || 0), this.toks.length - 1)]; }
    next() { return this.toks[this.p++]; }
    isOp(v, o) { const t = this.peek(o); return t.t === 'OP' && t.v === v; }
    isKw(v, o) { const t = this.peek(o); return t.t === 'KW' && t.v === v; }
    acceptOp(v) { if (this.isOp(v)) return this.next(); return null; }
    acceptKw(v) { if (this.isKw(v)) return this.next(); return null; }
    expectOp(v, what) {
      if (this.isOp(v)) return this.next();
      const t = this.peek();
      let msg = '这里应该是 “' + v + '”' + (what ? '（' + what + '）' : '') + '，但遇到了 ' + this.desc(t);
      if (v === ':' ) msg = '语法错误：' + (what || '这里') + '末尾缺少冒号 “:”';
      throw new CompileError(msg, t.line);
    }
    expectKw(v) { if (this.isKw(v)) return this.next(); this.err('这里应该是关键字 ' + v); }
    desc(t) { if (t.t === 'NEWLINE') return '行尾'; if (t.t === 'INDENT') return '多余的缩进'; if (t.t === 'DEDENT') return '缩进结束'; if (t.t === 'EOF') return '文件结尾'; return '“' + t.v + '”'; }
    err(msg, t) { t = t || this.peek(); throw new CompileError(msg, t.line); }
    name() { const t = this.peek(); if (t.t !== 'NAME') this.err('这里应该是一个名字，但遇到了 ' + this.desc(t) + (t.t === 'KW' ? '（' + t.v + ' 是关键字，不能作为名字）' : '')); this.p++; return t.v; }

    parseFile() {
      const body = [];
      while (this.peek().t !== 'EOF') {
        if (this.peek().t === 'NEWLINE') { this.next(); continue; }
        if (this.peek().t === 'INDENT') this.err('缩进错误（IndentationError）：这一行多了不该有的缩进');
        body.push(...this.parseStatement());
      }
      return { type: 'Module', body };
    }
    parseBlock(what) {
      // after ':'
      if (this.peek().t !== 'NEWLINE') {
        // simple statements on same line
        const stmts = this.parseSimpleLine();
        return stmts;
      }
      this.next();
      if (this.peek().t !== 'INDENT') this.err('缩进错误（IndentationError）：' + (what || '这里') + '后面的代码块需要缩进');
      this.next();
      const body = [];
      while (this.peek().t !== 'DEDENT' && this.peek().t !== 'EOF') {
        if (this.peek().t === 'NEWLINE') { this.next(); continue; }
        if (this.peek().t === 'INDENT') this.err('缩进错误（IndentationError）：这一行的缩进不一致');
        body.push(...this.parseStatement());
      }
      if (this.peek().t === 'DEDENT') this.next();
      return body;
    }
    parseStatement() {
      const t = this.peek();
      const line = t.line;
      if (t.t === 'KW') {
        switch (t.v) {
          case 'if': return [this.parseIf()];
          case 'while': {
            this.next(); const test = this.parseNamedExpr(); this.expectOp(':', 'while 语句');
            const body = this.parseBlock('while 语句');
            let orelse = [];
            if (this.isKw('else')) { this.next(); this.expectOp(':', 'else'); orelse = this.parseBlock('else'); }
            return [{ type: 'While', test, body, orelse, line }];
          }
          case 'for': {
            this.next(); const target = this.parseTargetList(); this.expectKw('in'); const iter = this.parseTestList(); this.expectOp(':', 'for 语句');
            const body = this.parseBlock('for 语句');
            let orelse = [];
            if (this.isKw('else')) { this.next(); this.expectOp(':', 'else'); orelse = this.parseBlock('else'); }
            return [{ type: 'For', target, iter, body, orelse, line }];
          }
          case 'def': return [this.parseDef([])];
          case 'class': return [this.parseClass([])];
          case 'try': return [this.parseTry()];
          case 'with': {
            this.next(); const items = [];
            do { const e = this.parseTest(); let as = null; if (this.acceptKw('as')) as = this.parseTarget(); items.push({ e, as }); } while (this.acceptOp(','));
            this.expectOp(':', 'with 语句');
            return [{ type: 'With', items, body: this.parseBlock('with'), line }];
          }
          case 'async': this.err('暂不支持 async');
        }
      }
      if (t.t === 'OP' && t.v === '@') {
        const decos = [];
        while (this.acceptOp('@')) { decos.push(this.parseNamedExpr()); if (this.peek().t !== 'NEWLINE') this.err('装饰器后面应该换行'); this.next(); }
        if (this.isKw('def')) return [this.parseDef(decos)];
        if (this.isKw('class')) return [this.parseClass(decos)];
        this.err('装饰器后面应该是 def 或 class');
      }
      return this.parseSimpleLine();
    }
    parseSimpleLine() {
      const stmts = [this.parseSmall()];
      while (this.acceptOp(';')) { if (this.peek().t === 'NEWLINE') break; stmts.push(this.parseSmall()); }
      const t = this.peek();
      if (t.t !== 'NEWLINE' && t.t !== 'EOF') {
        if (t.t === 'OP' && t.v === ':' ) this.err('语法错误：这里不应该出现冒号');
        if (t.t === 'OP' && t.v === '=' ) this.err('语法错误：不能给这个表达式赋值');
        this.err('语法错误：遇到了意外的 ' + this.desc(t) + '（是不是少了运算符、逗号或括号？）');
      }
      if (t.t === 'NEWLINE') this.next();
      return stmts;
    }
    parseSmall() {
      const t = this.peek();
      const line = t.line;
      if (t.t === 'KW') {
        switch (t.v) {
          case 'pass': this.next(); return { type: 'Pass', line };
          case 'break': this.next(); return { type: 'Break', line };
          case 'continue': this.next(); return { type: 'Continue', line };
          case 'return': { this.next(); let value = null; if (!this.atEndOfSimple()) value = this.parseTestListStar(); return { type: 'Return', value, line }; }
          case 'global': case 'nonlocal': { this.next(); const names = [this.name()]; while (this.acceptOp(',')) names.push(this.name()); return { type: t.v === 'global' ? 'Global' : 'Nonlocal', names, line }; }
          case 'del': { this.next(); const targets = [this.parseExpr()]; while (this.acceptOp(',')) targets.push(this.parseExpr()); return { type: 'Del', targets, line }; }
          case 'raise': { this.next(); let exc = null, cause = null; if (!this.atEndOfSimple()) { exc = this.parseTest(); if (this.acceptKw('from')) cause = this.parseTest(); } return { type: 'Raise', exc, cause, line }; }
          case 'assert': { this.next(); const test = this.parseTest(); let msg = null; if (this.acceptOp(',')) msg = this.parseTest(); return { type: 'Assert', test, msg, line }; }
          case 'import': {
            this.next(); const names = [];
            do { let nm = this.name(); while (this.acceptOp('.')) nm += '.' + this.name(); let as = null; if (this.acceptKw('as')) as = this.name(); names.push({ name: nm, as }); } while (this.acceptOp(','));
            return { type: 'Import', names, line };
          }
          case 'from': {
            this.next(); let mod = ''; while (this.acceptOp('.')) mod += '.'; if (this.peek().t === 'NAME') { mod += this.name(); while (this.acceptOp('.')) mod += '.' + this.name(); }
            this.expectKw('import'); const names = [];
            const paren = this.acceptOp('(');
            if (this.acceptOp('*')) names.push({ name: '*' });
            else do { if (paren && this.isOp(')')) break; const nm = this.name(); let as = null; if (this.acceptKw('as')) as = this.name(); names.push({ name: nm, as }); } while (this.acceptOp(','));
            if (paren) this.expectOp(')');
            return { type: 'ImportFrom', module: mod, names, line };
          }
          case 'yield': { this.next(); let value = null; if (this.acceptKw('from')) { value = this.parseTest(); return { type: 'Expr', value: { type: 'YieldFrom', value, line }, line }; } if (!this.atEndOfSimple()) value = this.parseTestListStar(); return { type: 'Expr', value: { type: 'Yield', value, line }, line }; }
        }
      }
      // expression / assignment
      const first = this.parseTestListStar();
      if (this.isOp('=')) {
        const targets = [first];
        let value;
        for (;;) {
          this.next();
          if (this.isKw('yield')) { this.next(); value = { type: 'Yield', value: this.parseTestListStar(), line }; }
          else value = this.parseTestListStar();
          if (this.isOp('=')) { targets.push(value); continue; }
          break;
        }
        for (const tg of targets) this.checkTarget(tg);
        return { type: 'Assign', targets, value, line };
      }
      const t2 = this.peek();
      if (t2.t === 'OP' && /^(\+|-|\*|\/|\/\/|%|\*\*|>>|<<|&|\||\^|@)=$/.test(t2.v)) {
        this.next();
        this.checkTarget(first);
        const value = this.parseTestList();
        return { type: 'AugAssign', target: first, op: t2.v.slice(0, -1), value, line };
      }
      if (this.isOp(':')) {
        // annotated assignment
        this.next(); const ann = this.parseTest(); let value = null;
        if (this.acceptOp('=')) value = this.parseTestList();
        this.checkTarget(first);
        return { type: 'AnnAssign', target: first, ann, value, line };
      }
      return { type: 'Expr', value: first, line };
    }
    checkTarget(e) {
      switch (e.type) {
        case 'Name': case 'Attribute': case 'Subscript': return;
        case 'Tuple': case 'List': e.elts.forEach(x => this.checkTarget(x.type === 'Starred' ? x.value : x)); return;
        case 'Starred': this.checkTarget(e.value); return;
      }
      let what = '表达式';
      if (e.type === 'Call') what = '函数调用';
      else if (e.type === 'Const') what = '常量';
      else if (e.type === 'Compare') what = '比较表达式（判断相等要用 ==，赋值用 =，两者不要搞混）';
      throw new CompileError('语法错误：不能给' + what + '赋值', e.line);
    }
    atEndOfSimple() { const t = this.peek(); return t.t === 'NEWLINE' || t.t === 'EOF' || (t.t === 'OP' && t.v === ';'); }
    parseIf() {
      const line = this.peek().line;
      this.next();
      const test = this.parseNamedExpr();
      this.expectOp(':', 'if 语句');
      const body = this.parseBlock('if 语句');
      let orelse = [];
      if (this.isKw('elif')) { const el = this.peek(); el.v = 'if'; el.t = 'KW'; orelse = [this.parseIf()]; orelse[0].isElif = true; }
      else if (this.isKw('else')) { this.next(); this.expectOp(':', 'else'); orelse = this.parseBlock('else'); }
      return { type: 'If', test, body, orelse, line };
    }
    parseDef(decos) {
      const line = this.peek().line;
      this.expectKw('def');
      const name = this.name();
      this.expectOp('(', '函数参数');
      const params = this.parseParams(')');
      this.expectOp(')');
      if (this.acceptOp('->')) this.parseTest();
      this.expectOp(':', '函数定义');
      const body = this.parseBlock('函数定义');
      const endLine = this.toks[this.p - 1].line;
      return { type: 'FuncDef', name, params, body, decos, line, endLine };
    }
    parseParams(close) {
      const params = [];
      let kwonly = false;
      while (!this.isOp(close)) {
        if (this.acceptOp('/')) { this.acceptOp(','); continue; }
        if (this.acceptOp('**')) { params.push({ name: this.name(), kind: 'kwargs' }); if (close === ')' && this.acceptOp(':')) this.parseTest(); }
        else if (this.acceptOp('*')) { if (this.peek().t === 'NAME') { params.push({ name: this.name(), kind: 'varargs' }); if (close === ')' && this.acceptOp(':')) this.parseTest(); } kwonly = true; }
        else {
          const nm = this.name();
          if (close === ')' && this.acceptOp(':')) this.parseTest();
          let def = null;
          if (this.acceptOp('=')) def = this.parseTest();
          params.push({ name: nm, def, kind: kwonly ? 'kwonly' : 'normal' });
        }
        if (!this.acceptOp(',')) break;
      }
      return params;
    }
    parseClass(decos) {
      const line = this.peek().line;
      this.expectKw('class');
      const name = this.name();
      let bases = [];
      if (this.acceptOp('(')) { if (!this.isOp(')')) bases = this.parseCallArgs(); this.expectOp(')'); }
      this.expectOp(':', '类定义');
      const body = this.parseBlock('类定义');
      return { type: 'ClassDef', name, bases, body, decos, line, endLine: this.toks[this.p - 1].line };
    }
    parseTry() {
      const line = this.peek().line;
      this.next(); this.expectOp(':', 'try');
      const body = this.parseBlock('try');
      const handlers = [];
      while (this.isKw('except')) {
        const hl = this.peek().line;
        this.next();
        let typ = null, name = null;
        if (!this.isOp(':')) { typ = this.parseTest(); if (this.acceptKw('as')) name = this.name(); else if (this.acceptOp(',')) name = this.name(); }
        this.expectOp(':', 'except');
        handlers.push({ typ, name, body: this.parseBlock('except'), line: hl });
      }
      let orelse = [], finalbody = [];
      if (this.isKw('else')) { this.next(); this.expectOp(':'); orelse = this.parseBlock('else'); }
      if (this.isKw('finally')) { this.next(); this.expectOp(':'); finalbody = this.parseBlock('finally'); }
      if (!handlers.length && !finalbody.length) this.err('try 语句需要至少一个 except 或 finally');
      return { type: 'Try', body, handlers, orelse, finalbody, line };
    }

    // ---- expressions ----
    parseTargetList() {
      const line = this.peek().line;
      const first = this.parseTargetAtom();
      if (!this.isOp(',')) return first;
      const elts = [first];
      while (this.acceptOp(',')) { if (this.isKw('in') || this.isOp('=')) break; elts.push(this.parseTargetAtom()); }
      return { type: 'Tuple', elts, line };
    }
    parseTargetAtom() { if (this.acceptOp('*')) return { type: 'Starred', value: this.parseBitOr(), line: this.peek().line }; return this.parseBitOr(); }
    parseTarget() { return this.parseTargetList(); }
    parseTestList() {
      const line = this.peek().line;
      const first = this.parseTest();
      if (!this.isOp(',')) return first;
      const elts = [first];
      while (this.acceptOp(',')) { if (this.endOfList()) break; elts.push(this.parseTest()); }
      return { type: 'Tuple', elts, line };
    }
    parseTestListStar() {
      const line = this.peek().line;
      const first = this.isOp('*') ? (this.next(), { type: 'Starred', value: this.parseOr(), line }) : this.parseTest();
      if (!this.isOp(',')) return first;
      const elts = [first];
      while (this.acceptOp(',')) { if (this.endOfList()) break; elts.push(this.isOp('*') ? (this.next(), { type: 'Starred', value: this.parseOr(), line }) : this.parseTest()); }
      return { type: 'Tuple', elts, line };
    }
    endOfList() { const t = this.peek(); return t.t === 'NEWLINE' || t.t === 'EOF' || (t.t === 'OP' && (t.v === '=' || t.v === ')' || t.v === ']' || t.v === '}' || t.v === ';' || t.v === ':')) || (t.t === 'OP' && /^.+=$/.test(t.v) && t.v !== '==' && t.v !== '<=' && t.v !== '>=' && t.v !== '!='); }
    parseNamedExpr() {
      if (this.peek().t === 'NAME' && this.isOp(':=', 1)) { const line = this.peek().line; const name = this.name(); this.next(); const value = this.parseTest(); return { type: 'NamedExpr', target: { type: 'Name', id: name, line }, value, line }; }
      return this.parseTest();
    }
    parseTest() {
      const line = this.peek().line;
      if (this.isKw('lambda')) {
        this.next();
        const params = this.parseParams(':');
        this.expectOp(':', 'lambda');
        const body = this.parseTest();
        return { type: 'Lambda', params, body, line };
      }
      const e = this.parseOr();
      if (this.isKw('if')) {
        // conditional expression (but not comprehension "if")
        const save = this.p;
        this.next();
        const test = this.parseOr();
        if (!this.isKw('else')) { this.p = save; return e; }
        this.next();
        const orelse = this.parseTest();
        return { type: 'IfExp', test, body: e, orelse, line };
      }
      return e;
    }
    parseOr() {
      let e = this.parseAnd();
      while (this.isKw('or')) { const line = this.next().line; e = { type: 'BoolOp', op: 'or', values: [e, this.parseAnd()], line }; }
      return e;
    }
    parseAnd() {
      let e = this.parseNot();
      while (this.isKw('and')) { const line = this.next().line; e = { type: 'BoolOp', op: 'and', values: [e, this.parseNot()], line }; }
      return e;
    }
    parseNot() {
      if (this.isKw('not')) { const line = this.next().line; return { type: 'UnaryOp', op: 'not', operand: this.parseNot(), line }; }
      return this.parseComparison();
    }
    parseComparison() {
      const left = this.parseBitOr();
      const ops = [], comps = [];
      for (;;) {
        const t = this.peek();
        let op = null;
        if (t.t === 'OP' && ['<', '>', '==', '>=', '<=', '!='].includes(t.v)) { this.next(); op = t.v; }
        else if (t.t === 'KW' && t.v === 'in') { this.next(); op = 'in'; }
        else if (t.t === 'KW' && t.v === 'not' && this.isKw('in', 1)) { this.next(); this.next(); op = 'not in'; }
        else if (t.t === 'KW' && t.v === 'is') { this.next(); op = this.acceptKw('not') ? 'is not' : 'is'; }
        else break;
        ops.push(op); comps.push(this.parseBitOr());
      }
      if (!ops.length) return left;
      return { type: 'Compare', left, ops, comps, line: left.line };
    }
    parseBin(next, ops) {
      let e = next();
      for (;;) {
        const t = this.peek();
        if (t.t === 'OP' && ops.includes(t.v)) { this.next(); e = { type: 'BinOp', op: t.v, left: e, right: next(), line: t.line }; }
        else break;
      }
      return e;
    }
    parseBitOr() { return this.parseBin(() => this.parseBitXor(), ['|']); }
    parseBitXor() { return this.parseBin(() => this.parseBitAnd(), ['^']); }
    parseBitAnd() { return this.parseBin(() => this.parseShift(), ['&']); }
    parseShift() { return this.parseBin(() => this.parseArith(), ['<<', '>>']); }
    parseArith() { return this.parseBin(() => this.parseTerm(), ['+', '-']); }
    parseTerm() { return this.parseBin(() => this.parseFactor(), ['*', '/', '//', '%', '@']); }
    parseFactor() {
      const t = this.peek();
      if (t.t === 'OP' && (t.v === '-' || t.v === '+' || t.v === '~')) {
        this.next();
        const operand = this.parseFactor();
        if (t.v === '-' && operand.type === 'Const' && (typeof operand.v === 'bigint' || typeof operand.v === 'number')) return { type: 'Const', v: -operand.v, line: t.line };
        return { type: 'UnaryOp', op: t.v, operand, line: t.line };
      }
      return this.parsePower();
    }
    parsePower() {
      let e = this.parseAwaitPrimary();
      if (this.isOp('**')) { const line = this.next().line; e = { type: 'BinOp', op: '**', left: e, right: this.parseFactor(), line }; }
      return e;
    }
    parseAwaitPrimary() {
      let e = this.parseAtom();
      for (;;) {
        const t = this.peek();
        if (t.t !== 'OP') break;
        if (t.v === '(') {
          this.next();
          const args = this.isOp(')') ? [] : this.parseCallArgs();
          this.expectOp(')', '函数调用');
          e = { type: 'Call', func: e, args, line: t.line };
        } else if (t.v === '[') {
          this.next();
          const index = this.parseSubscript();
          this.expectOp(']', '下标');
          e = { type: 'Subscript', obj: e, index, line: t.line };
        } else if (t.v === '.') {
          this.next();
          const nt = this.peek();
          if (nt.t !== 'NAME' && nt.t !== 'KW') this.err('点号 . 后面应该是属性名');
          this.next();
          e = { type: 'Attribute', obj: e, name: nt.v, line: t.line };
        } else break;
      }
      return e;
    }
    parseSubscript() {
      const line = this.peek().line;
      const one = () => {
        let lo = null, hi = null, step = null;
        if (!this.isOp(':')) { lo = this.parseTest(); if (!this.isOp(':')) return lo; }
        this.expectOp(':');
        if (!this.isOp(']') && !this.isOp(':') && !this.isOp(',')) hi = this.parseTest();
        if (this.acceptOp(':')) { if (!this.isOp(']') && !this.isOp(',')) step = this.parseTest(); }
        return { type: 'Slice', lo, hi, step, line };
      };
      const first = one();
      if (!this.isOp(',')) return first;
      const elts = [first];
      while (this.acceptOp(',')) { if (this.isOp(']')) break; elts.push(one()); }
      return { type: 'Tuple', elts, line };
    }
    parseCallArgs() {
      const args = [];
      for (;;) {
        if (this.isOp(')')) break;
        const line = this.peek().line;
        if (this.acceptOp('**')) args.push({ kind: 'kwstar', value: this.parseTest(), line });
        else if (this.acceptOp('*')) args.push({ kind: 'star', value: this.parseTest(), line });
        else if (this.peek().t === 'NAME' && this.isOp('=', 1)) { const name = this.name(); this.next(); args.push({ kind: 'kw', name, value: this.parseTest(), line }); }
        else {
          let v = this.parseNamedExpr();
          if (this.isKw('for')) v = { type: 'GeneratorExp', elt: v, gens: this.parseCompFor(), line };
          args.push({ kind: 'pos', value: v, line });
        }
        if (!this.acceptOp(',')) break;
      }
      return args;
    }
    parseCompFor() {
      const gens = [];
      while (this.isKw('for')) {
        this.next();
        const target = this.parseTargetList();
        this.expectKw('in');
        const iter = this.parseOr();
        const ifs = [];
        while (this.isKw('if')) { this.next(); ifs.push(this.parseOrNoCond()); }
        gens.push({ target, iter, ifs });
      }
      return gens;
    }
    parseOrNoCond() { return this.parseOr(); }
    parseAtom() {
      const t = this.next();
      const line = t.line;
      switch (t.t) {
        case 'NUMBER': return { type: 'Const', v: t.v, line };
        case 'STRING': {
          let parts = [];
          let tok = t;
          const pushTok = (tk) => { if (tk.f) parts.push(...this.parseFString(tk.v, tk.line, tk.rawStr)); else parts.push(tk.v); };
          pushTok(tok);
          while (this.peek().t === 'STRING') pushTok(this.next());
          if (parts.every(p => typeof p === 'string')) return { type: 'Const', v: parts.join(''), line };
          return { type: 'FString', parts, line };
        }
        case 'NAME': return { type: 'Name', id: t.v, line };
        case 'KW':
          if (t.v === 'True') return { type: 'Const', v: true, line };
          if (t.v === 'False') return { type: 'Const', v: false, line };
          if (t.v === 'None') return { type: 'Const', v: null, line };
          if (t.v === 'yield') { let value = null; if (!this.isOp(')')) value = this.parseTestList(); return { type: 'Yield', value, line }; }
          if (t.v === 'await') this.err('暂不支持 await');
          break;
        case 'OP':
          if (t.v === '(') {
            if (this.acceptOp(')')) return { type: 'Tuple', elts: [], line };
            if (this.isKw('yield')) { this.next(); const v = this.isOp(')') ? null : this.parseTestList(); this.expectOp(')'); return { type: 'Yield', value: v, line }; }
            const first = this.isOp('*') ? (this.next(), { type: 'Starred', value: this.parseOr(), line }) : this.parseNamedExpr();
            if (this.isKw('for')) { const gens = this.parseCompFor(); this.expectOp(')'); return { type: 'GeneratorExp', elt: first, gens, line }; }
            if (this.acceptOp(')')) { if (first.type === 'Starred') this.err('不能单独使用 *'); first.paren = true; return first; }
            const elts = [first];
            while (this.acceptOp(',')) { if (this.isOp(')')) break; elts.push(this.isOp('*') ? (this.next(), { type: 'Starred', value: this.parseOr(), line }) : this.parseTest()); }
            this.expectOp(')', '括号');
            return { type: 'Tuple', elts, line };
          }
          if (t.v === '[') {
            if (this.acceptOp(']')) return { type: 'List', elts: [], line };
            const first = this.isOp('*') ? (this.next(), { type: 'Starred', value: this.parseOr(), line }) : this.parseNamedExpr();
            if (this.isKw('for')) { const gens = this.parseCompFor(); this.expectOp(']'); return { type: 'ListComp', elt: first, gens, line }; }
            const elts = [first];
            while (this.acceptOp(',')) { if (this.isOp(']')) break; elts.push(this.isOp('*') ? (this.next(), { type: 'Starred', value: this.parseOr(), line }) : this.parseTest()); }
            this.expectOp(']', '列表');
            return { type: 'List', elts, line };
          }
          if (t.v === '{') {
            if (this.acceptOp('}')) return { type: 'Dict', keys: [], values: [], line };
            if (this.acceptOp('**')) {
              const keys = [null], values = [this.parseOr()];
              while (this.acceptOp(',')) { if (this.isOp('}')) break; if (this.acceptOp('**')) { keys.push(null); values.push(this.parseOr()); } else { keys.push(this.parseTest()); this.expectOp(':'); values.push(this.parseTest()); } }
              this.expectOp('}'); return { type: 'Dict', keys, values, line };
            }
            const first = this.isOp('*') ? (this.next(), { type: 'Starred', value: this.parseOr(), line }) : this.parseTest();
            if (this.acceptOp(':')) {
              const v = this.parseTest();
              if (this.isKw('for')) { const gens = this.parseCompFor(); this.expectOp('}'); return { type: 'DictComp', key: first, value: v, gens, line }; }
              const keys = [first], values = [v];
              while (this.acceptOp(',')) {
                if (this.isOp('}')) break;
                if (this.acceptOp('**')) { keys.push(null); values.push(this.parseOr()); continue; }
                keys.push(this.parseTest()); this.expectOp(':', '字典的键值对'); values.push(this.parseTest());
              }
              this.expectOp('}', '字典');
              return { type: 'Dict', keys, values, line };
            }
            if (this.isKw('for')) { const gens = this.parseCompFor(); this.expectOp('}'); return { type: 'SetComp', elt: first, gens, line }; }
            const elts = [first];
            while (this.acceptOp(',')) { if (this.isOp('}')) break; elts.push(this.parseTest()); }
            this.expectOp('}', '集合');
            return { type: 'Set', elts, line };
          }
          if (t.v === '...') return { type: 'Const', v: null, ellipsis: true, line };
          break;
      }
      if (t.t === 'INDENT') throw new CompileError('缩进错误（IndentationError）：这一行多了不该有的缩进', t.line);
      if (t.t === 'NEWLINE' || t.t === 'EOF') throw new CompileError('语法错误：这一行没有写完（表达式不完整，或者括号没有闭合）', t.line);
      throw new CompileError('语法错误：这里不应该出现 ' + this.desc(t), t.line);
    }
    parseFString(raw, line, isRaw) {
      const parts = [];
      let lit = '';
      for (let i = 0; i < raw.length; i++) {
        const c = raw[i];
        if (c === '{') {
          if (raw[i + 1] === '{') { lit += '{'; i++; continue; }
          if (lit) { parts.push(isRaw ? lit : unescape(lit, line)); lit = ''; }
          // find matching }
          let depth = 1, j = i + 1, inStr = null;
          let exprEnd = -1, convPos = -1, specPos = -1;
          for (; j < raw.length; j++) {
            const ch = raw[j];
            if (inStr) { if (ch === inStr) inStr = null; continue; }
            if (ch === '"' || ch === "'") { inStr = ch; continue; }
            if (ch === '{' || ch === '[' || ch === '(') depth++;
            else if (ch === '}' || ch === ']' || ch === ')') { depth--; if (depth === 0) break; }
            else if (depth === 1 && ch === '!' && raw[j + 1] !== '=' && convPos < 0 && specPos < 0) convPos = j;
            else if (depth === 1 && ch === ':' && specPos < 0) specPos = j;
          }
          if (j >= raw.length) throw new CompileError('f-string 里的 { 没有闭合', line);
          let exprSrc = raw.slice(i + 1, convPos >= 0 ? convPos : (specPos >= 0 ? specPos : j));
          let conv = convPos >= 0 ? raw.slice(convPos + 1, specPos >= 0 ? specPos : j) : null;
          let spec = specPos >= 0 ? raw.slice(specPos + 1, j) : null;
          let selfDoc = false;
          if (/=\s*$/.test(exprSrc) && !/[=!<>]=\s*$/.test(exprSrc)) { selfDoc = exprSrc; exprSrc = exprSrc.replace(/=\s*$/, ''); }
          const sub = lex(exprSrc.trim());
          sub.forEach(tk => tk.line = line);
          const p = new Parser(sub.filter(tk => tk.t !== 'NEWLINE' && tk.t !== 'INDENT' && tk.t !== 'DEDENT'));
          const expr = p.parseTestList();
          let specParts = null;
          if (spec && spec.includes('{')) specParts = this.parseFString(spec, line, true);
          if (selfDoc) parts.push(selfDoc);
          parts.push({ expr, conv: conv || (selfDoc && !spec ? 'r' : null), spec, specParts });
          i = j;
          continue;
        }
        if (c === '}') { if (raw[i + 1] === '}') i++; lit += '}'; continue; }
        lit += c;
      }
      if (lit) parts.push(isRaw ? lit : unescape(lit, line));
      return parts;
    }
  }

  DSV.pyParse = function (src) {
    const toks = lex(src.replace(/\r\n/g, '\n'));
    const p = new Parser(toks);
    return p.parseFile();
  };
})(typeof window !== 'undefined' ? window : globalThis);
