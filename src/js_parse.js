// ===== JavaScript / TypeScript lexer + parser =====
(function (G) {
  const DSV = G.DSV;
  const { CompileError } = DSV;

  const PUNCT = ['>>>=', '...', '===', '!==', '**=', '<<=', '>>=', '>>>', '&&=', '||=', '??=',
    '=>', '?.', '??', '**', '++', '--', '&&', '||', '==', '!=', '<=', '>=', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '<<', '>>',
    '{', '}', '(', ')', '[', ']', ';', ',', '<', '>', '+', '-', '*', '/', '%', '&', '|', '^', '!', '~', '?', ':', '=', '.', '@', '#'];
  const KEYWORDS = new Set(['break', 'case', 'catch', 'class', 'const', 'continue', 'debugger', 'default', 'delete', 'do', 'else', 'export', 'extends', 'finally', 'for', 'function', 'if', 'import', 'in', 'instanceof', 'new', 'return', 'super', 'switch', 'this', 'throw', 'try', 'typeof', 'var', 'void', 'while', 'with', 'null', 'true', 'false']);

  function lex(src) {
    const toks = [];
    let i = 0, line = 1, nl = false;
    const n = src.length;
    const regexAllowed = () => {
      const t = toks[toks.length - 1];
      if (!t) return true;
      if (t.t === 'num' || t.t === 'str' || t.t === 'tpl' || t.t === 'regex') return false;
      if (t.t === 'name') return KEYWORDS.has(t.v) && !['this', 'super', 'null', 'true', 'false'].includes(t.v);
      if (t.t === 'p') return !(t.v === ')' || t.v === ']' || t.v === '}');
      return true;
    };
    const push = (t, v, extra) => { toks.push(Object.assign({ t, v, line, nl }, extra || {})); nl = false; };
    while (i < n) {
      const c = src[i];
      if (c === '\n') { line++; nl = true; i++; continue; }
      if (c === ' ' || c === '\t' || c === '\r' || c === '﻿' || c === ' ') { i++; continue; }
      if (c === '/' && src[i + 1] === '/') { while (i < n && src[i] !== '\n') i++; continue; }
      if (c === '/' && src[i + 1] === '*') { i += 2; while (i < n && !(src[i] === '*' && src[i + 1] === '/')) { if (src[i] === '\n') { line++; nl = true; } i++; } if (i >= n) throw new CompileError('注释 /* 没有闭合', line); i += 2; continue; }
      if (/[A-Za-z_$]/.test(c) || c.charCodeAt(0) > 127) {
        let j = i + 1;
        while (j < n && (/[A-Za-z0-9_$]/.test(src[j]) || src.charCodeAt(j) > 127)) j++;
        push('name', src.slice(i, j));
        i = j; continue;
      }
      if (/[0-9]/.test(c) || (c === '.' && /[0-9]/.test(src[i + 1] || ''))) {
        let j = i, v;
        if (c === '0' && /[xXbBoO]/.test(src[i + 1] || '')) {
          j = i + 2; while (j < n && /[0-9a-fA-F_]/.test(src[j])) j++;
          const base = { x: 16, b: 2, o: 8 }[src[i + 1].toLowerCase()];
          v = parseInt(src.slice(i + 2, j).replace(/_/g, ''), base);
        } else {
          while (j < n && /[0-9_]/.test(src[j])) j++;
          if (src[j] === '.') { j++; while (j < n && /[0-9_]/.test(src[j])) j++; }
          if (/[eE]/.test(src[j] || '') && /[0-9+-]/.test(src[j + 1] || '')) { j++; if (/[+-]/.test(src[j])) j++; while (j < n && /[0-9]/.test(src[j])) j++; }
          v = parseFloat(src.slice(i, j).replace(/_/g, ''));
        }
        if (src[j] === 'n') { push('num', BigInt(src.slice(i, j).replace(/_/g, ''))); i = j + 1; continue; }
        push('num', v);
        i = j; continue;
      }
      if (c === '"' || c === "'") {
        let j = i + 1, s = '';
        while (j < n && src[j] !== c) {
          if (src[j] === '\n') throw new CompileError('字符串没有闭合（缺少 ' + c + '）', line);
          if (src[j] === '\\') { const [ch, nj] = esc(src, j); s += ch; j = nj; if (ch === '' && src[j - 1] === '\n') line++; continue; }
          s += src[j++];
        }
        if (j >= n) throw new CompileError('字符串没有闭合（缺少 ' + c + '）', line);
        push('str', s);
        i = j + 1; continue;
      }
      if (c === '`') {
        // template literal: collect quasis + expression sources
        const startLine = line;
        let j = i + 1, cur = '';
        const quasis = [], exprs = [];
        for (;;) {
          if (j >= n) throw new CompileError('模板字符串没有闭合（缺少 `）', startLine);
          const ch = src[j];
          if (ch === '`') { j++; break; }
          if (ch === '\\') { const [e2, nj] = esc(src, j); cur += e2; j = nj; continue; }
          if (ch === '$' && src[j + 1] === '{') {
            quasis.push(cur); cur = '';
            let depth = 1, k = j + 2, inS = null;
            const exStart = k, exLine = line;
            for (; k < n; k++) {
              const d = src[k];
              if (d === '\n') line++;
              if (inS) { if (d === '\\') { k++; continue; } if (d === inS) inS = null; continue; }
              if (d === '"' || d === "'" || d === '`') { inS = d; continue; }
              if (d === '{') depth++;
              else if (d === '}') { depth--; if (depth === 0) break; }
            }
            exprs.push({ src: src.slice(exStart, k), line: exLine });
            j = k + 1; continue;
          }
          if (ch === '\n') line++;
          cur += ch; j++;
        }
        quasis.push(cur);
        toks.push({ t: 'tpl', quasis, exprs, line: startLine, nl });
        nl = false;
        i = j; continue;
      }
      if (c === '/' && regexAllowed()) {
        let j = i + 1, inClass = false;
        while (j < n) {
          const d = src[j];
          if (d === '\n') throw new CompileError('正则表达式没有闭合', line);
          if (d === '\\') { j += 2; continue; }
          if (d === '[') inClass = true; else if (d === ']') inClass = false;
          else if (d === '/' && !inClass) break;
          j++;
        }
        const body = src.slice(i + 1, j);
        j++;
        let flags = '';
        while (j < n && /[a-z]/.test(src[j])) flags += src[j++];
        push('regex', body, { flags });
        i = j; continue;
      }
      let p = null;
      for (const o of PUNCT) if (src.startsWith(o, i)) { p = o; break; }
      if (p === '?.' && /[0-9]/.test(src[i + 2] || '')) p = '?';
      if (!p) throw new CompileError('无法识别的字符：' + c, line);
      push('p', p);
      i += p.length;
    }
    push('eof', '');
    return toks;
  }
  function esc(src, j) {
    const n = src[j + 1];
    switch (n) {
      case 'n': return ['\n', j + 2]; case 't': return ['\t', j + 2]; case 'r': return ['\r', j + 2]; case 'b': return ['\b', j + 2];
      case 'f': return ['\f', j + 2]; case 'v': return ['\v', j + 2]; case '0': return ['\0', j + 2];
      case 'x': return [String.fromCharCode(parseInt(src.substr(j + 2, 2), 16)), j + 4];
      case 'u': if (src[j + 2] === '{') { const e = src.indexOf('}', j); return [String.fromCodePoint(parseInt(src.slice(j + 3, e), 16)), e + 1]; } return [String.fromCharCode(parseInt(src.substr(j + 2, 4), 16)), j + 6];
      case '\n': return ['', j + 2];
      case '\r': return ['', src[j + 2] === '\n' ? j + 3 : j + 2];
      default: return [n, j + 2];
    }
  }

  class Parser {
    constructor(toks, ts) { this.toks = toks; this.p = 0; this.ts = ts; this.inClass = 0; }
    peek(o) { return this.toks[Math.min(this.p + (o || 0), this.toks.length - 1)]; }
    next() { return this.toks[this.p++]; }
    is(v, o) { const t = this.peek(o); return (t.t === 'p' || t.t === 'name') && t.v === v; }
    isP(v, o) { const t = this.peek(o); return t.t === 'p' && t.v === v; }
    isName(o) { return this.peek(o).t === 'name'; }
    accept(v) { if (this.is(v)) return this.next(); return null; }
    expect(v, what) {
      if (this.is(v)) return this.next();
      const t = this.peek();
      throw new CompileError('这里应该是 “' + v + '”' + (what ? '（' + what + '）' : '') + '，但遇到了 ' + this.desc(t), t.line);
    }
    desc(t) { if (t.t === 'eof') return '文件结尾'; if (t.t === 'tpl') return '模板字符串'; return '“' + String(t.v) + '”'; }
    err(msg, t) { t = t || this.peek(); throw new CompileError(msg, t.line); }
    ident(what) {
      const t = this.peek();
      if (t.t !== 'name') this.err('这里应该是一个名字' + (what ? '（' + what + '）' : '') + '，但遇到了 ' + this.desc(t));
      this.p++; return t.v;
    }
    semi() {
      if (this.accept(';')) return;
      const t = this.peek();
      if (t.t === 'eof' || this.isP('}') || t.nl) return;
      this.err('语句末尾缺少分号或换行（遇到了 ' + this.desc(t) + '）');
    }

    // ---------- TypeScript types (skipped) ----------
    skipType(noArrow) {
      this.skipUnion();
      if (this.isP('=>') && !noArrow) { this.next(); this.skipType(); }
      // conditional types: A extends B ? C : D
      if (this.is('extends') && this.ts) { this.next(); this.skipUnion(); if (this.accept('?')) { this.skipType(); this.expect(':'); this.skipType(); } }
    }
    skipUnion() {
      this.accept('|'); this.accept('&');
      this.skipPostfixType();
      while (this.isP('|') || this.isP('&')) { this.next(); this.skipPostfixType(); }
    }
    skipPostfixType() {
      this.skipPrimaryType();
      for (;;) {
        if (this.isP('[') && !this.peek().nl) { this.next(); if (!this.isP(']')) this.skipType(); this.expect(']'); continue; }
        break;
      }
    }
    skipPrimaryType() {
      const t = this.peek();
      if (t.t === 'p') {
        if (t.v === '(') {
          // parenthesized type or function type params
          this.next(); let depth = 1;
          while (depth > 0) { if (this.isP('(')) depth++; else if (this.isP(')')) depth--; if (this.peek().t === 'eof') this.err('类型没有闭合'); this.next(); }
          return;
        }
        if (t.v === '{') { this.skipBalanced('{', '}'); return; }
        if (t.v === '[') { this.skipBalanced('[', ']'); return; }
        if (t.v === '<') { this.skipTypeArgs(); this.skipPrimaryType(); return; }
        if (t.v === '-') { this.next(); this.next(); return; }
      }
      if (t.t === 'str' || t.t === 'num' || t.t === 'tpl') { this.next(); return; }
      if (t.t === 'name') {
        if (t.v === 'keyof' || t.v === 'typeof' || t.v === 'readonly' || t.v === 'unique' || t.v === 'infer') { this.next(); this.skipPrimaryType(); return; }
        if (t.v === 'new') { this.next(); this.skipPrimaryType(); return; }
        this.next();
        while (this.isP('.') && this.isName(1)) { this.next(); this.next(); }
        if (this.isP('<')) this.skipTypeArgs();
        if (t.v === 'asserts' && this.isName()) { this.next(); if (this.is('is')) { this.next(); this.skipType(); } }
        if (this.is('is') && this.isName(1) === false) { }
        if (this.is('is')) { this.next(); this.skipType(); }
        return;
      }
      this.err('无法识别的类型注解');
    }
    skipBalanced(open, close) {
      let depth = 0;
      do { if (this.isP(open)) depth++; else if (this.isP(close)) depth--; if (this.peek().t === 'eof') this.err('缺少 ' + close); this.next(); } while (depth > 0);
    }
    skipTypeArgs() {
      this.expect('<');
      let depth = 1;
      while (depth > 0) {
        const t = this.peek();
        if (t.t === 'eof') this.err('泛型参数没有闭合');
        if (t.t === 'p') {
          if (t.v === '<') depth++;
          else if (t.v === '>') depth--;
          else if (t.v === '>>') { depth -= 2; if (depth < 0) { this.toks[this.p] = Object.assign({}, t, { v: '>' }); depth = 0; return; } }
          else if (t.v === '>>>') depth -= 3;
          else if (t.v === '=>' ) { }
        }
        this.next();
      }
    }
    tryTypeArgsCall() {
      // f<T>(...) or new Foo<T>(...) : speculative
      if (!this.ts || !this.isP('<')) return false;
      const save = this.p;
      try { this.skipTypeArgs(); if (this.isP('(') || this.peek().t === 'tpl') return true; } catch (e) { if (!e.isCompile) throw e; }
      this.p = save;
      return false;
    }
    typeAnn() { if (this.ts && this.isP(':')) { this.next(); this.skipType(); return true; } return false; }

    // ---------- program ----------
    parseProgram() {
      const body = [];
      while (this.peek().t !== 'eof') { const s = this.parseStatement(true); if (s) body.push(s); }
      return { type: 'Program', body };
    }
    parseStatement(top) {
      const t = this.peek();
      const line = t.line;
      if (t.t === 'p') {
        if (t.v === '{') return this.parseBlock();
        if (t.v === ';') { this.next(); return { type: 'Empty', line }; }
        if (t.v === '@') { this.next(); this.parseLHS(); return this.parseStatement(top); }
      }
      if (t.t === 'name') {
        // labels
        if (this.isP(':', 1) && !KEYWORDS.has(t.v)) { this.next(); this.next(); const body = this.parseStatement(); return { type: 'Labeled', label: t.v, body, line }; }
        switch (t.v) {
          case 'var': case 'let': case 'const': {
            if (t.v === 'let' && !(this.isName(1) || this.isP('[', 1) || this.isP('{', 1))) break;
            if (t.v === 'const' && this.is('enum', 1)) { this.next(); return this.parseEnum(); }
            const d = this.parseVarDecl(); this.semi(); return d;
          }
          case 'function': return this.parseFunction(true);
          case 'async':
            if (this.is('function', 1) && !this.peek(1).nl) this.err('暂不支持 async 函数（可视化器只模拟同步执行）');
            break;
          case 'class': return this.parseClass(true);
          case 'if': {
            this.next(); this.expect('('); const test = this.parseExpression(); this.expect(')', 'if 条件结尾');
            const cons = this.parseStatement(); let alt = null;
            if (this.accept('else')) alt = this.parseStatement();
            return { type: 'If', test, cons, alt, line };
          }
          case 'while': { this.next(); this.expect('('); const test = this.parseExpression(); this.expect(')'); return { type: 'While', test, body: this.parseStatement(), line }; }
          case 'do': { this.next(); const body = this.parseStatement(); const wl = this.peek().line; this.expect('while'); this.expect('('); const test = this.parseExpression(); this.expect(')'); this.accept(';'); return { type: 'DoWhile', test, body, line, testLine: wl }; }
          case 'for': return this.parseFor();
          case 'return': { this.next(); let arg = null; if (!this.isP(';') && !this.isP('}') && !this.peek().nl && this.peek().t !== 'eof') arg = this.parseExpression(); this.semi(); return { type: 'Return', arg, line }; }
          case 'break': case 'continue': { this.next(); let label = null; if (this.isName() && !this.peek().nl && !KEYWORDS.has(this.peek().v)) label = this.next().v; this.semi(); return { type: t.v === 'break' ? 'Break' : 'Continue', label, line }; }
          case 'throw': { this.next(); if (this.peek().nl) this.err('throw 后面不能换行'); const arg = this.parseExpression(); this.semi(); return { type: 'Throw', arg, line }; }
          case 'try': {
            this.next(); const block = this.parseBlock(); let param = null, handler = null, finalizer = null, hline = 0;
            if (this.is('catch')) { hline = this.next().line; if (this.accept('(')) { param = this.parseBindingTarget(); this.typeAnn(); this.expect(')'); } handler = this.parseBlock(); }
            if (this.accept('finally')) finalizer = this.parseBlock();
            return { type: 'Try', block, param, handler, finalizer, line, hline };
          }
          case 'switch': {
            this.next(); this.expect('('); const disc = this.parseExpression(); this.expect(')'); this.expect('{');
            const cases = [];
            while (!this.accept('}')) {
              const cl = this.peek().line;
              let test = null;
              if (this.accept('case')) test = this.parseExpression(); else this.expect('default');
              this.expect(':');
              const body = [];
              while (!this.is('case') && !this.is('default') && !this.isP('}')) body.push(this.parseStatement());
              cases.push({ test, body, line: cl });
            }
            return { type: 'Switch', disc, cases, line };
          }
          case 'import': if (!this.isP('(', 1)) { while (!this.isP(';') && !this.peek().nl && this.peek().t !== 'eof') this.next(); if (this.isP(';')) this.next(); else while (this.peek().t !== 'eof' && !this.peek().nl) this.next(); return { type: 'Empty', line }; } break;
          case 'export': { this.next(); if (this.accept('default')) { if (this.is('function') || this.is('class')) return this.parseStatement(); const e = this.parseExpression(); this.semi(); return { type: 'Expr', expr: e, line }; } if (this.isP('{')) { this.skipBalanced('{', '}'); this.semi(); return { type: 'Empty', line }; } return this.parseStatement(top); }
          case 'debugger': this.next(); this.semi(); return { type: 'Empty', line };
        }
        if (this.ts) {
          if ((t.v === 'interface') && this.isName(1)) { this.next(); this.next(); if (this.isP('<')) this.skipTypeArgs(); while (!this.isP('{')) this.next(); this.skipBalanced('{', '}'); return { type: 'Empty', line }; }
          if (t.v === 'type' && this.isName(1) && !this.peek(1).nl) { this.next(); this.next(); if (this.isP('<')) this.skipTypeArgs(); this.expect('='); this.skipType(); this.semi(); return { type: 'Empty', line }; }
          if (t.v === 'enum' && this.isName(1)) return this.parseEnum();
          if (t.v === 'declare') { this.next(); while (!this.isP(';') && !this.peek().nl && this.peek().t !== 'eof') { if (this.isP('{')) { this.skipBalanced('{', '}'); break; } this.next(); } this.accept(';'); return { type: 'Empty', line }; }
          if (t.v === 'abstract' && this.is('class', 1)) { this.next(); return this.parseClass(true); }
          if (t.v === 'namespace' || t.v === 'module') { if (this.isName(1)) { this.next(); this.next(); return this.parseBlock(); } }
        }
      }
      const expr = this.parseExpression();
      this.semi();
      return { type: 'Expr', expr, line };
    }
    parseEnum() {
      const line = this.peek().line;
      this.expect('enum');
      const name = this.ident();
      this.expect('{');
      const members = [];
      while (!this.accept('}')) {
        const k = this.peek().t === 'str' ? this.next().v : this.ident();
        let init = null;
        if (this.accept('=')) init = this.parseAssign();
        members.push({ k, init });
        if (!this.accept(',')) { this.expect('}'); break; }
      }
      return { type: 'Enum', name, members, line };
    }
    parseBlock() {
      const line = this.peek().line;
      this.expect('{', '代码块开头');
      const body = [];
      while (!this.isP('}')) {
        if (this.peek().t === 'eof') this.err('缺少右花括号 }，代码块没有闭合', this.toks[this.toks.length - 1]);
        body.push(this.parseStatement());
      }
      const endLine = this.next().line;
      return { type: 'Block', body, line, endLine };
    }
    parseVarDecl(noIn) {
      const line = this.peek().line;
      const kind = this.next().v;
      const decls = [];
      for (;;) {
        const dl = this.peek().line;
        const id = this.parseBindingTarget();
        if (this.ts) { this.accept('!'); this.typeAnn(); }
        let init = null;
        if (this.accept('=')) init = this.parseAssign(noIn);
        else if (kind === 'const' && !noIn) this.err('const 声明必须同时赋初值');
        decls.push({ id, init, line: dl });
        if (!this.accept(',')) break;
      }
      return { type: 'Var', kind, decls, line };
    }
    parseBindingTarget() {
      const t = this.peek();
      if (this.isP('[')) return this.parseArrayPattern();
      if (this.isP('{')) return this.parseObjectPattern();
      const name = this.ident('变量名');
      if (KEYWORDS.has(name) && !['this'].includes(name)) this.err('“' + name + '” 是关键字，不能作为变量名');
      return { type: 'Id', name, line: t.line };
    }
    parseArrayPattern() {
      const line = this.peek().line;
      this.expect('[');
      const elems = [];
      while (!this.accept(']')) {
        if (this.isP(',')) { this.next(); elems.push(null); continue; }
        if (this.accept('...')) { elems.push({ type: 'Rest', arg: this.parseBindingTarget() }); this.accept(','); continue; }
        let tgt = this.parseBindingTarget();
        if (this.accept('=')) tgt = { type: 'Default', target: tgt, def: this.parseAssign() };
        elems.push(tgt);
        if (!this.accept(',')) { this.expect(']'); break; }
      }
      return { type: 'ArrPat', elems, line };
    }
    parseObjectPattern() {
      const line = this.peek().line;
      this.expect('{');
      const props = [];
      while (!this.accept('}')) {
        if (this.accept('...')) { props.push({ rest: this.parseBindingTarget() }); this.accept(','); continue; }
        let key, computed = false;
        if (this.accept('[')) { key = this.parseAssign(); this.expect(']'); computed = true; }
        else if (this.peek().t === 'str' || this.peek().t === 'num') key = String(this.next().v);
        else key = this.ident('属性名');
        let tgt;
        if (this.accept(':')) tgt = this.parseBindingTarget();
        else tgt = { type: 'Id', name: key, line };
        if (this.accept('=')) tgt = { type: 'Default', target: tgt, def: this.parseAssign() };
        props.push({ key, computed, target: tgt });
        if (!this.accept(',')) { this.expect('}'); break; }
      }
      return { type: 'ObjPat', props, line };
    }
    parseFor() {
      const line = this.peek().line;
      this.expect('for');
      if (this.is('await')) this.err('暂不支持 for await');
      this.expect('(');
      let init = null;
      if (this.is('var') || this.is('const') || (this.is('let') && (this.isName(1) || this.isP('[', 1) || this.isP('{', 1)))) {
        const kindTok = this.peek();
        const save = this.p;
        this.next();
        const tgt = this.parseBindingTarget();
        if (this.is('of') || this.is('in')) {
          const of = this.next().v === 'of';
          const right = of ? this.parseAssign() : this.parseExpression();
          this.expect(')');
          const body = this.parseStatement();
          return { type: of ? 'ForOf' : 'ForIn', kind: kindTok.v, left: tgt, right, body, line };
        }
        this.p = save;
        init = this.parseVarDecl(true);
      } else if (!this.isP(';')) {
        const e = this.parseExpression(true);
        if (this.is('of') || this.is('in')) {
          const of = this.next().v === 'of';
          const right = of ? this.parseAssign() : this.parseExpression();
          this.expect(')');
          return { type: of ? 'ForOf' : 'ForIn', kind: null, left: this.toPattern(e), right, body: this.parseStatement(), line };
        }
        init = { type: 'Expr', expr: e, line };
      }
      this.expect(';', 'for 循环的初始化部分后面');
      const test = this.isP(';') ? null : this.parseExpression();
      this.expect(';', 'for 循环的条件后面');
      const update = this.isP(')') ? null : this.parseExpression();
      this.expect(')', 'for 循环头结尾');
      const body = this.parseStatement();
      return { type: 'For', init, test, update, body, line };
    }

    // ---------- functions & classes ----------
    parseFunction(isDecl, isExpr) {
      const line = this.peek().line;
      this.expect('function');
      const gen = !!this.accept('*');
      let name = null;
      if (this.isName()) name = this.next().v;
      if (this.ts && this.isP('<')) this.skipTypeArgs();
      const params = this.parseParams();
      if (this.ts && this.isP(':')) { this.next(); this.skipType(); }
      if (this.ts && !this.isP('{') && isDecl) { this.semi(); return { type: 'Empty', line }; }
      const body = this.parseBlock();
      const fn = { type: 'Function', name, params, body, line, endLine: body.endLine, gen };
      if (isDecl) { if (!name) this.err('函数声明需要名字'); return { type: 'FuncDecl', fn, line }; }
      return fn;
    }
    parseParams() {
      this.expect('(', '参数列表');
      const params = [];
      while (!this.accept(')')) {
        let isProp = false;
        while (this.ts && (this.is('public') || this.is('private') || this.is('protected') || this.is('readonly') || this.is('override')) && (this.isName(1) || this.isP('[', 1) || this.isP('{', 1))) { this.next(); isProp = true; }
        if (isProp) { params.paramProps = params.paramProps || []; params.paramProps.push(this.peek().v); }
        if (this.accept('...')) { const tgt = this.parseBindingTarget(); this.typeAnn(); params.push({ type: 'Rest', arg: tgt }); this.accept(','); continue; }
        if (this.ts && this.is('this') && (this.isP(':', 1))) { this.next(); this.typeAnn(); this.accept(','); continue; }
        let tgt = this.parseBindingTarget();
        if (this.ts) { this.accept('?'); this.typeAnn(); }
        if (this.accept('=')) tgt = { type: 'Default', target: tgt, def: this.parseAssign() };
        params.push(tgt);
        if (!this.accept(',')) { this.expect(')', '参数列表结尾'); break; }
      }
      return params;
    }
    parseClass(isDecl) {
      const line = this.peek().line;
      this.expect('class');
      let name = null;
      if (this.isName() && !this.is('extends') && !this.is('implements')) name = this.next().v;
      if (this.ts && this.isP('<')) this.skipTypeArgs();
      let superClass = null;
      if (this.accept('extends')) { superClass = this.parseLHS(); if (this.ts && this.isP('<')) this.skipTypeArgs(); }
      if (this.ts && this.accept('implements')) { do { this.skipType(); } while (this.accept(',')); }
      this.expect('{', '类体');
      const members = [];
      this.inClass++;
      while (!this.accept('}')) {
        if (this.accept(';')) continue;
        const ml = this.peek().line;
        let isStatic = false, kind = 'method', isGen = false;
        while (this.isP('@')) { this.next(); this.parseLHS(); }
        const mods = () => { let any = false; while (this.ts && ['public', 'private', 'protected', 'readonly', 'abstract', 'override', 'declare'].includes(this.peek().v) && !this.isP('(', 1) && !this.isP('=', 1) && !this.isP(':', 1) && !this.isP(';', 1)) { this.next(); any = true; } return any; };
        mods();
        if (this.is('static') && !this.isP('(', 1) && !this.isP('=', 1)) { this.next(); isStatic = true; }
        mods();
        if (isStatic && this.isP('{')) { const b = this.parseBlock(); members.push({ kind: 'staticBlock', body: b, line: ml }); continue; }
        if (this.is('async') && !this.isP('(', 1)) this.err('暂不支持 async 方法');
        if (this.accept('*')) isGen = true;
        if ((this.is('get') || this.is('set')) && !this.isP('(', 1) && !this.isP('=', 1) && !this.isP(';', 1) && !this.isP(':', 1)) kind = this.next().v;
        let key, computed = false;
        if (this.accept('[')) { key = this.parseAssign(); this.expect(']'); computed = true; }
        else if (this.isP('#')) { this.next(); key = '#' + this.ident(); }
        else if (this.peek().t === 'str' || this.peek().t === 'num') key = String(this.next().v);
        else key = this.ident('成员名');
        if (this.ts) { this.accept('?'); this.accept('!'); }
        if (this.isP('(') || (this.ts && this.isP('<'))) {
          if (this.ts && this.isP('<')) this.skipTypeArgs();
          const params = this.parseParams();
          if (this.ts && this.isP(':')) { this.next(); this.skipType(); }
          if (this.ts && !this.isP('{')) { this.semi(); continue; } // abstract / overload
          const body = this.parseBlock();
          const fn = { type: 'Function', name: computed ? null : key, params, body, line: ml, endLine: body.endLine, isMethod: true, gen: isGen };
          if (key === 'constructor' && !isStatic) { fn.isCtor = true; members.push({ kind: 'ctor', fn, line: ml }); }
          else members.push({ kind, key, computed, isStatic, fn, line: ml });
        } else {
          // field
          this.typeAnn();
          let init = null;
          if (this.accept('=')) init = this.parseAssign();
          this.semi();
          members.push({ kind: 'field', key, computed, isStatic, init, line: ml });
        }
      }
      this.inClass--;
      const cls = { type: 'Class', name, superClass, members, line };
      if (isDecl) { if (!name) this.err('类声明需要名字'); return { type: 'ClassDecl', cls, line }; }
      return cls;
    }

    // ---------- expressions ----------
    parseExpression(noIn) {
      const e = this.parseAssign(noIn);
      if (this.isP(',')) {
        const list = [e];
        while (this.accept(',')) list.push(this.parseAssign(noIn));
        return { type: 'Seq', list, line: e.line };
      }
      return e;
    }
    isArrowAhead() {
      // at '(' : scan to matching ')' and check for '=>'
      let depth = 0, j = 0;
      for (;;) {
        const t = this.peek(j);
        if (t.t === 'eof') return false;
        if (t.t === 'p') {
          if (t.v === '(' || t.v === '[' || t.v === '{') depth++;
          else if (t.v === ')' || t.v === ']' || t.v === '}') { depth--; if (depth === 0) break; }
        }
        j++;
      }
      const after = this.peek(j + 1);
      if (after.t === 'p' && after.v === '=>') return true;
      if (this.ts && after.t === 'p' && after.v === ':') {
        // (a: T): R => ...
        let k = j + 2, d = 0;
        for (; k < j + 60; k++) {
          const t = this.peek(k);
          if (t.t === 'eof') return false;
          if (t.t === 'p' && (t.v === '(' || t.v === '{' || t.v === '[' || t.v === '<')) d++;
          if (t.t === 'p' && (t.v === ')' || t.v === '}' || t.v === ']' || t.v === '>')) d--;
          if (d === 0 && t.t === 'p' && t.v === '=>') return true;
          if (d < 0 || (d === 0 && t.t === 'p' && (t.v === ';' || t.v === ','))) return false;
        }
      }
      return false;
    }
    parseArrow(line) {
      let params;
      if (this.isName()) params = [{ type: 'Id', name: this.next().v, line }];
      else params = this.parseParams();
      if (this.ts && this.isP(':')) { this.next(); this.skipType(true); }
      this.expect('=>');
      if (this.isP('{')) { const body = this.parseBlock(); return { type: 'Function', name: null, params, body, line, endLine: body.endLine, arrow: true }; }
      const e = this.parseAssign();
      return { type: 'Function', name: null, params, body: { type: 'Block', body: [{ type: 'Return', arg: e, line: e.line || line }], line, endLine: line }, line, endLine: line, arrow: true, exprBody: true };
    }
    parseAssign(noIn) {
      const t = this.peek();
      const line = t.line;
      // arrow functions
      if (t.t === 'name' && this.isP('=>', 1) && !KEYWORDS.has(t.v)) return this.parseArrow(line);
      if (t.t === 'name' && t.v === 'async' && (this.isName(1) && this.isP('=>', 2) || this.isP('(', 1) && false)) this.err('暂不支持 async 函数');
      if (this.isP('(') && this.isArrowAhead()) return this.parseArrow(line);
      if (this.ts && this.isP('<') && this.isName(1)) {
        // generic arrow <T>(x: T) => ...
        const save = this.p;
        try { this.skipTypeArgs(); if (this.isP('(') && this.isArrowAhead()) return this.parseArrow(line); } catch (e) { if (!e.isCompile) throw e; }
        this.p = save;
      }
      if (this.is('yield') && !this.isName(1) === false || this.is('yield')) {
        if (this.is('yield')) { this.next(); const delegate = !!this.accept('*'); let arg = null; if (!this.isP(')') && !this.isP(']') && !this.isP('}') && !this.isP(',') && !this.isP(';') && !this.peek().nl) arg = this.parseAssign(); return { type: 'Yield', arg, delegate, line }; }
      }
      const left = this.parseCond(noIn);
      const op = this.peek();
      if (op.t === 'p' && ['=', '+=', '-=', '*=', '/=', '%=', '**=', '<<=', '>>=', '>>>=', '&=', '|=', '^=', '&&=', '||=', '??='].includes(op.v)) {
        this.next();
        const right = this.parseAssign(noIn);
        let target = left;
        if (op.v === '=' && (left.type === 'Array' || left.type === 'Object')) target = this.toPattern(left);
        else if (!['Id', 'Member'].includes(left.type)) throw new CompileError('赋值号左边必须是变量或属性（不能给这个表达式赋值）', op.line);
        return { type: 'Assign', op: op.v, target, right, line: op.line };
      }
      return left;
    }
    toPattern(e) {
      switch (e.type) {
        case 'Id': case 'Member': return e;
        case 'Array': return { type: 'ArrPat', elems: e.elems.map(x => x === null ? null : (x.type === 'Spread' ? { type: 'Rest', arg: this.toPattern(x.arg) } : this.toPattern(x))), line: e.line };
        case 'Object': return { type: 'ObjPat', props: e.props.map(p => p.spread ? { rest: this.toPattern(p.value) } : { key: p.key, computed: p.computed, target: this.toPattern(p.value) }), line: e.line };
        case 'Assign': if (e.op === '=') return { type: 'Default', target: this.toPattern(e.target), def: e.right };
      }
      throw new CompileError('无效的解构赋值目标', e.line);
    }
    parseCond(noIn) {
      const test = this.parseBinary(0, noIn);
      if (this.isP('?')) {
        const line = this.next().line;
        const cons = this.parseAssign();
        this.expect(':', '三目运算符');
        const alt = this.parseAssign(noIn);
        return { type: 'Cond', test, cons, alt, line };
      }
      return test;
    }
    prec(t, noIn) {
      if (t.t === 'name') {
        if (t.v === 'instanceof') return 7;
        if (t.v === 'in' && !noIn) return 7;
        if (t.v === 'as' && this.ts) return 12;
        if (t.v === 'satisfies' && this.ts) return 12;
        return -1;
      }
      if (t.t !== 'p') return -1;
      switch (t.v) {
        case '??': return 1; case '||': return 1; case '&&': return 2; case '|': return 3; case '^': return 4; case '&': return 5;
        case '==': case '!=': case '===': case '!==': return 6;
        case '<': case '>': case '<=': case '>=': return 7;
        case '<<': case '>>': case '>>>': return 8;
        case '+': case '-': return 9;
        case '*': case '/': case '%': return 10;
        case '**': return 11;
      }
      return -1;
    }
    parseBinary(minPrec, noIn) {
      let left = this.parseUnary();
      for (;;) {
        const t = this.peek();
        const pr = this.prec(t, noIn);
        if (pr <= minPrec) break;
        this.next();
        if (t.v === 'as' || t.v === 'satisfies') { if (this.is('const')) this.next(); else this.skipType(); continue; }
        const right = t.v === '**' ? this.parseBinary(pr - 1, noIn) : this.parseBinary(pr, noIn);
        if (t.v === '&&' || t.v === '||' || t.v === '??') left = { type: 'Logical', op: t.v, left, right, line: t.line };
        else left = { type: 'Binary', op: t.v, left, right, line: t.line };
      }
      return left;
    }
    parseUnary() {
      const t = this.peek();
      const line = t.line;
      if (t.t === 'p') {
        if (t.v === '!' || t.v === '-' || t.v === '+' || t.v === '~') { this.next(); const arg = this.parseUnary(); if (t.v === '-' && arg.type === 'Num') return { type: 'Num', v: -arg.v, line }; return { type: 'Unary', op: t.v, arg, line }; }
        if (t.v === '++' || t.v === '--') { this.next(); const arg = this.parseUnary(); if (!['Id', 'Member'].includes(arg.type)) this.err('++/-- 只能用在变量或属性上'); return { type: 'Update', op: t.v, prefix: true, arg, line }; }
        if (t.v === '<' && this.ts) { this.skipTypeArgs(); return this.parseUnary(); }
      }
      if (t.t === 'name') {
        if (t.v === 'typeof' || t.v === 'void' || t.v === 'delete') { this.next(); return { type: 'Unary', op: t.v, arg: this.parseUnary(), line }; }
        if (t.v === 'await') this.err('暂不支持 await（可视化器只模拟同步执行）');
      }
      const e = this.parsePostfix();
      return e;
    }
    parsePostfix() {
      const e = this.parseLHS();
      const t = this.peek();
      if (t.t === 'p' && (t.v === '++' || t.v === '--') && !t.nl) {
        this.next();
        if (!['Id', 'Member'].includes(e.type)) this.err('++/-- 只能用在变量或属性上');
        return { type: 'Update', op: t.v, prefix: false, arg: e, line: t.line };
      }
      if (this.ts && this.isP('!') && !t.nl && !this.isP('=', 1)) { this.next(); }
      return e;
    }
    parseLHS() {
      let e;
      const t = this.peek();
      if (t.t === 'name' && t.v === 'new') {
        const line = this.next().line;
        if (this.isP('.')) { this.next(); this.ident(); e = { type: 'Undef', line }; }
        else {
          let callee = this.parseMemberOnly();
          if (this.ts && this.isP('<')) this.skipTypeArgs();
          let args = [];
          if (this.isP('(')) args = this.parseArgs();
          e = { type: 'New', callee, args, line };
        }
      } else e = this.parsePrimary();
      return this.parseTail(e, true);
    }
    parseMemberOnly() {
      let e;
      if (this.is('new')) { const line = this.next().line; const callee = this.parseMemberOnly(); const args = this.isP('(') ? this.parseArgs() : []; e = { type: 'New', callee, args, line }; }
      else e = this.parsePrimary();
      for (;;) {
        if (this.isP('.')) { this.next(); const name = this.isP('#') ? (this.next(), '#' + this.ident()) : this.ident(); e = { type: 'Member', obj: e, prop: { type: 'Str', v: name }, computed: false, line: e.line }; continue; }
        if (this.isP('[')) { this.next(); const prop = this.parseExpression(); this.expect(']'); e = { type: 'Member', obj: e, prop, computed: true, line: e.line }; continue; }
        break;
      }
      return e;
    }
    parseTail(e, allowCall) {
      for (;;) {
        const t = this.peek();
        if (t.t === 'p') {
          if (t.v === '.') { this.next(); const nt = this.peek(); let name; if (nt.t === 'p' && nt.v === '#') { this.next(); name = '#' + this.ident(); } else { if (nt.t !== 'name') this.err('点号 . 后面应该是属性名'); this.next(); name = nt.v; } e = { type: 'Member', obj: e, prop: { type: 'Str', v: name }, computed: false, line: t.line }; continue; }
          if (t.v === '?.') {
            this.next();
            if (this.isP('(')) { e = { type: 'Call', callee: e, args: this.parseArgs(), optional: true, line: t.line }; continue; }
            if (this.isP('[')) { this.next(); const prop = this.parseExpression(); this.expect(']'); e = { type: 'Member', obj: e, prop, computed: true, optional: true, line: t.line }; continue; }
            const name = this.ident('属性名');
            e = { type: 'Member', obj: e, prop: { type: 'Str', v: name }, computed: false, optional: true, line: t.line };
            continue;
          }
          if (t.v === '[') { this.next(); const prop = this.parseExpression(); this.expect(']', '下标'); e = { type: 'Member', obj: e, prop, computed: true, line: t.line }; continue; }
          if (t.v === '(' && allowCall) { e = { type: 'Call', callee: e, args: this.parseArgs(), line: t.line }; continue; }
          if (t.v === '<' && this.ts && allowCall) { if (this.tryTypeArgsCall()) continue; }
          if (t.v === '!' && this.ts && !t.nl && !this.isP('=', 1)) { this.next(); continue; }
        }
        if (t.t === 'tpl' && !t.nl) { // tagged template: treat as call with string
          const q = this.next(); e = { type: 'Call', callee: e, args: [this.tplNode(q)], line: t.line }; continue;
        }
        break;
      }
      return e;
    }
    parseArgs() {
      this.expect('(');
      const args = [];
      while (!this.accept(')')) {
        if (this.accept('...')) args.push({ type: 'Spread', arg: this.parseAssign() });
        else args.push(this.parseAssign());
        if (!this.accept(',')) { this.expect(')', '函数调用的参数'); break; }
      }
      return args;
    }
    tplNode(t) {
      const exprs = t.exprs.map(x => {
        const sub = lex(x.src); sub.forEach(tk => tk.line = x.line);
        const p = new Parser(sub, this.ts);
        const e = p.parseExpression();
        return e;
      });
      return { type: 'Tpl', quasis: t.quasis, exprs, line: t.line };
    }
    parsePrimary() {
      const t = this.next();
      const line = t.line;
      switch (t.t) {
        case 'num': return { type: 'Num', v: t.v, line };
        case 'str': return { type: 'Str', v: t.v, line };
        case 'tpl': return this.tplNode(t);
        case 'regex': return { type: 'Regex', body: t.v, flags: t.flags, line };
        case 'name':
          switch (t.v) {
            case 'true': return { type: 'Bool', v: true, line };
            case 'false': return { type: 'Bool', v: false, line };
            case 'null': return { type: 'Null', line };
            case 'undefined': return { type: 'Id', name: 'undefined', line };
            case 'this': return { type: 'This', line };
            case 'super': return { type: 'Super', line };
            case 'function': this.p--; return this.parseFunction(false, true);
            case 'class': this.p--; return this.parseClass(false);
          }
          if (KEYWORDS.has(t.v) && !['of', 'get', 'set', 'static', 'let'].includes(t.v)) throw new CompileError('这里不应该出现关键字 “' + t.v + '”', line);
          return { type: 'Id', name: t.v, line };
        case 'p':
          if (t.v === '(') {
            const e = this.parseExpression();
            this.expect(')', '括号');
            return e;
          }
          if (t.v === '[') {
            const elems = [];
            while (!this.accept(']')) {
              if (this.isP(',')) { this.next(); elems.push(null); continue; }
              if (this.accept('...')) elems.push({ type: 'Spread', arg: this.parseAssign() });
              else elems.push(this.parseAssign());
              if (!this.accept(',')) { this.expect(']', '数组'); break; }
            }
            return { type: 'Array', elems, line };
          }
          if (t.v === '{') {
            const props = [];
            while (!this.accept('}')) {
              if (this.accept('...')) { props.push({ spread: true, value: this.parseAssign() }); if (!this.accept(',')) { this.expect('}'); break; } continue; }
              let kind = 'init';
              if ((this.is('get') || this.is('set')) && !this.isP(':', 1) && !this.isP('(', 1) && !this.isP(',', 1) && !this.isP('}', 1)) kind = this.next().v;
              if (this.is('async') && !this.isP(':', 1) && !this.isP('(', 1) && !this.isP(',', 1) && !this.isP('}', 1)) this.err('暂不支持 async 方法');
              const gen = !!this.accept('*');
              let key, computed = false;
              const kt = this.peek();
              if (this.accept('[')) { key = this.parseAssign(); this.expect(']'); computed = true; }
              else if (kt.t === 'str' || kt.t === 'num') { this.next(); key = String(kt.v); }
              else if (kt.t === 'name') { this.next(); key = kt.v; }
              else this.err('对象字面量里应该是属性名');
              if (this.isP('(')) {
                const params = this.parseParams();
                if (this.ts && this.isP(':')) { this.next(); this.skipType(); }
                const body = this.parseBlock();
                props.push({ key, computed, kind: kind === 'init' ? 'method' : kind, value: { type: 'Function', name: computed ? null : key, params, body, line: kt.line, endLine: body.endLine, isMethod: true, gen } });
              } else if (this.accept(':')) props.push({ key, computed, value: this.parseAssign() });
              else {
                // shorthand (possibly with default in patterns)
                let value = { type: 'Id', name: key, line: kt.line };
                if (this.isP('=')) { this.next(); value = { type: 'Assign', op: '=', target: value, right: this.parseAssign(), line: kt.line }; }
                props.push({ key, computed: false, value, shorthand: true });
              }
              if (!this.accept(',')) { this.expect('}', '对象字面量'); break; }
            }
            return { type: 'Object', props, line };
          }
          if (t.v === '#') { const nm = this.ident(); return { type: 'Str', v: '#' + nm, line }; }
          break;
        case 'eof': throw new CompileError('代码在这里意外结束了（是不是少了右括号或花括号？）', line);
      }
      throw new CompileError('这里不应该出现 ' + this.desc(t), line);
    }
  }

  DSV.jsParse = function (src, ts) {
    const toks = lex(src);
    const p = new Parser(toks, !!ts);
    return p.parseProgram();
  };
})(typeof window !== 'undefined' ? window : globalThis);
