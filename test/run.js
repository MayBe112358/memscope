const DSV = require('./load');
const fs = require('fs');
const [,, lang, file, ...rest] = process.argv;
const code = fs.readFileSync(file, 'utf8');
const opts = { maxSteps: 20000 };
for (const r of rest) { const [k, v] = r.split('='); if (k === 'args') opts.args = v.split(' ').filter(Boolean); if (k === 'stdin') opts.stdin = v.replace(/\\n/g, '\n'); }
const t0 = Date.now();
const res = DSV.langs[lang].run(code, opts);
const ms = Date.now() - t0;
if (res.compileError) { console.log('COMPILE ERROR line', res.compileError.line, res.compileError.msg); process.exit(0); }
console.log('--- stdout ---'); console.log(res.out);
console.log('--- steps:', res.steps.length, 'time', ms + 'ms');
if (res.error) console.log('ERROR', res.error);
const verbose = process.env.V;
if (verbose) {
  res.steps.forEach((s, i) => {
    if (verbose === 'last' && i < res.steps.length - 3) return;
    console.log('#' + i, 'line', s.line, s.ev, s.msgs.map(m => m.text).join(' | '));
    if (verbose === 'full' || verbose === 'last') console.log(JSON.stringify(s.snap, null, 0).slice(0, 3000));
  });
}
for (const s of res.steps) for (const m of s.msgs) if (m.cls === 'warn' || m.cls === 'leak' || m.cls === 'error') console.log('MSG', m.cls, m.text);
