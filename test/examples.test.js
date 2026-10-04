const DSV = require('./load');
let bad = 0;
for (const ex of DSV.examples) {
  const t0 = Date.now();
  let res;
  try { res = DSV.langs[ex.lang].run(ex.code, { args: (ex.args || '').split(' ').filter(Boolean), stdin: ex.stdin || '', maxSteps: 5000 }); }
  catch (e) { console.log('CRASH', ex.id, e.stack); bad++; continue; }
  const ms = Date.now() - t0;
  const warns = [];
  for (const s of res.steps) for (const m of s.msgs) if (m.cls === 'warn' || m.cls === 'leak') warns.push(m.text);
  const status = res.compileError ? 'COMPILE ' + res.compileError.line + ' ' + res.compileError.msg : (res.error ? 'ERR ' + res.error.kind + ' ' + res.error.msg : 'ok');
  if (status !== 'ok' && ex.id !== 'c-errors') bad++;
  console.log((status === 'ok' ? '✓' : '✗'), ex.id.padEnd(18), String(res.steps.length).padStart(5), 'steps', String(ms).padStart(4) + 'ms', status === 'ok' ? '' : status);
  console.log('   out:', JSON.stringify(res.out).slice(0, 150));
  if (warns.length) console.log('   warn:', warns.slice(0, 3).join(' | ').slice(0, 300));
}
console.log('bad:', bad);
