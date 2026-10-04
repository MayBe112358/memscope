const fs = require('fs'), path = require('path'), vm = require('vm');
const files = ['core.js','clike_lex.js','clike_parse.js','clike_interp.js','clike_eval.js','clike_lib.js','clike_snap.js','py_parse.js','py_interp.js','py_lib.js','js_parse.js','js_interp.js','js_lib.js','examples.js'];
const ctx = { console };
ctx.globalThis = ctx;
vm.createContext(ctx);
for (const f of files) {
  const p = path.join(__dirname, '../src', f);
  if (!fs.existsSync(p)) continue;
  vm.runInContext(fs.readFileSync(p, 'utf8'), ctx, { filename: f });
}
module.exports = ctx.DSV;
