// 构建：把 src/ 下的脚本按顺序拼进 shell.html，生成单文件的 index.html
const fs = require('fs');
const order = ['core.js', 'clike_lex.js', 'clike_parse.js', 'clike_interp.js', 'clike_eval.js', 'clike_lib.js', 'clike_snap.js', 'py_parse.js', 'py_interp.js', 'py_lib.js', 'js_parse.js', 'js_interp.js', 'js_lib.js', 'examples.js', 'editor.js', 'viz.js', 'app.js'];
let js = '';
for (const f of order) {
  const src = fs.readFileSync('src/' + f, 'utf8');
  if (/<\/script/i.test(src)) throw new Error('</script in ' + f);
  js += '\n// ---- ' + f + ' ----\n' + src;
}
const shell = fs.readFileSync('src/shell.html', 'utf8');
const head = '<!doctype html>\n<html lang="zh-CN">\n<head>\n<meta charset="utf-8">\n<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">\n<style>:root{padding-top:env(safe-area-inset-top,0px);padding-bottom:env(safe-area-inset-bottom,0px)}body{margin:0}[hidden]{display:none!important}</style>\n</head>\n<body>\n';
const out = head + shell + '\n<script>\n"use strict";\n' + js + '\n</script>\n</body>\n</html>\n';
fs.writeFileSync('index.html', out);
console.log('built index.html', (out.length / 1024).toFixed(1) + 'KB');
