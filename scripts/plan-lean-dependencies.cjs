/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';
const fs = require('node:fs'), path = require('node:path'), assert = require('node:assert/strict');
const crypto = require('node:crypto'), {execFileSync} = require('node:child_process');
const moduleName = /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/;

// Lake parses the actual headers and determines local module ownership. Its
// transImports facet lists dependencies before importers. The result schedules
// builds; it is not evidence that a source or an existing object was checked.
function plan(lake, target, sourceRoot = path.resolve(__dirname, '..')) {
  assert.equal(typeof lake, 'string'); assert(lake.length > 0);
  assert(moduleName.test(target), 'canonical library target required');
  const query = targets => execFileSync(lake, ['--json','query',...targets], {
    cwd:sourceRoot, encoding:'utf8', timeout:110000, maxBuffer:16*1024*1024,
    stdio:['ignore','pipe','inherit']
  });
  const roots = JSON.parse(query([target+':modules']));
  assert(Array.isArray(roots) && roots.length > 0, 'nonempty library required');
  assert(roots.every(n => typeof n === 'string' && moduleName.test(n)), 'invalid root module');
  assert.equal(new Set(roots).size, roots.length, 'duplicate library module');
  const lines = query(roots.map(n => '+'+n+':transImports')).trimEnd().split('\n');
  assert.equal(lines.length, roots.length, 'one closure per root required');
  const order = [], seen = new Set();
  const add = name => {
    assert(typeof name === 'string' && moduleName.test(name), 'invalid dependency module');
    if (!seen.has(name)) { seen.add(name); order.push(name); }
  };
  for (let i = 0; i < roots.length; i++) {
    const imports = JSON.parse(lines[i]); assert(Array.isArray(imports), 'dependency array required');
    imports.forEach(add); add(roots[i]);
  }
  const hash = file => crypto.createHash('sha256').update(fs.readFileSync(file)).digest('hex');
  const files = ['lean-toolchain','lakefile.lean','lake-manifest.json',
    ...order.map(name => name.replaceAll('.','/')+'.lean')];
  const sources = files.map(file => {
    const absolute = path.resolve(sourceRoot,file);
    assert(fs.lstatSync(absolute).isFile(), 'regular source file required: '+file);
    assert.equal(fs.realpathSync(absolute), absolute, 'source aliases are not supported: '+file);
    return {file,sha256:hash(absolute)};
  });
  return {target,roots,order,sources};
}
if (require.main === module) {
  const [lake,target,out,...extra] = process.argv.slice(2);
  assert.equal(extra.length,0,'usage: plan-lean-dependencies.cjs LAKE LIBRARY NEW_OUTPUT_DIRECTORY');
  assert(lake && target && out,'usage: plan-lean-dependencies.cjs LAKE LIBRARY NEW_OUTPUT_DIRECTORY');
  assert(path.isAbsolute(out), 'absolute output directory required');
  const result = plan(lake,target);
  fs.mkdirSync(out);
  fs.writeFileSync(out+'/plan.json',JSON.stringify(result,null,2)+'\n',{flag:'wx'});
  fs.writeFileSync(out+'/modules.txt',result.order.join('\n')+'\n',{flag:'wx'});
  fs.writeFileSync(out+'/INPUTS.sha256',result.sources.map(s=>s.sha256+'  '+s.file+'\n').join(''),{flag:'wx'});
  console.log(JSON.stringify({target,roots:result.roots.length,modules:result.order.length}));
}
module.exports = {plan};
