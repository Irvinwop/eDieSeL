/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';
const fs = require('node:fs'), path = require('node:path'), os = require('node:os');
const assert = require('node:assert/strict'), {spawnSync} = require('node:child_process');
const {plan} = require('../scripts/plan-lean-dependencies.cjs');
const lake = process.env.EDSL_LAKE || 'lake';
const root = fs.mkdtempSync(path.join(os.tmpdir(),'edsl-dependency-plan-'));
const put = (file,text) => {
  fs.mkdirSync(path.dirname(root+'/'+file),{recursive:true});
  fs.writeFileSync(root+'/'+file,text);
};
const run = (args,pass=true) => {
  const result = spawnSync(lake,args,{cwd:root,encoding:'utf8',timeout:110000,
    env:{...process.env,LEAN_NUM_THREADS:'1'},maxBuffer:4*1024*1024});
  assert.ifError(result.error);
  if (pass) assert.equal(result.status,0,result.stdout+result.stderr);
  else assert.notEqual(result.status,0,'stale or invalid source unexpectedly accepted');
  return result;
};
try {
  put('lean-toolchain',fs.readFileSync(path.resolve(__dirname,'../lean-toolchain'),'utf8'));
  put('lakefile.lean','import Lake\nopen Lake DSL\npackage schedulerFixture where\n' +
    '  moreLeanArgs := #["-j1", "-DwarningAsError=true", "-DautoImplicit=false", '+
    '"-DmaxHeartbeats=300000", "-DmaxRecDepth=128"]\n' +
    'lean_lib Support where\n  roots := #[`Support.Leaf, `Support.Path]\n' +
    'lean_lib Checks where\n  roots := #[`Checks.Contract, `Checks.Second]\n');
  put('Support/Leaf.lean','def advance (n : Nat) : Nat := n + 2\n');
  put('Support/Path.lean','import Support.Leaf\ndef twice (n : Nat) : Nat := advance (advance n)\n');
  put('Checks/Contract.lean','import Support.Path\nexample : twice 38 = 42 := by decide\n');
  put('Checks/Second.lean','import Support.Leaf\nexample : advance 40 = 42 := by decide\n');
  // Initial workspace load creates Lake's ordinary empty-dependency manifest.
  run(['--json','query','Checks:modules']);
  const result = plan(lake,'Checks',root);
  assert.deepEqual(new Set(result.order),new Set([
    'Support.Leaf','Support.Path','Checks.Contract','Checks.Second']));
  for (const [dependency,importer] of [['Support.Leaf','Support.Path'],
    ['Support.Path','Checks.Contract'],['Support.Leaf','Checks.Second']])
    assert(result.order.indexOf(dependency) < result.order.indexOf(importer),
      'dependency scheduled after importer');
  run(['--rehash','--no-build','build','Checks'],false);
  for (const name of result.order) run(['--rehash','build','+'+name+':leanArts']);
  run(['--rehash','--no-build','build','Checks']);
  // This changes the independent arithmetic contracts. Reusing the old objects
  // would incorrectly accept both proofs; Lake must refuse the stale target.
  put('Support/Leaf.lean','def advance (n : Nat) : Nat := n + 3\n');
  run(['--rehash','--no-build','build','Checks'],false);
  for (const name of ['Checks.Contract','Checks.Second']) {
    const invalid = run(['--rehash','build','+'+name+':leanArts'],false);
    assert.match(invalid.stdout+invalid.stderr,/error:.*(?:Contract|Second)\.lean:/,
      'invalid arithmetic contract must be rechecked and rejected');
  }
  // Graph discovery must use Lean/Lake's parser rather than a line-based regex.
  put('Support/Leaf.lean','import Checks.Contract\ndef advance (n : Nat) : Nat := n + 2\n');
  assert.throws(()=>plan(lake,'Checks',root),/Command failed/,'cyclic imports must be rejected');
  console.log('Real Lake dependency order, cold build, stale-input and invalid-contract checks passed.');
} finally {
  fs.rmSync(root,{recursive:true,force:true});
}
