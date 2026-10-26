/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs'), os = require('node:os'), path = require('node:path');
const {plan, importsOnly} = require('../scripts/ci/replay-plan.cjs');
const temp = fs.mkdtempSync(path.join(os.tmpdir(), 'edsl-replay-plan-'));
const catalogue = path.join(temp, 'All.lean'), aggregate = path.join(temp, 'Full.lean');
const owned = 'ABCDEFGHIJKLMNOPQRSTUVWX'.split('').map(letter => 'Owned.'+letter);
const expected = [...owned, 'CorpusCertificateChecks', 'corpus.Certify', 'tests.Client'].sort();
try {
  fs.writeFileSync(catalogue, '/- catalogue /- nested comment -/ -/\n'+owned.map(x => 'import '+x+'\n').join(''));
  fs.writeFileSync(aggregate, 'import EDSL.All\nimport CorpusCertificateChecks\nimport corpus.Certify\nimport tests.Client\nimport Owned.A\n');
  const output = path.join(temp, 'roots');
  const units = plan(catalogue, aggregate, output);
  assert.equal(units.length, 20);
  assert(units.every(unit => unit.roots.length > 0));
  // Compare actual generated import files with the independent required root
  // inventory. Loss, duplicate assignment or omitted named checks must fail.
  const actual = units.flatMap(unit => importsOnly(path.join(output, 'KernelReplay'+unit.id+'.lean')));
  assert.deepEqual(actual.sort(), expected);
  assert.equal(new Set(actual).size, actual.length);
  for (const unit of units) {
    const audit = fs.readFileSync(path.join(output, 'AuditKernelReplay'+unit.id+'.lean'), 'utf8');
    assert.match(audit, /#audit_edsl_owners\n/);
    assert.match(audit, /#audit_edsl\n/);
  }
  fs.appendFileSync(catalogue, 'theorem extra : True := by trivial\n');
  assert.throws(() => plan(catalogue, aggregate, path.join(temp, 'unsafe')), /import-only/);
  fs.writeFileSync(catalogue, owned.map(x => 'import '+x+'\n').join(''));
  fs.writeFileSync(aggregate, 'import EDSL.All\nimport corpus.Certify\n');
  assert.throws(() => plan(catalogue, aggregate, path.join(temp, 'incomplete')), /named checks/);
  console.log('Replay planner: exact root coverage/uniqueness, 20 nonempty shards, owner audits, declaration and missing-check rejection passed.');
} finally { fs.rmSync(temp, {recursive:true, force:true}); }
