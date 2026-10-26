/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs'), os = require('node:os'), path = require('node:path');
const {spawnSync} = require('node:child_process');
const repo = path.resolve(__dirname, '..');
const root = fs.mkdtempSync(path.join(os.tmpdir(), 'edsl-replay-transport-'));
function write(name, text) {
  const file = path.join(root, name); fs.mkdirSync(path.dirname(file), {recursive:true});
  fs.writeFileSync(file, text); return file;
}
function run(command, args, expected = 0) {
  const result = spawnSync(command, args, {cwd:root, encoding:'utf8'});
  assert.equal(result.status, expected, `${command} ${args.join(' ')}\n${result.stdout}${result.stderr}`);
  return result;
}
function manifest(name, files) {
  write(name, run('sha256sum', ['--', ...files]).stdout);
}
try {
  run('git', ['init', '--quiet']);
  for (const name of ['scripts/ci/corpus-replay.sh', 'scripts/ci/replay-plan.cjs', 'scripts/audit-lean-source.cjs']) {
    const file = write(name, fs.readFileSync(path.join(repo, name)));
    fs.chmodSync(file, fs.statSync(path.join(repo, name)).mode);
  }
  write('EDSL/All.lean', 'ABCDEFGHIJKLMNOPQRSTUVWX'.split('').map(x => 'import Owned.'+x+'\n').join(''));
  write('corpus/v1/gcc/final.elf', 'owned synthetic input; never executed');
  write('corpus/v1/clang/final.elf', 'another owned synthetic input; never executed');
  run('git', ['add', '.']);
  write('artifacts/corpus-certificates/LATEST', path.join(root, 'gate')+'\n');
  // Opaque synthetic object bytes exercise transport/integrity only. This
  // fixture never invokes Lean and establishes no proof or certificate claim.
  write('.lake/build/lib/lean/Owned/A.olean', 'synthetic stored-object bytes');
  const executable = write('.lake/build/bin/tool', '#!/bin/sh\nexit 0\n');
  fs.chmodSync(executable, 0o755);
  write('gate/lib/corpus/Certify.olean', 'synthetic private-object bytes');
  write('gate/PREPARED.md', 'synthetic preparation transport fixture');
  write('gate/scope.txt', 'full-project-and-corpus-cli\n');
  write('gate/replay-build-targets.txt', 'EDSL.All\n');
  write('gate/source/CorpusFullReplay.lean', 'import EDSL.All\nimport CorpusCertificateChecks\nimport corpus.Certify\n');
  write('gate/source/CorpusCertificateChecks.lean', 'example : 2 + 2 = 4 := by decide\n');
  write('gate/source/CorpusCLI.lean', 'import corpus.Certify\n');
  write('gate/Audit.lean', 'import EDSL.Audit\n');
  write('gate/check-report.jq', 'true\n');
  write('gate/fresh-target.txt', 'CorpusFullReplay\n');
  write('gate/fresh-receipt-label.txt', 'fresh-project-and-corpus\n');
  manifest('gate/source-before.sha256', ['EDSL/All.lean']);
  manifest('gate/frozen-before.sha256', ['corpus/v1/gcc/final.elf', 'corpus/v1/clang/final.elf']);
  manifest('gate/gate-inputs.sha256', ['gate/source/CorpusFullReplay.lean', 'gate/source/CorpusCertificateChecks.lean',
    'gate/source/CorpusCLI.lean', 'gate/Audit.lean', 'gate/check-report.jq', 'gate/scope.txt',
    'gate/fresh-target.txt', 'gate/fresh-receipt-label.txt']);
  manifest('gate/modules-before.sha256', ['.lake/build/lib/lean/Owned/A.olean', 'gate/lib/corpus/Certify.olean']);
  run('bash', ['scripts/ci/corpus-replay.sh', 'pack']);
  const payload = '.cache/ci-corpus-replay';
  const listing = run('tar', ['-tf', payload+'/inputs.tar']).stdout;
  for (const name of ['prepared/source/CorpusCertificateChecks.lean', 'prepared/source/CorpusFullReplay.lean',
    'prepared/Audit.lean', 'proof-inputs.sha256', 'private/corpus/Certify.olean'])
    assert(listing.includes(payload+'/'+name+'\n'), name+' absent from replay transport');
  fs.chmodSync(executable, 0o644);
  run('tar', ['-xf', payload+'/inputs.tar']);
  assert.equal(fs.statSync(executable).mode & 0o777, 0o755, 'transport lost executable mode');
  // Every mutation below must fail before a build/replay is attempted. Check
  // manifest rejection rather than accepting any incidental missing-tool error.
  function rejectsMutation(file, replacement) {
    const before = fs.readFileSync(path.join(root, file));
    fs.writeFileSync(path.join(root, file), replacement);
    const result = run('bash', ['scripts/ci/corpus-replay.sh', 'shard', '01'], 1);
    assert.match(result.stdout+result.stderr, /differ|FAILED|checksum|WARNING/);
    assert(!fs.existsSync(path.join(root, payload+'/receipts/01/lake.stdout')), 'mutated inputs reached Lake');
    fs.writeFileSync(path.join(root, file), before);
  }
  rejectsMutation(payload+'/roots/KernelReplay01.lean', 'import Owned.A\n');
  rejectsMutation(payload+'/prepared/source/CorpusCertificateChecks.lean', 'example : True := by trivial\n');
  rejectsMutation('EDSL/All.lean', 'import Owned.A\n');
  const extra = write(payload+'/roots/Unexpected.lean', 'example : True := by trivial\n');
  const result = run('bash', ['scripts/ci/corpus-replay.sh', 'shard', '01'], 1);
  assert.match(result.stdout+result.stderr, /differ/);
  assert(!fs.existsSync(path.join(root, payload+'/receipts/01/lake.stdout')));
  fs.unlinkSync(extra);
  console.log('Replay transport: retained named sources, tar modes and pre-build rejection of changed roots/assertions/tracked sources/additions passed. No Lean replay was run.');
} finally { fs.rmSync(root, {recursive:true, force:true}); }
