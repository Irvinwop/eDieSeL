/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';

// Black-box filesystem regressions. The fixture must be actual current public
// capture/replay output, not statements constructed by the replay renderer.
// Copies rebase only manifest paths and the timed command's exact last source
// path token. This test-path metadata rebase does not constitute a fresh replay;
// captured fields, theorem bytes, diagnostics and axiom lines are unchanged.
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const assert = require('node:assert/strict');
const { spawnSync } = require('node:child_process');
assert.equal(process.argv.length, 4, 'usage: node tests/check-sequential-sub64-replay.cjs ACTUAL_OUTPUT_DIR SCRATCH_PARENT');
const [fixture, scratchParent] = process.argv.slice(2);
assert(path.isAbsolute(fixture) && path.isAbsolute(scratchParent));
assert.equal(fs.realpathSync(fixture), fixture, 'fixture must be its normalized actual path');
assert.equal(fs.realpathSync(scratchParent), scratchParent, 'scratch parent must be its normalized actual path');
const checker = path.resolve(__dirname, '../scripts/check-sequential-sub64-replay.cjs');
const work = fs.mkdtempSync(path.join(scratchParent, 'binding-controls-'));
const digest = bytes => crypto.createHash('sha256').update(bytes).digest('hex');
const testedSources = [checker, __filename].map(file => ({ file, sha256: digest(fs.readFileSync(file)) }));
const shardNames = Array.from({ length: 8 }, (_, i) => `NativeSub64_${String(i + 1).padStart(2, '0')}`);
const requiredFiles = ['observations.jsonl', 'NativeSequentialSub64.lean', 'replay/REPLAY.json',
  ...shardNames.flatMap(n => ['replay/' + n + '.lean', n + '.log'])];
const fixtureHashes = requiredFiles.map(file => ({ file: path.join(fixture, file), sha256: digest(fs.readFileSync(path.join(fixture, file))) }));
function edit(root, file, transform) {
  const target = path.join(root, file);
  fs.writeFileSync(target, transform(fs.readFileSync(target, 'utf8')));
}
function manifest(root, transform) {
  edit(root, 'replay/REPLAY.json', s => JSON.stringify(transform(JSON.parse(s)), null, 2) + '\n');
}
function stamp(root, file) {
  manifest(root, m => {
    const hash = digest(fs.readFileSync(path.join(root, file)));
    if (file === 'NativeSequentialSub64.lean') m.inputSHA256 = hash;
    else m.shards.find(e => e.file === path.join(root, file)).sha256 = hash;
    return m;
  });
}
function source(root, file, transform, rehash = true) {
  edit(root, file, transform);
  if (rehash) stamp(root, file);
}
function snapshots(root, transform) {
  edit(root, 'observations.jsonl', s => transform(s.trimEnd().split('\n').map(JSON.parse)).map(o => JSON.stringify(o)).join('\n') + '\n');
}
function firstTheorem(s, transform) { return s.replace(/^theorem .+$/m, transform); }
function firstSnapshot(root, transform) { snapshots(root, rows => { transform(rows[0]); return rows; }); }
function firstWindow(root, transform) { snapshots(root, rows => { rows.slice(0, 10).forEach(transform); return rows; }); }
function increment(value) { return String(BigInt(value) + 1n); }
const raw = 'NativeSequentialSub64.lean', shard = 'replay/NativeSub64_01.lean', log = 'NativeSub64_01.log';
function logEdit(root, transform) { edit(root, log, transform); }
function axiomEdit(root, transform) { logEdit(root, s => s.replace(/^'.+' depends on axioms: \[[^\]]*\]$/m, transform)); }
function auditEdit(root, transform) { logEdit(root, s => s.replace(/^Audited .+$/m, transform)); }
function run(mode, root) {
  const child = spawnSync(process.execPath, [checker, mode, root], { encoding: 'utf8', timeout: 20000, maxBuffer: 1024 * 1024 });
  assert.ifError(child.error);
  assert.equal(child.signal, null, 'checker must exit normally');
  const output = child.status === 0 ? child.stdout : child.stderr;
  let parsed;
  try { parsed = JSON.parse(output); } catch { throw new Error('checker did not return structured output: ' + output); }
  return { exitStatus: child.status, ...parsed };
}
function commandSource(text, from, to) {
  const lines = text.split('\n');
  const indices = lines.map((line, i) => line.startsWith('\tCommand being timed: ') ? i : -1).filter(i => i >= 0);
  assert.equal(indices.length, 1, 'exactly one timed command is required for test-path metadata rebase');
  const i = indices[0], suffix = ' ' + from + '"';
  assert(lines[i].endsWith(suffix), 'timed command must end with the exact original source path');
  lines[i] = lines[i].slice(0, -suffix.length) + ' ' + to + '"';
  return lines.join('\n');
}
function copyFixture(index) {
  const root = path.join(work, 'case-' + String(index).padStart(3, '0'));
  fs.mkdirSync(path.join(root, 'replay'), { recursive: true });
  for (const file of requiredFiles) fs.copyFileSync(path.join(fixture, file), path.join(root, file));
  manifest(root, m => {
    m.input = path.join(root, raw);
    m.shards.forEach((e, i) => { e.file = path.join(root, 'replay', shardNames[i] + '.lean'); });
    return m;
  });
  // Rebase test-path metadata only, after validating the untouched original.
  // Never rewrite diagnostics/axiom lines or source/observation bytes here.
  for (const n of shardNames) {
    edit(root, n + '.log', text => commandSource(text,
      path.join(fixture, 'replay', n + '.lean'), path.join(root, 'replay', n + '.lean')));
  }
  return root;
}
const cases = [];
function reject(name, code, reason, mutate, mode = '--snapshots') { cases.push({ name, code, reason, mutate, mode }); }
function rejectKernel(name, code, reason, mutate) { reject(name, code, reason, mutate, '--kernel'); }

reject('captured output register changed', 'SNAPSHOT_RAW_BINDING', /observed_r29_0_0: after differs/, root => firstSnapshot(root, o => { o.after[15] = increment(o.after[15]); }));
reject('captured input register changed', 'SNAPSHOT_RAW_BINDING', /observed_r29_0_0: before differs/, root => firstSnapshot(root, o => { o.before[15] = increment(o.before[15]); }));
reject('captured effective flags changed', 'SNAPSHOT_RAW_BINDING', /effectiveFlags differs/, root => firstSnapshot(root, o => { o.effectiveFlags = increment(o.effectiveFlags); }));
reject('captured output flags changed', 'SNAPSHOT_RAW_BINDING', /afterFlags differs/, root => firstSnapshot(root, o => { o.afterFlags = increment(o.afterFlags); }));
reject('serialized instruction bytes changed consistently for a window', 'SNAPSHOT_RAW_BINDING', /bytes differs/, root => firstWindow(root, o => { o.bytes[2] ^= 1; }));
reject('serialized PC and continuation shifted together', 'SNAPSHOT_RAW_BINDING', /pc differs/, root => firstWindow(root, o => { o.pc = increment(o.pc); o.end = increment(o.end); }));
reject('serialized continuation has impossible byte span', 'SNAPSHOT_PC_SPAN', /observations.jsonl:1/, root => firstSnapshot(root, o => { o.end = increment(o.end); }));
reject('raw continuation changed with an updated manifest', 'SNAPSHOT_RAW_BINDING', /end differs/, root => source(root, raw, s => firstTheorem(s, line => line.replace(/,([0-9]+),\[\]\) :=/, (_, end) => ',' + increment(end) + ',[]) :='))));
reject('raw output flags changed with an updated manifest', 'SNAPSHOT_RAW_BINDING', /afterFlags differs/, root => source(root, raw, s => firstTheorem(s, line => line.replace(/,([0-9]+),([0-9]+),\[\]\) :=/, (_, flags, end) => ',' + increment(flags) + ',' + end + ',[]) :='))));
reject('raw model footprint weakened', 'THEOREM_PROPOSITION_SYNTAX', /NativeSequentialSub64.lean: theorem 1/, root => source(root, raw, s => firstTheorem(s, line => line.replace(',[]) :=', ',[0]) :='))));

reject('noncanonical leading zero in uint64', 'DECIMAL_CANONICAL', /before\[15\]/, root => firstSnapshot(root, o => { o.before[15] = '0' + o.before[15]; }));
reject('hexadecimal uint64 serialization', 'DECIMAL_CANONICAL', /afterFlags/, root => firstSnapshot(root, o => { o.afterFlags = '0x202'; }));
reject('exponent uint64 serialization', 'DECIMAL_CANONICAL', /afterFlags/, root => firstSnapshot(root, o => { o.afterFlags = '1e3'; }));
reject('uint64 serialized as a JSON number', 'DECIMAL_CANONICAL', /before\[15\]/, root => firstSnapshot(root, o => { o.before[15] = Number(o.before[15]); }));
reject('uint64 overflow', 'UINT64_RANGE', /before\[15\]/, root => firstSnapshot(root, o => { o.before[15] = '18446744073709551616'; }));
reject('negative uint64', 'DECIMAL_CANONICAL', /afterFlags/, root => firstSnapshot(root, o => { o.afterFlags = '-1'; }));
reject('requested flags metadata also range checked', 'UINT64_RANGE', /requestedFlags/, root => firstSnapshot(root, o => { o.requestedFlags = '18446744073709551616'; }));
reject('missing captured register', 'REGISTER_COUNT', /before/, root => firstSnapshot(root, o => { o.before.pop(); }));
reject('byte exceeds uint8 range', 'INTEGER_RANGE', /bytes\[0\]/, root => firstSnapshot(root, o => { o.bytes[0] = 256; }));
reject('fractional byte', 'INTEGER_CANONICAL', /numeric token 72\.5/, root => firstSnapshot(root, o => { o.bytes[0] = 72.5; }));
reject('exponent byte serialization', 'INTEGER_CANONICAL', /numeric token [0-9]+e0/, root => edit(root, 'observations.jsonl', s => s.replace(/"bytes":\[([0-9]+)/, (_, byte) => '"bytes":[' + byte + 'e0')));
reject('negative zero metadata serialization', 'INTEGER_CANONICAL', /numeric token -0/, root => edit(root, 'observations.jsonl', s => s.replace('"vector":0', '"vector":-0')));
reject('invalid architectural register metadata', 'INTEGER_RANGE', /destination/, root => firstSnapshot(root, o => { o.destination = 16; }));
reject('request descriptor changes between vectors', 'SNAPSHOT_DESCRIPTOR_CHANGED', /observations.jsonl:2/, root => firstSnapshot(root, o => { o.source = (o.source + 1) % 16; }));
reject('operation metadata does not match selected case profile', 'SNAPSHOT_OPERATION', /observations.jsonl:1/, root => firstSnapshot(root, o => { o.operation = 'immediate'; }));
reject('duplicate JSON property cannot hide an alteration', 'JSON_DUPLICATE_KEY', /afterFlags/, root => edit(root, 'observations.jsonl', s => s.replace('{', '{"afterFlags":"1",')));
reject('missing JSON observation', 'SNAPSHOT_COUNT', /679/, root => snapshots(root, rows => rows.slice(1)));
reject('duplicate JSON observation with count preserved', 'SNAPSHOT_NAME_DUPLICATE', /observed_r29_0_0/, root => snapshots(root, rows => { rows[1] = rows[0]; return rows; }));
reject('mutant JSON observation', 'SNAPSHOT_NAME_NOT_SELECTED', /mutant_source/, root => firstSnapshot(root, o => { o.name = 'mutant_source'; }));
reject('malformed JSON name', 'SNAPSHOT_NAME_SYNTAX', /observations.jsonl:1/, root => firstSnapshot(root, o => { o.name = 'r29_0.bad'; }));

reject('missing raw theorem', 'THEOREM_COUNT', /679/, root => source(root, raw, s => s.replace(/^theorem .+\n/m, '')));
reject('duplicate raw theorem with count preserved', 'THEOREM_NAME_DUPLICATE', /observed_r29_0_0/, root => source(root, raw, s => {
  const lines = s.match(/^theorem .+$/gm); return s.replace(lines[1], lines[0]);
}));
reject('mutant theorem name', 'THEOREM_NAME_NOT_SELECTED', /observed_mutant_source_0/, root => source(root, raw, s => firstTheorem(s, l => l.replace(/theorem [^ ]+/, 'theorem observed_mutant_source_0'))));
reject('raw theorem order changed', 'THEOREM_NAME_ORDER', /wrong shard\/name partition/, root => source(root, raw, s => {
  const lines = s.match(/^theorem .+$/gm); return s.replace(lines[0] + '\n' + lines[1], lines[1] + '\n' + lines[0]);
}));
reject('shard proposition changed with a matching source hash', 'SHARD_PROPOSITION', /observed_r29_0_0/, root => source(root, shard, s => firstTheorem(s, line => line.replace(/,([0-9]+),([0-9]+),\[\]\) :=/, (_, flags, end) => ',' + increment(flags) + ',' + end + ',[]) :='))));
reject('kernel proof suffix omitted', 'THEOREM_PROOF', /decide$/, root => source(root, shard, s => firstTheorem(s, l => l.replace(' +kernel', ''))));
reject('nonkernel reduction substituted', 'THEOREM_PROOF', /decide \+native/, root => source(root, shard, s => firstTheorem(s, l => l.replace('+kernel', '+native'))));
reject('shard replaced with a selected theorem from the next shard', 'THEOREM_NAME_ORDER', /wrong shard\/name partition/, root => source(root, shard, s => firstTheorem(s, l => l.replace('observed_r29_0_0', 'observed_r29_8_5'))));
reject('forbidden kernel option in source', 'SOURCE_OPTIONS', /NativeSub64_01.lean/, root => source(root, shard, s => s.replace('set_option autoImplicit false', 'set_option debug.skipKernelTC true\nset_option autoImplicit false')));
reject('asynchronous elaboration restored', 'SOURCE_OPTIONS', /NativeSub64_01.lean/, root => source(root, shard, s => s.replace('set_option Elab.async false', 'set_option Elab.async true')));
reject('asynchronous elaboration control missing', 'SOURCE_OPTIONS', /NativeSub64_01.lean/, root => source(root, shard, s => s.replace('set_option Elab.async false\n', '')));
reject('proof budget silently changed', 'SOURCE_OPTIONS', /NativeSub64_01.lean/, root => source(root, shard, s => s.replace('maxHeartbeats 300000', 'maxHeartbeats 300001')));
reject('extra import', 'SOURCE_IMPORTS', /NativeSub64_01.lean/, root => source(root, shard, s => s.replace('import EDSL.Audit', 'import EDSL.Audit\nimport Lean')));
reject('production observer changed', 'SOURCE_HEADER', /helper\/production profile differs/, root => source(root, shard, s => s.replace('Sequential.stepWith', 'Sequential.step')));
reject('register frame helper weakened', 'SOURCE_HEADER', /helper\/production profile differs/, root => source(root, raw, s => s.replace(',.r15]', ']')));
reject('axiom print target altered', 'SOURCE_TRAILER', /axiom commands/, root => source(root, shard, s => s.replace('#print axioms EDSL.Tests.NativeSequentialSub64.observed_r29_0_0', '#print axioms EDSL.Tests.NativeSequentialSub64.observed_r29_8_5')));
reject('source audit command omitted', 'SOURCE_TRAILER', /one audit/, root => source(root, shard, s => s.replace('#audit_edsl\n', '')));

reject('raw source bytes changed without restamping', 'MANIFEST_INPUT_HASH', /actual [a-f0-9]{64}/, root => source(root, raw, s => s + '\n', false));
reject('shard source bytes changed without restamping', 'MANIFEST_SHARD_HASH', /shard 1; expected/, root => source(root, shard, s => s + '\n', false));
reject('manifest raw hash altered', 'MANIFEST_INPUT_HASH', /expected 0{64}/, root => manifest(root, m => { m.inputSHA256 = '0'.repeat(64); return m; }));
reject('manifest shard hash altered', 'MANIFEST_SHARD_HASH', /expected 0{64}/, root => manifest(root, m => { m.shards[0].sha256 = '0'.repeat(64); return m; }));
reject('manifest input references a different file', 'MANIFEST_INPUT_PATH', /this outputDir/, root => manifest(root, m => { m.input += '.other'; return m; }));
reject('manifest shard references a different current source', 'MANIFEST_SHARD_PATH', /shard 1 must refer/, root => manifest(root, m => { m.shards[0].file = m.shards[1].file; return m; }));
reject('manifest shard order swapped', 'MANIFEST_SHARD_PATH', /shard 1 must refer/, root => manifest(root, m => { [m.shards[0], m.shards[1]] = [m.shards[1], m.shards[0]]; return m; }));
reject('manifest selected shard missing', 'MANIFEST_SHARD_COUNT', /REPLAY.json/, root => manifest(root, m => { m.shards.pop(); return m; }));
reject('manifest profile changed', 'MANIFEST_PROFILE', /production\/proof\/limits/, root => manifest(root, m => { m.proof = 'decide'; return m; }));
reject('extra Lean source in replay directory', 'SHARD_FILE_SET', /exactly eight/, root => fs.writeFileSync(path.join(root, 'replay/NativeSub64_09.lean'), fs.readFileSync(path.join(root, shard))));
reject('source file redirected by symlink', 'FILE_TYPE', /regular file required/, root => { fs.unlinkSync(path.join(root, raw)); fs.symlinkSync(path.join(fixture, raw), path.join(root, raw)); });

rejectKernel('post-replay mode also binds captured flags', 'SNAPSHOT_RAW_BINDING', /afterFlags differs/, root => firstSnapshot(root, o => { o.afterFlags = increment(o.afterFlags); }));
rejectKernel('missing shard log', 'LOG_FILE_SET', /exactly eight/, root => fs.unlinkSync(path.join(root, log)));
rejectKernel('extra shard log', 'LOG_FILE_SET', /exactly eight/, root => fs.copyFileSync(path.join(root, log), path.join(root, 'NativeSub64_09.log')));
rejectKernel('wrong selected log copied to first shard', 'LOG_AXIOM_NAME', /observed_r29_8_5/, root => fs.copyFileSync(path.join(root, 'NativeSub64_02.log'), path.join(root, log)));
rejectKernel('missing per-theorem axiom line', 'LOG_AXIOM_MISSING', /all 85/, root => logEdit(root, s => s.replace(/^'.+' depends on axioms: .+\n/m, '')));
rejectKernel('duplicate per-theorem axiom line', 'LOG_AXIOM_DUPLICATE', /observed_r29_0_0/, root => axiomEdit(root, l => l + '\n' + l));
rejectKernel('wrong axiom theorem name', 'LOG_AXIOM_NAME', /observed_mutant_source_0/, root => axiomEdit(root, l => l.replace('observed_r29_0_0', 'observed_mutant_source_0')));
rejectKernel('missing theorem axiom dependency', 'LOG_AXIOM_DEPENDENCIES', /\[propext\]/, root => axiomEdit(root, l => l.replace(', Quot.sound', '')));
rejectKernel('unknown theorem axiom dependency', 'LOG_AXIOM_DEPENDENCIES', /EDSL.unchecked/, root => axiomEdit(root, l => l.replace('Quot.sound', 'EDSL.unchecked')));
rejectKernel('extra generic standard axiom in finite theorem', 'LOG_AXIOM_DEPENDENCIES', /Classical.choice/, root => axiomEdit(root, l => l.replace('Quot.sound', 'Quot.sound, Classical.choice')));
rejectKernel('sorryAx in theorem dependency', 'LOG_SORRY', /NativeSub64_01.log:1/, root => axiomEdit(root, l => l.replace('Quot.sound', 'sorryAx')));
rejectKernel('missing transitive audit success', 'LOG_AUDIT_MISSING', /preceded audit success/, root => auditEdit(root, () => ''));
rejectKernel('duplicate transitive audit success', 'LOG_AUDIT_DUPLICATE', /NativeSub64_01.log:/, root => auditEdit(root, l => l + '\n' + l));
rejectKernel('audit scope reduced to local-looking count', 'LOG_AUDIT_SCOPE', /imported and local/, root => auditEdit(root, l => l.replace(/[0-9]+/, '1')));
rejectKernel('actual Lean error after otherwise complete success output', 'LOG_DIAGNOSTIC', /error: synthetic control/, root => logEdit(root, s => s + 'NativeSub64_01.lean:1:0: error: synthetic control\n'));
rejectKernel('actual Lean warning', 'LOG_DIAGNOSTIC', /warning: synthetic control/, root => logEdit(root, s => s + 'NativeSub64_01.lean:1:0: warning: synthetic control\n'));
rejectKernel('actual unapproved-axiom diagnostic', 'LOG_UNAPPROVED_AXIOM', /depends on unapproved axiom/, root => logEdit(root, s => s + 'EDSL.synthetic depends on unapproved axiom EDSL.unchecked\n'));
rejectKernel('disabled kernel diagnostic', 'LOG_KERNEL_DISABLED', /NativeSub64_01.log:/, root => logEdit(root, s => s + 'set_option debug.skipKernelTC true\n'));
rejectKernel('disabled kernel in the logged command', 'LOG_KERNEL_DISABLED', /NativeSub64_01.log:/, root => logEdit(root, s => s.replace(' -j1 ', ' -Ddebug.skipKernelTC=true -j1 ')));
rejectKernel('logged compiler thread profile changed', 'LOG_COMMAND_PROFILE', /one-thread kernel command/, root => logEdit(root, s => s.replace(' -j1 ', ' -j2 ')));
rejectKernel('logged compiler warning policy changed', 'LOG_COMMAND_PROFILE', /one-thread kernel command/, root => logEdit(root, s => s.replace('-DwarningAsError=true', '-DwarningAsError=false')));
rejectKernel('logged compiler adds a weakening option', 'LOG_COMMAND_PROFILE', /unexpected compiler arguments/, root => logEdit(root, s => s.replace('-DmaxRecDepth=128 ', '-DmaxRecDepth=128 -DautoImplicit=true ')));
rejectKernel('foreign nonexistent same-basename logged source', 'LOG_SOURCE_PATH', /exact current shard/, root => {
  const foreign = path.join(root, 'nonexistent', 'NativeSub64_01.lean');
  assert(!fs.existsSync(foreign), 'negative path must not exist');
  logEdit(root, text => commandSource(text, path.join(root, shard), foreign));
});
rejectKernel('different current shard named in first log', 'LOG_SOURCE_PATH', /exact current shard/, root => {
  const other = path.join(root, 'replay/NativeSub64_02.lean');
  assert(fs.statSync(other).isFile(), 'control uses an actual different selected shard');
  logEdit(root, text => commandSource(text, path.join(root, shard), other));
});
rejectKernel('historical standalone source basename rejected', 'LOG_SOURCE_PATH', /exact current shard/, root => {
  logEdit(root, text => commandSource(text, path.join(root, shard), path.join(root, 'NativeSub64.lean')));
});
rejectKernel('missing logged compiler status', 'LOG_TIME_MISSING', /incomplete time\/status/, root => logEdit(root, s => s.replace(/^\tExit status: .+\n/m, '')));
rejectKernel('logged nonzero compiler status', 'LOG_EXIT_STATUS', /: 1$/, root => logEdit(root, s => s.replace(/^\tExit status: .+$/m, '\tExit status: 1')));
rejectKernel('unrecognized output cannot conceal diagnostics', 'LOG_UNRECOGNIZED', /synthetic unexpected output/, root => logEdit(root, s => s + 'synthetic unexpected output\n'));

const results = [];
try {
  // Refuse an invalid or historical original before rebasing any copied paths.
  const originalBaseline = ['--snapshots', '--kernel'].map(mode => {
    const r = run(mode, fixture); assert.equal(r.exitStatus, 0, 'untouched original failed: ' + JSON.stringify(r));
    return { mode, status: r.status, files: r.files };
  });
  const start = copyFixture(0);
  const positive = ['--snapshots', '--kernel'].map(mode => {
    const r = run(mode, start); assert.equal(r.exitStatus, 0, JSON.stringify(r));
    return { mode, status: r.status, files: r.files };
  });
  // Before replay the source gate must not pretend to require/runtime-check logs.
  for (const n of shardNames) fs.unlinkSync(path.join(start, n + '.log'));
  const beforeReplay = run('--snapshots', start);
  assert.equal(beforeReplay.exitStatus, 0, JSON.stringify(beforeReplay));
  fs.rmSync(start, { recursive: true, force: true });
  for (const [i, test] of cases.entries()) {
    const root = copyFixture(i + 1);
    try {
      const baseline = run(test.mode, root);
      assert.equal(baseline.exitStatus, 0, test.name + ': unmodified baseline failed: ' + JSON.stringify(baseline));
      test.mutate(root);
      const failure = run(test.mode, root);
      assert.equal(failure.exitStatus, 1, test.name + ': alteration unexpectedly passed');
      assert.equal(failure.code, test.code, test.name + ': wrong gate: ' + JSON.stringify(failure));
      assert.match(failure.reason, test.reason, test.name + ': wrong reason');
      assert(!fs.existsSync(path.join(root, 'kernel-proved.txt')), 'checker must never create a kernel success marker');
      results.push({ name: test.name, mode: test.mode, baseline: baseline.status,
        expectedCode: test.code, actualCode: failure.code, reason: failure.reason, status: 'pass' });
    } finally { fs.rmSync(root, { recursive: true, force: true }); }
  }
  for (const entry of fixtureHashes) assert.equal(digest(fs.readFileSync(entry.file)), entry.sha256, 'fixture changed');
  for (const entry of testedSources) assert.equal(digest(fs.readFileSync(entry.file)), entry.sha256, 'tested source changed during the controls');
  process.stdout.write(JSON.stringify({ status: 'pass', node: process.version,
    method: 'untouched actual current public output validated first; fresh passing filesystem baseline before every mutation; no generator used to make expectations',
    testPathMetadataRebase: 'copied manifest input/shard paths and each timed command last source token only; captured fields, theorems, diagnostics and axiom lines unchanged; no fresh replay claim',
    originalBaseline, positive, testedSources, snapshotModeWithoutLogs: beforeReplay.status, originalsUnchanged: true,
    controls: results }, null, 2) + '\n');
} catch (e) {
  process.stderr.write(JSON.stringify({ status: 'fail', completedControls: results, error: e.stack }) + '\n');
  process.exitCode = 1;
} finally { fs.rmSync(work, { recursive: true, force: true }); }
