/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs'), os = require('node:os'), path = require('node:path');
const {spawnSync} = require('node:child_process');
const root = fs.mkdtempSync(path.join(os.tmpdir(), 'edsl-source-audit-'));
const scanner = path.resolve(__dirname, '../scripts/audit-lean-source.cjs');
function write(name, text) {
  const file = path.join(root, name); fs.mkdirSync(path.dirname(file), {recursive:true});
  fs.writeFileSync(file, text); return file;
}
function run(args, expected, diagnostic) {
  const result = spawnSync(process.execPath, [scanner, ...args], {encoding:'utf8'});
  assert.equal(result.status, expected, result.stderr);
  if (diagnostic) assert.match(result.stderr, diagnostic);
}
try {
  const good = write('kernel proofs.lean', 'example : 2 + 2 = 4 := by decide\nexample : True := by decide +kernel\n');
  run(['--', good], 0);
  // These inputs specify forbidden behavior independently of the matcher.
  const negatives = [
    ['tactic.lean', 'example : True := by native_decide\n', /native_decide/],
    ['quoted.lean', 'example : True := by «native_decide»\n', /native_decide/],
    ['axiom.lean', 'def unchecked := Lean.ofReduceBool\n', /ofReduceBool/],
    ['qualified.lean', 'def unchecked := Lean.«ofReduceBool»\n', /ofReduceBool/],
    ['macro.lean', 'macro "oracle" : tactic => `(tactic| native_decide)\n', /native_decide/],
    ['comment.lean', '-- native_decide remains forbidden in final source text\n', /native_decide/]
  ];
  for (const [name, text, diagnostic] of negatives) run(['--', write(name, text)], 1, diagnostic);
  // Actual recursive discovery must reach a new generated module with an
  // unfamiliar filename; a fixed allowlist or tracked-only scan would miss it.
  const generated = path.join(root, 'generated');
  write('generated/deep/new module.lean', 'example : True := by native_decide\n');
  run(['--generated', generated], 1, /new module\.lean:1:.*native_decide/);
  fs.unlinkSync(path.join(generated, 'deep/new module.lean'));
  write('generated/deep/checked.lean', 'example : True := by decide +kernel\n');
  run(['--generated', generated], 0);
  // Real native gates retain linked provider objects and negative binary
  // admission fixtures. They must not turn a valid proof-source audit red.
  const binary = write('native.bin', 'owned synthetic bytes');
  fs.symlinkSync(binary, path.join(generated, 'provider.olean'));
  fs.symlinkSync(path.join(root, 'absent.bin'), path.join(generated, 'dangling.bin'));
  fs.symlinkSync(generated, path.join(generated, 'cycle'));
  const empty = path.join(root, 'empty-native-directory'); fs.mkdirSync(empty);
  fs.symlinkSync(empty, path.join(generated, 'rejected-destination'));
  run(['--generated', generated], 0);
  // A directory alias must not hide a forbidden generated proof, and an
  // actual Lean-source alias remains a rejected source shape.
  const aliased = path.join(root, 'aliased-proof'); fs.mkdirSync(aliased);
  fs.writeFileSync(path.join(aliased, 'bad.lean'), 'example : True := by native_decide\n');
  const alias = path.join(generated, 'source-alias'); fs.symlinkSync(aliased, alias);
  run(['--generated', generated], 1, /bad\.lean:1:.*native_decide/);
  fs.unlinkSync(alias);
  const leanAlias = path.join(generated, 'aliased.lean'); fs.symlinkSync(good, leanAlias);
  run(['--generated', generated], 2, /regular Lean source required/);
  fs.unlinkSync(leanAlias);
  fs.symlinkSync(path.join(root, 'missing.lean'), leanAlias);
  run(['--generated', generated], 2, /regular Lean source required/);
  fs.unlinkSync(leanAlias);
  run(['--', path.join(root, 'missing.lean')], 2, /ENOENT/);
  console.log('Lean source scanner: kernel positives, six forbidden-source negatives, recursive generated input, mixed artifacts, alias/cycle and missing-file checks passed.');
} finally { fs.rmSync(root, {recursive:true, force:true}); }
