/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';
const fs = require('node:fs');
const path = require('node:path');
const {execFileSync} = require('node:child_process');

// Deliberately conservative source policy, including comments, strings and
// quoted identifiers. This is a spelling check, not a Lean parser or proof.
// In particular, kernel `decide` and `decide +kernel` are permitted.
const forbidden = /(^|[^A-Za-z0-9_'])(native_decide|ofReduceBool)(?=$|[^A-Za-z0-9_'])/g;
function scanFile(file) {
  if (!fs.lstatSync(file).isFile()) throw new Error('regular Lean source required: '+file);
  const source = fs.readFileSync(file, 'utf8');
  const errors = [];
  source.split('\n').forEach((line, index) => {
    forbidden.lastIndex = 0;
    for (const match of line.matchAll(forbidden))
      errors.push(`${file}:${index+1}: forbidden Lean source identifier ${match[2]}`);
  });
  return errors;
}
function generatedFiles(root, visited = new Set()) {
  if (!fs.existsSync(root)) {
    // A dangling Lean alias is still an attempted proof-source input. Native
    // negative fixtures may legitimately retain dangling non-source links.
    if (root.endsWith('.lean') && fs.lstatSync(root, {throwIfNoEntry:false})?.isSymbolicLink())
      throw new Error('regular Lean source required: '+root);
    return [];
  }
  const info = fs.lstatSync(root);
  if (info.isSymbolicLink()) {
    if (root.endsWith('.lean')) throw new Error('regular Lean source required: '+root);
    // Inspect directory aliases too, so a generated source cannot escape the
    // audit behind an alias. Ignore ordinary non-source artifact links.
    if (!fs.statSync(root).isDirectory()) return [];
  } else if (info.isFile()) {
    if (!root.endsWith('.lean')) throw new Error('Lean source required: '+root);
    return [root];
  } else if (!info.isDirectory()) throw new Error('source directory required: '+root);
  const real = fs.realpathSync(root);
  if (visited.has(real)) return [];
  visited.add(real);
  return fs.readdirSync(root).sort().flatMap(name => {
    const file = path.join(root, name), item = fs.lstatSync(file);
    if (item.isDirectory() || name.endsWith('.lean')) return generatedFiles(file, visited);
    if (item.isSymbolicLink()) {
      // Existing binary-admission controls include file/directory links. A
      // directory may contain final Lean sources; a regular binary cannot.
      if (fs.existsSync(file) && fs.statSync(file).isDirectory()) return generatedFiles(file, visited);
    }
    return [];
  });
}
function main(args) {
  const files = new Set(); let tracked = false, generated = 0;
  while (args.length) {
    const arg = args.shift();
    if (arg === '--tracked') {
      if (tracked) throw new Error('duplicate --tracked');
      tracked = true;
      const names = execFileSync('git', ['ls-files','--cached','-z','--','*.lean'], {encoding:'utf8'}).split('\0').filter(Boolean);
      if (!names.length) throw new Error('empty tracked Lean inventory');
      names.forEach(name => files.add(name));
    } else if (arg === '--generated') {
      if (!args.length) throw new Error('--generated requires a path');
      const names = generatedFiles(args.shift()); generated += names.length;
      names.forEach(name => files.add(name));
    } else if (arg === '--') { args.splice(0).forEach(name => files.add(name)); }
    else throw new Error('usage: audit-lean-source.cjs [--tracked] [--generated PATH] [-- FILE ...]');
  }
  if (!files.size) throw new Error('no Lean inputs');
  let failures = 0;
  for (const file of [...files].sort()) {
    const errors = scanFile(file); failures += errors.length;
    errors.forEach(error => process.stderr.write(error+'\n'));
  }
  if (failures) return 1;
  process.stdout.write(`Lean source audit passed: ${files.size} files (${generated} generated inputs); kernel decide allowed.\n`);
  return 0;
}
if (require.main === module) {
  try { process.exitCode = main(process.argv.slice(2)); }
  catch (error) { process.stderr.write(error.message+'\n'); process.exitCode = 2; }
}
module.exports = {scanFile, generatedFiles, main};
