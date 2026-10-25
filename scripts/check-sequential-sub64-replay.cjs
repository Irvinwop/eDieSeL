/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';

// File/evidence joins only. No arithmetic oracle, generator import, evaluation of
// Lean, compiler invocation, or success-marker writes belong in this checker.
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const { TextDecoder } = require('node:util');

const NS = 'EDSL.Tests.NativeSequentialSub64';
const U64 = (1n << 64n) - 1n;
const THEOREM_AXIOMS = ['propext', 'Quot.sound'];
// EDSL.Audit's generic transitive policy; the finite theorems use only the two
// above. This is not a zero-axiom claim or permission for project axioms.
const TRANSITIVE_AXIOMS = ['propext', 'Quot.sound', 'Classical.choice'];
const windows = [
  ...['r29_', 'r2b_'].flatMap(p => Array.from({ length: 16 }, (_, i) => p + i)),
  ...[0, 3, 4, 7, 8, 11, 12, 15].map(i => 'alias' + i),
  ...['x29_', 'x2b_'].flatMap(p => Array.from({ length: 4 }, (_, i) => p + i)),
  ...Array.from({ length: 16 }, (_, i) => 'imm' + i),
  'rsp_min', 'rsp_neg1', 'r12_one', 'r12_max',
];
const names = windows.flatMap(w => Array.from({ length: 10 }, (_, v) => `observed_${w}_${v}`));
const selected = new Set(names);
const shardFiles = Array.from({ length: 8 }, (_, i) => `NativeSub64_${String(i + 1).padStart(2, '0')}`);
const imports = ['import EDSL.X86.Sequential.MachineChoices', 'import EDSL.Audit'];
const rawOptions = [
  'set_option autoImplicit false', 'set_option warningAsError true',
  'set_option maxHeartbeats 300000', 'set_option maxRecDepth 128',
];
// Fixed, reviewed helper definitions. Exact checking prevents replacing observe
// with a weaker proposition while keeping the 680 names and counts intact.
const helpers = `namespace EDSL.Tests.NativeSequentialSub64
open EDSL.X86
def allRegisters : List Register := [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]
def entry (code : List Byte) (pc : Word) (registers : List Word) (flags : Word) : State where
  registers r := registers.getD (allRegisters.idxOf r) 0
  rip := pc
  flags := flags
  memory := {
    read := fun a => if pc.toNat ≤ a.toNat ∧ a.toNat < pc.toNat + code.length
      then code[a.toNat - pc.toNat]? else none
    executable := fun a => decide (pc.toNat ≤ a.toNat ∧ a.toNat < pc.toNat + code.length)
    writable := fun _ => false }
def observe (initial : State) : Option (List Word × Word × Word × List Sequential.Read) := do
  let observation ← (Sequential.stepWith ⟨true,false,true,false,true,false⟩ initial).toOption
  match observation.result with
  | .next final => return (allRegisters.map final.registers,final.flags,final.rip,observation.reads)
  | _ => none
`;
const preamble = '/- Finite CPU snapshots; independently checked C requests, not universal ISA evidence. -/\n';

class EvidenceError extends Error {
  constructor(code, message) { super(message); this.code = code; }
}
function check(condition, code, detail) {
  if (!condition) throw new EvidenceError(code, detail);
}
function same(a, b) { return JSON.stringify(a) === JSON.stringify(b); }
function keys(value, expected, where) {
  check(value !== null && typeof value === 'object' && !Array.isArray(value) &&
    same(Object.keys(value).sort(), [...expected].sort()), 'JSON_KEYS', where + ': unexpected/missing keys');
}

// JSON.parse accepts repeated keys. Reject them before parsing so a serializer
// cannot give the checker and a different consumer contradictory field values.
function json(text, where) {
  const stack = [];
  const tokens = /"(?:[^"\\\u0000-\u001f]|\\(?:["\\/bfnrt]|u[0-9a-fA-F]{4}))*"|[{}\[\]:,]|[^\s{}\[\]:,"]+/g;
  let previous = '', m;
  while ((m = tokens.exec(text))) {
    const token = m[0];
    if (token === '{') stack.push({ kind: '{', keys: new Set() });
    else if (token === '[') stack.push({ kind: '[' });
    else if (token === '}' || token === ']') stack.pop();
    else if (token.startsWith('"') && stack.at(-1)?.kind === '{' && (previous === '{' || previous === ',')) {
      let key;
      try { key = JSON.parse(token); } catch { throw new EvidenceError('JSON_PARSE', where); }
      check(!stack.at(-1).keys.has(key), 'JSON_DUPLICATE_KEY', where + ': ' + key);
      stack.at(-1).keys.add(key);
    }
    else if (/^[-0-9]/.test(token)) {
      check(/^-?(0|[1-9][0-9]*)$/.test(token) && token !== '-0', 'INTEGER_CANONICAL', where + ': numeric token ' + token);
    }
    previous = token;
  }
  try { return JSON.parse(text); } catch { throw new EvidenceError('JSON_PARSE', where + ': invalid JSON'); }
}
function uint64(value, where) {
  check(typeof value === 'string' && /^(0|[1-9][0-9]*)$/.test(value), 'DECIMAL_CANONICAL', where);
  check(value.length <= 20 && BigInt(value) <= U64, 'UINT64_RANGE', where);
  return value;
}
function integer(value, lo, hi, where) {
  check(Number.isSafeInteger(value) && !Object.is(value, -0) && value >= lo && value <= hi,
    'INTEGER_RANGE', where);
}
function words(values, where) {
  check(Array.isArray(values) && values.length === 16, 'REGISTER_COUNT', where);
  values.forEach((v, i) => uint64(v, `${where}[${i}]`));
  return values;
}
function bytes(values, where) {
  check(Array.isArray(values), 'BYTE_LIST', where);
  values.forEach((v, i) => integer(v, 0, 255, `${where}[${i}]`));
  return values;
}

function parseSnapshots(text) {
  check(text.endsWith('\n') && !text.includes('\r'), 'JSONL_FORMAT', 'observations.jsonl: LF-terminated records required');
  const seen = new Set(), descriptors = new Map();
  const rows = text.slice(0, -1).split('\n').map((line, i) => {
    const where = `observations.jsonl:${i + 1}`;
    const o = json(line, where);
    keys(o, ['name', 'vector', 'operation', 'destination', 'source', 'immediate', 'pc', 'end',
      'bytes', 'before', 'after', 'requestedFlags', 'effectiveFlags', 'afterFlags'], where);
    check(typeof o.name === 'string' && /^[A-Za-z][A-Za-z0-9_]*$/.test(o.name), 'SNAPSHOT_NAME_SYNTAX', where);
    check(windows.includes(o.name), 'SNAPSHOT_NAME_NOT_SELECTED', where + ': ' + o.name);
    integer(o.vector, 0, 9, where + ': vector');
    const name = `observed_${o.name}_${o.vector}`;
    check(!seen.has(name), 'SNAPSHOT_NAME_DUPLICATE', where + ': ' + name);
    seen.add(name);
    const immediate = /^(imm[0-9]+|rsp_min|rsp_neg1|r12_one|r12_max)$/.test(o.name);
    check(o.operation === (immediate ? 'immediate' : 'register'), 'SNAPSHOT_OPERATION', where);
    integer(o.destination, 0, 15, where + ': destination');
    integer(o.source, 0, 15, where + ': source');
    integer(o.immediate, -128, 127, where + ': immediate');
    check(immediate ? o.source === 0 : o.immediate === 0, 'SNAPSHOT_DESCRIPTOR', where);
    for (const field of ['pc', 'end', 'requestedFlags', 'effectiveFlags', 'afterFlags']) uint64(o[field], `${where}: ${field}`);
    words(o.before, where + ': before'); words(o.after, where + ': after'); bytes(o.bytes, where + ': bytes');
    check(o.bytes.length === (immediate ? 4 : 3), 'SNAPSHOT_BYTE_COUNT', where);
    check(BigInt(o.end) - BigInt(o.pc) === BigInt(o.bytes.length), 'SNAPSHOT_PC_SPAN', where);
    const descriptor = [o.operation, o.destination, o.source, o.immediate, o.pc, o.end, o.bytes];
    if (descriptors.has(o.name)) check(same(descriptor, descriptors.get(o.name)), 'SNAPSHOT_DESCRIPTOR_CHANGED', where);
    else descriptors.set(o.name, descriptor);
    return { ...o, theorem: name };
  });
  check(rows.length === 680, 'SNAPSHOT_COUNT', `expected 680 records, got ${rows.length}`);
  check(same(rows.map(o => o.theorem), names), 'SNAPSHOT_NAME_ORDER', 'expected each selected window/vector exactly once in publication order');
  return rows;
}

function parseSource(source, label, expectedNames, kernel) {
  check(source.endsWith('\n') && !source.includes('\r'), 'SOURCE_FORMAT', label + ': LF-terminated source required');
  const lines = source.slice(0, -1).split('\n');
  const options = kernel ? [...rawOptions, 'set_option Elab.async false'] : rawOptions;
  check(same(lines.filter(l => /^\s*import\b/.test(l)), imports), 'SOURCE_IMPORTS', label);
  check(same(lines.filter(l => /^\s*set_option\b/.test(l)), options), 'SOURCE_OPTIONS', label);
  const header = preamble + imports.join('\n') + '\n' + options.join('\n') + '\n' + helpers;
  check(source.startsWith(header), 'SOURCE_HEADER', label + ': helper/production profile differs');
  const rest = source.slice(header.length).split('\n');
  const marker = kernel ? '-- Exact CPU observations, kernel decision under the unchanged fixed limits.' : '-- BEGIN OBSERVATIONS';
  check(rest.shift() === marker, 'SOURCE_MARKER', label);
  const theoremLines = [];
  while (rest[0]?.startsWith('theorem ')) theoremLines.push(rest.shift());
  const seen = new Set();
  const parsed = theoremLines.map((line, i) => {
    const where = `${label}: theorem ${i + 1}`;
    // Parse literals from the actual proposition. Do not render an expected
    // theorem from JSON or call the emitter/generator's render/parse functions.
    const head = /^theorem ([A-Za-z][A-Za-z0-9_]*) : (.*) := by (.*)$/.exec(line);
    check(head, 'THEOREM_SYNTAX', where);
    const [, name, proposition, proof] = head;
    check(selected.has(name), 'THEOREM_NAME_NOT_SELECTED', where + ': ' + name);
    check(!seen.has(name), 'THEOREM_NAME_DUPLICATE', where + ': ' + name); seen.add(name);
    check(proof === (kernel ? 'decide +kernel' : 'decide'), 'THEOREM_PROOF', where + ': ' + proof);
    const m = /^observe \(entry \[([0-9,]+)\] ([0-9]+) \[([0-9,]+)\] ([0-9]+)\) = some \(\[([0-9,]+)\],([0-9]+),([0-9]+),\[\]\)$/.exec(proposition);
    check(m, 'THEOREM_PROPOSITION_SYNTAX', where);
    const byteTokens = m[1].split(',');
    byteTokens.forEach(t => check(/^(0|[1-9][0-9]*)$/.test(t), 'DECIMAL_CANONICAL', where + ': byte'));
    const fields = { bytes: byteTokens.map(Number), pc: m[2], before: m[3].split(','),
      effectiveFlags: m[4], after: m[5].split(','), afterFlags: m[6], end: m[7] };
    bytes(fields.bytes, where); words(fields.before, where); words(fields.after, where);
    for (const f of ['pc', 'effectiveFlags', 'afterFlags', 'end']) uint64(fields[f], where + ': ' + f);
    return { name, line, proposition, fields };
  });
  check(parsed.length === expectedNames.length, 'THEOREM_COUNT', `${label}: expected ${expectedNames.length}, got ${parsed.length}`);
  check(same(parsed.map(t => t.name), expectedNames), 'THEOREM_NAME_ORDER', label + ': wrong shard/name partition');
  const trailer = kernel
    ? [`end ${NS}`, ...expectedNames.map(n => `#print axioms ${NS}.${n}`), '#audit_edsl', '']
    : ['-- END OBSERVATIONS', `end ${NS}`, '#audit_edsl', ''];
  check(same(rest, trailer), 'SOURCE_TRAILER', label + ': expected exact namespace end, axiom commands and one audit; no other commands');
  return parsed;
}

// /usr/bin/time -v output from the supported harness. Unknown diagnostics are
// rejected, not discarded. Neither command strings nor any other text is run.
const timeKeys = new Map([
  ['Command being timed', /^"[^\r\n]+"$/],
  ...['User time (seconds)', 'System time (seconds)'].map(k => [k, /^[0-9]+\.[0-9]+$/]),
  ['Percent of CPU this job got', /^[0-9]+%$/],
  ['Elapsed (wall clock) time (h:mm:ss or m:ss)', /^[0-9]+:[0-9:.]+$/],
  ...['Average shared text size (kbytes)', 'Average unshared data size (kbytes)',
    'Average stack size (kbytes)', 'Average total size (kbytes)',
    'Maximum resident set size (kbytes)', 'Average resident set size (kbytes)',
    'Major (requiring I/O) page faults', 'Minor (reclaiming a frame) page faults',
    'Voluntary context switches', 'Involuntary context switches', 'Swaps',
    'File system inputs', 'File system outputs', 'Socket messages sent',
    'Socket messages received', 'Signals delivered', 'Page size (bytes)', 'Exit status']
    .map(k => [k, /^(0|[1-9][0-9]*)$/]),
]);
function commandProfile(command, expectedSource, where) {
  // GNU time prints argv as a quoted, space-separated line, not shell code.
  // The supported profile therefore requires paths without whitespace. Never
  // evaluate this representation, even to recover quoting or variable values.
  const argv = command.slice(1, -1).split(/\s+/);
  check(!argv.some(a => /^-Ddebug\.skipKernelTC(?:=|$)/.test(a)), 'LOG_KERNEL_DISABLED', where);
  const options = ['-j1', '-DwarningAsError=true', '-DautoImplicit=false', '-DmaxHeartbeats=300000', '-DmaxRecDepth=128'];
  check(same(argv.slice(0, 4), ['timeout', '--signal=TERM', '--kill-after=5s', '120s']) &&
    path.isAbsolute(argv[4] || '') && path.basename(argv[4]) === 'lean' && same(argv.slice(5, 10), options),
    'LOG_COMMAND_PROFILE', where + ': expected the bounded one-thread kernel command profile');
  const rest = argv.slice(10);
  check(rest.length === 1, 'LOG_COMMAND_PROFILE', where + ': unexpected compiler arguments');
  // The public gate checks the actual source in this run directory. Historical
  // logs, same-basename sources and object-producing commands are not a bypass.
  check(rest[0] === expectedSource, 'LOG_SOURCE_PATH',
    where + ': logged source must be the exact current shard: ' + expectedSource);
}
function parseLog(text, label, expectedNames, expectedSource) {
  check(text.endsWith('\n') && !text.includes('\r'), 'LOG_FORMAT', label);
  const expected = new Set(expectedNames.map(n => `${NS}.${n}`));
  const seen = new Set(), timed = new Map();
  let audited = null;
  for (const [i, line] of text.slice(0, -1).split('\n').entries()) {
    if (line === '') continue;
    const where = `${label}:${i + 1}`;
    // Recognize the positive line before looking for a real unapproved-axiom
    // diagnostic: "no unapproved axioms" is explicitly a successful audit.
    const audit = /^Audited ([1-9][0-9]*) EDSL declarations; no unapproved axioms$/.exec(line);
    if (audit) {
      check(audited === null, 'LOG_AUDIT_DUPLICATE', where);
      check(seen.size === 85, 'LOG_AXIOM_MISSING', where + ': audit requires all 85 theorem axiom lines');
      check(timed.size === 0, 'LOG_AUDIT_ORDER', where + ': audit must precede timing output');
      const count = Number(audit[1]);
      check(Number.isSafeInteger(count) && count > 88, 'LOG_AUDIT_SCOPE', where + ': expected imported and local EDSL declarations');
      audited = count; continue;
    }
    const time = /^\t([^\r\n]+): (.*)$/.exec(line);
    // The last ': ' separates GNU time's key from value; its elapsed-time key
    // itself contains colons, but no ': ' sequence. Paths in the command are
    // parsed as argv metadata, never scanned as if they were Lean diagnostics.
    if (time && timeKeys.has(time[1])) {
      check(audited !== null, 'LOG_AUDIT_MISSING', where + ': timing output preceded audit success');
      check(!timed.has(time[1]), 'LOG_TIME_DUPLICATE', where);
      check(timeKeys.get(time[1]).test(time[2]), 'LOG_TIME_VALUE', where);
      if (time[1] === 'Command being timed') commandProfile(time[2], expectedSource, where);
      timed.set(time[1], time[2]); continue;
    }
    check(!/sorryAx|\bsorry\b|\badmit\b/.test(line), 'LOG_SORRY', where);
    check(!/debug\.skipKernelTC|native_decide|ofReduceBool|\bkernel(?: checking| checks?)?(?: is)? disabled\b|\bdisabled kernel\b/i.test(line), 'LOG_KERNEL_DISABLED', where);
    check(!/(?:^|[\s:])(?:error|warning):|\bpanic\b|uncaught exception|deep recursion|maximum recursion|timed? out|Command (?:exited with non-zero status|terminated by signal)/i.test(line), 'LOG_DIAGNOSTIC', where + ': ' + line);
    check(!/\bdepends on unapproved axiom\b/i.test(line), 'LOG_UNAPPROVED_AXIOM', where + ': ' + line);
    const axiom = /^'([A-Za-z0-9_.]+)' depends on axioms: \[([^\]]*)\]$/.exec(line);
    if (axiom) {
      check(audited === null && timed.size === 0, 'LOG_AXIOM_ORDER', where);
      check(expected.has(axiom[1]), 'LOG_AXIOM_NAME', where + ': ' + axiom[1]);
      check(!seen.has(axiom[1]), 'LOG_AXIOM_DUPLICATE', where + ': ' + axiom[1]);
      check(axiom[2] === THEOREM_AXIOMS.join(', '), 'LOG_AXIOM_DEPENDENCIES', where + ': [' + axiom[2] + ']');
      seen.add(axiom[1]); continue;
    }
    throw new EvidenceError('LOG_UNRECOGNIZED', where + ': ' + line);
  }
  check(seen.size === 85 && [...expected].every(n => seen.has(n)), 'LOG_AXIOM_MISSING', label + ': expected all 85 theorem names exactly once');
  check(audited !== null, 'LOG_AUDIT_MISSING', label);
  check(timed.size === timeKeys.size, 'LOG_TIME_MISSING', label + ': incomplete time/status envelope');
  check(timed.get('Exit status') === '0', 'LOG_EXIT_STATUS', label + ': ' + timed.get('Exit status'));
  check(timed.get('Swaps') === '0', 'LOG_SWAPS', label);
  return { sourcePath: expectedSource, theoremAxiomLines: seen.size, auditDeclarations: audited, reportedExitStatus: 0,
    maximumRSSKiB: Number(timed.get('Maximum resident set size (kbytes)')) };
}

function validate(mode, outputDir) {
  check(mode === '--snapshots' || mode === '--kernel', 'CLI_USAGE', 'expected --snapshots or --kernel');
  check(typeof outputDir === 'string' && path.isAbsolute(outputDir) && path.resolve(outputDir) === outputDir,
    'OUTPUT_PATH', 'outputDir must be an absolute normalized path');
  check(fs.realpathSync(outputDir) === outputDir && fs.statSync(outputDir).isDirectory(), 'OUTPUT_PATH', outputDir);
  const files = [];
  function read(relative) {
    const file = path.join(outputDir, relative);
    let st;
    try { st = fs.lstatSync(file); }
    catch (e) { if (e.code === 'ENOENT') throw new EvidenceError('FILE_MISSING', relative); throw e; }
    check(st.isFile() && !st.isSymbolicLink(), 'FILE_TYPE', relative + ': regular file required');
    check(st.size <= 16 * 1024 * 1024, 'FILE_SIZE', relative);
    const buffer = fs.readFileSync(file);
    let source;
    try { source = new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(buffer); }
    catch { throw new EvidenceError('FILE_UTF8', relative); }
    const entry = { file, bytes: buffer.length, sha256: crypto.createHash('sha256').update(buffer).digest('hex') };
    files.push(entry);
    return { ...entry, source };
  }
  const replayDir = path.join(outputDir, 'replay');
  check(fs.realpathSync(replayDir) === replayDir, 'REPLAY_PATH', replayDir);
  check(same(fs.readdirSync(replayDir).filter(f => f.endsWith('.lean')).sort(), shardFiles.map(n => n + '.lean')),
    'SHARD_FILE_SET', 'replay: expected exactly eight selected Lean sources');
  const snapshots = read('observations.jsonl'), raw = read('NativeSequentialSub64.lean');
  const manifestFile = read('replay/REPLAY.json');
  const manifest = json(manifestFile.source, 'replay/REPLAY.json');
  keys(manifest, ['input', 'inputSHA256', 'production', 'proof', 'maxHeartbeats', 'maxRecDepth', 'observations', 'shards'], 'REPLAY.json');
  check(manifest.input === raw.file, 'MANIFEST_INPUT_PATH', 'REPLAY.json input must be this outputDir/NativeSequentialSub64.lean');
  check(manifest.inputSHA256 === raw.sha256, 'MANIFEST_INPUT_HASH', `REPLAY.json: expected ${manifest.inputSHA256}; actual ${raw.sha256}`);
  check(manifest.production === 'Sequential.stepWith (actual decodeAt and executeWith)' && manifest.proof === 'decide +kernel' &&
    manifest.maxHeartbeats === 300000 && manifest.maxRecDepth === 128 && manifest.observations === 680,
    'MANIFEST_PROFILE', 'REPLAY.json: production/proof/limits/observations differ');
  check(Array.isArray(manifest.shards) && manifest.shards.length === 8, 'MANIFEST_SHARD_COUNT', 'REPLAY.json');
  const shards = shardFiles.map((n, i) => {
    const source = read(`replay/${n}.lean`), entry = manifest.shards[i];
    keys(entry, ['file', 'sha256', 'observations'], `REPLAY.json: shard ${i + 1}`);
    check(entry.file === source.file, 'MANIFEST_SHARD_PATH', `REPLAY.json: shard ${i + 1} must refer to ${source.file}`);
    check(entry.sha256 === source.sha256, 'MANIFEST_SHARD_HASH', `REPLAY.json: shard ${i + 1}; expected ${entry.sha256}; actual ${source.sha256}`);
    check(entry.observations === 85, 'MANIFEST_SHARD_PROFILE', `REPLAY.json: shard ${i + 1}`);
    return source;
  });
  const rows = parseSnapshots(snapshots.source);
  const rawTheorems = parseSource(raw.source, 'NativeSequentialSub64.lean', names, false);
  for (let i = 0; i < 680; i++) {
    for (const field of ['bytes', 'pc', 'before', 'effectiveFlags', 'after', 'afterFlags', 'end']) {
      check(same(rawTheorems[i].fields[field], rows[i][field]), 'SNAPSHOT_RAW_BINDING', `${names[i]}: ${field} differs between JSON and raw proposition`);
    }
  }
  const evidence = shards.map((shard, i) => {
    const expectedNames = names.slice(i * 85, (i + 1) * 85);
    const actual = parseSource(shard.source, path.basename(shard.file), expectedNames, true);
    for (let j = 0; j < 85; j++) {
      // Byte-for-byte theorem identity, allowing only the required proof suffix.
      check(actual[j].line === rawTheorems[i * 85 + j].line + ' +kernel', 'SHARD_PROPOSITION', `${shardFiles[i]}: ${expectedNames[j]} differs from raw emitted theorem`);
    }
    return { file: shard.file, sha256: shard.sha256, first: expectedNames[0], last: expectedNames.at(-1), observations: 85 };
  });
  if (mode === '--kernel') {
    check(same(fs.readdirSync(outputDir).filter(f => /^NativeSub64.*\.log$/.test(f)).sort(), shardFiles.map(n => n + '.log')),
      'LOG_FILE_SET', 'expected exactly eight selected shard logs');
    for (let i = 0; i < 8; i++) {
      const log = read(shardFiles[i] + '.log');
      evidence[i].log = { file: log.file, sha256: log.sha256,
        ...parseLog(log.source, path.basename(log.file), names.slice(i * 85, (i + 1) * 85), shards[i].file) };
    }
    check(new Set(evidence.map(e => e.log.auditDeclarations)).size === 1, 'LOG_AUDIT_INCONSISTENT', 'transitive audit scope differs across standalone shards');
  }
  for (const file of files) {
    const stat = fs.lstatSync(file.file);
    check(stat.isFile() && !stat.isSymbolicLink() &&
      crypto.createHash('sha256').update(fs.readFileSync(file.file)).digest('hex') === file.sha256,
      'FILE_CHANGED', file.file + ': changed during evidence validation');
  }
  return {
    status: mode === '--kernel' ? 'kernel-evidence-pass' : 'snapshot-binding-pass',
    evidenceOnly: true, kernelOrNativeExecuted: false, outputDir, observations: 680, standaloneShards: 8,
    boundFields: ['bytes', 'pc', 'before[16]', 'effectiveFlags', 'after[16]', 'afterFlags', 'end', 'empty model operand reads'],
    metadata: 'name/vector select the theorem; requestedFlags and request descriptors are validated metadata, not additional Lean premises',
    sourceProfile: { imports, options: [...rawOptions, 'set_option Elab.async false'], proof: 'decide +kernel',
      theoremAxioms: THEOREM_AXIOMS, transitiveAuditAllowedAxioms: TRANSITIVE_AXIOMS },
    manifestAssociations: 'exact current raw input path/hash and all eight current shard paths/hashes; logs name their exact current shard sources',
    executionAuthority: 'The harness must compile these validated current sources and enforce actual process success. This checker validates files and does not execute or authenticate a compiler run.',
    shards: evidence, files,
  };
}

if (require.main === module) {
  try {
    check(process.argv.length === 4, 'CLI_USAGE', 'usage: node scripts/check-sequential-sub64-replay.cjs --snapshots|--kernel ABSOLUTE_OUTPUT_DIR');
    process.stdout.write(JSON.stringify(validate(process.argv[2], process.argv[3]), null, 2) + '\n');
  } catch (e) {
    process.stderr.write(JSON.stringify({ status: 'fail', code: e.code || 'IO_ERROR', reason: e.message }) + '\n');
    process.exitCode = 1;
  }
}
module.exports = { validate, EvidenceError };
