/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';
const fs = require('fs'), path = require('path'), assert = require('assert/strict');
const crypto = require('crypto');
const hash = f => crypto.createHash('sha256').update(fs.readFileSync(f)).digest('hex');
// Retain exact decimal words rather than rounding them through JavaScript Number.
function exactJSON(line) {
  return JSON.parse(line.replace(/"(?:\\.|[^"\\])*"|[0-9]+/g,
    token => token[0] === '"' ? token : JSON.stringify(token)));
}
function word(value) {
  assert.equal(typeof value, 'string'); assert.match(value, /^(0|[1-9][0-9]*)$/);
  assert(BigInt(value) < (1n << 64n)); return value;
}
function words(values) {
  assert(Array.isArray(values)); assert.equal(values.length, 16);
  return '[' + values.map(word).join(',') + ']';
}
function prepare(out) {
  assert(path.isAbsolute(out)); assert.equal(fs.realpathSync(out), out);
  const fixture = path.join(__dirname, '../fixtures/native/and64-immediate');
  const cases = JSON.parse(fs.readFileSync(fixture + '/cases.json', 'utf8'));
  assert.equal(cases.positives.length, 25); assert.equal(cases.mutants.length, 5);
  const symbols = new Map();
  for (const line of fs.readFileSync(out + '/symbols.txt', 'utf8').split('\n')) {
    const m = /^([0-9a-fA-F]+)\s+\S\s+(edsl_logical_\S+)$/.exec(line);
    if (m) { assert(!symbols.has(m[2])); symbols.set(m[2], BigInt('0x' + m[1])); }
  }
  const start = symbols.get('edsl_logical_section_start'); assert.notEqual(start, undefined);
  const section = fs.readFileSync(out + '/instructions.bin');
  assert.equal(BigInt(section.length), symbols.get('edsl_logical_section_end') - start);
  for (const c of [...cases.positives, ...cases.mutants]) {
    const first = symbols.get('edsl_logical_' + c.n), last = symbols.get('edsl_logical_' + c.n + '_end');
    assert.notEqual(first, undefined); assert.notEqual(last, undefined);
    assert(first >= start && last >= first && last - start <= BigInt(section.length));
    assert.equal(last - first, BigInt(c.b.length));
    assert.deepEqual([...section.subarray(Number(first - start), Number(last - start))], c.b);
  }
  const lines = fs.readFileSync(out + '/measured.jsonl', 'utf8').trim().split('\n');
  assert.equal(lines.length, 100);
  const rawResults = fs.readFileSync(out + '/result.log', 'utf8');
  for (const c of cases.mutants) {
    assert.equal(rawResults.split('\n').filter(l => new RegExp('^REJECTED ' + c.n + ' vector [0-3]$').test(l)).length, 1);
  }
  assert(rawResults.includes('PASS 100 selected observations;'));
  const replay = out + '/replay'; assert(!fs.existsSync(replay)); fs.mkdirSync(replay);
  const shards = [], observations = [], names = new Set();
  for (let i = 0; i < 25; i++) {
    const c = cases.positives[i];
    let source = 'import tests.And64NativeBase\nset_option autoImplicit false\nset_option warningAsError true\nset_option maxHeartbeats 300000\nset_option maxRecDepth 128\nset_option Elab.async false\nnamespace EDSL.Tests.FreshAnd64Native\nopen X86\nopen EDSL.Tests.And64Native\n';
    for (let v = 0; v < 4; v++) {
      const r = exactJSON(lines[4 * i + v]);
      assert.deepEqual(Object.keys(r).sort(), ['name','bytes','pc','next','requestedFlags','effectiveFlags','requestedInstalledGPRs','measuredPostGPRs','measuredPostFlags'].sort());
      assert.equal(r.name, c.n + '_' + v); assert.match(r.name, /^[A-Za-z][A-Za-z0-9_]*$/);
      assert(!names.has(r.name)); names.add(r.name);
      assert.deepEqual(r.bytes.map(x => Number(word(x))), c.b);
      const pc = word(r.pc), next = word(r.next);
      assert.equal(BigInt(pc), symbols.get('edsl_logical_' + c.n));
      assert.equal(BigInt(next), symbols.get('edsl_logical_' + c.n + '_end'));
      word(r.requestedFlags); word(r.effectiveFlags);
      const before = words(r.requestedInstalledGPRs), after = words(r.measuredPostGPRs);
      const flags = word(r.measuredPostFlags), af = (BigInt(flags) & 16n) !== 0n;
      // No result oracle: the expected state is the actual captured CPU state.
      source += 'theorem observed_' + r.name + ' : observe ' + af + ' (entry [' + c.b.join(',') + '] ' + pc + ' ' + before + ' ' + r.effectiveFlags + ') = some (' + after + ',' + flags + ',' + next + ',[]) := by cbv\n';
      source += '#print axioms EDSL.Tests.FreshAnd64Native.observed_' + r.name + '\n';
      observations.push({name:r.name, rawSHA256:crypto.createHash('sha256').update(lines[4*i+v]).digest('hex')});
    }
    source += 'end EDSL.Tests.FreshAnd64Native\n#audit_edsl\n';
    const name = 'FreshAnd64_' + String(i + 1).padStart(2, '0');
    const file = replay + '/' + name + '.lean'; fs.writeFileSync(file, source, {flag:'wx'});
    shards.push({name, file, sha256:hash(file), observations:4});
  }
  const result = {schema:'and64-native-replay-v1', observations:100, mutantsRejected:5,
    inputSHA256:hash(out+'/measured.jsonl'), fixtureSHA256:hash(fixture+'/cases.json'),
    sectionSHA256:hash(out+'/instructions.bin'), symbolsSHA256:hash(out+'/symbols.txt'),
    generatorSHA256:hash(__filename), shards, rows:observations, kernelReplay:false};
  fs.writeFileSync(out + '/REPLAY.json', JSON.stringify(result,null,2)+'\n', {flag:'wx'});
  return result;
}
if (require.main === module) { const [out,...extra] = process.argv.slice(2); assert.equal(extra.length,0); console.log(JSON.stringify(prepare(out))); }
module.exports = {exactJSON, prepare};
