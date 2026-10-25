/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';
const fs = require('node:fs'), path = require('node:path'), assert = require('node:assert/strict');
const crypto = require('node:crypto'), {execFileSync} = require('node:child_process');
const sourceRoot = path.resolve(__dirname, '..');
const fixture = 'fixtures/native/displaced-data/';
const namespace = 'EDSL.Tests.DisplacedDataNative';
const limit = 1n << 64n;
// The inventory fixes identities and operand widths, not observation results.
const profiles = [
  ['load32',4], ['store32',4], ['load64',8], ['store64',8],
  ['add32',4], ['add64',8], ['cmp8imm',1], ['cmp8left',1], ['cmp32',4],
  ['cmp8right',1], ['cmp8rex',1], ['movzx',1], ['movzxlong',1],
  ['r13zero',8], ['rspzero',8], ['rexindex',8], ['noindex',8],
  ['scale0',8], ['scale1',8], ['scale3',8]
];
const mutants = [
  {name:'mutant_width',bytes:[139,71,8]}, {name:'mutant_disp',bytes:[72,139,71,24]},
  {name:'mutant_bank',bytes:[76,139,71,8]}, {name:'mutant_scale',bytes:[79,139,100,101,128]}
];
const replayProfile = {
  target:'Linux x86-64', productionStep:'EDSL.X86.Sequential.step',
  base:'tests.DisplacedDataNativeBase', proof:'cbv',
  warningAsError:true, autoImplicit:false, maxHeartbeats:300000, maxRecDepth:128,
  threads:1, memoryMax:3221225472, memorySwapMax:0, cpuQuota:'100%', tasksMax:64,
  innerSeconds:120, unitSeconds:130,
  rip:'4096 + exact linked instruction length; relocated, not CPU sampled',
  memory:'8 leading bytes plus operand width; unchanged public initial/view permissions',
  scope:'Finite owned observations; no CPU/OS universal refinement or corpus credit'
};
const header = '/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/\n' +
  'import tests.DisplacedDataNativeBase\nimport EDSL.X86.Sequential.Machine\n' +
  'import EDSL.X86.Sequential.DisplacedData\n' +
  'set_option autoImplicit false\nset_option warningAsError true\n' +
  'set_option maxHeartbeats 300000\nset_option maxRecDepth 128\n' +
  'set_option Elab.async false\nnamespace ' + namespace + '\n';
const trailer = 'end ' + namespace + '\n#audit_edsl\n';
const digest = bytes => crypto.createHash('sha256').update(bytes).digest('hex');
function read(file) {
  assert(fs.lstatSync(file).isFile(), 'regular file required: ' + file);
  return fs.readFileSync(file);
}
const hash = file => digest(read(file));
function outputDirectory(out) {
  assert.equal(typeof out, 'string', 'absolute output directory required');
  assert(path.isAbsolute(out)); assert.equal(fs.realpathSync(out), out);
}
function word(text) {
  assert.match(text, /^(0|[1-9][0-9]{0,19})$/, 'canonical unsigned decimal required');
  const value = BigInt(text); assert(value < limit, 'uint64 overflow'); return value;
}
function probes() {
  const selected = JSON.parse(read(path.join(sourceRoot, fixture, 'PROBES.json')));
  assert.equal(selected.length, 20);
  for (let i = 0; i < selected.length; i++) {
    const p = selected[i]; assert.deepEqual(Object.keys(p).sort(), ['bytes','name']);
    assert.equal(p.name, profiles[i][0]); assert(Array.isArray(p.bytes));
    assert(p.bytes.length > 0 && p.bytes.length <= 15);
    for (const b of p.bytes) assert(Number.isInteger(b) && b >= 0 && b <= 255);
  }
  return selected;
}
function parseCapture(text, selected) {
  assert(text.endsWith('\n') && !text.includes('\r'), 'LF-terminated capture required');
  const lines = text.slice(0,-1).split('\n');
  assert.equal(lines.shift(), 'EDSL-DISP8-V1', 'capture version differs');
  assert.equal(lines.pop(), 'END 80 4', 'capture footer differs');
  assert.equal(lines.length, 80, 'exactly 80 observations required');
  const seen = new Set();
  const rows = lines.map((raw, i) => {
    const f = raw.split(' '); assert.equal(f.length, 45, 'observation field count differs');
    assert.equal(f[0], 'OBS');
    const p = selected.find(p => p.name === f[1]); assert(p, 'unselected probe identity');
    assert.match(f[2], /^[01]$/, 'invalid seed'); assert.match(f[3], /^[01]$/, 'invalid profile');
    const identity = f.slice(1,4).join(':');
    assert(!seen.has(identity), 'duplicate observation identity'); seen.add(identity);
    assert.equal(identity, selected[Math.floor(i/4)].name + ':' + Math.floor(i%4/2) + ':' + i%2,
      'observation identity/order differs');
    const length = word(f[4]), address = word(f[5]), width = word(f[6]);
    assert.equal(length, BigInt(p.bytes.length), 'captured instruction length differs');
    assert.equal(width, BigInt(profiles[Math.floor(i/4)][1]), 'captured operand width differs');
    assert.equal(f[7], Buffer.from(p.bytes).toString('hex'), 'captured instruction bytes differ');
    assert(address >= 8n && address + width < limit, 'wrapped DATA neighborhood');
    assert(address + width <= 4096n || address - 8n >= 4096n + length,
      'DATA neighborhood overlaps relocated code');
    const hex = (s, n) => {
      assert.match(s, /^[0-9a-f]+$/, 'canonical lowercase hex required');
      assert.equal(BigInt(s.length), 2n*n, 'captured hex length differs');
      return [...Buffer.from(s,'hex')];
    };
    const data = hex(f[42], width), before = hex(f[43], width+8n), after = hex(f[44], width+8n);
    assert.deepEqual(data, before.slice(8), 'operand bytes differ from before neighborhood');
    return {identity, name:p.name, seed:f[2], profile:f[3], raw, bytes:p.bytes,
      length, address, width, pre:f.slice(8,24).map(word), preFlags:word(f[24]),
      post:f.slice(25,41).map(word), postFlags:word(f[41]), data, before, after};
  });
  assert.equal(seen.size, 80); return rows;
}
// Locate the whole linked ELF section independently of objcopy's extraction.
// Only the ELF64 little-endian Linux x86-64 executable profile is admitted.
function elfSection(elf) {
  assert(elf.length >= 64, 'truncated ELF');
  assert.deepEqual([...elf.subarray(0,7)], [127,69,76,70,2,1,1], 'ELF profile differs');
  assert.equal(elf.readUInt16LE(16), 2); assert.equal(elf.readUInt16LE(18), 62);
  assert.equal(elf.readUInt32LE(20), 1); assert.equal(elf.readUInt16LE(58), 64);
  const count = elf.readUInt16LE(60), strings = elf.readUInt16LE(62), table = elf.readBigUInt64LE(40);
  assert(count > 0 && strings > 0 && strings < count, 'unsupported ELF section table');
  const range = (start, size) => {
    assert(start >= 0n && size >= 0n && start+size <= BigInt(elf.length), 'ELF range outside file');
    return elf.subarray(Number(start), Number(start+size));
  };
  const sections = range(table, BigInt(count)*64n);
  const sh = i => sections.subarray(i*64,(i+1)*64);
  const str = sh(strings), names = range(str.readBigUInt64LE(24), str.readBigUInt64LE(32));
  const matches = [];
  for (let i = 0; i < count; i++) {
    const s = sh(i), start = s.readUInt32LE(0), end = names.indexOf(0,start);
    assert(start < names.length && end >= start, 'invalid ELF section name');
    if (names.subarray(start,end).toString('ascii') === '.edsl_disp8') matches.push(s);
  }
  assert.equal(matches.length, 1, 'exactly one linked .edsl_disp8 section required');
  const s = matches[0], size = s.readBigUInt64LE(32);
  assert.equal(s.readUInt32LE(4), 1); assert.equal(s.readBigUInt64LE(8), 6n);
  assert(size > 0n && size <= 1048576n, 'linked section exceeds native authentication bound');
  return {address:s.readBigUInt64LE(16), bytes:range(s.readBigUInt64LE(24),size)};
}
function linked(out, selected) {
  const elf = read(out+'/probe.elf'), section = elfSection(elf), extraction = read(out+'/instructions.bin');
  assert(extraction.equals(section.bytes), 'whole linked section differs from extraction');
  const recorded = read(out+'/symbols.txt');
  const actual = execFileSync('nm', ['-n','--defined-only',out+'/probe.elf'],
    {timeout:10000, maxBuffer:4*1024*1024, env:{...process.env, LC_ALL:'C'}});
  assert(recorded.equals(actual), 'linked nm output differs');
  const symbols = new Map();
  for (const line of recorded.toString('utf8').split('\n')) {
    const m = /^([0-9a-fA-F]+)\s+\S\s+(edsl_disp8_\S+)$/.exec(line);
    if (m) { assert(!symbols.has(m[2]), 'duplicate linked symbol'); symbols.set(m[2],BigInt('0x'+m[1])); }
  }
  assert.equal(symbols.get('edsl_disp8_section_start'), section.address);
  assert.equal(symbols.get('edsl_disp8_section_end'), section.address+BigInt(extraction.length));
  const spans = new Map();
  for (const p of [...selected,...mutants]) {
    const begin = symbols.get('edsl_disp8_'+p.name), end = symbols.get('edsl_disp8_'+p.name+'_end');
    assert.notEqual(begin, undefined, 'missing linked probe start');
    assert.notEqual(end, undefined, 'missing linked probe end');
    assert(begin >= section.address && end >= begin && end <= section.address+BigInt(extraction.length),
      'linked instruction span outside section');
    assert.equal(end-begin, BigInt(p.bytes.length), 'linked instruction length differs');
    assert.deepEqual([...extraction.subarray(Number(begin-section.address),Number(end-section.address))],
      p.bytes, 'linked instruction bytes differ');
    spans.set(p.name, {begin:String(begin), end:String(end)});
  }
  return spans;
}
function sourceBindings() {
  const files = new Set(['lean-toolchain','lakefile.lean', 'scripts/verify-displaced-data.sh',
    'scripts/prepare-displaced-data-replay.cjs','scripts/plan-lean-dependencies.cjs',
    'tests/displaced-data-replay.cjs','tests/lean-dependency-plan.cjs',
    ...['check.c','probe.S','PROBES.json'].map(n => fixture+n)]);
  const pending = ['tests.DisplacedDataNativeBase','EDSL.X86.Sequential.Machine',
    'EDSL.X86.Sequential.DisplacedData'];
  while (pending.length) {
    const name = pending.pop(), file = name.replaceAll('.','/')+'.lean';
    if (files.has(file)) continue;
    files.add(file);
    const source = read(path.join(sourceRoot,file)).toString('utf8');
    for (const m of source.matchAll(/^\s*(?:public\s+)?import\s+([A-Za-z0-9_. \t]+)/gm)) {
      for (const imported of m[1].trim().split(/\s+/))
        if (/^(EDSL|tests)\./.test(imported)) pending.push(imported);
    }
  }
  return [...files].sort().map(file => ({file, sha256:hash(path.join(sourceRoot,file))}));
}
const inputs = ['probe.elf','instructions.bin','symbols.txt','observations.txt'];
const inputBindings = out => inputs.map(file => ({file,sha256:hash(out+'/'+file)}));
const shardName = i => 'FreshDisplacedData_'+String(i+1).padStart(2,'0');
const theoremName = i => 'freshObservation'+i;
const list = values => '['+values.join(',')+']';
const stores = new Set(['store32','store64']);
function render(r, i) {
  const reads = stores.has(r.name) ? '[]' : `[⟨.data,${r.address},${r.width}⟩]`;
  return `theorem ${theoremName(i)} (af : Bool) : view af (initial ${list(r.bytes)} ${list(r.pre)} ${r.preFlags} ${r.address} ${list(r.before)}) ${r.address} ${r.width} = .ok (${list(r.post)},${r.postFlags},${4096n+r.length},${reads},${list(r.after.map(b=>'some '+b))}) := by cbv\n` +
    `#print axioms ${namespace}.${theoremName(i)}\n`;
}
function prepare(out) {
  outputDirectory(out);
  const selected = probes(), spans = linked(out,selected);
  const rows = parseCapture(read(out+'/observations.txt').toString('utf8'),selected);
  assert(!fs.existsSync(out+'/replay') && !fs.existsSync(out+'/REPLAY.json'), 'new replay output required');
  fs.mkdirSync(out+'/replay');
  const shards = [];
  for (let i = 0; i < 20; i++) {
    const name = shardName(i), file = 'replay/'+name+'.lean';
    fs.writeFileSync(out+'/'+file, header+rows.slice(4*i,4*i+4).map((r,j)=>render(r,4*i+j)).join('')+trailer,
      {flag:'wx'});
    shards.push({name,file,sha256:hash(out+'/'+file),theorems:[0,1,2,3].map(j=>theoremName(4*i+j))});
  }
  const result = {schema:'displaced-data-native-replay-v1', observations:80, windows:20,
    mutantsRejected:4, kernelReplay:false, replayProfile, inputs:inputBindings(out), sources:sourceBindings(),
    rows:rows.map((r,i)=>({identity:r.identity, theorem:theoremName(i), line:i+2,
      rawSHA256:digest(r.raw), linked:spans.get(r.name)})), shards};
  fs.writeFileSync(out+'/REPLAY.json',JSON.stringify(result,null,2)+'\n',{flag:'wx'});
  check(out);
  return {observations:80, windows:20, shards:20, mutantsRejected:4, kernelReplay:false};
}
// Parse actual proposition literals. Do not verify binding by re-running render.
function checkShard(source, rows, offset) {
  assert(source.startsWith(header) && source.endsWith(trailer), 'Lean shard profile/audit differs');
  const body = source.slice(header.length,-trailer.length).split('\n');
  assert.equal(body.pop(), ''); assert.equal(body.length, 8, 'four fresh theorems and axiom prints required');
  const syntax = /^theorem (freshObservation[0-9]+) \(af : Bool\) : view af \(initial (\[[0-9,]+\]) (\[[0-9,]+\]) ([0-9]+) ([0-9]+) (\[[0-9,]+\])\) ([0-9]+) ([0-9]+) = \.ok \((\[[0-9,]+\]),([0-9]+),([0-9]+),(\[\]|\[⟨\.data,[0-9]+,[0-9]+⟩\]),(\[(?:some [0-9]+,)*some [0-9]+\])\) := by cbv$/;
  const numbers = text => text.slice(1,-1).split(',').map(word);
  const bytes = text => numbers(text).map(b => { assert(b < 256n,'Lean byte overflow'); return Number(b); });
  for (let j = 0; j < 4; j++) {
    const m = syntax.exec(body[2*j]); assert(m, 'Lean proposition syntax/proof differs');
    const r = rows[j], name = theoremName(offset+j);
    assert.equal(m[1],name,'fresh theorem identity differs');
    assert.equal(body[2*j+1],`#print axioms ${namespace}.${name}`,'fresh theorem axiom target differs');
    assert.deepEqual(bytes(m[2]),r.bytes,'instruction bytes differ');
    assert.deepEqual(numbers(m[3]),r.pre,'initial GPRs differ');
    assert.equal(word(m[4]),r.preFlags,'initial flags differ');
    assert.equal(word(m[5]),r.address,'initial DATA address differs');
    assert.deepEqual(bytes(m[6]),r.before,'initial neighborhood differs');
    assert.equal(word(m[7]),r.address,'view DATA address differs');
    assert.equal(word(m[8]),r.width,'view DATA width differs');
    assert.deepEqual(numbers(m[9]),r.post,'final GPRs differ');
    assert.equal(word(m[10]),r.postFlags,'final flags differ');
    assert.equal(word(m[11]),4096n+r.length,'relocated RIP differs');
    const footprint = /^\[⟨\.data,([0-9]+),([0-9]+)⟩\]$/.exec(m[12]);
    const reads = footprint ? [word(footprint[1]),word(footprint[2])] : [];
    assert.deepEqual(reads, stores.has(r.name)?[]:[r.address,r.width],'DATA read footprint differs');
    assert.deepEqual(bytes(m[13].replaceAll('some ','')),r.after,'final neighborhood differs');
  }
}
function checkKernel(out, manifest) {
  assert(fs.existsSync(out+'/kernel-passed.txt'), 'all 20 fresh shard checks are required');
  assert.equal(read(out+'/kernel-passed.txt').toString('utf8'),
    manifest.shards.map(s=>s.name+'\n').join(''), 'all 20 fresh shard checks are required');
  const allowed = new Set(['propext','Quot.sound','Classical.choice']);
  for (const shard of manifest.shards) {
    const lines = read(out+'/'+shard.name+'.log').toString('utf8').trimEnd().split('\n');
    assert.equal(lines.length, 5, 'four axiom diagnostics and one transitive audit required');
    for (let j = 0; j < 4; j++) {
      const prefix = `'${namespace}.${shard.theorems[j]}' `;
      assert(lines[j].startsWith(prefix), 'kernel axiom diagnostic target differs');
      const text = lines[j].slice(prefix.length);
      if (text !== 'does not depend on any axioms') {
        const m = /^depends on axioms: \[([^\]]+)\]$/.exec(text);
        assert(m, 'kernel axiom diagnostic differs');
        for (const axiom of m[1].split(', ')) assert(allowed.has(axiom),'unapproved theorem axiom');
      }
    }
    assert.match(lines[4],/^Audited [1-9][0-9]* EDSL declarations; no unapproved axioms$/,
      'transitive dependency audit required');
  }
}
function check(out, kernel = false) {
  outputDirectory(out);
  const selected = probes(), spans = linked(out,selected);
  const rows = parseCapture(read(out+'/observations.txt').toString('utf8'),selected);
  const manifest = JSON.parse(read(out+'/REPLAY.json'));
  assert.equal(manifest.schema,'displaced-data-native-replay-v1');
  assert.equal(manifest.observations,80); assert.equal(manifest.windows,20);
  assert.equal(manifest.mutantsRejected,4); assert.equal(manifest.kernelReplay,false);
  assert.deepEqual(manifest.replayProfile,replayProfile,'replay proof/resource profile differs');
  assert.equal(manifest.shards.length,20,'exactly 20 shards required');
  assert.deepEqual(fs.readdirSync(out+'/replay').sort(),
    Array.from({length:20},(_,i)=>shardName(i)+'.lean'), 'exactly 20 fresh shard files required');
  for (let i = 0; i < 20; i++) {
    const s = manifest.shards[i], name = shardName(i), file = 'replay/'+name+'.lean';
    assert.equal(s.name,name); assert.equal(s.file,file,'shard path differs');
    assert.deepEqual(s.theorems,[0,1,2,3].map(j=>theoremName(4*i+j)));
    const source = read(out+'/'+file);
    checkShard(source.toString('utf8'),rows.slice(4*i,4*i+4),4*i);
    assert.equal(s.sha256,digest(source),'shard hash differs');
  }
  assert.deepEqual(manifest.inputs,inputBindings(out),'capture/ELF/extraction/symbol hashes differ');
  assert.deepEqual(manifest.sources,sourceBindings(),'source bindings differ');
  assert.deepEqual(manifest.rows,rows.map((r,i)=>({identity:r.identity,theorem:theoremName(i),line:i+2,
    rawSHA256:digest(r.raw),linked:spans.get(r.name)})), 'raw observation/linked span bindings differ');
  if (kernel) checkKernel(out,manifest);
  return {observations:80, windows:20, shards:20, mutantsRejected:4, kernelReplay:kernel};
}
if (require.main === module) {
  const args = process.argv.slice(2);
  if (args.length === 1 && args[0] === '--sources') {
    for (const s of sourceBindings()) console.log(s.sha256+'  '+s.file);
  } else {
    const mode = args[0]?.startsWith('--') ? args.shift() : '--prepare';
    assert.equal(args.length,1,'usage: prepare-displaced-data-replay.cjs [--check|--kernel] OUTPUT_DIRECTORY');
    assert(['--prepare','--check','--kernel'].includes(mode),'unknown mode');
    console.log(JSON.stringify(mode === '--prepare' ? prepare(args[0]) : check(args[0],mode === '--kernel')));
  }
}
module.exports = {prepare,check};
