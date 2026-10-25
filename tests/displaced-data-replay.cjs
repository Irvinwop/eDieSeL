/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';
// Regressions use an actual native capture and its actual generated statements.
// No replacement CPU oracle or expected propositions are constructed here.
const fs = require('node:fs'), path = require('node:path'), assert = require('node:assert/strict');
const crypto = require('node:crypto');
const {prepare,check} = require('../scripts/prepare-displaced-data-replay.cjs');
assert.equal(process.argv.length,3,'usage: node tests/displaced-data-replay.cjs ACTUAL_OUTPUT_DIRECTORY');
const out = process.argv[2];
assert(path.isAbsolute(out)); assert.equal(fs.realpathSync(out),out);
const digest = bytes => crypto.createHash('sha256').update(bytes).digest('hex');
const hash = file => digest(fs.readFileSync(file));
const inputs = ['probe.elf','instructions.bin','symbols.txt','observations.txt'];
const shards = fs.readdirSync(out+'/replay').sort();
const originals = [...inputs,'REPLAY.json',...shards.map(n=>'replay/'+n)];
const before = originals.map(f=>hash(out+'/'+f));
check(out);
const work = fs.mkdtempSync(out+'/binding-controls.');
const current = work+'/current', results = [];
function copy(replay = true) {
  fs.rmSync(current,{recursive:true,force:true}); fs.mkdirSync(current);
  for (const file of inputs) fs.copyFileSync(out+'/'+file,current+'/'+file);
  if (replay) {
    fs.copyFileSync(out+'/REPLAY.json',current+'/REPLAY.json'); fs.mkdirSync(current+'/replay');
    for (const name of shards) fs.copyFileSync(out+'/replay/'+name,current+'/replay/'+name);
  }
  return current;
}
function edit(dir, file, change) {
  const target = dir+'/'+file, raw = fs.readFileSync(target,'utf8'), next = change(raw);
  assert.notEqual(next,raw,'control must actually change '+file); fs.writeFileSync(target,next);
}
function manifest(dir, change) {
  const file = dir+'/REPLAY.json', m = JSON.parse(fs.readFileSync(file));
  change(m); fs.writeFileSync(file,JSON.stringify(m,null,2)+'\n');
}
function captureRow(dir, index, change) {
  edit(dir,'observations.txt',text=>{
    const lines = text.slice(0,-1).split('\n'), fields = lines[index+1].split(' ');
    change(fields); lines[index+1] = fields.join(' '); return lines.join('\n')+'\n';
  });
  // Hashes are updated deliberately: literal joins must catch the change.
  manifest(dir,m=>{
    m.inputs.find(i=>i.file==='observations.txt').sha256 = hash(dir+'/observations.txt');
    const lines = fs.readFileSync(dir+'/observations.txt','utf8').slice(0,-1).split('\n');
    m.rows[index].rawSHA256 = digest(lines[index+1]);
  });
}
function shardEdit(dir, index, change) {
  const file = 'replay/'+shards[index]; edit(dir,file,change);
  manifest(dir,m=>{m.shards[index].sha256 = hash(dir+'/'+file);});
}
function increment(s) { return String(BigInt(s)+1n); }
function flipHex(s) { return (parseInt(s.slice(0,2),16)^1).toString(16).padStart(2,'0')+s.slice(2); }
function reject(label, pattern, change, kernel = false) {
  const dir = copy(); change(dir);
  let failure;
  try { check(dir,kernel); } catch (e) { failure = e; }
  assert(failure,label+' was incorrectly admitted');
  assert.match(failure.message,pattern,label+' failed for the wrong reason');
  results.push({control:label,rejected:true,reason:failure.message.split('\n')[0]});
}
try {
  // A second generation from the untouched actual capture must be accepted.
  // This prevents existing output or unrelated filesystem errors from counting
  // as successful negative controls.
  const fresh = copy(false); prepare(fresh); check(fresh);
  reject('truncated-capture',/capture footer differs/,d=>edit(d,'observations.txt',s=>s.slice(0,-50)+'\n'));
  reject('extra-record',/exactly 80 observations required/,d=>edit(d,'observations.txt',s=>
    s.replace('END 80 4\n',s.split('\n')[1]+'\nEND 80 4\n')));
  reject('extra-blank-line',/capture footer differs/,d=>edit(d,'observations.txt',s=>s+'\n'));
  reject('different-version',/capture version differs/,d=>edit(d,'observations.txt',s=>s.replace('V1','V2')));
  reject('duplicate-observation',/duplicate observation identity/,d=>edit(d,'observations.txt',s=>{
    const lines = s.split('\n'); lines[2] = lines[1]; return lines.join('\n');
  }));
  reject('missing-observation',/exactly 80 observations required/,d=>edit(d,'observations.txt',s=>{
    const lines = s.split('\n'); lines.splice(1,1); return lines.join('\n');
  }));
  reject('unselected-identity',/unselected probe identity/,d=>captureRow(d,0,f=>{f[1]='mutant_width';}));
  reject('missing-input-combination',/duplicate observation identity/,d=>captureRow(d,1,f=>{f[3]='0';}));
  reject('out-of-profile-seed',/invalid seed/,d=>captureRow(d,0,f=>{f[2]='2';}));
  reject('out-of-profile-placement',/invalid profile/,d=>captureRow(d,0,f=>{f[3]='2';}));
  reject('wrong-identity-width',/captured operand width differs/,d=>captureRow(d,0,f=>{f[6]='8';}));
  reject('wrong-instruction-length',/captured instruction length differs/,d=>captureRow(d,0,f=>{f[4]='4';}));
  reject('wrong-captured-bytes',/captured instruction bytes differ/,d=>captureRow(d,0,f=>{f[7]=flipHex(f[7]);}));
  reject('negative-decimal',/canonical unsigned decimal required/,d=>captureRow(d,0,f=>{f[5]='-1';}));
  reject('overflow-decimal',/uint64 overflow/,d=>captureRow(d,0,f=>{f[5]='18446744073709551616';}));
  reject('leading-zero-decimal',/canonical unsigned decimal required/,d=>captureRow(d,0,f=>{f[8]='0'+f[8];}));
  reject('exponent-decimal',/canonical unsigned decimal required/,d=>captureRow(d,0,f=>{f[24]='1e3';}));
  reject('hexadecimal-decimal',/canonical unsigned decimal required/,d=>captureRow(d,0,f=>{f[41]='0x602';}));
  reject('missing-register-field',/observation field count differs/,d=>captureRow(d,0,f=>{f.splice(23,1);}));
  reject('extra-field',/observation field count differs/,d=>captureRow(d,0,f=>{f.push('0');}));
  reject('noncanonical-spacing',/observation field count differs/,d=>edit(d,'observations.txt',s=>s.replace('OBS load32','OBS  load32')));
  reject('uppercase-hex',/canonical lowercase hex required/,d=>captureRow(d,0,f=>{f[42]=f[42].toUpperCase();}));
  reject('truncated-neighborhood',/captured hex length differs/,d=>captureRow(d,0,f=>{f[44]=f[44].slice(2);}));
  reject('operand-before-disagreement',/operand bytes differ from before neighborhood/,d=>captureRow(d,0,f=>{f[42]=flipHex(f[42]);}));
  reject('missing-mutant-verdict',/capture footer differs/,d=>edit(d,'observations.txt',s=>s.replace('END 80 4','END 80 3')));
  reject('CRLF-capture',/LF-terminated capture required/,d=>edit(d,'observations.txt',s=>s.replaceAll('\n','\r\n')));
  reject('missing-final-newline',/LF-terminated capture required/,d=>edit(d,'observations.txt',s=>s.slice(0,-1)));
  // Exercise every captured GPR, including words above Number's exact range.
  // A renderer dropping, swapping or rounding any one word fails these joins.
  for (let r = 0; r < 16; r++) {
    reject('initial-gpr-'+r,/initial GPRs differ/,d=>captureRow(d,0,f=>{f[8+r]=increment(f[8+r]);}));
    reject('final-gpr-'+r,/final GPRs differ/,d=>captureRow(d,0,f=>{f[25+r]=increment(f[25+r]);}));
  }
  reject('measured-initial-flags',/initial flags differ/,d=>captureRow(d,0,f=>{f[24]=increment(f[24]);}));
  reject('measured-final-flags',/final flags differ/,d=>captureRow(d,0,f=>{f[41]=increment(f[41]);}));
  reject('measured-DATA-address',/initial DATA address differs/,d=>captureRow(d,0,f=>{f[5]=increment(f[5]);}));
  reject('initial-neighborhood-padding',/initial neighborhood differs/,d=>captureRow(d,0,f=>{f[43]=flipHex(f[43]);}));
  reject('initial-operand-and-neighborhood',/initial neighborhood differs/,d=>captureRow(d,0,f=>{
    f[42]=flipHex(f[42]); f[43]=f[43].slice(0,16)+f[42];
  }));
  reject('final-neighborhood-padding',/final neighborhood differs/,d=>captureRow(d,0,f=>{f[44]=flipHex(f[44]);}));
  reject('final-store-operand',/final neighborhood differs/,d=>captureRow(d,4,f=>{
    f[44]=f[44].slice(0,16)+flipHex(f[44].slice(16));
  }));
  for (const field of [4,6,...Array.from({length:34},(_,i)=>i+8)]) {
    reject('overflow-field-'+field,/uint64 overflow/,d=>captureRow(d,0,f=>{f[field]='18446744073709551616';}));
  }
  reject('extraction-harness-byte',/whole linked section differs from extraction/,d=>{
    const file = d+'/instructions.bin', bytes = fs.readFileSync(file); bytes[0]^=1; fs.writeFileSync(file,bytes);
  });
  reject('truncated-extraction',/whole linked section differs from extraction/,d=>{
    const file = d+'/instructions.bin'; fs.writeFileSync(file,fs.readFileSync(file).subarray(0,-1));
  });
  reject('extra-extraction-byte',/whole linked section differs from extraction/,d=>fs.appendFileSync(d+'/instructions.bin',Buffer.from([0])));
  reject('ELF-harness-byte',/whole linked section differs from extraction/,d=>{
    const file = d+'/probe.elf', elf = fs.readFileSync(file), section = fs.readFileSync(d+'/instructions.bin');
    const offset = elf.indexOf(section); assert(offset >= 0 && elf.indexOf(section,offset+1) < 0);
    elf[offset]^=1; fs.writeFileSync(file,elf);
  });
  reject('linked-symbol-offset',/linked nm output differs/,d=>edit(d,'symbols.txt',s=>s.replace(
    /^([0-9a-f]+)(\s+\S\s+edsl_disp8_load32_end)$/m,
    (_,address,suffix)=>(BigInt('0x'+address)+1n).toString(16).padStart(address.length,'0')+suffix)));
  reject('proposition-instruction-byte',/instruction bytes differ/,d=>shardEdit(d,0,s=>s.replace('initial [139,79,4]','initial [139,79,5]')));
  reject('proposition-relocated-RIP',/relocated RIP differs/,d=>shardEdit(d,0,s=>s.replace(',4099,',',4100,')));
  reject('proposition-read-footprint',/DATA read footprint differs/,d=>shardEdit(d,0,s=>s.replace(/\[⟨\.data,[0-9]+,4⟩\]/,'[]')));
  reject('proposition-store-footprint',/DATA read footprint differs/,d=>shardEdit(d,1,s=>s.replace(',[],[some',',[⟨.data,0,4⟩],[some')));
  reject('proposition-native-reduction',/Lean proposition syntax\/proof differs/,d=>shardEdit(d,0,s=>s.replace(':= by cbv',':= by native_decide')));
  reject('proposition-duplicate-name',/fresh theorem identity differs/,d=>shardEdit(d,0,s=>s.replace('theorem freshObservation1','theorem freshObservation0')));
  reject('missing-transitive-audit',/Lean shard profile\/audit differs/,d=>shardEdit(d,0,s=>s.replace('#audit_edsl\n','')));
  reject('weakened-heartbeat-limit',/Lean shard profile\/audit differs/,d=>shardEdit(d,0,s=>s.replace('maxHeartbeats 300000','maxHeartbeats 300001')));
  reject('changed-axiom-print-target',/fresh theorem axiom target differs/,d=>shardEdit(d,0,s=>s.replace(
    '#print axioms EDSL.Tests.DisplacedDataNative.freshObservation0',
    '#print axioms EDSL.Tests.DisplacedDataNative.freshObservation1')));
  reject('missing-shard',/exactly 20 fresh shard files required/,d=>fs.unlinkSync(d+'/replay/'+shards[19]));
  reject('extra-shard',/exactly 20 fresh shard files required/,d=>fs.copyFileSync(d+'/replay/'+shards[0],d+'/replay/Unexpected.lean'));
  reject('changed-source-binding',/source bindings differ/,d=>manifest(d,m=>{m.sources[0].sha256='0'.repeat(64);}));
  reject('changed-capture-hash',/capture\/ELF\/extraction\/symbol hashes differ/,d=>manifest(d,m=>{
    m.inputs.find(i=>i.file==='observations.txt').sha256='0'.repeat(64);
  }));
  reject('changed-shard-hash',/shard hash differs/,d=>manifest(d,m=>{m.shards[0].sha256='0'.repeat(64);}));
  reject('changed-linked-span-binding',/raw observation\/linked span bindings differ/,d=>manifest(d,m=>{
    m.rows[0].linked.end=increment(m.rows[0].linked.end);
  }));
  reject('native-only-is-not-kernel-replay',/all 20 fresh shard checks are required/,()=>{},true);
  assert.deepEqual(originals.map(f=>hash(out+'/'+f)),before,'controls changed original evidence');
  check(out);
  fs.writeFileSync(out+'/BINDING-CONTROLS.json',JSON.stringify({
    schema:'displaced-data-binding-controls-v1', actualCaptureSHA256:hash(out+'/observations.txt'),
    generatorSHA256:hash(path.resolve(__dirname,'../scripts/prepare-displaced-data-replay.cjs')),
    testsSHA256:hash(__filename), untouchedActualAccepted:true, regeneratedActualAccepted:true,
    controls:results, kernelReplay:false
  },null,2)+'\n');
  console.log(JSON.stringify({controls:results.length,allRejected:true,kernelReplay:false}));
} finally { fs.rmSync(work,{recursive:true,force:true}); }
