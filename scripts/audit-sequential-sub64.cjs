/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';
const fs=require('fs'),path=require('path'),assert=require('assert/strict');
const out=process.argv[2];
assert(path.isAbsolute(out)&&fs.realpathSync(out)===out);
assert.equal(fs.realpathSync(__filename),path.join(__dirname,'audit-sequential-sub64.cjs'));
const observations=fs.readFileSync(out+'/observations.jsonl','utf8').trimEnd().split('\n').map(JSON.parse);
assert.equal(observations.length,680);
const symbols=new Map(fs.readFileSync(out+'/symbols.txt','utf8').trim().split('\n').map(line=>{
  const m=/^([0-9a-f]+) [A-Za-z] (.+)$/.exec(line);assert(m,line);return [m[2],BigInt('0x'+m[1])];
}));
const section=fs.readFileSync(out+'/instructions.bin');
const start=symbols.get('edsl_sub64_section_start'),end=symbols.get('edsl_sub64_section_end');
assert.equal(BigInt(section.length),end-start);
const all16=Array.from({length:16},(_,i)=>i), windows=new Map();
const sorted=xs=>[...new Set(xs)].sort((a,b)=>a-b);
const arithmetic=0x8d5n;
for(const o of observations){
  assert.equal(o.before.length,16);assert.equal(o.after.length,16);
  assert.equal(BigInt(o.pc),symbols.get('edsl_sub64_'+o.name));
  assert.equal(BigInt(o.end),symbols.get('edsl_sub64_'+o.name+'_end'));
  assert.equal(BigInt(o.bytes.length),BigInt(o.end)-BigInt(o.pc));
  assert.deepEqual([...section.subarray(Number(BigInt(o.pc)-start),Number(BigInt(o.end)-start))],o.bytes);
  assert.equal(BigInt(o.effectiveFlags)&~arithmetic,BigInt(o.afterFlags)&~arithmetic);
  for(let r=0;r<16;r++)if(r!==o.destination)assert.equal(o.before[r],o.after[r]);
  if(!windows.has(o.name))windows.set(o.name,[]);windows.get(o.name).push(o);
}
assert.equal(windows.size,68);
for(const cases of windows.values())assert.deepEqual(cases.map(o=>o.vector),Array.from({length:10},(_,i)=>i));
const ws=[...windows.values()].map(c=>c[0]);
// Byte classification below measures coverage only. It never supplies semantic
// expected values, operands, registers or flags to the C oracle or Lean replay.
const reg=ws.filter(o=>o.operation==='register'),imm=ws.filter(o=>o.operation==='immediate');
assert.equal(reg.length,48);assert.equal(imm.length,20);
assert.deepEqual(sorted(reg.map(o=>o.bytes[0])),[0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f]);
for(const opcode of [0x29,0x2b]){
  const direction=reg.filter(o=>o.bytes[1]===opcode);
  assert.deepEqual(sorted(direction.map(o=>o.destination)),all16);
  assert.deepEqual(sorted(direction.map(o=>o.source)),all16);
  assert.deepEqual(sorted(direction.filter(o=>o.bytes[0]&2).map(o=>o.bytes[0])),[0x4a,0x4b,0x4e,0x4f]);
  assert(direction.some(o=>o.destination===o.source));
}
assert(reg.some(o=>o.destination===4&&o.source===4));
assert(reg.some(o=>o.destination===12&&o.source===12));
assert.deepEqual(sorted(imm.map(o=>o.destination)),all16);
assert.deepEqual(sorted(imm.map(o=>o.immediate)),[-128,-1,0,1,127]);
assert.deepEqual(sorted(imm.map(o=>o.bytes[0])),[0x48,0x49]);
for(const bank of [0,1])assert.deepEqual(sorted(imm.filter(o=>Math.floor(o.destination/8)===bank).map(o=>o.immediate)),[-128,-1,0,1,127]);
for(const o of reg)assert.equal(o.bytes.length,3);
for(const o of imm){assert.equal(o.bytes.length,4);assert.equal(o.bytes[1],0x83);}
const flags={};
for(const [name,bit] of [['CF',0],['PF',2],['AF',4],['ZF',6],['SF',7],['OF',11]]){
  const set=observations.filter(o=>(BigInt(o.afterFlags)>>BigInt(bit))&1n).length;
  assert(set>0&&set<680);flags[name]={set,clear:680-set};
}
const sign=x=>x<(1n<<63n)?x:x-(1n<<64n);
const categories={borrow:0,highHalf:0,signedOverflow:0,alias:0,dfSet:0,dfClear:0};
for(const o of observations){
  const l=BigInt(o.before[o.destination]);
  const r=o.operation==='register'?BigInt(o.before[o.source]):BigInt.asUintN(64,BigInt(o.immediate));
  if(l<r)categories.borrow++;
  if(l>0xffffffffn||r>0xffffffffn)categories.highHalf++;
  const d=sign(l)-sign(r);if(d<-(1n<<63n)||d>=(1n<<63n))categories.signedOverflow++;
  if(o.operation==='register'&&o.destination===o.source)categories.alias++;
  categories[(BigInt(o.effectiveFlags)&0x400n)?'dfSet':'dfClear']++;
}
for(const n of Object.values(categories))assert(n>0);
const source=fs.readFileSync(out+'/NativeSequentialSub64.lean','utf8');
assert.equal((source.match(/^theorem observed_/gm)||[]).length,680);
assert.equal((source.match(/:= by decide$/gm)||[]).length,680);
assert(source.includes('Sequential.stepWith ⟨true,false,true,false,true,false⟩'));
assert(!/native_decide|\bsorry\b|\badmit\b|^axiom /m.test(source));
const result={role:'Finite coverage audit, not an opcode-derived semantic oracle',positiveWindows:68,
  ownedNegativeWindows:8,positiveObservations:680,registerWindows:48,immediateWindows:20,
  registers:'All 16 as source and destination for each register opcode, and destination for immediate',
  rexWBytes:sorted(reg.map(o=>o.bytes[0])),immediates:sorted(imm.map(o=>o.immediate)),
  ignoredX:'Each R/B combination in each opcode direction',
  flags,categories,fullGPRFrameChecks:680,fullOtherRFLAGSFrameChecks:680,
  extractedPositiveBytesMatch:true,generatedKernelDecisions:680,
  choiceProfile:'CF=true PF=false AF=true ZF=false SF=true OF=false; SUB defines all six',
  emptyOperandReads:'Requested model footprint only; not a CPU memory-access trace'};
fs.writeFileSync(out+'/axis-audit.json',JSON.stringify(result,null,2)+'\n',{flag:'wx'});
console.log(JSON.stringify({axisAudit:'pass',windows:68,observations:680}));
