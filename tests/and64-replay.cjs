/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';
const fs=require('fs'), path=require('path'), assert=require('assert/strict');
const {prepare}=require('../scripts/prepare-and64-replay.cjs');
const [out]=process.argv.slice(2);
assert(path.isAbsolute(out)); assert.equal(fs.realpathSync(out),out);
const root=fs.mkdtempSync(out+'/binding-controls.');
const results=[];
function reject(label,change) {
  const dir=root+'/'+label; fs.mkdirSync(dir);
  for(const n of ['instructions.bin','symbols.txt','measured.jsonl','result.log'])
    fs.copyFileSync(out+'/'+n,dir+'/'+n);
  change(dir);
  assert.throws(()=>prepare(dir),undefined,label+' was incorrectly admitted');
  results.push({control:label,rejected:true});
}
function replaceLine(dir,index,change) {
  const file=dir+'/measured.jsonl',lines=fs.readFileSync(file,'utf8').trim().split('\n');
  lines[index]=change(lines[index]); fs.writeFileSync(file,lines.join('\n')+'\n');
}
try {
  reject('different-linked-byte',d=>{
    const f=d+'/instructions.bin',b=fs.readFileSync(f);b[0]^=1;fs.writeFileSync(f,b);
  });
  reject('truncated-capture',d=>{
    const f=d+'/measured.jsonl';fs.writeFileSync(f,fs.readFileSync(f,'utf8').trim().split('\n').slice(0,-1).join('\n')+'\n');
  });
  reject('captured-pc-mismatch',d=>replaceLine(d,0,l=>l.replace(/"pc":[0-9]+/,'"pc":0')));
  reject('captured-code-mismatch',d=>replaceLine(d,0,l=>l.replace('"bytes":[72,','"bytes":[73,')));
  reject('captured-name-mismatch',d=>replaceLine(d,0,l=>l.replace('"name":"bank0_0"','"name":"bank1_0"')));
  reject('out-of-word-range',d=>replaceLine(d,0,l=>l.replace(/"measuredPostFlags":[0-9]+/,'"measuredPostFlags":18446744073709551616')));
  reject('missing-mutant-verdict',d=>{
    const f=d+'/result.log';fs.writeFileSync(f,fs.readFileSync(f,'utf8').replace(/^REJECTED bad_sign.*\n/m,''));
  });
  fs.writeFileSync(out+'/BINDING-CONTROLS.json',JSON.stringify(results,null,2)+'\n',{flag:'wx'});
  console.log(JSON.stringify({controls:results.length,allRejected:true}));
} finally {fs.rmSync(root,{recursive:true,force:true});}
