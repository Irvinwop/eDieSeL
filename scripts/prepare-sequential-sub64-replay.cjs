/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';
const fs=require('fs'),path=require('path'),assert=require('assert/strict'),crypto=require('crypto');
function parse(source){
  const rawHeader=source.split('-- BEGIN OBSERVATIONS\n')[0];
  assert(rawHeader.includes('set_option maxRecDepth 128\n'));
  // Disable asynchronous declaration checking as well as the caller's -j1.
  // Otherwise blocked per-declaration checking tasks can exhaust TasksMax=64.
  const header=rawHeader.replace('set_option maxRecDepth 128\n',
    'set_option maxRecDepth 128\nset_option Elab.async false\n');
  const raw=source.split('\n').filter(l=>l.startsWith('theorem observed_'));
  assert.equal(raw.length,680);assert(raw.every(l=>l.endsWith(':= by decide')));
  assert(header.includes('Sequential.stepWith ⟨true,false,true,false,true,false⟩'));
  // This changes only the proof reduction strategy. Literal bytes, captured
  // inputs/outputs, the production call and every proposition stay unchanged.
  const lines=raw.map(l=>l+' +kernel');
  return {header,lines};
}
function render(header,lines){
  const names=lines.map(l=>/^theorem (observed_[A-Za-z0-9_]+) :/.exec(l)[1]);
  return header+'-- Exact CPU observations, kernel decision under the unchanged fixed limits.\n'+lines.join('\n')+
    '\nend EDSL.Tests.NativeSequentialSub64\n'+names.map(n=>'#print axioms EDSL.Tests.NativeSequentialSub64.'+n).join('\n')+'\n#audit_edsl\n';
}
if(require.main===module){
  const [input,out]=process.argv.slice(2);
  assert(path.isAbsolute(input)&&path.isAbsolute(out));
  assert.equal(fs.realpathSync(input),input);assert.equal(path.resolve(out),out);assert(!fs.existsSync(out));
  const parsed=parse(fs.readFileSync(input,'utf8'));fs.mkdirSync(out);
  const manifest=[];
  for(let i=0;i<8;i++){
    const file=path.join(out,'NativeSub64_'+String(i+1).padStart(2,'0')+'.lean');
    const source=render(parsed.header,parsed.lines.slice(i*85,(i+1)*85));
    fs.writeFileSync(file,source,{flag:'wx'});
    manifest.push({file,sha256:crypto.createHash('sha256').update(source).digest('hex'),observations:85});
  }
  fs.writeFileSync(out+'/REPLAY.json',JSON.stringify({input,inputSHA256:crypto.createHash('sha256').update(fs.readFileSync(input)).digest('hex'),
    production:'Sequential.stepWith (actual decodeAt and executeWith)',proof:'decide +kernel',
    maxHeartbeats:300000,maxRecDepth:128,observations:680,shards:manifest},null,2)+'\n',{flag:'wx'});
}
module.exports={parse,render};
