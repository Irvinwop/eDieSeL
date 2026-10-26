/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
'use strict';
const fs = require('node:fs'), path = require('node:path');
const SHARDS = 20;
function importsOnly(file) {
  const source = fs.readFileSync(file, 'utf8');
  // Fail closed on catalogue changes: only comments, blank lines and one
  // canonical import per line may be expanded. Declarations must be replayed.
  let clean = '', depth = 0;
  for (let i = 0; i < source.length;) {
    if (source.startsWith('/-', i)) { depth++; i += 2; }
    else if (depth && source.startsWith('-/', i)) { depth--; i += 2; }
    else if (!depth && source.startsWith('--', i)) {
      while (i < source.length && source[i] !== '\n') i++;
    } else { if (!depth) clean += source[i]; i++; }
  }
  if (depth) throw new Error('unterminated catalogue comment: '+file);
  const roots = [];
  for (const line of clean.split('\n').map(x => x.trim()).filter(Boolean)) {
    const match = /^import ([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)$/.exec(line);
    if (!match) throw new Error('replay expansion requires an import-only aggregate: '+file);
    roots.push(match[1]);
  }
  if (!roots.length) throw new Error('empty replay aggregate: '+file);
  return roots;
}
function plan(catalogue, aggregate, output) {
  const all = importsOnly(catalogue), full = importsOnly(aggregate);
  if (!full.includes('EDSL.All') || !full.includes('CorpusCertificateChecks') || !full.includes('corpus.Certify'))
    throw new Error('full project, named checks and private corpus CLI must all be covered');
  const roots = [...new Set(full.flatMap(root => root === 'EDSL.All' ? all : [root]))].sort();
  if (roots.includes('EDSL.All') || roots.length < SHARDS) throw new Error('invalid expanded replay roots');
  const units = Array.from({length:SHARDS}, (_, index) => ({
    id:String(index+1).padStart(2, '0'), roots:roots.filter((_, n) => n % SHARDS === index)
  }));
  fs.mkdirSync(output, {recursive:false});
  for (const unit of units) {
    const module = 'KernelReplay'+unit.id;
    fs.writeFileSync(path.join(output, module+'.lean'), unit.roots.map(root => 'import '+root+'\n').join(''));
    fs.writeFileSync(path.join(output, 'Audit'+module+'.lean'),
      `import ${module}\nimport EDSL.Audit\nimport EDSL.Audit.Owners\n#audit_edsl\n#audit_edsl_owners\n`);
  }
  fs.writeFileSync(path.join(output, 'plan.json'), JSON.stringify({shards:SHARDS, roots:roots.length, units}, null, 2)+'\n');
  console.log(`Replay plan: ${roots.length} roots, ${SHARDS} nonempty shards; EDSL.All and CorpusFullReplay are import-only.`);
  return units;
}
if (require.main === module) {
  try {
    const args = process.argv.slice(2);
    if (args.length !== 3) throw new Error('usage: replay-plan.cjs CATALOGUE FULL_AGGREGATE NEW_OUTPUT_DIRECTORY');
    plan(...args);
  } catch (error) { console.error(error.message); process.exitCode = 1; }
}
module.exports = {importsOnly, plan, SHARDS};
