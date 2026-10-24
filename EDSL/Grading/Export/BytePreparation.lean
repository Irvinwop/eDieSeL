/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ByteQuotation
import EDSL.Grading.Export.Preparation

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Pure, untrusted preparation of an observed complete byte list and its ordered
chunks. Every replacement is built with `byteExpr`, without generating a
complete-file reference or a `List.take`/`List.drop` expression.

This module neither reads files nor validates byte provenance, declaration
eligibility, a target contract, or semantic preservation. The caller supplies
finite IO and an independently chosen expected contract. `Prepare.validate`,
export, and the independent kernel checker retain their own admission policies.

The caps bound producer setup, accepted byte count, key count, and explicit name
visits. They are not a time, instruction, stack, or allocation theorem. Native
Nat arithmetic, name comparison/tree housekeeping, byte quotation, allocation,
and GC still require external process limits. In particular, an input is already
allocated before this function receives it. Quotation contains each byte once
in the complete-file value and once across all chunk values, with expression
and balanced-append overhead from `byteExpr`. -/
namespace EDSLGrader.Export.BytePreparation
open Lean EDSL

/-- Caller-selected producer caps, independent of exporter/checker policy. -/
structure Limits where
  maxBytes : Nat := 1048576
  maxChunks : Nat := 16384
  maxChunkSize : Nat := 65536
  maxNameParts : Nat := 64
  maxComponentBytes : Nat := 4096
  maxNameWork : Nat := 1048576

/-- Names are in byte order. The positive chunk size is checked before any scan;
all chunks except the last have this size, and the last is nonempty and no larger.
An empty file has no chunk names. Keys must be nonanonymous and pairwise distinct,
including the complete-file key. Eligibility remains `Prepare.validate`'s job. -/
structure Config where
  fileName : Name
  chunkNames : Array Name
  chunkSize : Nat

/-- Count at most `maxBytes` cons cells without first traversing an unbounded
input with `List.length`. An overflow returns no partial preparation. -/
private def boundedLength (maxBytes : Nat) (bytes : List X86.Byte) : Except String Nat := do
  let mut rest := bytes
  let mut count := 0
  for _ in [:maxBytes] do
    match rest with
    | [] => return count
    | _ :: tail =>
      rest := tail
      count := count + 1
  if !rest.isEmpty then throw "byte count bound"
  return count

/-- Count nonanonymous name components, including aggregate component work.
Diagnostic strings deliberately contain no unbounded input names or numbers. -/
private def checkName (lim : Limits) (used : Nat) (name : Name) : Except String Nat := do
  let mut rest := name
  let mut work := used
  for _ in [:lim.maxNameParts] do
    match rest with
    | .anonymous => return work
    | .str parent component =>
      if work >= lim.maxNameWork then throw "name work bound"
      work := work + 1
      if component.utf8ByteSize > lim.maxComponentBytes then
        throw "name component byte bound"
      rest := parent
    | .num parent _ =>
      if work >= lim.maxNameWork then throw "name work bound"
      work := work + 1
      rest := parent
  if !rest.isAnonymous then throw "name part bound"
  return work

private def checkKeys (lim : Limits) (config : Config) : Except String Unit := do
  let mut work ← checkName lim 0 config.fileName
  if config.fileName.isAnonymous then throw "anonymous complete-file key"
  let mut seen : NameSet := {}
  seen := seen.insert config.fileName
  for name in config.chunkNames do
    work ← checkName lim work name
    if name.isAnonymous then throw "anonymous chunk key"
    if seen.contains name then throw "duplicate or overlapping byte-preparation key"
    seen := seen.insert name

/-- Build one complete-file value override and ordered literal chunk inlinings.
The array-size cap and exact chunk-count check precede key-table allocation and
all quotation. Chunking advances one remaining suffix with `List.splitAt`; it
never drops a growing prefix from the original list. No output is returned on
failure. This helper supplies syntax, not evidence of its original provenance or
of preservation; transformed declarations and the final proposition must still
be checked independently. -/
def prepare (lim : Limits) (config : Config) (bytes : List X86.Byte) :
    Except String Prepare.Preparation := do
  if config.chunkSize == 0 then throw "zero chunk size"
  if config.chunkSize > lim.maxChunkSize then throw "chunk size bound"
  if config.chunkNames.size > lim.maxChunks then throw "chunk key count bound"
  let count ← boundedLength lim.maxBytes bytes
  let expectedChunks := count / config.chunkSize +
    (if count % config.chunkSize == 0 then 0 else 1)
  if config.chunkNames.size != expectedChunks then throw "chunk count mismatch"
  checkKeys lim config
  let mut entries : Array (Name × Expr) := #[]
  let mut rest := bytes
  for name in config.chunkNames do
    let (chunk, tail) := rest.splitAt config.chunkSize
    entries := entries.push (name, EDSLGrader.byteExpr chunk)
    rest := tail
  return {
    definitionValues := #[(config.fileName, EDSLGrader.byteExpr bytes)]
    inlineConstants := entries }

end EDSLGrader.Export.BytePreparation
