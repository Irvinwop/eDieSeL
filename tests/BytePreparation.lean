/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export.BytePreparation
import EDSL.Grading.Export.Core
import EDSL.Grading.Runtime.Checker
import Lean.Util.Path

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Pure byte setup followed by actual export, codec and checked kernel replay.
Compile tests.fixtures.BytePreparationClient first. This controller imports the
client separately from its fixed foundation and spells out expected byte lists;
no client theorem type or preparation output selects the final proposition. -/
namespace BytePreparationTests
open Lean EDSL EDSLGrader EDSLGrader.Runtime

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap {α : Type} (result : Except Failure α) : IO α :=
  match result with
  | .ok value => pure value
  | .error failure => throw (IO.userError s!"unexpected failure: {failure}")

private def prepared (config : Export.BytePreparation.Config) (bytes : List X86.Byte)
    (lim : Export.BytePreparation.Limits := {}) : IO Export.Prepare.Preparation :=
  match Export.BytePreparation.prepare lim config bytes with
  | .ok value => pure value
  | .error reason => throw (IO.userError ("unexpected byte setup failure: " ++ reason))

private def expectSetupFailure (reason : String) (config : Export.BytePreparation.Config)
    (bytes : List X86.Byte) (lim : Export.BytePreparation.Limits := {}) : IO Unit :=
  match Export.BytePreparation.prepare lim config bytes with
  | .ok _ => throw (IO.userError ("invalid byte setup accepted: " ++ reason))
  | .error actual => require (actual == reason)
      s!"wrong byte setup rejection: expected '{reason}', got '{actual}'"

private def rejected {α : Type} (result : Except Failure α) (context : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError (context ++ ": unexpectedly accepted"))
  | .error failure => require (failure.kind == .rejected) s!"{context}: {failure}"

private def hasName (packet : Export.PreparedPacket) (name : Name) : Bool :=
  packet.declarations.any fun declaration => declaration.getNames.contains name

/-- This uses ordinary list quotation, independently of byteExpr's balanced
quotation and the producer's chunking. The caller supplies the complete literal. -/
private def expectedBytes (bytes : List X86.Byte) : Expr :=
  let literal := toExpr bytes
  mkApp3 (mkConst ``Eq [Level.one]) (toTypeExpr (List X86.Byte)) literal literal

private def expectedLength (n : Nat) : Expr :=
  mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat) (toExpr n) (toExpr n)

private def expectedLengths (a b c : Nat) : Expr :=
  mkApp2 (mkConst ``And) (expectedLength a)
    (mkApp2 (mkConst ``And) (expectedLength b) (expectedLength c))

private def six : Export.BytePreparation.Config := {
  fileName := `BytePreparationFixture.file
  chunkNames := #[`BytePreparationFixture.first, `BytePreparationFixture.second,
    `BytePreparationFixture.third]
  chunkSize := 2 }

private def one : Export.BytePreparation.Config := {
  fileName := `BytePreparationFixture.oneFile
  chunkNames := #[`BytePreparationFixture.oneChunk]
  chunkSize := 1 }

private def empty : Export.BytePreparation.Config := {
  fileName := `BytePreparationFixture.emptyFile
  chunkNames := #[]
  chunkSize := 2 }

private def loadEnvironments : IO (Kernel.Environment × Kernel.Environment) := do
  initSearchPath (← findSysroot)
  let trusted ← importModules
    #[{ module := `EDSL.Grading.Export.BytePreparation },
      { module := `EDSL.Grading.Export.Core },
      { module := `EDSL.Grading.Runtime.Checker }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  let client ← importModules #[{ module := `tests.fixtures.BytePreparationClient }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  return (trusted.toKernelEnv, client.toKernelEnv)

/-- Reject the regression that reintroduces whole-file kernel slicing. These
are dependency properties of the emitted closure, not comparisons of assigned
preparation fields. Checking the resulting packet below establishes typing. -/
private def requireLiteralClosure (packet : Export.PreparedPacket) : IO Unit := do
  require (hasName packet six.fileName) "complete-file definition was not exported"
  for name in [`BytePreparationFixture.original, `BytePreparationFixture.first,
      `BytePreparationFixture.second, `BytePreparationFixture.third] do
    require (!(hasName packet name)) s!"obsolete byte dependency exported: {name}"
  for declaration in packet.declarations do
    let expressions := match declaration with
      | .defnDecl value => [value.type, value.value]
      | .thmDecl value => [value.type, value.value]
      | _ => []
    for expression in expressions do
      let references := expression.getUsedConstants
      require (!references.contains ``List.take && !references.contains ``List.drop)
        "exported packet reintroduced kernel take/drop traversal"

private def setupCases : IO Unit := do
  let bytes : List X86.Byte := [0, 255, 17, 128, 254, 1]
  expectSetupFailure "zero chunk size" { six with chunkSize := 0 } bytes
  expectSetupFailure "zero chunk size" { empty with chunkSize := 0 } []
  expectSetupFailure "chunk count mismatch"
    { six with chunkNames := #[`BytePreparationFixture.first, `BytePreparationFixture.second] } bytes
  expectSetupFailure "chunk count mismatch"
    { six with chunkNames := six.chunkNames.push `BytePreparationFixture.extra } bytes
  expectSetupFailure "chunk count mismatch" { empty with chunkNames := #[`unused] } []
  expectSetupFailure "chunk count mismatch" empty [1]
  expectSetupFailure "anonymous complete-file key" { six with fileName := .anonymous } bytes
  expectSetupFailure "anonymous chunk key"
    { six with chunkNames := #[.anonymous, `second, `third] } bytes
  expectSetupFailure "duplicate or overlapping byte-preparation key"
    { six with chunkNames := #[`first, `first, `third] } bytes
  expectSetupFailure "duplicate or overlapping byte-preparation key"
    { six with chunkNames := #[six.fileName, `second, `third] } bytes
  expectSetupFailure "byte count bound" six bytes { maxBytes := 5 }
  expectSetupFailure "chunk key count bound" six bytes { maxChunks := 2 }
  expectSetupFailure "chunk size bound" six bytes { maxChunkSize := 1 }
  expectSetupFailure "name part bound" six bytes { maxNameParts := 1 }
  expectSetupFailure "name component byte bound" six bytes { maxComponentBytes := 1 }
  -- Each two-component name fits separately; four names exceed the aggregate
  -- allowance of seven visits. Resetting fuel per key would accept this input.
  expectSetupFailure "name work bound" six bytes { maxNameWork := 7 }

private def replayCases (trusted client : Kernel.Environment) : IO Unit := do
  let correctBytes : List X86.Byte := [0, 255, 17, 128, 254, 1]
  let fixed := expectedBytes [0, 255, 17, 128, 254, 1]
  let correct ← prepared six correctBytes {
    maxBytes := 6, maxChunks := 3, maxChunkSize := 2,
    maxNameParts := 2, maxComponentBytes := 22, maxNameWork := 8 }
  for mode in [Export.Mode.reference, .body] do
    let packet ← unwrap <| Export.exportTheoremPrepared trusted client
      `BytePreparationFixture.root correct mode
    requireLiteralClosure packet
    let checked ← unwrap <| checkPacket trusted {} fixed packet.text
    require (checked.kernelChecks > 1) "packet bypassed checked declaration reconstruction"

    let lengths ← unwrap <| Export.exportTheoremPrepared trusted client
      `BytePreparationFixture.partitionLengths correct mode
    let _ ← unwrap <| checkPacket trusted {} (expectedLengths 2 2 2) lengths.text

    -- This malformed partition preserves every byte and the complete join.
    -- Its failure must come from the independent interval geometry.
    let uneven := { correct with inlineConstants := #[
      (`BytePreparationFixture.first, toExpr ([0] : List X86.Byte)),
      (`BytePreparationFixture.second, toExpr ([255, 17, 128] : List X86.Byte)),
      (`BytePreparationFixture.third, toExpr ([254, 1] : List X86.Byte))] }
    let unevenJoin ← unwrap <| Export.exportTheoremPrepared trusted client
      `BytePreparationFixture.root uneven mode
    let _ ← unwrap <| checkPacket trusted {} fixed unevenJoin.text
    let unevenLengths ← unwrap <| Export.exportTheoremPrepared trusted client
      `BytePreparationFixture.partitionLengths uneven mode
    rejected (checkPacket trusted {} (expectedLengths 2 2 2) unevenLengths.text)
      "byte-preserving incorrect chunk boundaries"

    let partialPreparation ← prepared six [0, 255, 17, 128, 254]
    let partialLengths ← unwrap <| Export.exportTheoremPrepared trusted client
      `BytePreparationFixture.partitionLengths partialPreparation mode
    let _ ← unwrap <| checkPacket trusted {} (expectedLengths 2 2 1) partialLengths.text

    -- The full file and its first chunk cross byteExpr's 16-byte leaf threshold;
    -- the final three bytes exercise a short final chunk.
    let wide ← prepared {
      fileName := `BytePreparationFixture.wideFile
      chunkNames := #[`BytePreparationFixture.wideFirst, `BytePreparationFixture.wideLast]
      chunkSize := 17 }
      [0,255,17,128,254,1,64,32,16,8,4,2,3,5,7,11,13,19,23,29]
    let wideJoin ← unwrap <| Export.exportTheoremPrepared trusted client
      `BytePreparationFixture.wideRoot wide mode
    let _ ← unwrap <| checkPacket trusted {}
      (expectedBytes [0,255,17,128,254,1,64,32,16,8,4,2,3,5,7,11,13,19,23,29]) wideJoin.text
    let wideLengths ← unwrap <| Export.exportTheoremPrepared trusted client
      `BytePreparationFixture.wideLengths wide mode
    let _ ← unwrap <| checkPacket trusted {}
      (mkApp2 (mkConst ``And) (expectedLength 17) (expectedLength 3)) wideLengths.text

    -- Each altered observation still produces a typed packet for its own exact
    -- bytes, including a shortened final chunk. The fixed external statement
    -- must reject it even though its internal theorem remains valid.
    for (context, altered) in ([
        ("misordered chunks", [17, 128, 0, 255, 254, 1]),
        ("tampered boundary byte", [0, 255, 17, 129, 254, 1]),
        ("truncated final chunk", [0, 255, 17, 128, 254])] : List (String × List X86.Byte)) do
      let replacement ← prepared six altered
      let wrongPacket ← unwrap <| Export.exportTheoremPrepared trusted client
        `BytePreparationFixture.root replacement mode
      requireLiteralClosure wrongPacket
      let _ ← unwrap <| checkPacket trusted {} (expectedBytes altered) wrongPacket.text
      rejected (checkPacket trusted {} fixed wrongPacket.text) context

    -- Keys are positional. A caller that swaps them, or a producer that attaches
    -- a literal to the wrong key, must not pass the fixed statement.
    let misplaced ← prepared { six with chunkNames := #[`BytePreparationFixture.second,
      `BytePreparationFixture.first, `BytePreparationFixture.third] } correctBytes
    let misplacedPacket ← unwrap <| Export.exportTheoremPrepared trusted client
      `BytePreparationFixture.root misplaced mode
    rejected (checkPacket trusted {} fixed misplacedPacket.text) "misordered chunk keys"
    let truncatedChunk := { correct with inlineConstants := correct.inlineConstants.map fun entry =>
      if entry.1 == `BytePreparationFixture.third then
        (entry.1, toExpr ([254] : List X86.Byte))
      else entry }
    let truncatedPacket ← unwrap <| Export.exportTheoremPrepared trusted client
      `BytePreparationFixture.root truncatedChunk mode
    rejected (checkPacket trusted {} fixed truncatedPacket.text) "literal chunk truncated independently"

    -- Empty input requires no chunks; a one-byte input occupies either a full
    -- one-byte chunk or a short two-byte chunk, without padding or omission.
    let emptyPreparation ← prepared empty [] { maxBytes := 0, maxChunks := 0 }
    let emptyPacket ← unwrap <| Export.exportTheoremPrepared trusted client
      `BytePreparationFixture.emptyRoot emptyPreparation mode
    let _ ← unwrap <| checkPacket trusted {} (expectedBytes []) emptyPacket.text
    for size in [1, 2] do
      let singleton ← prepared { one with chunkSize := size } [255]
      let singletonPacket ← unwrap <| Export.exportTheoremPrepared trusted client
        `BytePreparationFixture.oneRoot singleton mode
      let _ ← unwrap <| checkPacket trusted {} (expectedBytes [255]) singletonPacket.text

  -- Structural byte setup cannot decide whether a key names an eligible client
  -- declaration. That separate exporter boundary must still reject missing keys.
  let missing ← prepared { six with fileName := `BytePreparationFixture.missing } correctBytes
  match Export.exportTheoremPrepared trusted client `BytePreparationFixture.root missing with
  | .ok _ => throw (IO.userError "missing complete-file key passed exporter validation")
  | .error failure =>
    require (failure.kind == .unsupported)
      s!"missing complete-file key rejected unexpectedly: {failure}"

def main : IO Unit := do
  setupCases
  let (trusted, client) ← loadEnvironments
  require ((trusted.find? `BytePreparationFixture.root).isNone)
    "client theorem entered the trusted replay snapshot"
  require ((client.find? `BytePreparationFixture.root).isSome)
    "client theorem was not imported"
  replayCases trusted client
  IO.println "BytePreparation: literal export/kernel replay, exact/partial/empty geometry, independent byte rejection and setup bounds passed"

#eval main
end BytePreparationTests
