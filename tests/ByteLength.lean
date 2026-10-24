/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export.ByteLength
import EDSL.Grading.Export.Core
import EDSL.Grading.Runtime.Checker
import Lean.Util.Path
import tests.fixtures.PreparedRefinementClient

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Actual export/codec/kernel integration. Expected lengths are fixed below;
neither Candidate.claim nor Candidate.literalLength supplies a checking goal.
Compile tests.fixtures.PreparedRefinementClient separately first. -/
namespace ByteLengthTests
open Lean EDSL EDSLGrader EDSLGrader.Runtime

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap {α : Type} (result : Except Failure α) : IO α :=
  match result with
  | .ok value => pure value
  | .error failure => throw (IO.userError s!"unexpected packet failure: {failure}")

private def certificate (context : String)
    (result : Except String Export.ByteLength.Candidate) : IO Export.ByteLength.Candidate :=
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError (context ++ ": " ++ reason))

private def constructorRejected (context : String)
    (result : Except String Export.ByteLength.Candidate) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError (context ++ ": unsupported quotation accepted"))
  | .error reason => require (!reason.isEmpty) (context ++ ": missing rejection reason")

private def kernelRejected (trusted : Kernel.Environment) (expected : Expr)
    (text context : String) : IO Unit :=
  match checkPacketDetailed trusted {} expected text with
  | .ok _ => throw (IO.userError (context ++ ": kernel accepted the wrong contract"))
  | .error failure =>
    require (failure.failure.kind == .rejected && failure.site.phase == .finalProof)
      s!"{context}: expected final kernel rejection, got {repr failure}"

private def helperName : Name := `EDSLGrader.Export.ByteLength.appendLength

private def loadEnvironments : IO (Kernel.Environment × Kernel.Environment) := do
  initSearchPath (← findSysroot)
  let trusted ← importModules
    #[{ module := `EDSL.Grading.Export.Core },
      { module := `EDSL.Grading.Runtime.Checker }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  let client ← importModules #[{ module := `tests.fixtures.PreparedRefinementClient }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  return (trusted.toKernelEnv, client.toKernelEnv)

-- Ordinary literal quotation is independent of balanced byteExpr construction.
private def expectedLength (bytes : List X86.Byte) (n : Nat) : Expr :=
  let length := mkApp2 (mkConst ``List.length [Level.zero])
    (toTypeExpr X86.Byte) (toExpr bytes)
  mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat) length (toExpr n)

private def expectedIdentity (left right : List X86.Byte) : Expr :=
  mkApp3 (mkConst ``Eq [Level.one]) (toTypeExpr (List X86.Byte))
    (toExpr left) (toExpr right)

private def appendQuotation (left right : Expr) : Expr :=
  mkApp3 (mkConst ``List.append [Level.zero]) (toTypeExpr X86.Byte) left right

private def sixteen : List X86.Byte :=
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]

private def seventeen : List X86.Byte :=
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]

private def thirtyThree : List X86.Byte :=
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,
   17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]

private def checkLength (trusted : Kernel.Environment) (supports : List Declaration)
    (bytes : List X86.Byte) (n : Nat) (candidate : Export.ByteLength.Candidate) : IO Unit := do
  let text ← unwrap (encodePacket supports candidate.proof)
  let checked ← unwrap (checkPacket trusted {} (expectedLength bytes n) text)
  let some (.thmInfo _) := checked.env.find? helperName
    | throw (IO.userError "generic append helper was not replayed as an ordinary theorem")
  require ((trusted.find? helperName).isNone) "kernel replay mutated its trusted snapshot"

private def constructorCases : IO Unit := do
  constructorRejected "producer byte-count bound"
    (Export.ByteLength.quoteWithLength 16 seventeen)
  constructorRejected "existing quotation byte-count bound"
    (Export.ByteLength.fromQuotation 16 (byteExpr seventeen))
  constructorRejected "literal leaf longer than sixteen"
    (Export.ByteLength.fromQuotation 64 (toExpr seventeen))
  constructorRejected "named list instead of quotation"
    (Export.ByteLength.fromQuotation 64 (mkConst `PreparedRefinementFixture.file))
  let nil := toExpr ([] : List X86.Byte)
  let wrapped := Expr.letE `bytes (toTypeExpr (List X86.Byte)) nil (.bvar 0) false
  constructorRejected "unsupported let quotation"
    (Export.ByteLength.fromQuotation 0 wrapped)
  -- Empty leaves isolate the append-depth restriction from the byte allowance.
  let deep := (List.range 17).foldl (fun acc _ => appendQuotation acc nil) nil
  constructorRejected "append nesting beyond sixteen"
    (Export.ByteLength.fromQuotation 0 deep)

private def replayCases (trusted client : Kernel.Environment) : IO Unit := do
  let helperPacket ← unwrap <| Export.exportTheorem trusted client
    `PreparedRefinementFixture.helperCarrier .body
  require (helperPacket.declarations.any fun decl => decl.getNames.contains helperName)
    "actual client helper dependency was omitted from export"
  let supports := helperPacket.declarations

  for (bytes, n) in ([([], 0), ([255], 1), (sixteen, 16), (seventeen, 17),
      (thirtyThree, 33)] : List (List X86.Byte × Nat)) do
    let candidate ← certificate "quoteWithLength" (Export.ByteLength.quoteWithLength n bytes)
    checkLength trusted supports bytes n candidate

  -- The odd 33-byte split includes an append below one branch. Recognition is
  -- tested on the already constructed expression, independently of its metrics.
  let existing ← certificate "fromQuotation"
    (Export.ByteLength.fromQuotation 33 (byteExpr thirtyThree))
  checkLength trusted supports thirtyThree 33 existing

  -- A full sixteen-byte leaf followed by a final three-byte leaf exercises
  -- composition without assuming the producer's balanced partition algorithm.
  let shortFinal := appendQuotation (toExpr sixteen) (toExpr ([254,0,255] : List X86.Byte))
  let short ← certificate "short final leaf" (Export.ByteLength.fromQuotation 19 shortFinal)
  checkLength trusted supports
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,254,0,255] 19 short

  let text ← unwrap (encodePacket supports existing.proof)
  kernelRejected trusted (expectedLength thirtyThree 32) text "wrong fixed numeral"
  kernelRejected trusted (expectedLength seventeen 33) text "different-length literal paired with the proof"

  let altered : List X86.Byte := [255,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]
  let permuted : List X86.Byte := [16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0]
  for changed in [altered, permuted] do
    let lengthOnly ← certificate "same-length observation"
      (Export.ByteLength.quoteWithLength 17 changed)
    -- Acceptance here is intended: a length certificate cannot distinguish
    -- same-length observations. It must not become an exact-byte certificate.
    checkLength trusted supports seventeen 17 lengthOnly
    let lengthText ← unwrap (encodePacket supports lengthOnly.proof)
    kernelRejected trusted (expectedIdentity seventeen changed) lengthText
      "length proof used as exact-byte identity"

def main : IO Unit := do
  constructorCases
  let (trusted, client) ← loadEnvironments
  require ((trusted.find? helperName).isNone) "generic helper was seeded into the trusted snapshot"
  require ((trusted.find? `PreparedRefinementFixture.root).isNone)
    "client fixture entered the trusted snapshot"
  require ((client.find? helperName).isSome) "client generic helper metadata missing"
  replayCases trusted client
  IO.println "ByteLength: independent fixed lengths, checked fresh helper, kernel counterexamples and explicit quotation bounds passed"

#eval main
end ByteLengthTests
