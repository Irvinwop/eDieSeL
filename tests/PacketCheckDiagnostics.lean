/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Lean
import EDSL.Grading.Runtime.Checker

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Diagnostic regressions use independently typed contracts and owned synthetic
negative declaration data. Kernel errors and dependency audits execute for real;
no synthetic axiom is installed in this module's environment. -/
namespace PacketCheckDiagnosticsTests
open Lean EDSLGrader.Runtime

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap {α : Type} (result : Except Failure α) : IO α := do
  match result with
  | .ok value => return value
  | .error failure => throw (IO.userError s!"unexpected fixture failure: {failure}")

private def truth : Expr := mkConst ``True
private def intro : Expr := mkConst ``True.intro
private def nat : Expr := mkConst ``Nat
private def helperName : Name := `PacketCheckFixture.seven

private def helper : Declaration := .defnDecl {
  name := helperName, levelParams := [], type := nat, value := mkRawNatLit 7,
  hints := .abbrev, safety := .safe, all := [helperName] }

private def theoremData (name : Name) (type value : Expr) : Declaration :=
  .thmDecl { name, levelParams := [], type, value, all := [name] }

private def encode (shared : Bool) (decls : List Declaration) (proof : Expr) : IO String :=
  unwrap (if shared then encodePacket decls proof else encodeTreePacket decls proof)

private def reject (env : Kernel.Environment) (lim : Limits) (expected : Expr)
    (text : String) (phase : PacketCheckPhase) (entry : Option Nat) (completed : Nat)
    (kind : FailureKind) : IO PacketCheckFailure := do
  let failure ← match checkPacketDetailed env lim expected text with
    | .ok _ => throw (IO.userError s!"unexpected acceptance at {repr phase}")
    | .error failure => pure failure
  require (failure.failure.kind == kind && failure.site.phase == phase &&
    failure.site.entry == entry && failure.site.completedDeclarations == completed)
    s!"wrong failure location/category: {repr failure}"
  match checkPacket env lim expected text with
  | .ok _ => throw (IO.userError "legacy API accepted a rejected contract")
  | .error legacy =>
    require (legacy.kind == kind && legacy.message == failure.failure.message)
      "legacy failure category/message changed"
  require ((env.find? helperName).isNone) "failed checking leaked an auxiliary into its input"
  return failure

private def beforePacket (env : Kernel.Environment) : IO Unit := do
  let text ← encode true [] intro
  let expected ← reject env {} (.bvar 0) text .expected none 0 .malformed
  require (expected.site.decoderSteps == 0 && expected.site.auditSteps == 0)
    "an invalid independent expectation reached packet work"
  let _ ← reject env {} truth "[" .envelope none 0 .malformed
  let budget ← reject env { kernelHeartbeats := 0 } truth text .kernelBudget none 0 .resource
  require budget.site.kernelCeiling.isNone "no kernel call should have a zero quota"

private def declarationCases (env : Kernel.Environment) (shared : Bool) : IO Unit := do
  let missing := mkConst `PacketCheckFixture.doesNotExist
  let badDecode := theoremData `PacketCheckFixture.missing truth missing
  let decodeFailure ← reject env {} truth (← encode shared [helper, badDecode] intro)
    .declarationDecode (some 1) 1 .malformed
  require (decodeFailure.failure.message == "unknown constant" &&
    decodeFailure.site.decoderSteps > 0 && decodeFailure.site.auditSteps > 0)
    "decoder failure lost successful prefix work"
  require decodeFailure.site.kernelCeiling.isNone "decoder failure claims a kernel attempt"

  let badType := theoremData `PacketCheckFixture.badType truth (mkRawNatLit 4)
  let kernelFailure ← reject env {} truth (← encode shared [helper, badType] intro)
    .declarationKernel (some 1) 1 .rejected
  require (kernelFailure.site.kernelCeiling == some 6666666)
    "second of three checks lost its fixed cumulative ceiling"

  -- Four generated constants fit individually: type, recursor and two constructors.
  -- The preceding helper makes their aggregate five, above the independent cap four.
  let color : Name := `PacketCheckFixture.Color
  let group : Declaration := .inductDecl [] 0 [{
    name := color, type := .sort 1, ctors := [
      { name := `PacketCheckFixture.Color.red, type := mkConst color },
      { name := `PacketCheckFixture.Color.blue, type := mkConst color }] }] false
  let names ← reject env { maxDeclarations := 4 } truth
    (← encode shared [helper, group] intro) .declarationNames (some 1) 1 .resource
  require (names.failure.message == "declared constant names" && names.site.kernelCeiling.isNone)
    "aggregate generated-name policy was not applied before the kernel"

  let nestedName : Name := `PacketCheckFixture.Nested
  let nested := mkConst nestedName
  let nestedGroup : Declaration := .inductDecl [] 0 [{
    name := nestedName, type := .sort 1, ctors := [
      { name := `PacketCheckFixture.Nested.leaf, type := nested },
      { name := `PacketCheckFixture.Nested.node,
        type := .forallE `xs (mkApp (mkConst ``List [0]) nested) nested .default }] }] false
  let shape ← reject env {} truth (← encode shared [helper, nestedGroup] intro)
    .inductiveShape (some 1) 1 .unsupported
  require (shape.failure.message == "nested inductive group" && shape.site.kernelCeiling.isNone)
    "a kernel-checked nested group bypassed protocol shape admission"

  let localAxiom := `PacketCheckFixture.unapproved
  let auditedEnv ← unwrap (forceDeclaration env 10000000 512 (.axiomDecl {
    name := localAxiom, levelParams := [], type := mkConst ``False, isUnsafe := false }))
  let axiomUse := theoremData `PacketCheckFixture.hiddenAxiom
    (mkConst ``False) (mkConst localAxiom)
  let auditFailure ← reject auditedEnv {} truth
    (← encode shared [helper, axiomUse] intro) .declarationAudit (some 1) 1 .audit
  require (auditFailure.failure.message == "unapproved axiom" &&
    auditFailure.site.kernelCeiling.isNone)
    "a well-typed auxiliary bypassed dependency admission"
  let finalAudit ← reject auditedEnv {} (mkConst ``False)
    (← encode shared [helper] (mkConst localAxiom)) .finalProof none 1 .audit
  require (finalAudit.failure.message == "unapproved axiom" &&
    finalAudit.site.kernelCeiling == some 10000000)
    "grouped final proof lost its dependency audit/planned ceiling"


private def proofCases (env : Kernel.Environment) (shared : Bool) : IO Unit := do
  let unknown := mkConst `PacketCheckFixture.missingRoot
  let decoding ← reject env {} truth (← encode shared [helper] unknown) .proofDecode none 1 .malformed
  let rootFailure ← reject env {} (mkConst ``False) (← encode shared [helper] intro)
    .finalProof none 1 .rejected
  require (rootFailure.site.kernelCeiling == some 10000000 &&
    rootFailure.site.decoderSteps > decoding.site.decoderSteps &&
    rootFailure.site.auditSteps == decoding.site.auditSteps)
    "final proof failure lost its successful prefix/ceiling"

  -- The contract says eight, independently of the encoded definition seven.
  -- Kernel reduction must account for the successor and replayed helper.
  let eight := mkRawNatLit 8
  let expected := mkApp3 (mkConst ``Eq [1]) nat eight eight
  let computed := mkApp (mkConst ``Nat.succ) (mkConst helperName)
  let proof := mkApp2 (mkConst ``Eq.refl [1]) nat computed
  let text ← encode shared [helper] proof
  let checked ← match checkPacketDetailed env {} expected text with
    | .ok checked => pure checked
    | .error failure => throw (IO.userError s!"independent arithmetic contract failed: {repr failure}")
  require (checked.declarations == 1 && checked.kernelChecks == 2 &&
    (checked.env.find? helperName).isSome && (env.find? helperName).isNone)
    "successful replay or isolated auxiliary environment was lost"
  let wrong := mkApp3 (mkConst ``Eq [1]) nat eight (mkRawNatLit 9)
  let _ ← reject env {} wrong text .finalProof none 1 .rejected
  pure ()

run_cmd do
  let env := (← getEnv).toKernelEnv
  beforePacket env
  for shared in [false, true] do
    declarationCases env shared
    proofCases env shared
  logInfo "Packet diagnostics: independent kernel/audit failures, declaration locations and isolated arithmetic replay passed"

end PacketCheckDiagnosticsTests
