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

/-! Refinement is an untrusted syntax operation. These checks encode its whole
result and replay all old and new declarations against an independent contract.
Compile tests.fixtures.PreparedRefinementClient separately first. -/
namespace PreparedRefinementTests
open Lean EDSL EDSLGrader EDSLGrader.Runtime

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap {α : Type} (result : Except Failure α) : IO α :=
  match result with
  | .ok value => pure value
  | .error failure => throw (IO.userError s!"unexpected refinement/replay failure: {failure}")

private def reject {α : Type} (kind : FailureKind) (result : Except Failure α)
    (context : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError (context ++ ": unexpectedly accepted"))
  | .error failure => require (failure.kind == kind) s!"{context}: {failure}"

private def helperName : Name := `EDSLGrader.Export.ByteLength.appendLength
private def targetName : Name := `PreparedRefinementFixture.aux
private def oldProofName : Name := `PreparedRefinementFixture.oldLengthProof
private def rootName : Name := `PreparedRefinementFixture.root

-- These observed bytes differ from the fixture's original source. The expected
-- length below is the fixed numeral 33, independently of all producer metrics.
private def observed : List X86.Byte :=
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,
   17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]

private def expected : Expr :=
  let length := mkApp2 (mkConst ``List.length [Level.zero])
    (toTypeExpr X86.Byte) (toExpr observed)
  mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat) length (toExpr (33 : Nat))

private def loadEnvironments : IO (Kernel.Environment × Kernel.Environment) := do
  initSearchPath (← findSysroot)
  let trusted ← importModules
    #[{ module := `EDSL.Grading.Export.Core },
      { module := `EDSL.Grading.Runtime.Checker }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  let client ← importModules #[{ module := `tests.fixtures.PreparedRefinementClient }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  return (trusted.toKernelEnv, client.toKernelEnv)

private def hasName (closure : Export.PreparedClosure) (name : Name) : Bool :=
  closure.declarations.any fun decl => decl.getNames.contains name

private def ownerNames (closure : Export.PreparedClosure) : List Name :=
  closure.declarations.map fun decl => decl.getNames.headD Name.anonymous

private def encode (closure : Export.PreparedClosure) : IO String :=
  unwrap (encodePacket closure.declarations closure.value)

private def replay (trusted : Kernel.Environment) (closure : Export.PreparedClosure) : IO Checked := do
  unwrap (checkPacket trusted {} expected (← encode closure))

private def generatedProof (closure : Export.PreparedClosure) : IO Expr := do
  let some (.defnDecl file) := closure.declarations.find?
      (fun decl => decl.getNames.contains `PreparedRefinementFixture.file)
    | throw (IO.userError "prepared file definition missing")
  match Export.ByteLength.fromQuotation 33 file.value with
  | .ok candidate => pure candidate.proof
  | .error reason => throw (IO.userError ("length syntax construction failed: " ++ reason))

-- Compare retained old entries in their original order, rather than deriving
-- an expected closure by rerunning dependency discovery or proof construction.
private def oldEntriesPreserved (before after : Export.PreparedClosure) : IO Unit := do
  require (after.value == before.value) "refinement changed the selected root expression"
  let oldNames := before.declarations.flatMap fun decl => decl.getNames
  let retained := after.declarations.filter fun decl =>
    decl.getNames.any fun name => oldNames.contains name
  require (retained.length == before.declarations.length) "old declarations were dropped or duplicated"
  for (old, current) in before.declarations.zip retained do
    require (old.getNames == current.getNames) "refinement reordered or renamed old declarations"
    match old, current with
    | .defnDecl a, .defnDecl b =>
      require (a.name == b.name && a.levelParams == b.levelParams && a.all == b.all &&
        a.safety == b.safety && a.hints == b.hints && a.type == b.type && a.value == b.value)
        s!"old definition changed: {a.name}"
    | .thmDecl a, .thmDecl b =>
      require (a.name == b.name && a.levelParams == b.levelParams && a.all == b.all &&
        a.type == b.type) s!"old theorem metadata/type changed: {a.name}"
      if a.name != targetName then
        require (a.value == b.value) s!"unselected old theorem value changed: {a.name}"
    | _, _ => throw (IO.userError "fixture declaration kind changed")

private def supportPlacement (before after : Export.PreparedClosure) : IO Unit := do
  require (!(hasName before helperName) && hasName after helperName)
    "generic helper was not discovered as fresh support"
  let names := ownerNames after
  require (names.idxOf helperName + 1 == names.idxOf targetName)
    "fresh generic helper was not inserted immediately before its use"
  for name in [`PreparedRefinementFixture.unrelated,
      `EDSLGrader.Export.ByteLength.quoteWithLength,
      `EDSLGrader.Export.ByteLength.fromQuotation] do
    require (!(hasName after name)) s!"unneeded support was emitted: {name}"

private def kernelRejectedAt (trusted : Kernel.Environment) (closure : Export.PreparedClosure)
    (name : Name) (context : String) : IO Unit := do
  let index := (ownerNames closure).idxOf name
  require (index < closure.declarations.length) (context ++ ": expected retained declaration missing")
  let text ← encode closure
  match checkPacketDetailed trusted {} expected text with
  | .ok _ => throw (IO.userError (context ++ ": bad declaration accepted"))
  | .error failure =>
    require (failure.failure.kind == .rejected && failure.site.phase == .declarationKernel &&
      failure.site.entry == some index && failure.site.completedDeclarations == index)
      s!"{context}: expected declaration kernel rejection, got {repr failure}"

private def corruptOldProof (closure : Export.PreparedClosure) : Export.PreparedClosure :=
  { closure with declarations := closure.declarations.map fun decl =>
      match decl with
      | .thmDecl value =>
        if value.name == oldProofName then .thmDecl { value with value := mkConst ``True.intro }
        else decl
      | _ => decl }

private def eligibilityCases (trusted client : Kernel.Environment)
    (closure : Export.PreparedClosure) (mode : Export.Mode) : IO Unit := do
  for key in [`PreparedRefinementFixture.missing, `PreparedRefinementFixture.file,
      ``True.intro, `EDSLGrader.Internal.refinement, `PreparedRefinementFixture.poly] do
    reject .unsupported (Export.refineTheoremValue trusted client closure key (mkConst ``True.intro))
      s!"ineligible refinement key {key}"
  if mode == .body then
    reject .unsupported (Export.refineTheoremValue trusted client closure rootName
      (mkConst ``True.intro)) "body-mode root absent from emitted declarations"
  reject .unsupported (Export.refineTheoremValue trusted client closure targetName
    (mkConst targetName)) "self-reference"
  reject .unsupported (Export.refineTheoremValue trusted client closure targetName
    (mkConst `PreparedRefinementFixture.later)) "old forward theorem reference"
  reject .unsupported (Export.refineTheoremValue trusted client closure targetName
    (.bvar 0)) "unscoped bound variable"
  reject .unsupported (Export.refineTheoremValue trusted client closure targetName
    (.sort (.param `unbound))) "undeclared replacement universe"

private def fieldBudgetCase (trusted client : Kernel.Environment)
    (before first : Export.PreparedClosure) (rhs : Expr) : IO Unit := do
  -- Use the completed request's reported cost as a cap, not a hand-coded copy
  -- of its walk count. Replaying that request must fit; an additional request
  -- must charge more fields even when its helper already exists in the closure.
  let shared : Export.PreparedLimits := { maxPreparedFields := first.preparation.fields }
  let bounded ← unwrap <| Export.refineTheoremValue trusted client before targetName rhs {} shared
  let _ ← replay trusted bounded
  reject .resource (Export.refineTheoremValue trusted client bounded targetName rhs {} shared)
    "repeated refinement reset or refunded the exhausted cumulative field allowance"

private def discoveryBudgetCase (trusted client : Kernel.Environment)
    (before first : Export.PreparedClosure) (rhs : Expr) : IO Unit := do
  -- Calibrate against a successful request, without reproducing its fuel walk.
  -- The same request fits from before; another request must consume more fuel.
  let shared : Export.Limits := { maxSteps := first.discoverySteps }
  let bounded ← unwrap <| Export.refineTheoremValue trusted client before targetName rhs shared
  let _ ← replay trusted bounded
  reject .resource (Export.refineTheoremValue trusted client bounded targetName rhs shared)
    "repeated refinement reset or refunded exhausted cumulative discovery fuel"

private def freshSupportCases (trusted client : Kernel.Environment)
    (before : Export.PreparedClosure) : IO Unit := do
  let firstName := `PreparedRefinementFixture.freshLengthProof
  let secondName := `PreparedRefinementFixture.freshLengthBridge
  let bodyForward := `PreparedRefinementFixture.bodyForward
  let typeForward := `PreparedRefinementFixture.typeForward
  let laterName := `PreparedRefinementFixture.later
  for name in [firstName, secondName, bodyForward, typeForward,
      `PreparedRefinementFixture.indexedLength] do
    require (!(hasName before name) && (trusted.find? name).isNone)
      s!"fresh-support case already existed in the old closure/snapshot: {name}"

  -- Requiring a chain, rather than one helper, checks that discovery emits each
  -- dependency before its use. Kernel replay independently checks the result.
  let chainRhs := mkConst secondName
  let chain ← unwrap <| Export.refineTheoremValue trusted client before targetName chainRhs
  oldEntriesPreserved before chain
  require (hasName chain firstName && hasName chain secondName)
    "transitive fresh-support chain was not emitted"
  let names := ownerNames chain
  require (names.idxOf firstName < names.idxOf secondName &&
    names.idxOf secondName < names.idxOf targetName)
    "transitive fresh-support chain was emitted after one of its uses"
  let _ ← replay trusted chain

  -- The returned boundary admits this complete chain, while the old closure's
  -- boundary cannot admit its required fresh declarations. No manually copied
  -- dependency-discovery count is used as the oracle.
  let exact : Export.Limits := { maxDeclarations := chain.declaredNames }
  let bounded ← unwrap <| Export.refineTheoremValue trusted client before targetName chainRhs exact
  let _ ← replay trusted bounded
  let noFresh : Export.Limits := { maxDeclarations := before.declaredNames }
  reject .resource (Export.refineTheoremValue trusted client before targetName chainRhs noFresh)
    "fresh-support chain exceeded the declared-name allowance"

  -- These fixture preconditions distinguish the two failure paths: removing
  -- body-reference validation or type-reference validation must be observable.
  let some (.thmInfo bodyInfo) := client.find? bodyForward
    | throw (IO.userError "body-forward helper metadata missing")
  let some (.thmInfo typeInfo) := client.find? typeForward
    | throw (IO.userError "type-forward helper metadata missing")
  require (bodyInfo.value.getUsedConstants.contains laterName &&
    !(bodyInfo.type.getUsedConstants.contains laterName))
    "body-forward fixture did not isolate the later reference in its value"
  require (typeInfo.type.getUsedConstants.contains laterName &&
    !(typeInfo.value.getUsedConstants.contains laterName))
    "type-forward fixture did not isolate the later reference in its type"
  reject .unsupported (Export.refineTheoremValue trusted client before targetName
    (mkConst bodyForward)) "fresh helper body reached an old forward theorem"
  reject .unsupported (Export.refineTheoremValue trusted client before targetName
    (mkConst typeForward)) "fresh helper type reached an old forward theorem"

private def refinementCases (trusted client : Kernel.Environment) : IO Unit := do
  let preparation : Export.Prepare.Preparation := {
    definitionValues := #[(`PreparedRefinementFixture.file, byteExpr observed)]
    inlineConstants := #[(`PreparedRefinementFixture.expectedCount, toExpr (33 : Nat))] }
  for mode in [Export.Mode.reference, .body] do
    let before ← unwrap <| Export.discoverTheoremPrepared trusted client rootName preparation mode
    require (hasName before oldProofName && hasName before targetName &&
      hasName before `PreparedRefinementFixture.later && hasName before `PreparedRefinementFixture.poly)
      "fixture did not retain the old proof, refinement target and forward/poly theorems"
    require (hasName before rootName == (mode == .reference)) "export root mode changed"
    require (!(hasName before `PreparedRefinementFixture.original))
      "overridden file retained its original source dependency"
    let _ ← replay trusted before

    let some (.thmDecl preparedTarget) := before.declarations.find?
        (fun decl => decl.getNames.contains targetName)
      | throw (IO.userError "prepared refinement target missing")
    let some (.thmInfo originalTarget) := client.find? targetName
      | throw (IO.userError "original refinement target missing")
    require (!(preparedTarget.type == originalTarget.type))
      "inline preparation did not exercise a changed target type"
    let rhs ← generatedProof before
    let after ← unwrap <| Export.refineTheoremValue trusted client before targetName rhs
    oldEntriesPreserved before after
    supportPlacement before after
    let checked ← replay trusted after
    let some (.thmInfo _) := checked.env.find? helperName
      | throw (IO.userError "new helper was not checked as an ordinary declaration")
    require ((trusted.find? helperName).isNone) "checked helper leaked into the trusted snapshot"

    -- Both terms are closed syntax. Refinement must accept them without claiming
    -- typing, and the independent checker must reject the changed auxiliary.
    let wrongTruth ← unwrap <| Export.refineTheoremValue trusted client before targetName
      (mkConst ``True.intro)
    kernelRejectedAt trusted wrongTruth targetName "closed proof of True in length theorem"
    let wrongNumeral := mkApp2 (mkConst ``Eq.refl [Level.one])
      (mkConst ``Nat) (toExpr (34 : Nat))
    let wrongLength ← unwrap <| Export.refineTheoremValue trusted client before targetName wrongNumeral
    kernelRejectedAt trusted wrongLength targetName "closed proof for the wrong numeral"

    -- The replacement no longer uses oldLengthProof. Its corrupted old value
    -- must survive refinement and still be checked, rather than being pruned or
    -- silently restored from the client environment.
    let tampered := corruptOldProof before
    let retainedBad ← unwrap <| Export.refineTheoremValue trusted client tampered targetName rhs
    oldEntriesPreserved tampered retainedBad
    kernelRejectedAt trusted retainedBad oldProofName "unused corrupted old proof was retained"

    eligibilityCases trusted client before mode
    freshSupportCases trusted client before
    if mode == .reference then
      fieldBudgetCase trusted client before after rhs
      discoveryBudgetCase trusted client before after rhs

def main : IO Unit := do
  let (trusted, client) ← loadEnvironments
  require ((trusted.find? rootName).isNone && (trusted.find? helperName).isNone)
    "client fixture/helper entered the trusted replay snapshot"
  require ((client.find? rootName).isSome && (client.find? helperName).isSome)
    "separately compiled client metadata missing"
  refinementCases trusted client
  IO.println "PreparedRefinement: independent checked replay, retained entries, transitive support order, forward-reference failures and cumulative budgets passed"

#eval main
end PreparedRefinementTests
