/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export.Core
import EDSL.Grading.Runtime.Checker
import Lean.Util.Path
import tests.fixtures.GeneratedRefinementClient

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Integration tests for untrusted generated refinement syntax. The independent
contract is the functional statement ∀ n : Nat, n + 0 = n, constructed below
without reading a source theorem type or a generated payload claim. All replay
uses the real packet codec and checkPacketDetailed, including unused entries.
Compile the separate client fixture first; execution belongs to the parent. -/
namespace GeneratedRefinementTests
open Lean EDSLGrader EDSLGrader.Runtime

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap {α : Type} (result : Except Failure α) : IO α :=
  match result with
  | .ok value => pure value
  | .error failure => throw (IO.userError s!"unexpected generated refinement failure: {failure}")

private def reject {α : Type} (kind : FailureKind) (result : Except Failure α)
    (context : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError (context ++ ": unexpectedly accepted"))
  | .error failure => require (failure.kind == kind) s!"{context}: {failure}"

-- Name-validation failures need not share a diagnostic classification, but
-- resource exhaustion or an internal failure is not evidence of validation.
private def rejectName {α : Type} (result : Except Failure α) (context : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError (context ++ ": invalid generated name accepted"))
  | .error failure =>
    require (failure.kind == .malformed || failure.kind == .unsupported) s!"{context}: {failure}"

private def targetName : Name := `GeneratedRefinementFixture.aux
private def oldProofName : Name := `GeneratedRefinementFixture.oldProof
private def laterName : Name := `GeneratedRefinementFixture.later
private def rootName : Name := `GeneratedRefinementFixture.root
private def helperName : Name := `GeneratedRefinementFixture.keepWitness
private def identityName : Name := `GeneratedRefinementPayload.identity
private def baseName : Name := `GeneratedRefinementPayload.base
private def leftName : Name := `GeneratedRefinementPayload.left
private def rightName : Name := `GeneratedRefinementPayload.right
private def joinName : Name := `GeneratedRefinementPayload.join
private def unusedName : Name := `GeneratedRefinementPayload.unused
private def extraName : Name := `GeneratedRefinementPayload.nextUnused

private def nat : Expr := mkConst ``Nat
private def zero : Expr := mkRawNatLit 0
private def add (a b : Expr) : Expr := mkApp2 (mkConst ``Nat.add) a b
private def natEq (a b : Expr) : Expr := mkApp3 (mkConst ``Eq [Level.one]) nat a b
private def natRefl (a : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) nat a

private def contract : Expr :=
  .forallE `n nat (natEq (add (.bvar 0) zero) (.bvar 0)) .default

private def falseContract : Expr :=
  .forallE `n nat
    (natEq (add (.bvar 0) zero) (mkApp (mkConst ``Nat.succ) (.bvar 0))) .default

private def identityType : Expr := .forallE `argument nat nat .default
private def identityValue : Expr := .lam `identityInput nat (.bvar 0) .default

private def generatedGoal : Expr :=
  .forallE `candidateInput nat
    (natEq (add (mkApp (mkConst identityName) (.bvar 0)) zero) (.bvar 0)) .default

private def baseProof : Expr := .lam `baseInput nat (natRefl (.bvar 0)) .default

private def branchProof (type witness : Expr) : Expr :=
  mkApp4 (mkConst helperName [Level.one]) type witness generatedGoal (mkConst baseName)

private def joinProof : Expr :=
  let n : Expr := .bvar 0
  let a := add (mkApp (mkConst identityName) n) zero
  let left := mkApp (mkConst leftName) n
  let right := mkApp (mkConst rightName) n
  let reverse := mkApp4 (mkConst ``Eq.symm [Level.one]) nat a n right
  let roundTrip := mkApp6 (mkConst ``Eq.trans [Level.one]) nat n a n reverse right
  .lam `joinInput nat
    (mkApp6 (mkConst ``Eq.trans [Level.one]) nat a n n left roundTrip) .default

private def boolGoal : Expr :=
  .forallE `flag (mkConst ``Bool)
    (mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) (.bvar 0) (.bvar 0)) .default

private def boolProof : Expr :=
  .lam `flagProof (mkConst ``Bool)
    (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (.bvar 0)) .default

-- Request order is deliberately opposite the dependency order. Both branches
-- require the same base and fresh source helper, and join requires both branches.
-- unused has no path from the replacement proof, but must still be checked.
private def requests : Array Export.GeneratedSingleton := #[
  .thm joinName generatedGoal joinProof,
  .thm rightName generatedGoal (branchProof (mkConst ``Bool) (mkConst ``Bool.true)),
  .thm leftName generatedGoal (branchProof nat zero),
  .thm baseName generatedGoal baseProof,
  .defn identityName identityType identityValue,
  .thm unusedName boolGoal boolProof]

private def loadEnvironments : IO (Kernel.Environment × Kernel.Environment) := do
  initSearchPath (← findSysroot)
  let trusted ← importModules
    #[{ module := `EDSL.Grading.Export.Core },
      { module := `EDSL.Grading.Runtime.Checker }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  let client ← importModules #[{ module := `tests.fixtures.GeneratedRefinementClient }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  return (trusted.toKernelEnv, client.toKernelEnv)

private def hasName (closure : Export.PreparedClosure) (name : Name) : Bool :=
  closure.declarations.any fun decl => decl.getNames.contains name

private def ownerNames (closure : Export.PreparedClosure) : List Name :=
  closure.declarations.map fun decl => decl.getNames.headD Name.anonymous

private def theoremAt (closure : Export.PreparedClosure) (name : Name) : IO TheoremVal := do
  let some (.thmDecl value) := closure.declarations.find?
      (fun decl => decl.getNames.contains name)
    | throw (IO.userError s!"emitted theorem missing: {name}")
  pure value

private def encode (closure : Export.PreparedClosure) : IO String :=
  unwrap (encodePacket closure.declarations closure.value)

private def replay (trusted : Kernel.Environment) (closure : Export.PreparedClosure) : IO Checked := do
  let text ← encode closure
  match checkPacketDetailed trusted {} contract text with
  | .ok checked => pure checked
  | .error failure => throw (IO.userError s!"unexpected independent replay failure: {repr failure}")

private def refine (trusted client : Kernel.Environment) (closure : Export.PreparedClosure)
    (rhs : Expr) (generated : Array Export.GeneratedSingleton)
    (lim : Export.Limits := {}) (preparedLim : Export.PreparedLimits := {}) :
    Except Failure Export.PreparedClosure :=
  Export.refineTheoremValueWithGenerated trusted client closure targetName rhs generated lim preparedLim

-- Expr's BEq is alpha equivalence in pinned Lean. Expr.equal also compares
-- binder names/annotations. Metadata absent from the wire is compared explicitly.
private def retainedDeclaration (selected : Name) (old current : Declaration) : Bool :=
  match old, current with
  | .defnDecl a, .defnDecl b =>
    a.name == b.name && a.levelParams == b.levelParams && a.all == b.all &&
      a.safety == b.safety && a.hints == b.hints &&
      Expr.equal a.type b.type && Expr.equal a.value b.value
  | .thmDecl a, .thmDecl b =>
    a.name == b.name && a.levelParams == b.levelParams && a.all == b.all &&
      Expr.equal a.type b.type && (a.name == selected || Expr.equal a.value b.value)
  | .opaqueDecl a, .opaqueDecl b =>
    a.name == b.name && a.levelParams == b.levelParams && a.all == b.all &&
      a.isUnsafe == b.isUnsafe && Expr.equal a.type b.type && Expr.equal a.value b.value
  | .inductDecl ps np lhsTypes unsafeA, .inductDecl qs nq rhsTypes unsafeB =>
    ps == qs && np == nq && unsafeA == unsafeB && lhsTypes.length == rhsTypes.length &&
      (lhsTypes.zip rhsTypes).all fun (a, b) =>
        a.name == b.name && Expr.equal a.type b.type && a.ctors.length == b.ctors.length &&
          (a.ctors.zip b.ctors).all fun (ac, bc) =>
            ac.name == bc.name && Expr.equal ac.type bc.type
  | _, _ => false

private def oldEntriesPreserved (before after : Export.PreparedClosure)
    (selected : Name := targetName) : IO Unit := do
  require (Expr.equal before.value after.value) "refinement changed the selected root expression"
  let oldNames := before.declarations.flatMap fun decl => decl.getNames
  let retained := after.declarations.filter fun decl =>
    decl.getNames.any fun name => oldNames.contains name
  require (retained.length == before.declarations.length) "old declarations were dropped or duplicated"
  for (old, current) in before.declarations.zip retained do
    require (old.getNames == current.getNames) "old declaration order or names changed"
    require (retainedDeclaration selected old current)
      s!"old declaration fields/metadata changed: {old.getNames}"

private def payloadsPreserved (closure : Export.PreparedClosure)
    (generated : Array Export.GeneratedSingleton) : IO Unit := do
  for payload in generated do
    let emitted := closure.declarations.filter fun decl => decl.getNames.contains payload.name
    require (emitted.length == 1) s!"generated entry missing or duplicated: {payload.name}"
    match payload, emitted.head? with
    | .defn name type value, some (.defnDecl actual) =>
      require (actual.name == name && actual.levelParams.isEmpty && actual.all == [name] &&
        actual.safety == .safe && actual.hints == .regular 0 &&
        Expr.equal actual.type type && Expr.equal actual.value value)
        s!"generated definition was changed or given noncanonical metadata: {name}"
    | .thm name type proof, some (.thmDecl actual) =>
      require (actual.name == name && actual.levelParams.isEmpty && actual.all == [name] &&
        Expr.equal actual.type type && Expr.equal actual.value proof)
        s!"generated theorem was changed or given noncanonical metadata: {name}"
    | _, _ => throw (IO.userError s!"generated declaration kind changed: {payload.name}")

private def kernelRejectedAt (trusted : Kernel.Environment) (closure : Export.PreparedClosure)
    (name : Name) (context : String) : IO Unit := do
  let index := (ownerNames closure).idxOf name
  require (index < closure.declarations.length) (context ++ ": bad declaration was dropped")
  let text ← encode closure
  match checkPacketDetailed trusted {} contract text with
  | .ok _ => throw (IO.userError (context ++ ": invalid theorem accepted"))
  | .error failure =>
    require (failure.failure.kind == .rejected && failure.site.phase == .declarationKernel &&
      failure.site.entry == some index && failure.site.completedDeclarations == index)
      s!"{context}: expected declaration kernel refusal, got {repr failure}"

private def falseExpectedRejected (trusted : Kernel.Environment)
    (closure : Export.PreparedClosure) : IO Unit := do
  let text ← encode closure
  match checkPacketDetailed trusted {} falseContract text with
  | .ok _ => throw (IO.userError "packet selected its own final proposition")
  | .error failure =>
    require (failure.failure.kind == .rejected && failure.site.phase == .finalProof &&
      failure.site.completedDeclarations == closure.declarations.length)
      s!"false external contract: expected final kernel refusal, got {repr failure}"

-- Give the already-prepared target an alpha-equivalent but structurally
-- different binder label. Reloading its original source type would lose it.
private def relabelTarget (closure : Export.PreparedClosure) : Export.PreparedClosure :=
  { closure with declarations := closure.declarations.map fun decl =>
      match decl with
      | .thmDecl value =>
        if value.name == targetName then
          match value.type with
          | .forallE _ type body info =>
            .thmDecl { value with type := .forallE `retainedAuxInput type body info }
          | _ => decl
        else decl
      | _ => decl }

private def corruptOldProof (closure : Export.PreparedClosure) : Export.PreparedClosure :=
  { closure with declarations := closure.declarations.map fun decl =>
      match decl with
      | .thmDecl value =>
        if value.name == oldProofName then .thmDecl { value with value := mkConst ``True.intro }
        else decl
      | _ => decl }

private def placement (before after : Export.PreparedClosure) : IO Unit := do
  require (!(hasName before helperName) && hasName after helperName)
    "polymorphic source helper was not discovered as fresh support"
  let names := ownerNames after
  -- These are semantic dependency edges of the hand-written diamond, not an
  -- expected traversal order among otherwise independent siblings.
  for (dependency, use) in [(identityName, baseName), (baseName, leftName),
      (baseName, rightName), (helperName, leftName), (helperName, rightName),
      (leftName, joinName), (rightName, joinName)] do
    require (names.idxOf dependency < names.idxOf use)
      s!"support emitted after its use: {dependency} -> {use}"
  for name in helperName :: requests.toList.map (fun payload => payload.name) do
    require (names.idxOf oldProofName < names.idxOf name &&
      names.idxOf name < names.idxOf targetName)
      s!"new support not between old prefix and target: {name}"
  require (!(hasName after `GeneratedRefinementFixture.unrelated))
    "unrelated source theorem was emitted"

private def positiveCase (trusted client : Kernel.Environment) (before : Export.PreparedClosure) :
    IO Export.PreparedClosure := do
  let rhs := mkConst joinName
  let after ← unwrap <| refine trusted client before rhs requests
  oldEntriesPreserved before after
  payloadsPreserved after requests
  placement before after
  let target ← theoremAt after targetName
  require (Expr.equal target.value rhs) "target value was not replaced"
  require (after.preparation.fields > before.preparation.fields &&
    after.preparation.steps > before.preparation.steps &&
    after.preparation.nameWork > before.preparation.nameWork &&
    after.discoverySteps > before.discoverySteps)
    "successful refinement failed to accumulate actual costs"
  let checked ← replay trusted after
  for name in helperName :: requests.toList.map (fun payload => payload.name) do
    require ((checked.env.find? name).isSome) s!"support was not independently checked: {name}"
    require ((trusted.find? name).isNone) s!"replay changed the trusted snapshot: {name}"
  let some (.thmInfo helper) := checked.env.find? helperName
    | throw (IO.userError "checked source helper theorem missing")
  require (!helper.levelParams.isEmpty) "source helper lost its polymorphic declaration"
  falseExpectedRejected trusted after
  pure after

private def reuseCases (trusted client : Kernel.Environment) (first : Export.PreparedClosure) : IO Unit := do
  -- The second request refers to retained generated names that never appeared
  -- in client metadata. Its only supplied payload is a new, unused theorem.
  let next : Array Export.GeneratedSingleton := #[.thm extraName boolGoal boolProof]
  let second ← unwrap <| refine trusted client first (mkConst joinName) next
  oldEntriesPreserved first second
  payloadsPreserved second next
  let _ ← replay trusted second
  require ((client.find? joinName).isNone && (client.find? extraName).isNone)
    "generated prefix reuse depended on fabricated client metadata"
  rejectName (refine trusted client first (mkConst joinName) requests)
    "resubmitted names from an earlier generated prefix"
  -- The compatibility wrapper must likewise see retained generated supports.
  let compatibility ← unwrap <| Export.refineTheoremValue trusted client first targetName (mkConst joinName)
  oldEntriesPreserved first compatibility
  let _ ← replay trusted compatibility
  pure ()

private def kernelNegativeCases (trusted client : Kernel.Environment)
    (before : Export.PreparedClosure) : IO Unit := do
  let wrongIdentity := requests.map fun payload =>
    match payload with
    | .defn name type _ =>
      if name == identityName then
        .defn name type (.lam `identityInput nat (add (.bvar 0) (mkRawNatLit 1)) .default)
      else payload
    | _ => payload
  let changedFunction ← unwrap <| refine trusted client before (mkConst joinName) wrongIdentity
  payloadsPreserved changedFunction wrongIdentity
  -- n ↦ n+1 is a valid function definition. Its functional certificate is the
  -- first bad declaration; this must be a kernel failure rather than pruning.
  kernelRejectedAt trusted changedFunction baseName "identity mutated to successor"

  let wrongProof := requests.map fun payload =>
    match payload with
    | .thm name type _ =>
      if name == baseName then .thm name type (mkConst ``True.intro) else payload
    | _ => payload
  let changedProof ← unwrap <| refine trusted client before (mkConst joinName) wrongProof
  payloadsPreserved changedProof wrongProof
  kernelRejectedAt trusted changedProof baseName "wrong closed generated theorem proof"

  let badUnused := requests.map fun payload =>
    match payload with
    | .thm name type _ =>
      if name == unusedName then .thm name type (mkConst ``True.intro) else payload
    | _ => payload
  let unusedBad ← unwrap <| refine trusted client before (mkConst joinName) badUnused
  payloadsPreserved unusedBad badUnused
  kernelRejectedAt trusted unusedBad unusedName "unused invalid generated theorem"

  let tampered := corruptOldProof before
  let retainedBad ← unwrap <| refine trusted client tampered (mkConst joinName) requests
  oldEntriesPreserved tampered retainedBad
  payloadsPreserved retainedBad requests
  kernelRejectedAt trusted retainedBad oldProofName "unused corrupted old theorem"

private def nameCases (trusted client : Kernel.Environment)
    (before : Export.PreparedClosure) : IO Unit := do
  -- All invalid requests here are unused by rhs. Omitting their traversal or
  -- checking collisions only for discovered names would accept these cases.
  let rhs := mkConst oldProofName
  for name in [``Nat, helperName, oldProofName, `GeneratedRefinementFixture.Token,
      `GeneratedRefinementFixture.Token.unit, `GeneratedRefinementFixture.Token.rec,
      Name.anonymous, `EDSLGrader.Internal.generated] do
    for payload in [Export.GeneratedSingleton.defn name identityType identityValue,
        Export.GeneratedSingleton.thm name boolGoal boolProof] do
      rejectName (refine trusted client before rhs #[payload]) s!"unused generated name {name}"
  let duplicate : Array Export.GeneratedSingleton := #[
    .defn identityName identityType identityValue, .thm identityName boolGoal boolProof]
  rejectName (refine trusted client before rhs duplicate) "duplicate unused generated name"
  let sameKind : Array Export.GeneratedSingleton := #[
    .thm unusedName boolGoal boolProof, .thm unusedName boolGoal boolProof]
  rejectName (refine trusted client before rhs sameKind) "duplicate unused theorem request"

private def dependencyCases (trusted client : Kernel.Environment)
    (before : Export.PreparedClosure) : IO Unit := do
  let a := `GeneratedRefinementPayload.cycleA
  let b := `GeneratedRefinementPayload.cycleB
  let missing := `GeneratedRefinementPayload.missing
  -- Both fields must contribute edges, including a singleton's own name.
  let cases : List (String × Array Export.GeneratedSingleton) := [
    ("body self reference", #[.defn a identityType (mkConst a)]),
    ("type self reference", #[.defn a (mkConst a) identityValue]),
    ("two-name body cycle", #[.defn a identityType (mkConst b),
      .defn b identityType (mkConst a)]),
    ("type/body cycle", #[.defn a (mkConst b) identityValue,
      .defn b (.sort Level.one) (mkConst a)]),
    ("missing body dependency", #[.defn a identityType (mkConst missing)]),
    ("missing type dependency", #[.defn a (mkConst missing) identityValue])]
  for (context, generated) in cases do
    reject .unsupported (refine trusted client before (mkConst oldProofName) generated) context

  let inner := `GeneratedRefinementPayload.forwardInner
  let outer := `GeneratedRefinementPayload.forwardOuter
  for forbidden in [targetName, laterName] do
    let bodyChain : Array Export.GeneratedSingleton := #[
      .thm outer contract (mkConst inner), .thm inner contract (mkConst forbidden)]
    reject .unsupported (refine trusted client before (mkConst outer) bodyChain)
      s!"old target/suffix reached only through transitive generated body: {forbidden}"
    let typeChain : Array Export.GeneratedSingleton := #[
      .thm outer contract (mkConst inner),
      .thm inner (mkApp (mkConst `GeneratedRefinementFixture.proofIndexed) (mkConst forbidden))
        (mkConst oldProofName)]
    reject .unsupported (refine trusted client before (mkConst outer) typeChain)
      s!"old target/suffix reached only through transitive generated type: {forbidden}"

  -- Also cross the generated/source boundary, through two fresh source helpers.
  for (leaf, bridge, inType) in [
      (`GeneratedRefinementFixture.bodyForward, `GeneratedRefinementFixture.bodyForwardBridge, false),
      (`GeneratedRefinementFixture.typeForward, `GeneratedRefinementFixture.typeForwardBridge, true)] do
    require (!(hasName before leaf) && !(hasName before bridge)) "forward helper was not fresh"
    let some (.thmInfo info) := client.find? leaf
      | throw (IO.userError "forward source helper metadata missing")
    require ((info.type.getUsedConstants.contains laterName) == inType &&
      (info.value.getUsedConstants.contains laterName) == !inType)
      "forward helper failed to isolate its type/body dependency"
    let generated : Array Export.GeneratedSingleton := #[.thm outer contract (mkConst bridge)]
    reject .unsupported (refine trusted client before (mkConst outer) generated)
      s!"generated bridge reached old suffix through fresh source helper: {bridge}"

private def scopeCases (trusted client : Kernel.Environment)
    (before : Export.PreparedClosure) : IO Unit := do
  let name := `GeneratedRefinementPayload.scope
  let malformed : List (String × Expr) := [
    ("loose bound variable", .bvar 0),
    ("free variable", mkFVar ⟨`free⟩),
    ("expression metavariable", mkMVar ⟨`meta⟩),
    ("unbound universe", .sort (.param `unbound)),
    ("universe metavariable", .sort (.mvar ⟨`universeMeta⟩))]
  for (context, expression) in malformed do
    -- Unused payloads still require independent depth-zero field checks.
    for payload in [Export.GeneratedSingleton.defn name expression identityValue,
        Export.GeneratedSingleton.defn name nat expression] do
      reject .unsupported (refine trusted client before (mkConst oldProofName) #[payload]) context
  let shared : Expr := .bvar 0
  let bound := Expr.lam `inside nat shared .default
  let escaped := mkApp bound shared
  -- The same Expr is valid in the function's binder and invalid in its argument.
  -- This requires checking scope again after a successful memo hit.
  reject .unsupported (refine trusted client before (mkConst oldProofName)
    #[.defn name nat escaped]) "cached bound variable reused outside its binder"
  reject .unsupported (refine trusted client before (mkConst oldProofName)
    #[.defn name escaped identityValue]) "cached out-of-scope expression in a type"

private def eligibilityCases (trusted client : Kernel.Environment)
    (before : Export.PreparedClosure) (mode : Export.Mode) : IO Unit := do
  for name in [`GeneratedRefinementFixture.missing, `GeneratedRefinementFixture.unrelated,
      `GeneratedRefinementFixture.proofIndexed, `GeneratedRefinementFixture.throughToken,
      helperName, ``True.intro, identityName, joinName] do
    reject .unsupported (Export.refineTheoremValueWithGenerated trusted client before name
      (mkConst oldProofName) requests) s!"ineligible generated refinement target {name}"
  if mode == .body then
    reject .unsupported (Export.refineTheoremValueWithGenerated trusted client before rootName
      (mkConst joinName) requests) "body-mode root absent from emitted declarations"
  reject .unsupported (refine trusted client before (mkConst targetName) #[]) "replacement self reference"
  reject .unsupported (refine trusted client before (mkConst laterName) #[]) "replacement old forward reference"

private def arityCase (trusted client : Kernel.Environment)
    (before : Export.PreparedClosure) : IO Unit := do
  -- Preparation is syntactic: universe arity remains the independent decoder's
  -- responsibility. A monomorphic generated constant is used with one level.
  let after ← unwrap <| refine trusted client before (mkConst joinName [Level.one]) requests
  let index := (ownerNames after).idxOf targetName
  let text ← encode after
  match checkPacketDetailed trusted {} contract text with
  | .ok _ => throw (IO.userError "independent decoder accepted generated constant universe arity")
  | .error failure =>
    require (failure.failure.kind == .malformed && failure.site.phase == .declarationDecode &&
      failure.site.entry == some index && failure.site.completedDeclarations == index)
      s!"generated constant universe arity: wrong refusal site {repr failure}"

private def generousLimits : Export.Limits := { maxSteps := 10000000, maxDeclarations := 4096 }
private def generousPreparation : Export.PreparedLimits := {
  maxPreparationSteps := 20000000, maxPreparationNameWork := 20000000, maxPreparedFields := 100000 }

private def cumulativeBudgetCases (trusted client : Kernel.Environment)
    (before first : Export.PreparedClosure) : IO Unit := do
  -- Each exact cap comes from a successful complete request. The unrelated
  -- aggregate limits are generous. No expected DFS or expression counts are
  -- reproduced here, and the second request includes another unused payload.
  let caps : List (String × Export.Limits × Export.PreparedLimits) := [
    ("fields", generousLimits,
      { generousPreparation with maxPreparedFields := first.preparation.fields }),
    ("discovery", { generousLimits with maxSteps := first.discoverySteps }, generousPreparation),
    ("name work", generousLimits,
      { generousPreparation with maxPreparationNameWork := first.preparation.nameWork }),
    ("preparation steps", generousLimits,
      { generousPreparation with maxPreparationSteps := first.preparation.steps })]
  let next : Array Export.GeneratedSingleton := #[.thm extraName boolGoal boolProof]
  for (context, limits, preparation) in caps do
    let bounded ← unwrap <| refine trusted client before (mkConst joinName) requests limits preparation
    let _ ← replay trusted bounded
    reject .resource (refine trusted client bounded (mkConst joinName) next limits preparation)
      ("repeated request reset/refunded shared " ++ context)
  let exact : Export.Limits := { generousLimits with maxDeclarations := first.declaredNames }
  let bounded ← unwrap <| refine trusted client before (mkConst joinName) requests exact generousPreparation
  let _ ← replay trusted bounded
  let noNew : Export.Limits := { generousLimits with maxDeclarations := before.declaredNames }
  reject .resource (refine trusted client before (mkConst joinName) requests noNew generousPreparation)
    "declared-name cap permitting no new names"
  reject .resource (refine trusted client before (mkConst oldProofName)
    #[.thm unusedName boolGoal boolProof] noNew generousPreparation)
    "unused generated entry evaded the declared-name cap"

private def freshSourceGroupCase (trusted client : Kernel.Environment)
    (before : Export.PreparedClosure) : IO Unit := do
  let tree := `GeneratedRefinementFixture.FreshTree
  let leaf := `GeneratedRefinementFixture.FreshTree.leaf
  let branch := `GeneratedRefinementFixture.FreshTree.branch
  let recursor := `GeneratedRefinementFixture.FreshTree.rec
  let sourceNames := [tree, recursor, leaf, branch]
  let valueName := `GeneratedRefinementPayload.freshTree
  for name in sourceNames do
    require (!(hasName before name) && (trusted.find? name).isNone &&
      (client.find? name).isSome) s!"fresh source group was not isolated: {name}"
  require ((client.find? valueName).isNone && (trusted.find? valueName).isNone)
    "fresh generated tree value already existed"
  let payload : Array Export.GeneratedSingleton := #[.defn valueName (mkConst tree)
    (mkApp2 (mkConst branch) (mkConst leaf) (mkConst leaf))]
  let after ← unwrap <| refine trusted client before (mkConst oldProofName) payload
  oldEntriesPreserved before after
  payloadsPreserved after payload
  let names := ownerNames after
  for name in sourceNames do
    require (hasName after name) s!"source group omitted a canonical name: {name}"
  require (names.idxOf tree < names.idxOf valueName && names.idxOf valueName < names.idxOf targetName)
    "fresh source group or generated value followed its use"
  let checked ← replay trusted after
  for name in valueName :: sourceNames do
    require ((checked.env.find? name).isSome) s!"fresh source group/value not checked: {name}"
  -- The supported group has a type, canonical recursor and two constructors.
  -- One generated definition requires five new logical names, independently
  -- of the producer's returned count or traversal order.
  let exact : Export.Limits := { maxDeclarations := before.declaredNames + 5 }
  let bounded ← unwrap <| refine trusted client before (mkConst oldProofName) payload exact
  let _ ← replay trusted bounded
  for allowance in [1, 4] do
    let short : Export.Limits := { maxDeclarations := before.declaredNames + allowance }
    reject .resource (refine trusted client before (mkConst oldProofName) payload short)
      "name cap admitted registry payload but omitted required source-group names"

private def refinementCases (trusted client : Kernel.Environment) : IO Unit := do
  for mode in [Export.Mode.reference, .body] do
    let discovered ← unwrap <| Export.discoverTheoremPrepared trusted client rootName {} mode
    let before := relabelTarget discovered
    for name in [oldProofName, targetName, laterName, `GeneratedRefinementFixture.Token,
        `GeneratedRefinementFixture.Token.unit, `GeneratedRefinementFixture.Token.rec] do
      require (hasName before name) s!"original source closure omitted a required old name: {name}"
    require (hasName before rootName == (mode == .reference)) "source discovery root mode changed"
    let names := ownerNames before
    require (names.idxOf oldProofName < names.idxOf targetName &&
      names.idxOf targetName < names.idxOf laterName) "old proof/aux/later chain was not present"
    let original ← theoremAt discovered targetName
    let prepared ← theoremAt before targetName
    require (!(Expr.equal original.type prepared.type)) "target type label was not changed before refinement"
    let _ ← replay trusted before

    let first ← positiveCase trusted client before
    reuseCases trusted client first
    kernelNegativeCases trusted client before
    nameCases trusted client before
    dependencyCases trusted client before
    scopeCases trusted client before
    eligibilityCases trusted client before mode
    if mode == .reference then
      -- In reference mode the root itself is emitted and remains eligible.
      let atRoot ← unwrap <| Export.refineTheoremValueWithGenerated trusted client before rootName
        (mkConst joinName) requests
      oldEntriesPreserved before atRoot rootName
      payloadsPreserved atRoot requests
      let _ ← replay trusted atRoot
      arityCase trusted client before
      cumulativeBudgetCases trusted client before first
      freshSourceGroupCase trusted client before

def main : IO Unit := do
  let (trusted, client) ← loadEnvironments
  for name in [rootName, targetName, oldProofName, laterName, helperName,
      `GeneratedRefinementFixture.Token, `GeneratedRefinementFixture.Token.unit,
      `GeneratedRefinementFixture.Token.rec, `GeneratedRefinementFixture.throughToken,
      `GeneratedRefinementFixture.proofIndexed, `GeneratedRefinementFixture.typeForward,
      `GeneratedRefinementFixture.typeForwardBridge, `GeneratedRefinementFixture.bodyForward,
      `GeneratedRefinementFixture.bodyForwardBridge, `GeneratedRefinementFixture.unrelated] do
    require ((trusted.find? name).isNone && (client.find? name).isSome)
      s!"client fixture/helper isolation failed: {name}"
  for name in extraName :: requests.toList.map (fun payload => payload.name) do
    require ((trusted.find? name).isNone && (client.find? name).isNone)
      s!"generated payload already existed in environment metadata: {name}"
  refinementCases trusted client
  IO.println "GeneratedRefinement: independent functional replay, generated scheduling/reuse, retained entries, rejection boundaries and shared budgets passed"

#eval main
end GeneratedRefinementTests
