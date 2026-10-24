/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Runtime.Packet
import EDSL.Grading.Runtime.Audit
import EDSL.Grading.Export.Preparation

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Client-side reconstruction of proof packets from compiled modules. This is
not a submission loader: only the client imports the requested module. The
grader separately supplies its fixed environment, task and artifact contract.

Names already present in the trusted snapshot remain references. Fresh safe
definitions, theorems, opaque declarations and simple nonnested inductive groups
are emitted in dependency order. Generated constructors and `.rec` constants
belong to their inductive group; other generated definitions are ordinary
dependencies. Mutual definitions, fresh axioms and nested inductives fail
explicitly. Source `partial` syntax can have safe opaque logical metadata; this
exporter, like the runtime, checks logical metadata rather than source history.
-/
namespace EDSLGrader.Export

open Lean EDSLGrader.Runtime

inductive Mode where
  | reference
  | body
  deriving BEq, Repr, Inhabited

/-- Client closure limits. The independent runtime applies its own packet,
expression, audit and kernel budgets when the exported data is submitted. -/
structure Limits where
  maxSteps : Nat := 100000
  maxDeclarations : Nat := 256
  maxOutputBytes : Nat := 4194304
  encoding : ClientEncodingLimits := {}

structure Packet where
  declarations : List Declaration
  value : Expr
  text : String
  /-- Includes constructors and generated recursors, not just packet entries. -/
  declaredNames : Nat
  discoverySteps : Nat

private def lookup (client : Kernel.Environment) (name : Name) : Except Failure ConstantInfo :=
  match client.find? name with
  | some info => pure info
  | none => fail .unsupported s!"client constant unavailable: {name}"

private def safeInfo (info : ConstantInfo) : Except Failure Unit := do
  if info.isUnsafe then return ← fail .audit s!"unsafe client constant: {info.name}"
  if info.isPartial then return ← fail .audit s!"partial client constant: {info.name}"

/-- Recover the entire kernel inductive group, including its original order,
universe parameters and parameter count. Constructor types supply the original
headers; no client constant is inserted into the trusted environment. -/
private def inductiveDeclaration (client : Kernel.Environment) (lim : Limits)
    (name : Name) : Except Failure Declaration := do
  let .inductInfo first ← lookup client name
    | fail .unsupported s!"inductive owner unavailable: {name}"
  if first.all.isEmpty then return ← fail .unsupported "empty inductive owner group"
  if first.all.length > lim.maxDeclarations then
    return ← fail .resource "client inductive group names"
  let mut types := []
  let mut names := 0
  for typeName in first.all do
    let info ← lookup client typeName
    safeInfo info
    let .inductInfo member := info
      | fail .unsupported s!"invalid inductive group member: {typeName}"
    if member.numNested != 0 then return ← fail .unsupported "nested client inductive group"
    if member.all != first.all || member.levelParams != first.levelParams ||
        member.numParams != first.numParams then
      return ← fail .unsupported "inconsistent client inductive group metadata"
    names := names + 2 + member.ctors.length
    if names > lim.maxDeclarations then return ← fail .resource "client inductive group names"
    let mut ctors := []
    for ctorName in member.ctors do
      let ctorInfo ← lookup client ctorName
      safeInfo ctorInfo
      let .ctorInfo ctor := ctorInfo
        | fail .unsupported s!"constructor unavailable: {ctorName}"
      if ctor.induct != member.name then return ← fail .unsupported "constructor owner mismatch"
      ctors := { name := ctor.name, type := ctor.type : Constructor } :: ctors
    types := ({ name := member.name, type := member.type, ctors := ctors.reverse } : InductiveType) :: types
  return .inductDecl first.levelParams first.numParams types.reverse false

private def reconstruct (client : Kernel.Environment) (lim : Limits)
    (info : ConstantInfo) : Except Failure Declaration := do
  safeInfo info
  match info with
  | .defnInfo value =>
    if value.all != [value.name] then return ← fail .unsupported "mutual client definitions"
    return .defnDecl value
  | .thmInfo value =>
    if value.all != [value.name] then return ← fail .unsupported "mutual client theorems"
    return .thmDecl value
  | .opaqueInfo value =>
    if value.all != [value.name] then return ← fail .unsupported "mutual client opaque declarations"
    return .opaqueDecl value
  | .inductInfo value => inductiveDeclaration client lim value.name
  | .ctorInfo value => inductiveDeclaration client lim value.induct
  | .recInfo value =>
    let some owner := value.all.head?
      | fail .unsupported s!"recursor owner unavailable: {value.name}"
    let decl ← inductiveDeclaration client lim owner
    unless decl.getNames.contains value.name do
      return ← fail .unsupported s!"noncanonical client recursor: {value.name}"
    return decl
  | .axiomInfo _ => fail .audit s!"fresh client axiom: {info.name}"
  | .quotInfo _ => fail .unsupported "fresh quotient primitives"

private inductive Work where
  | visit (name : Name)
  | emit (owner : Name) (decl : Declaration)

private structure Closure where
  completed : NameSet := {}
  /-- Each generated name is claimed by exactly one scheduled declaration. -/
  owners : NameMap Name := {}
  active : NameSet := {}
  declarations : Array Declaration := #[]
  declaredNames : Nat := 0
  steps : Nat := 0

/-- Include bodies, recursor rules and constructor/inductive owner edges. The
runtime audits these independently after checked reconstruction. -/
private def dependencies (client : Kernel.Environment) (decl : Declaration) :
    Except Failure (List Name) := do
  let mut deps : NameSet := {}
  for name in decl.getNames do
    let info ← lookup client name
    safeInfo info
    deps := deps ++ directDependencies info
  -- Group self-references are legal in inductive headers and recursor rules.
  let own : NameSet := .ofList decl.getNames
  return deps.toList.filter fun name => !own.contains name

/-- A bounded iterative DFS: groups are claimed before visiting dependencies,
and emitted afterwards. Completed names are never reconstructed twice. -/
private def discover (trusted client : Kernel.Environment) (lim : Limits) :
    Nat → List Work → Closure → Except Failure Closure
  | _, [], state => pure state
  | 0, _ :: _, _ => fail .resource "client dependency discovery steps"
  | fuel + 1, work :: rest, state => do
    let state := { state with steps := state.steps + 1 }
    match work with
    | .emit owner decl =>
      let completed := decl.getNames.foldl (fun seen name => seen.insert name) state.completed
      discover trusted client lim fuel rest { state with
        completed := completed
        active := state.active.erase owner
        declarations := state.declarations.push decl }
    | .visit name =>
      if (trusted.find? name).isSome || state.completed.contains name then
        return ← discover trusted client lim fuel rest state
      if let some owner := state.owners.find? name then
        if state.active.contains owner then
          return ← fail .unsupported s!"cyclic client declaration dependency: {name}"
        return ← fail .internal "incomplete client group traversal"
      let info ← lookup client name
      let decl ← reconstruct client lim info
      let declared := decl.getNames
      let some owner := declared.head? | fail .internal "empty reconstructed declaration"
      let count := state.declaredNames + declared.length
      if count > lim.maxDeclarations then return ← fail .resource "client declared constant names"
      let mut owners := state.owners
      for generated in declared do
        if generated.isAnonymous || certificationPrefix.isPrefixOf generated then
          return ← fail .unsupported s!"reserved client declaration name: {generated}"
        if (trusted.find? generated).isSome then
          return ← fail .unsupported s!"client group overlaps trusted names: {generated}"
        if owners.contains generated then return ← fail .unsupported "overlapping client groups"
        owners := owners.insert generated owner
      let deps ← dependencies client decl
      if deps.length > fuel then return ← fail .resource "client dependency discovery steps"
      discover trusted client lim fuel
        (deps.map Work.visit ++ .emit owner decl :: rest)
        { state with owners, active := state.active.insert owner, declaredNames := count }

/-- Export a closed monomorphic theorem reference, or its actual proof body.
The theorem's type is used only to discover auxiliary type dependencies. It is
never selected as a grading contract or advertised as successful grading.
Trusted names are identified by name; the grader replays all data against its
own installed snapshot and independently selected expected proposition. -/
def exportTheorem (trusted client : Kernel.Environment) (theoremName : Name)
    (mode : Mode := .reference) (lim : Limits := {}) : Except Failure Packet := do
  let .thmInfo target ← lookup client theoremName
    | fail .unsupported s!"export target is not a theorem: {theoremName}"
  if !target.levelParams.isEmpty then return ← fail .unsupported "polymorphic export theorem"
  if target.all != [target.name] then return ← fail .unsupported "mutual export theorem"
  let value := match mode with
    | .reference => mkConst theoremName
    | .body => target.value
  closed target.type
  closed value
  let roots := target.type.getUsedConstants.toList ++ value.getUsedConstants.toList
  let state ← discover trusted client lim lim.maxSteps (roots.map Work.visit) {}
  let declarations := state.declarations.toList
  let text ← encodePacketWith lim.encoding declarations value
  if text.utf8ByteSize > lim.maxOutputBytes then return ← fail .resource "client packet output bytes"
  return {
    declarations
    value
    text
    declaredNames := state.declaredNames
    discoverySteps := state.steps }

/-- Opt-in producer limits. Expression bounds apply to each walk; aggregate
bounds span map validation, roots and every emitted expression field. These
syntactic counters require the same external process bounds as preparation. -/
structure PreparedLimits where
  expression : Prepare.Limits := {}
  maxPreparationSteps : Nat := 2000000
  maxPreparationNameWork : Nat := 2000000
  maxPreparedFields : Nat := 4096

/-- Sums of validation metrics and successful expression walks. A field includes
one requested replacement RHS, root/type, or emitted type/value/header. Unique
counts sum per-walk structural keys; label replay can revisit syntax, so these
metrics do not assert linear, instruction, allocation or memory bounds. -/
structure PreparationStats where
  fields : Nat := 0
  steps : Nat := 0
  nameWork : Nat := 0
  unique : Nat := 0
  cacheHits : Nat := 0
  rebuilt : Nat := 0
  labelReplays : Nat := 0

/-- Complete untrusted producer data, available without encoding. Successful
closure discovery does not establish typing, preservation or runtime admission. -/
structure PreparedClosure where
  declarations : List Declaration
  value : Expr
  declaredNames : Nat
  discoverySteps : Nat
  preparation : PreparationStats

structure PreparedPacket extends Packet where
  preparation : PreparationStats

private def eligiblePreparationKey (trusted client : Kernel.Environment) (name : Name) : Bool :=
  if name.isAnonymous || certificationPrefix.isPrefixOf name || (trusted.find? name).isSome then
    false
  else
    match client.find? name with
    | some (.defnInfo original) =>
      original.name == name && original.safety == .safe &&
        original.levelParams.isEmpty && original.all == [name]
    | _ => false

private def remainingPreparationLimits (lim : PreparedLimits) (stats : PreparationStats) :
    Prepare.Limits :=
  { lim.expression with
    maxSteps := min lim.expression.maxSteps (lim.maxPreparationSteps - stats.steps)
    maxNameWork := min lim.expression.maxNameWork (lim.maxPreparationNameWork - stats.nameWork) }

private def preparationContext (lim : PreparedLimits) (stats : PreparationStats)
    (site : Prepare.FailureSite) (name : Name) (state : Option Prepare.State := none) : String :=
  Prepare.failureContext site name (remainingPreparationLimits lim stats)
    stats.fields stats.steps stats.nameWork state

/-- Validate exactly one immutable map. Even unused requests consume shared
field/name/work budgets; no candidate declaration supplies typing authority. -/
private def validatePreparation (trusted client : Kernel.Environment) (lim : PreparedLimits)
    (preparation : Prepare.Preparation) : Except Failure (Prepare.Tables × PreparationStats) := do
  let fields := preparation.definitionValues.size + preparation.inlineConstants.size
  if fields > lim.maxPreparedFields then return ← fail .resource "client preparation fields"
  let tables ← (Prepare.validate (remainingPreparationLimits lim {})
    (eligiblePreparationKey trusted client) preparation).mapError fun reason =>
      { kind := .unsupported, message := "client preparation map incomplete: " ++ reason }
  let stats : PreparationStats := {
    fields
    steps := tables.validationSteps
    nameWork := tables.validationNameWork
    unique := tables.validationUnique
    cacheHits := tables.validationCacheHits
    rebuilt := tables.validationRebuilt
    labelReplays := tables.validationLabelReplays }
  if stats.steps > lim.maxPreparationSteps || stats.nameWork > lim.maxPreparationNameWork then
    return ← fail .resource "client preparation aggregate validation work"
  return (tables, stats)

/-- Every field receives only the remaining shared fuel. Failed outcomes expose
only bounded site labels and scalar diagnostics, never partial expression data. -/
private def prepareField (lim : PreparedLimits) (stats : PreparationStats)
    (site : Prepare.FailureSite) (name : Name)
    (walk : Prepare.Limits → Prepare.Outcome) :
    Except Failure (Expr × Array Name × PreparationStats) := do
  if stats.fields >= lim.maxPreparedFields then
    return ← fail .resource ("client preparation fields" ++ preparationContext lim stats site name)
  if stats.steps >= lim.maxPreparationSteps then
    return ← fail .resource ("client preparation aggregate steps" ++ preparationContext lim stats site name)
  let outcome := walk (remainingPreparationLimits lim stats)
  let some output := outcome.output
    | fail .unsupported ("client expression preparation incomplete: " ++ outcome.reason ++
        preparationContext lim stats site name (some outcome.state))
  let next : PreparationStats := {
    fields := stats.fields + 1
    steps := stats.steps + outcome.state.steps
    nameWork := stats.nameWork + outcome.state.nameWork
    unique := stats.unique + outcome.state.memo.size
    cacheHits := stats.cacheHits + outcome.state.cacheHits
    rebuilt := stats.rebuilt + outcome.state.rebuilt
    labelReplays := stats.labelReplays + outcome.state.labelReplays }
  if next.steps > lim.maxPreparationSteps || next.nameWork > lim.maxPreparationNameWork then
    return ← fail .resource ("client preparation aggregate expression work" ++
      preparationContext lim stats site name (some outcome.state))
  return (output, outcome.state.references, next)

private def prepareExpression (lim : PreparedLimits) (tables : Prepare.Tables)
    (stats : PreparationStats) (site : Prepare.FailureSite) (name : Name)
    (e : Expr) (levelParams : List Name) :
    Except Failure (Expr × Array Name × PreparationStats) :=
  prepareField lim stats site name fun expressionLim =>
    Prepare.rewrite expressionLim tables.inlineConstants e levelParams

private def addPreparedReferences (seen : NameSet) (references : Array Name) : NameSet :=
  references.foldl (fun names name => names.insert name) seen

/-- Rebuild every emitted Expr field from its outcome, including types. Structure
updates retain all non-expression metadata and order. No alpha-equality shortcut
can silently retain an original type after substitution or label rebuilding. -/
private def prepareDeclaration (lim : PreparedLimits) (tables : Prepare.Tables)
    (stats : PreparationStats) (decl : Declaration) :
    Except Failure (Declaration × NameSet × PreparationStats) := do
  match decl with
  | .defnDecl original =>
    let (type, typeRefs, stats) ←
      prepareExpression lim tables stats .declarationType original.name original.type original.levelParams
    let (value, valueRefs, stats) ← prepareField lim stats .declarationValue original.name fun expressionLim =>
      Prepare.prepareDefinitionValue expressionLim tables original
    return (.defnDecl { original with type, value },
      addPreparedReferences (addPreparedReferences {} typeRefs) valueRefs, stats)
  | .thmDecl original =>
    let (type, typeRefs, stats) ←
      prepareExpression lim tables stats .declarationType original.name original.type original.levelParams
    let (value, valueRefs, stats) ←
      prepareExpression lim tables stats .declarationValue original.name original.value original.levelParams
    return (.thmDecl { original with type, value },
      addPreparedReferences (addPreparedReferences {} typeRefs) valueRefs, stats)
  | .opaqueDecl original =>
    let (type, typeRefs, stats) ←
      prepareExpression lim tables stats .declarationType original.name original.type original.levelParams
    let (value, valueRefs, stats) ←
      prepareExpression lim tables stats .declarationValue original.name original.value original.levelParams
    return (.opaqueDecl { original with type, value },
      addPreparedReferences (addPreparedReferences {} typeRefs) valueRefs, stats)
  | .inductDecl levelParams numParams types isUnsafe =>
    let mut stats := stats
    let mut references : NameSet := {}
    let mut preparedTypes : List InductiveType := []
    for member in types do
      let (type, refs, next) ←
        prepareExpression lim tables stats .inductiveHeader member.name member.type levelParams
      stats := next
      references := addPreparedReferences references refs
      let mut ctors : List Constructor := []
      for ctor in member.ctors do
        let (ctorType, refs, next) ←
          prepareExpression lim tables stats .constructorHeader ctor.name ctor.type levelParams
        stats := next
        references := addPreparedReferences references refs
        ctors := { ctor with type := ctorType } :: ctors
      preparedTypes := { member with type, ctors := ctors.reverse } :: preparedTypes
    return (.inductDecl levelParams numParams preparedTypes.reverse isUnsafe, references, stats)
  | _ => fail .internal "unsupported reconstructed prepared declaration"

/-- Preserve the original group's safety checks and ownership edges only.
Client recursor types/rules and original body dependencies are deliberately not
read: the independent kernel generates recursors from the prepared headers. -/
private def preparedOwnership (client : Kernel.Environment) (decl : Declaration) :
    Except Failure NameSet := do
  let mut deps : NameSet := {}
  for name in decl.getNames do
    let info ← lookup client name
    safeInfo info
    match info with
    | .inductInfo member =>
      for owner in member.all do deps := deps.insert owner
      for ctor in member.ctors do deps := deps.insert ctor
    | .ctorInfo ctor => deps := deps.insert ctor.induct
    | .recInfo recursor =>
      for owner in recursor.all do deps := deps.insert owner
    | _ => pure ()
  return deps

/-- Same group-claiming DFS as the original route, with dependency edges from
completed prepared fields and ownership metadata. Aggregate preparation state is
threaded through the entire traversal; no field/group resets it. -/
private def discoverPrepared (trusted client : Kernel.Environment) (lim : Limits)
    (preparedLim : PreparedLimits) (tables : Prepare.Tables) :
    Nat → List Work → Closure → PreparationStats →
      Except Failure (Closure × PreparationStats)
  | _, [], state, stats => pure (state, stats)
  | 0, _ :: _, _, _ => fail .resource "client dependency discovery steps"
  | fuel + 1, work :: rest, state, stats => do
    let state := { state with steps := state.steps + 1 }
    match work with
    | .emit owner decl =>
      let completed := decl.getNames.foldl (fun seen name => seen.insert name) state.completed
      discoverPrepared trusted client lim preparedLim tables fuel rest { state with
        completed := completed
        active := state.active.erase owner
        declarations := state.declarations.push decl } stats
    | .visit name =>
      if (trusted.find? name).isSome || state.completed.contains name then
        return ← discoverPrepared trusted client lim preparedLim tables fuel rest state stats
      if let some owner := state.owners.find? name then
        if state.active.contains owner then
          return ← fail .unsupported s!"cyclic client declaration dependency: {name}"
        return ← fail .internal "incomplete client group traversal"
      let info ← lookup client name
      let original ← reconstruct client lim info
      let declared := original.getNames
      let some owner := declared.head? | fail .internal "empty reconstructed declaration"
      let count := state.declaredNames + declared.length
      if count > lim.maxDeclarations then return ← fail .resource "client declared constant names"
      let mut owners := state.owners
      for generated in declared do
        if generated.isAnonymous || certificationPrefix.isPrefixOf generated then
          return ← fail .unsupported s!"reserved client declaration name: {generated}"
        if (trusted.find? generated).isSome then
          return ← fail .unsupported s!"client group overlaps trusted names: {generated}"
        if owners.contains generated then return ← fail .unsupported "overlapping client groups"
        owners := owners.insert generated owner
      let ownership ← preparedOwnership client original
      let (decl, references, stats) ← prepareDeclaration preparedLim tables stats original
      let own : NameSet := .ofList declared
      let deps := (references ++ ownership).toList.filter fun dependency => !own.contains dependency
      if deps.length > fuel then return ← fail .resource "client dependency discovery steps"
      discoverPrepared trusted client lim preparedLim tables fuel
        (deps.map Work.visit ++ .emit owner decl :: rest)
        { state with owners, active := state.active.insert owner, declaredNames := count } stats

/-- Bounded, opt-in closure preview with no encoder, environment installation,
inference, candidate evaluation or admission claim. The target type and selected
root are rewritten before root references are collected; every fresh declaration
is fully prepared before its dependencies are scheduled. Auxiliary fields use
that declaration's universe parameters; both root fields remain monomorphic.
The target type supplies discovery roots only, never the grading contract. -/
def discoverTheoremPrepared (trusted client : Kernel.Environment) (theoremName : Name)
    (preparation : Prepare.Preparation := {}) (mode : Mode := .reference) (lim : Limits := {})
    (preparedLim : PreparedLimits := {}) : Except Failure PreparedClosure := do
  let .thmInfo target ← lookup client theoremName
    | fail .unsupported s!"export target is not a theorem: {theoremName}"
  if !target.levelParams.isEmpty then return ← fail .unsupported "polymorphic export theorem"
  if target.all != [target.name] then return ← fail .unsupported "mutual export theorem"
  let (tables, stats) ← validatePreparation trusted client preparedLim preparation
  let (_, typeRefs, stats) ←
    prepareExpression preparedLim tables stats .rootType theoremName target.type []
  let sourceRoot := match mode with
    | .reference => mkConst theoremName
    | .body => target.value
  let (value, valueRefs, stats) ←
    prepareExpression preparedLim tables stats .rootValue theoremName sourceRoot []
  let roots := typeRefs.toList ++ valueRefs.toList
  let (state, stats) ← discoverPrepared trusted client lim preparedLim tables lim.maxSteps
    (roots.map Work.visit) {} stats
  return {
    declarations := state.declarations.toList
    value
    declaredNames := state.declaredNames
    discoverySteps := state.steps
    preparation := stats }

/-- Prepare the whole closure first, then apply the producer encoding profile and
output-byte limit. The grader must still check every emitted declaration and its
independently chosen root contract against its own immutable trusted snapshot. -/
def exportTheoremPrepared (trusted client : Kernel.Environment) (theoremName : Name)
    (preparation : Prepare.Preparation := {}) (mode : Mode := .reference) (lim : Limits := {})
    (preparedLim : PreparedLimits := {}) : Except Failure PreparedPacket := do
  let closure ← discoverTheoremPrepared trusted client theoremName preparation mode lim preparedLim
  let text ← encodePacketWith lim.encoding closure.declarations closure.value
  if text.utf8ByteSize > lim.maxOutputBytes then return ← fail .resource "client packet output bytes"
  return {
    declarations := closure.declarations
    value := closure.value
    text
    declaredNames := closure.declaredNames
    discoverySteps := closure.discoverySteps
    preparation := closure.preparation }

private structure RefinementBudget where
  steps : Nat
  preparation : PreparationStats

/-- Refinement also charges declaration/name-list and reference validation to
discovery fuel; supplied counters are starting costs, not authentication. -/
private def refinementStep (lim : Limits) (budget : RefinementBudget) :
    Except Failure RefinementBudget := do
  if budget.steps >= lim.maxSteps then
    return ← fail .resource "client refinement discovery steps"
  return { budget with steps := budget.steps + 1 }

/-- Match preparation's bounded name-component accounting without walking any
old expression field. Names are checked before name-set/environment lookups. -/
private def refinementName (lim : PreparedLimits) (budget : RefinementBudget) (name : Name) :
    Except Failure RefinementBudget := do
  let effective := remainingPreparationLimits lim budget.preparation
  let mut rest := name
  let mut work := 0
  for _ in [:effective.maxNameParts] do
    if work >= effective.maxNameWork then
      return ← fail .resource "client refinement name work"
    work := work + 1
    match rest with
    | .anonymous =>
      return { budget with preparation := { budget.preparation with
        nameWork := budget.preparation.nameWork + work } }
    | .str parent component =>
      if component.utf8ByteSize > effective.maxComponentBytes then
        return ← fail .resource "client refinement name component bytes"
      rest := parent
    | .num parent _ => rest := parent
  fail .resource "client refinement name parts"

private def refinementParameters (lim : Limits) (preparedLim : PreparedLimits)
    (budget : RefinementBudget) (params : List Name) : Except Failure RefinementBudget := do
  let mut budget := budget
  let mut seen : NameSet := {}
  for param in params do
    budget ← refinementStep lim budget
    if seen.size >= preparedLim.expression.maxLevelParams then
      return ← fail .resource "client refinement universe parameters"
    budget ← refinementName preparedLim budget param
    if param.isAnonymous || seen.contains param then
      return ← fail .malformed "invalid client refinement universe parameters"
    seen := seen.insert param
  return budget

private def refinementSingleton (lim : Limits) (preparedLim : PreparedLimits)
    (budget : RefinementBudget) (name : Name) (params all : List Name) :
    Except Failure RefinementBudget := do
  let budget ← refinementParameters lim preparedLim budget params
  let [member] := all
    | fail .unsupported "client refinement requires singleton declarations"
  let budget ← refinementStep lim budget
  let budget ← refinementName preparedLim budget member
  if member != name then return ← fail .malformed "client refinement singleton name mismatch"
  return budget

private def refinementPushName (lim : Limits) (preparedLim : PreparedLimits)
    (budget : RefinementBudget) (names : Array Name) (name : Name) :
    Except Failure (Array Name × RefinementBudget) := do
  let budget ← refinementStep lim budget
  if names.size >= lim.maxDeclarations then
    return ← fail .resource "client refinement declaration names"
  let budget ← refinementName preparedLim budget name
  return (names.push name, budget)

/-- Enumerate only producer-supported declaration shapes, bounding input lists
before calling getNames anywhere on the supplied closure. In particular an
inductive contributes its type, canonical recursor and constructor names. No old
type or proof is walked, compared with the client, or silently reconstructed. -/
private def refinementDeclarationNames (lim : Limits) (preparedLim : PreparedLimits)
    (budget : RefinementBudget) (decl : Declaration) :
    Except Failure (Array Name × RefinementBudget) := do
  let budget ← refinementStep lim budget
  match decl with
  | .defnDecl value =>
    if value.safety != .safe then return ← fail .audit "unsafe client refinement declaration"
    let budget ← refinementName preparedLim budget value.name
    let budget ← refinementSingleton lim preparedLim budget value.name value.levelParams value.all
    refinementPushName lim preparedLim budget #[] value.name
  | .thmDecl value =>
    let budget ← refinementName preparedLim budget value.name
    let budget ← refinementSingleton lim preparedLim budget value.name value.levelParams value.all
    refinementPushName lim preparedLim budget #[] value.name
  | .opaqueDecl value =>
    if value.isUnsafe then return ← fail .audit "unsafe client refinement declaration"
    let budget ← refinementName preparedLim budget value.name
    let budget ← refinementSingleton lim preparedLim budget value.name value.levelParams value.all
    refinementPushName lim preparedLim budget #[] value.name
  | .inductDecl params _ members isUnsafe =>
    if isUnsafe then return ← fail .audit "unsafe client refinement inductive"
    if members.isEmpty then return ← fail .malformed "empty client refinement inductive group"
    let mut budget ← refinementParameters lim preparedLim budget params
    let mut names : Array Name := #[]
    for member in members do
      let (next, charged) ← refinementPushName lim preparedLim budget names member.name
      names := next
      budget := charged
      let (next, charged) ←
        refinementPushName lim preparedLim budget names (member.name.appendCore `rec)
      names := next
      budget := charged
      for ctor in member.ctors do
        let (next, charged) ← refinementPushName lim preparedLim budget names ctor.name
        names := next
        budget := charged
    return (names, budget)
  | _ => fail .unsupported "unsupported supplied client refinement declaration"

private def refinementClaimNames (trusted : Kernel.Environment) (lim : Limits)
    (budget : RefinementBudget) (names : Array Name) (seen : NameSet)
    (owners : NameMap Name) (count : Nat) :
    Except Failure (NameSet × NameMap Name × Nat × RefinementBudget) := do
  let some owner := names[0]?
    | fail .malformed "empty client refinement declaration names"
  let mut budget := budget
  let mut seen := seen
  let mut owners := owners
  let mut count := count
  for name in names do
    budget ← refinementStep lim budget
    if count >= lim.maxDeclarations then
      return ← fail .resource "client refinement declared constant names"
    if name.isAnonymous || certificationPrefix.isPrefixOf name then
      return ← fail .unsupported "reserved client refinement declaration name"
    if (trusted.find? name).isSome then
      return ← fail .unsupported "client refinement overlaps trusted names"
    if seen.contains name || owners.contains name then
      return ← fail .malformed "duplicate or overlapping client refinement names"
    seen := seen.insert name
    owners := owners.insert name owner
    count := count + 1
  return (seen, owners, count, budget)

/-- Before discovery, unknown references may request fresh supports. Afterwards
only the trusted snapshot, strict old prefix, preceding new supports, and the
current supported inductive group's own names are available. -/
private def refinementReferences (trusted : Kernel.Environment) (lim : Limits)
    (preparedLim : PreparedLimits) (budget : RefinementBudget) (references : NameSet)
    (available : NameSet) (oldNames : NameSet) (allowFresh : Bool) :
    Except Failure RefinementBudget := do
  let mut budget := budget
  for reference in references.toList do
    budget ← refinementStep lim budget
    budget ← refinementName preparedLim budget reference
    if (trusted.find? reference).isSome || available.contains reference then continue
    if allowFresh && !oldNames.contains reference then continue
    return ← fail .unsupported "client refinement self, forward or unavailable reference"
  return budget

/-- Pure untrusted replacement of exactly one emitted fresh, safe, monomorphic
singleton theorem value. Its supplied prepared type is retained verbatim, even
when earlier preparation changed it from the client type. Every old declaration,
its order and metadata, and the root expression are retained; a missing emitted
theorem (including a body-mode root absent from declarations) fails explicitly.

The independently closed, monomorphic RHS uses empty substitution tables and
scope. Existing prepared names seed completed discovery, but are not an audit
preseed: references to the target or any later old entry are explicitly refused.
Fresh safe support declarations are reconstructed by the existing prepared DFS
with empty tables, then inserted immediately before the target in discovery
order. Supports may be polymorphic. Their actual types, values and ownership
edges must reference trusted names, the strict old prefix, or preceding supports;
only supported inductive groups may refer to their own generated names.

All supplied counters are untrusted starting costs. Actual old/new names are
counted and checked for duplicates, overlap and producer-supported metadata.
Input/prefix/reference validation consumes discovery fuel; key/metadata names,
the RHS and all support field walks consume cumulative preparation fuel. Support
fields are deliberately walked again for the final order check, and both walks
are charged. Old large expression fields are not rewalked. No original cost is
refunded. Native name/set/environment and getNames/ownership housekeeping still
require external process bounds; these counters are not a primitive resource
theorem. This preview does not encode, type-check, establish preservation, or
admit data. The independent kernel must check all supports, all retained entries
and the independently selected final proposition; encoding limits apply later. -/
def refineTheoremValue (trusted client : Kernel.Environment) (closure : PreparedClosure)
    (name : Name) (rhs : Expr) (lim : Limits := {}) (preparedLim : PreparedLimits := {}) :
    Except Failure PreparedClosure := do
  if closure.discoverySteps > lim.maxSteps || closure.declaredNames > lim.maxDeclarations then
    return ← fail .resource "client refinement supplied closure limits"
  if closure.preparation.fields > preparedLim.maxPreparedFields ||
      closure.preparation.steps > preparedLim.maxPreparationSteps ||
      closure.preparation.nameWork > preparedLim.maxPreparationNameWork then
    return ← fail .resource "client refinement supplied preparation limits"
  if preparedLim.expression.maxKeys == 0 then
    return ← fail .resource "client refinement key count"
  let mut budget : RefinementBudget := {
    steps := closure.discoverySteps, preparation := closure.preparation }
  budget ← refinementStep lim budget
  budget ← refinementName preparedLim budget name
  if name.isAnonymous || certificationPrefix.isPrefixOf name || (trusted.find? name).isSome then
    return ← fail .unsupported "ineligible client theorem refinement key"
  let info ← lookup client name
  safeInfo info
  let .thmInfo original := info
    | fail .unsupported "client refinement key is not a theorem"
  budget ← refinementName preparedLim budget original.name
  if original.name != name || !original.levelParams.isEmpty then
    return ← fail .unsupported "client refinement requires a matching monomorphic theorem"
  budget ← refinementSingleton lim preparedLim budget name original.levelParams original.all

  let mut oldNames : NameSet := {}
  let mut owners : NameMap Name := {}
  let mut availablePrefix : NameSet := {}
  let mut count := 0
  let mut before : List Declaration := []
  let mut after : List Declaration := []
  let mut target : Option TheoremVal := none
  for decl in closure.declarations do
    let (names, charged) ← refinementDeclarationNames lim preparedLim budget decl
    let (seen, claimed, actual, charged) ←
      refinementClaimNames trusted lim charged names oldNames owners count
    oldNames := seen
    owners := claimed
    count := actual
    budget := charged
    if names.contains name then
      let .thmDecl value := decl
        | fail .unsupported "emitted client refinement target is not a theorem"
      if value.name != original.name || value.levelParams != original.levelParams ||
          value.all != original.all then
        return ← fail .malformed "emitted client refinement theorem metadata mismatch"
      target := some value
    else if target.isNone then
      before := decl :: before
      for declared in names do availablePrefix := availablePrefix.insert declared
    else
      after := decl :: after
  if count != closure.declaredNames then
    return ← fail .malformed "client refinement supplied name count mismatch"
  let some targetValue := target
    | fail .unsupported "client refinement target is absent from emitted declarations"

  let tables : Prepare.Tables := {}
  let (value, references, stats) ← prepareField preparedLim budget.preparation
      .declarationValue name fun expressionLim => Prepare.rewrite expressionLim {} rhs []
  budget := { budget with preparation := stats }
  let roots := addPreparedReferences {} references
  budget ← refinementReferences trusted lim preparedLim budget roots availablePrefix oldNames true
  let initial : Closure := {
    completed := oldNames, owners, declaredNames := count, steps := budget.steps }
  let (discovered, stats) ← discoverPrepared trusted client lim preparedLim tables
    (lim.maxSteps - budget.steps) (references.toList.map Work.visit) initial budget.preparation
  budget := { steps := discovered.steps, preparation := stats }

  let mut available := availablePrefix
  let mut supports : List Declaration := []
  for support in discovered.declarations do
    let (names, charged) ← refinementDeclarationNames lim preparedLim budget support
    let (seen, claimed, actual, charged) ←
      refinementClaimNames trusted lim charged names oldNames owners count
    oldNames := seen
    owners := claimed
    count := actual
    budget := charged
    let (support, references, stats) ←
      prepareDeclaration preparedLim tables budget.preparation support
    budget := { budget with preparation := stats }
    let ownership ← preparedOwnership client support
    let own : NameSet := match support with
      | .inductDecl .. => .ofList names.toList
      | _ => {}
    budget ← refinementReferences trusted lim preparedLim budget (references ++ ownership)
      (available ++ own) oldNames false
    for declared in names do available := available.insert declared
    supports := support :: supports
  if count != discovered.declaredNames then
    return ← fail .internal "client refinement discovered name count mismatch"
  budget ← refinementReferences trusted lim preparedLim budget roots available oldNames false
  return {
    declarations := before.reverse ++ supports.reverse ++
      (.thmDecl { targetValue with value } :: after.reverse)
    value := closure.value
    declaredNames := count
    discoverySteps := budget.steps
    preparation := budget.preparation }

end EDSLGrader.Export
