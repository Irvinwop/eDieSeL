/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Lean
import EDSL.Grading.Runtime.Audit
import EDSL.Corpus.V1.CounterProofBundle
import EDSL.Corpus.V1.CounterCompletion

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Architecture regression over actual declaration types, values and generated
inductive/recursor metadata, using the production direct-dependency collector.
Both compiler families are imported together: imports alone are not edges.

Each direct proof bundle must retain its own instruction and independent rank
proofs without reaching the other compiler's behavior. Generic consumers of an
arbitrary bundle or ProvedSubject must not select compiler proofs themselves.
Shared compiler-indexed graph data and small ELF table hints remain allowed;
only the compiler-independent RankedEntry core excludes all corpus namespaces.

The old checkedRules dispatcher is a positive control for both behavior
namespaces. These checks concern declaration-closure architecture, not proof
acceptance, execution, or isolation of a final canonical certificate.
-/
namespace SelectedProofDependenciesTests
open Lean

/-- Keep actual private names for environment lookup. Every popped work item,
including duplicates, consumes the finite budget; absent metadata is an error. -/
private def closure (env : Kernel.Environment) (roots : Array Name) :
    Except String NameSet := do
  let mut pending := roots.toList
  let mut seen : NameSet := {}
  for _ in [:600000] do
    match pending with
    | [] => return seen
    | name :: rest =>
      pending := rest
      unless seen.contains name do
        let some info := env.find? name | throw s!"Missing actual dependency: {name}"
        seen := seen.insert name
        let dependencies := (EDSLGrader.Runtime.directDependencies info).toList.filter
          (fun dependency => !seen.contains dependency)
        pending := dependencies ++ pending
  throw "Selected-proof dependency-closure work limit"

private def normalized (names : NameSet) : NameSet :=
  names.toList.foldl (fun result name => result.insert (privateToUserName name)) {}

private def requireNames (label : String) (names : NameSet) (required : Array Name) :
    Except String Unit := do
  let names := normalized names
  for name in required do
    unless names.contains name do throw s!"{label}: required dependency absent: {name}"

private def exclude (label : String) (names : NameSet) (forbidden : Array Name) :
    Except String Unit := do
  for rawName in names.toList do
    let name := privateToUserName rawName
    if forbidden.any (fun ancestor => ancestor.isPrefixOf name) then
      throw s!"{label}: forbidden dependency: {rawName} (normalized: {name})"

private def gccBehavior : Array Name := #[`EDSL.Corpus.V1.CounterGCC]

-- Clang's rank proofs live beside, rather than inside, its behavior namespace.
private def clangBehavior : Array Name := #[
  `EDSL.Corpus.V1.CounterClang, `EDSL.Corpus.V1.CounterClangRank]

/-- Actual rule/entry selection from CounterCompletion, not generic data tables. -/
private def dispatchers : Array Name := #[
  `EDSL.Corpus.V1.CounterCommon.checkedRules,
  `EDSL.Corpus.V1.CounterCommon.checkedRankLaws,
  `EDSL.Corpus.V1.CounterCommon.checkedInitialNode,
  `EDSL.Corpus.V1.CounterCommon.checkedRules_entry]

/-- Check the direct declaration before traversing its transitive metadata.
Only its type is checked for a concrete index: the Compiler inductive's full
metadata legitimately contains both constructors during closure traversal. -/
private def directBundle (env : Kernel.Environment) (root ownIndex peerIndex : Name)
    (direct required forbidden : Array Name) : Except String Nat := do
  let some info := env.find? root | throw s!"Missing direct proof bundle: {root}"
  let some _body := info.value? (allowOpaque := true) |
    throw s!"Direct proof bundle has no actual body: {root}"
  let typeNames := normalized (info.type.getUsedConstantsAsSet)
  unless typeNames.contains ownIndex do
    throw s!"{root}: missing concrete compiler index in type: {ownIndex}"
  if typeNames.contains peerIndex then
    throw s!"{root}: opposite compiler index in direct type: {peerIndex}"
  requireNames s!"{root} direct type/body" (EDSLGrader.Runtime.directDependencies info) direct
  let seen ← closure env #[root]
  requireNames s!"{root} transitive metadata" seen required
  exclude s!"{root} transitive metadata" seen (forbidden ++ dispatchers)
  return seen.size

/-- All public helpers in Mixed/RankedEntry, including the structure metadata.
The core may depend on no version or other part of EDSL.Corpus. -/
private def coreRoots : Array Name := #[
  `EDSL.OS.TSO64.EffectSimulation.Mixed.RankedEntry,
  `EDSL.OS.TSO64.EffectSimulation.Mixed.RankedEntry.annotations,
  `EDSL.OS.TSO64.EffectSimulation.Mixed.RankedEntry.ghost,
  `EDSL.OS.TSO64.EffectSimulation.Mixed.RankedEntry.current,
  `EDSL.OS.TSO64.EffectSimulation.Mixed.RankedEntry.cohort,
  `EDSL.OS.TSO64.EffectSimulation.Mixed.RankedEntry.initialGhosts,
  `EDSL.OS.TSO64.EffectSimulation.Mixed.RankedEntry.initialCurrent]

/-- Real generic adapter declarations accepting retained proof data, without
specializing to either compiler. Completion helpers are included only because
they exist in CounterProofBundle; no synthetic getter or useful-route wrapper
is manufactured to claim coverage of a nonexistent public helper. -/
private def adapterRoots : Array Name := #[
  `EDSL.Corpus.V1.CounterCommon.ProofBundle,
  `EDSL.Corpus.V1.CounterCommon.ProofProvider,
  `EDSL.Corpus.V1.CounterCommon.ProofBundle.annotations,
  `EDSL.Corpus.V1.CounterCommon.ProofBundle.entry,
  `EDSL.Corpus.V1.CounterCommon.ProofBundle.ghost,
  `EDSL.Corpus.V1.CounterCommon.ProofBundle.current,
  `EDSL.Corpus.V1.CounterCommon.ProofBundle.completed_count,
  `EDSL.Corpus.V1.CounterCommon.ProofBundle.completed_events,
  `EDSL.Corpus.V1.CounterCommon.ProofBundle.completed_resources,
  `EDSL.Corpus.V1.CounterCommon.ProvedSubject,
  `EDSL.Corpus.V1.CounterCommon.provedRankedCohort,
  `EDSL.Corpus.V1.CounterCommon.provedInitialGhosts,
  `EDSL.Corpus.V1.CounterCommon.provedInitialGhosts_current]

run_cmd do
  let env := (← getEnv).toKernelEnv
  let seen ← match closure env #[`EDSL.Corpus.V1.CounterCommon.checkedRules] with
    | .ok seen => pure seen
    | .error message => throwError "{message}"
  -- Use the very same namespace matcher as the negative architecture checks.
  -- Merely importing both modules or seeing their names is insufficient.
  -- checkedRules selects instruction rules, not the separately supplied ranks.
  for family in #[`EDSL.Corpus.V1.CounterGCC, `EDSL.Corpus.V1.CounterClang] do
    match exclude "Old checkedRules positive control" seen #[family] with
    | .error _ => pure ()
    | .ok () => throwError "Old checkedRules control did not reach behavior namespace {family}"
  match requireNames "Old checkedRules positive control" seen
      #[`EDSL.Corpus.V1.CounterGCC.one, `EDSL.Corpus.V1.CounterClang.one] with
    | .ok () => pure ()
    | .error message => throwError "{message}"
  logInfo "SelectedProofDependencies: old checkedRules control reaches both instruction proof families"

run_cmd do
  let count ← match directBundle (← getEnv).toKernelEnv
      `EDSL.Corpus.V1.CounterGCC.proofBundle
      `EDSL.X86.VCGen.CompilerComparisons.Compiler.defaultGCC
      `EDSL.X86.VCGen.CompilerComparisons.Compiler.defaultClang
      #[`EDSL.Corpus.V1.CounterGCC.rules,
        `EDSL.Corpus.V1.CounterGCC.rankLaws,
        `EDSL.Corpus.V1.CounterGCC.entry_of_pre]
      #[`EDSL.Corpus.V1.CounterGCC.one,
        `EDSL.Corpus.V1.CounterGCC.one_next,
        `EDSL.Corpus.V1.CounterGCC.one_locked,
        `EDSL.Corpus.V1.CounterGCC.TerminationRank.ordinary_stage_decreases,
        `EDSL.Corpus.V1.CounterGCC.TerminationRank.locked_count_lt_requested]
      clangBehavior with
    | .ok count => pure count
    | .error message => throwError "{message}"
  logInfo m!"SelectedProofDependencies: direct GCC bundle retains own behavior/rank proofs and excludes Clang ({count} constants)"

run_cmd do
  let count ← match directBundle (← getEnv).toKernelEnv
      `EDSL.Corpus.V1.CounterClang.proofBundle
      `EDSL.X86.VCGen.CompilerComparisons.Compiler.defaultClang
      `EDSL.X86.VCGen.CompilerComparisons.Compiler.defaultGCC
      #[`EDSL.Corpus.V1.CounterClang.rules,
        `EDSL.Corpus.V1.CounterClang.rankLaws,
        `EDSL.Corpus.V1.CounterClang.entry_of_pre]
      #[`EDSL.Corpus.V1.CounterClang.one,
        `EDSL.Corpus.V1.CounterClang.one_ordinary,
        `EDSL.Corpus.V1.CounterClangRank.ordinary_stage_decreases,
        `EDSL.Corpus.V1.CounterClangRank.locked_count_lt_requested]
      gccBehavior with
    | .ok count => pure count
    | .error message => throwError "{message}"
  logInfo m!"SelectedProofDependencies: direct Clang bundle retains own behavior/rank proofs and excludes GCC ({count} constants)"

run_cmd do
  let seen ← match closure (← getEnv).toKernelEnv coreRoots with
    | .ok seen => pure seen
    | .error message => throwError "{message}"
  match exclude "Compiler-independent RankedEntry core" seen #[`EDSL.Corpus] with
    | .ok () => pure ()
    | .error message => throwError "{message}"
  logInfo m!"SelectedProofDependencies: RankedEntry core avoids every corpus namespace ({seen.size} constants)"

run_cmd do
  let seen ← match closure (← getEnv).toKernelEnv adapterRoots with
    | .ok seen => pure seen
    | .error message => throwError "{message}"
  match exclude "Arbitrary retained proof/ProvedSubject consumers" seen
      (gccBehavior ++ clangBehavior ++ dispatchers) with
    | .ok () => pure ()
    | .error message => throwError "{message}"
  logInfo m!"SelectedProofDependencies: generic bundle and subject helpers avoid compiler proof selection ({seen.size} constants)"

end SelectedProofDependenciesTests
