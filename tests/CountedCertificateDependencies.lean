/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Lean
import EDSL.Grading.Runtime.Audit
import EDSL.Corpus.V1.CountedCertificates

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Full certificate roots and their public all-input useful families must
retain the own complete file and exclude opposite complete-file evidence and
shared loaded-state dispatch. Small compiler graph/section hints may remain.
The old family constructor is a positive control for both-file reachability. -/
namespace CountedCertificateDependenciesTests
open Lean

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
        pending := (EDSLGrader.Runtime.directDependencies info).toList ++ pending
  throw "Full-certificate dependency work limit"

private def sharedLoaded : Array Name := #[
  `EDSL.Corpus.V1.CounterResources,
  `EDSL.Corpus.V1.CounterLoadedInputs,
  `EDSL.Corpus.V1.CountedCertificates.named,
  `EDSL.Corpus.V1.CountedCertificates.named_claim,
  `EDSL.Corpus.V1.CountedCertificates.loadedBatch,
  `EDSL.Corpus.V1.CountedCertificates.loaded_useful_with_cleanup,
  `EDSL.Corpus.V1.CountedCertificates.loaded_useful,
  `EDSL.Corpus.V1.CountedCertificates.wrapping_useful,
  `EDSL.Corpus.V1.CountedCertificates.certificate,
  `EDSL.Corpus.V1.CounterMixedGraphs.namedChecked,
  `EDSL.Corpus.V1.CounterMixedGraphs.namedValid,
  `EDSL.Corpus.V1.CounterOverlap.loadedSubjects,
  `EDSL.Corpus.V1.CounterOverlap.loadedSlots,
  `EDSL.Corpus.V1.CounterOverlap.loadedCohort,
  `EDSL.Corpus.V1.CounterOverlap.loadedGhosts,
  `EDSL.Corpus.V1.CounterOverlap.LoadedPrefix,
  `EDSL.Corpus.V1.CounterOverlap.construct_prefix,
  `EDSL.Corpus.V1.CounterOverlap.cleanup_of_returned,
  `EDSL.Corpus.V1.CounterOverlap.LoadedOutput,
  `EDSL.Corpus.V1.CounterOverlap.complete]

/-- Ban actual file dispatchers. Lean reuses generic generated match eliminators
for unrelated table hints; all of their dependencies are still traversed. -/
private def fileDispatchers : Array Name := #[
  `EDSL.Corpus.V1.CounterMixedGraphs.file,
  `EDSL.Corpus.V1.ArithmeticWindows.file,
  `EDSL.Corpus.V1.FrozenFunction.file]

private def isolated (env : Kernel.Environment) (roots : Array Name)
    (ownFile peer : Name) (peerLeaves : Array Name) : Except String Nat := do
  let seen ← closure env roots
  unless seen.contains ownFile do throw s!"Own complete file absent: {ownFile}"
  for rawName in seen.toList do
    let name := privateToUserName rawName
    if fileDispatchers.contains name ||
        sharedLoaded.any (fun ancestor => ancestor.isPrefixOf name) ||
        peerLeaves.any (fun ancestor => ancestor.isPrefixOf name) then
      throw s!"Shared/peer loaded evidence in complete certificate: {rawName}"
    if peer.isPrefixOf name then
      let short := name.toString
      if short.startsWith (peer.toString ++ ".file") ||
          name == Name.str peer "chunks" ||
          (Name.str peer "metadataAccepted").isPrefixOf name ||
          (Name.str peer "layoutAccepted").isPrefixOf name then
        throw s!"Opposite complete file or validation in certificate: {rawName}"
  return seen.size

run_cmd do
  let env := (← getEnv).toKernelEnv
  let roots := #[`EDSL.Corpus.V1.CountedCertificates.gcc,
    `EDSL.Corpus.V1.CountedCertificates.GCCCertificate.certificate,
    `EDSL.Corpus.V1.CountedCertificates.GCCCertificate.loaded_useful_with_cleanup,
    `EDSL.Corpus.V1.CountedCertificates.GCCCertificate.loaded_useful,
    `EDSL.Corpus.V1.CountedCertificates.GCCCertificate.wrapping_useful]
  let count ← match isolated env roots `EDSL.Corpus.V1.GCC.file `EDSL.Corpus.V1.Clang
      #[`EDSL.Corpus.V1.CountedCertificates.ClangAdmission,
        `EDSL.Corpus.V1.CountedCertificates.ClangPreparation,
        `EDSL.Corpus.V1.CountedCertificates.ClangCertificate] with
    | .ok count => pure count
    | .error message => throwError "{message}"
  logInfo m!"CountedCertificateDependencies: GCC complete/all-input roots are file-isolated ({count} constants)"

run_cmd do
  let env := (← getEnv).toKernelEnv
  let roots := #[`EDSL.Corpus.V1.CountedCertificates.clang,
    `EDSL.Corpus.V1.CountedCertificates.ClangCertificate.certificate,
    `EDSL.Corpus.V1.CountedCertificates.ClangCertificate.loaded_useful_with_cleanup,
    `EDSL.Corpus.V1.CountedCertificates.ClangCertificate.loaded_useful,
    `EDSL.Corpus.V1.CountedCertificates.ClangCertificate.wrapping_useful]
  let count ← match isolated env roots `EDSL.Corpus.V1.Clang.file `EDSL.Corpus.V1.GCC
      #[`EDSL.Corpus.V1.CountedCertificates.GCCAdmission,
        `EDSL.Corpus.V1.CountedCertificates.GCCPreparation,
        `EDSL.Corpus.V1.CountedCertificates.GCCCertificate] with
    | .ok count => pure count
    | .error message => throwError "{message}"
  logInfo m!"CountedCertificateDependencies: Clang complete/all-input roots are file-isolated ({count} constants)"

run_cmd do
  let seen ← match closure (← getEnv).toKernelEnv
      #[`EDSL.Corpus.V1.CountedCertificates.certificate] with
    | .ok seen => pure seen
    | .error message => throwError "{message}"
  unless seen.contains `EDSL.Corpus.V1.GCC.file && seen.contains `EDSL.Corpus.V1.Clang.file do
    throwError "Old full-family control must reach both original complete files"
  logInfo "CountedCertificateDependencies: old full-family control reaches both files"

end CountedCertificateDependenciesTests
