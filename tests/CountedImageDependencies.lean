/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Lean
import EDSL.Grading.Runtime.Audit
import EDSL.Corpus.V1.CountedCertificates.GCCAdmission
import EDSL.Corpus.V1.CountedCertificates.ClangAdmission
import EDSL.Corpus.V1.CountedCertificates.GCCPreparation
import EDSL.Corpus.V1.CountedCertificates.ClangPreparation

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Isolation concerns the actual transitive type/value/recursor dependencies,
not only import strings or the root theorem's declared result. The old shared
dispatcher is a deliberate positive control for cross-image reachability. -/
namespace CountedImageDependenciesTests
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
  throw "Dependency-closure work limit"

private def isolated (env : Kernel.Environment) (roots : Array Name)
    (ownFile : Name) (forbidden : Array Name) : Except String Nat := do
  let seen ← closure env roots
  unless seen.contains ownFile do throw s!"Own complete file is absent from closure: {ownFile}"
  for rawName in seen.toList do
    let name := privateToUserName rawName
    if forbidden.any (fun ancestor => ancestor.isPrefixOf name) ||
        name == `EDSL.Corpus.V1.CounterMixedGraphs.namedChecked then
      throw s!"Other image or shared admission in isolated closure: {rawName}"
  return seen.size

private def gccRoots : Array Name := #[
  `EDSL.Corpus.V1.CountedCertificates.GCCPreparation.started,
  `EDSL.Corpus.V1.CountedCertificates.GCCPreparation.present,
  `EDSL.Corpus.V1.CountedCertificates.GCCPreparation.loadedBatch,
  `EDSL.Corpus.V1.CountedCertificates.GCCAdmission.named,
  `EDSL.Corpus.V1.CountedCertificates.GCCAdmission.checked,
  `EDSL.Corpus.V1.CountedCertificates.GCCAdmission.rx,
  `EDSL.Corpus.V1.CountedCertificates.GCCAdmission.total,
  `EDSL.Corpus.V1.CountedCertificates.GCCAdmission.resources,
  `EDSL.Corpus.CountedResources.Image.code,
  `EDSL.Corpus.CountedResources.Image.full_image,
  `EDSL.Corpus.CountedResources.Image.target_fresh]

private def clangRoots : Array Name := #[
  `EDSL.Corpus.V1.CountedCertificates.ClangPreparation.started,
  `EDSL.Corpus.V1.CountedCertificates.ClangPreparation.present,
  `EDSL.Corpus.V1.CountedCertificates.ClangPreparation.loadedBatch,
  `EDSL.Corpus.V1.CountedCertificates.ClangAdmission.named,
  `EDSL.Corpus.V1.CountedCertificates.ClangAdmission.checked,
  `EDSL.Corpus.V1.CountedCertificates.ClangAdmission.rx,
  `EDSL.Corpus.V1.CountedCertificates.ClangAdmission.total,
  `EDSL.Corpus.V1.CountedCertificates.ClangAdmission.resources,
  `EDSL.Corpus.CountedResources.Image.code,
  `EDSL.Corpus.CountedResources.Image.full_image,
  `EDSL.Corpus.CountedResources.Image.target_fresh]

run_cmd do
  let env := (← getEnv).toKernelEnv
  let gcc ← match isolated env gccRoots `EDSL.Corpus.V1.GCC.file
      #[`EDSL.Corpus.V1.Clang, `EDSL.Corpus.V1.CountedCertificates.ClangAdmission,
        `EDSL.Corpus.V1.CountedCertificates.ClangPreparation] with
    | .ok count => pure count
    | .error message => throwError "{message}"
  logInfo m!"CountedImageDependencies: GCC admission, resources and actual loaded batches are isolated ({gcc} constants)"

run_cmd do
  let env := (← getEnv).toKernelEnv
  let clang ← match isolated env clangRoots `EDSL.Corpus.V1.Clang.file
      #[`EDSL.Corpus.V1.GCC, `EDSL.Corpus.V1.CountedCertificates.GCCAdmission,
        `EDSL.Corpus.V1.CountedCertificates.GCCPreparation] with
    | .ok count => pure count
    | .error message => throwError "{message}"
  logInfo m!"CountedImageDependencies: Clang admission, resources and actual loaded batches are isolated ({clang} constants)"

run_cmd do
  let seen ← match closure (← getEnv).toKernelEnv
      #[`EDSL.Corpus.V1.CounterMixedGraphs.namedChecked] with
    | .ok seen => pure seen
    | .error message => throwError "{message}"
  unless seen.contains `EDSL.Corpus.V1.GCC.file && seen.contains `EDSL.Corpus.V1.Clang.file do
    throwError "Shared-dispatch positive control failed to reach both full files"
  logInfo "CountedImageDependencies: shared-dispatch control reaches both original files"

end CountedImageDependenciesTests
