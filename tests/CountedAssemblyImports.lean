/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.CountedCertificate.Assembly
import EDSL.Corpus.CountedResources.Image
import EDSL.Corpus.CountedResources.Loaded
import Lean

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Guard the actual imported module closure of the reusable resource and
execution builders. Frozen clients belong in separate untrusted environments. -/
run_cmd do
  let modules := (← Lean.getEnv).header.moduleNames
  for moduleName in modules do
    if (`EDSL.Corpus.V1).isPrefixOf moduleName || moduleName == `EDSL ||
        moduleName == `EDSL.All then
      throwError "Frozen client or broad facade in reusable assembly closure: {moduleName}"
  for required in #[`EDSL.Corpus.CountedCertificate.Assembly,
      `EDSL.Corpus.CountedResources.Image, `EDSL.Corpus.CountedResources.Workers,
      `EDSL.Corpus.CountedResources.Loaded, `EDSL.OS.TSO64.ScheduleComposition] do
    unless modules.contains required do
      throwError "Missing actual reusable import: {required}"
  Lean.logInfo m!"CountedAssemblyImports: generic assembly/resource closure has no frozen clients"
