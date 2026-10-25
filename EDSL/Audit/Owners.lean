/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import Lean

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

/- Select declarations by actual defining module, including private and
compiler-generated names, rather than by a visible declaration-name prefix. -/
elab "#audit_edsl_owners" : command => do
  let environment ← Lean.getEnv
  let approved := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut total : Nat := 0
  let mut privateNames : Nat := 0
  let mut internalDetails : Nat := 0
  let mut privateOwners : Std.HashMap String Nat := {}
  let mut internalOwners : Std.HashMap String Nat := {}
  let mut actualAxioms : Array Lean.Name := #[]
  let mut owners : Array (Lean.Name × Nat) := #[]
  for owner in environment.header.moduleNames do
    Lean.logInfo m!"ACTUAL_IMPORT {owner}"
    if (`EDSL).isPrefixOf owner then owners := owners.push (owner, 0)
  for (name, info) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let owner := environment.header.moduleNames[index]!
      if (`EDSL).isPrefixOf owner then
        if info matches .axiomInfo _ then
          throwError "Project axiom: {owner}: {name}"
        total := total + 1
        if Lean.isPrivateName name then
          privateNames := privateNames + 1
          privateOwners := privateOwners.insert (toString owner)
            (privateOwners.getD (toString owner) 0 + 1)
        -- This is a descriptive count, never a filter on the audited set.
        -- All compiler-generated declarations are selected by actual owner.
        if name.isInternalDetail then
          internalDetails := internalDetails + 1
          internalOwners := internalOwners.insert (toString owner)
            (internalOwners.getD (toString owner) 0 + 1)
        for dependency in ← Lean.collectAxioms name do
          unless approved.contains dependency do
            throwError "{owner}: {name} depends on unapproved axiom {dependency}"
          unless actualAxioms.contains dependency do
            actualAxioms := actualAxioms.push dependency
        owners := owners.map fun (definingModule, count) =>
          (definingModule, if definingModule == owner then count + 1 else count)
  unless total > 0 do
    throwError "Incomplete owner audit: total={total}, private={privateNames}"
  for (owner, count) in owners do
    Lean.logInfo m!"OWNER_COUNT {owner} {count}"
  Lean.logInfo m!"OWNER_PRIVATE_COUNTS {Lean.Json.compress (Lean.toJson privateOwners.toList)}"
  Lean.logInfo m!"OWNER_INTERNAL_DETAIL_COUNTS {Lean.Json.compress (Lean.toJson internalOwners.toList)}"
  Lean.logInfo m!"OWNER_AXIOMS {Lean.Json.compress (Lean.toJson (actualAxioms.map toString))}"
  Lean.logInfo m!"OWNER_INTERNAL_DETAILS {internalDetails}"
  Lean.logInfo m!"OWNER_AUDIT_PASS total={total} private={privateNames} modules={owners.size}"
