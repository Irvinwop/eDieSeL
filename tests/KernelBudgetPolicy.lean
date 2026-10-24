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

/-! Policy regressions exercise the real decoder, dependency auditor and checked
kernel insertion. Synthetic negative declarations remain data in local snapshots.
The expected arithmetic contract is independent of the submitted expression. -/
namespace KernelBudgetPolicyTests
open Lean EDSLGrader.Runtime

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap {α : Type} (result : Except Failure α) : IO α := do
  match result with
  | .ok value => return value
  | .error failure => throw (IO.userError s!"unexpected fixture failure: {failure}")

private def nat : Expr := mkConst ``Nat
private def truth : Expr := mkConst ``True
private def intro : Expr := mkConst ``True.intro
private def sevenName : Name := `KernelBudgetFixture.seven
private def spareName : Name := `KernelBudgetFixture.spare

private def definition (name : Name) (n : Nat) : Declaration := .defnDecl {
  name, levelParams := [], type := nat, value := mkRawNatLit n,
  hints := .abbrev, safety := .safe, all := [name] }

private def theoremData (name : Name) (type value : Expr) : Declaration :=
  .thmDecl { name, levelParams := [], type, value, all := [name] }

private def encode (shared : Bool) (decls : List Declaration) (proof : Expr) : IO String :=
  unwrap (if shared then encodePacket decls proof else encodeTreePacket decls proof)

private def reject (policy : KernelBudgetPolicy) (env : Kernel.Environment)
    (lim : Limits) (expected : Expr) (text : String) (kind : FailureKind)
    (phase : PacketCheckPhase) : IO PacketCheckFailure := do
  let failure ← match checkPacketDetailedWithPolicy policy env lim expected text with
    | .error failure => pure failure
    | .ok _ => throw (IO.userError "unexpected policy acceptance")
  require (failure.failure.kind == kind && failure.site.phase == phase)
    s!"wrong policy rejection: {repr failure}"
  require ((env.find? sevenName).isNone) "policy checker mutated its trusted input"
  return failure

private def admissionCases (env : Kernel.Environment) (shared : Bool) : IO Unit := do
  let packet ← encode shared [definition sevenName 7] intro
  let _ ← reject .totalPool env { kernelHeartbeats := 0 } truth packet .resource .kernelBudget
  let _ ← reject .totalPool env { kernelRecDepth := 0 } truth packet .resource .kernelBudget
  -- Two checks cannot receive positive uniform shares from a budget of one.
  -- Pooling reaches the actual kernel, whose one-tick ceiling rejects this definition.
  let uniform ← reject .uniformPrefix env { kernelHeartbeats := 1 } truth packet
    .resource .kernelBudget
  let pooled ← reject .totalPool env { kernelHeartbeats := 1 } truth packet
    .resource .declarationKernel
  require (uniform.site.kernelCeiling.isNone && pooled.site.kernelCeiling == some 1 &&
    pooled.site.entry == some 0 && pooled.site.completedDeclarations == 0 &&
    pooled.failure.message == "kernel heartbeat limit")
    "pooling reused zero-quota admission or bypassed the forced kernel call"
  let _ ← reject .totalPool env { maxNodes := 0 } truth packet .resource .declarationDecode
  let _ ← reject .totalPool env { maxDeclarations := 0 } truth packet .resource .envelope
  pure ()

private def contractCases (env : Kernel.Environment) (shared : Bool) : IO Unit := do
  let eight := mkRawNatLit 8
  let expected := mkApp3 (mkConst ``Eq [1]) nat eight eight
  let calculated := mkApp (mkConst ``Nat.succ) (mkConst sevenName)
  let proof := mkApp2 (mkConst ``Eq.refl [1]) nat calculated
  let packet ← encode shared [definition sevenName 7] proof
  for policy in [KernelBudgetPolicy.uniformPrefix, .totalPool] do
    let checked ← unwrap (checkPacketWithPolicy policy env {} expected packet)
    require (checked.declarations == 1 && checked.kernelChecks == 2 &&
      (checked.env.find? sevenName).isSome && (env.find? sevenName).isNone)
      "policy lost the checked arithmetic closure or isolated input"
    let wrong := mkApp3 (mkConst ``Eq [1]) nat eight (mkRawNatLit 9)
    let failure ← reject policy env {} wrong packet .rejected .finalProof
    require (failure.site.completedDeclarations == 1) "wrong final proposition failed before replay"
  let invalid := theoremData `KernelBudgetFixture.badType truth (mkRawNatLit 4)
  let _ ← reject .totalPool env {} truth (← encode shared [invalid] intro)
    .rejected .declarationKernel
  pure ()

private def finalCeilingCases (env : Kernel.Environment) (shared : Bool) : IO Unit := do
  let packet ← encode shared [definition sevenName 7, definition spareName 0] intro
  let uniform ← reject .uniformPrefix env {} (mkConst ``False) packet .rejected .finalProof
  let pooled ← reject .totalPool env {} (mkConst ``False) packet .rejected .finalProof
  -- The fixed ten-million budget leaves one unused tick when split three ways.
  -- Pooling offers the declared total, including that remainder, at the final check.
  require (uniform.site.kernelCeiling == some 9999999 &&
    pooled.site.kernelCeiling == some 10000000 &&
    uniform.site.completedDeclarations == 2 && pooled.site.completedDeclarations == 2)
    "the final check used the wrong trusted policy or reset completion accounting"

private def dependencyCases (env : Kernel.Environment) (shared : Bool) : IO Unit := do
  let axiomName := `KernelBudgetFixture.unapproved
  let localEnv ← unwrap (forceDeclaration env 10000000 512 (.axiomDecl {
    name := axiomName, levelParams := [], type := mkConst ``False, isUnsafe := false }))
  let unused := theoremData `KernelBudgetFixture.hidden (mkConst ``False) (mkConst axiomName)
  let failure ← reject .totalPool localEnv {} truth
    (← encode shared [unused] intro) .audit .declarationAudit
  require (failure.failure.message == "unapproved axiom" &&
    failure.site.completedDeclarations == 0)
    "pooling admitted an unused well-typed auxiliary with an unapproved dependency"

private def noPacketPolicy (env : Kernel.Environment) : IO Unit := do
  let extra := "[\"edsl-proof-v1\",[],[\"const\",[\"True\",\"intro\"],[]],\"totalPool\"]"
  for policy in [KernelBudgetPolicy.uniformPrefix, .totalPool] do
    let failure ← reject policy env {} truth extra .malformed .envelope
    require (failure.failure.message == "packet shape or version")
      "a packet selected administrative kernel policy"

run_cmd do
  let env := (← getEnv).toKernelEnv
  for shared in [false, true] do
    admissionCases env shared
    contractCases env shared
    finalCeilingCases env shared
    dependencyCases env shared
  noPacketPolicy env
  logInfo "Kernel budget policies: independent contracts, real kernel limits, audit rejection and packet-policy separation passed"

end KernelBudgetPolicyTests
