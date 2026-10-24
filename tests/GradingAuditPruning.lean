/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Lean
import EDSL.Grading.Runtime.Checker

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Real checked packets exercise shared dependency auditing. The independent
contract is 2 + 2 = 4; synthetic unsafe/axiom fixtures exist only as declaration
data in a local kernel snapshot. No candidate code is compiled or evaluated. -/
namespace GradingAuditPruningTests
open Lean EDSLGrader.Runtime

private def arithmetic : Expr :=
  mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat)
    (mkApp2 (mkConst ``Nat.add) (mkNatLit 2) (mkNatLit 2)) (mkNatLit 4)

private def arithmeticProof : Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 4)

private def theoremData (name : Name) (value : Expr) : Declaration :=
  .thmDecl { name, levelParams := [], type := arithmetic, value }

/-- Two branches at each layer share the preceding pair. Let values are checked
and audited even when their bound proof is unused in the result. -/
private def diamond : List Declaration × Name := Id.run do
  let leaf := `AuditCachePacket.leaf
  let mut declarations := [theoremData leaf arithmeticProof]
  let mut left := leaf
  let mut right := leaf
  for layer in [:24] do
    let value := Expr.letE `shared arithmetic (mkConst left) (mkConst right) false
    let nextLeft := Name.str `AuditCachePacket s!"left{layer}"
    let nextRight := Name.str `AuditCachePacket s!"right{layer}"
    declarations := declarations ++ [theoremData nextLeft value, theoremData nextRight value]
    left := nextLeft
    right := nextRight
  return (declarations, right)

private def unwrap {α : Type} (result : Except Failure α) : IO α :=
  match result with
  | .ok value => pure value
  | .error failure => throw (IO.userError s!"fixture setup failed: {failure}")

private def requireFailure (kind : FailureKind) (phase : PacketCheckPhase)
    (result : Except PacketCheckFailure Checked) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError "invalid or over-budget packet accepted")
  | .error failure =>
    unless failure.failure.kind == kind && failure.site.phase == phase do
      throw (IO.userError s!"unexpected rejection: {repr failure}")

private def runCases (base : Kernel.Environment) (shared : Bool) : IO Unit := do
  let badAxiom := `AuditCacheFixture.unapproved
  let badUnsafe := `AuditCacheFixture.unsafeProof
  let env ← unwrap (forceDeclaration base 10000000 512 (.axiomDecl {
    name := badAxiom, levelParams := [], type := arithmetic, isUnsafe := false }))
  let env ← unwrap (forceDeclaration env 10000000 512 (.defnDecl {
    name := badUnsafe, levelParams := [], type := arithmetic, value := arithmeticProof,
    hints := .regular 0, safety := .unsafe }))
  let (declarations, root) := diamond
  let encode (ds : List Declaration) :=
    if shared then encodePacket ds (mkConst root) else encodeTreePacket ds (mkConst root)
  let packet ← unwrap (encode declarations)
  let limits : Limits := { maxAuditSteps := 128 }
  let checked ← match checkPacketDetailedWithPolicy .totalPool env limits arithmetic packet with
    | .ok value => pure value
    | .error failure => throw (IO.userError s!"shared arithmetic graph rejected: {repr failure}")
  -- Forty-nine different submitted declarations cannot fit thirty-two queue pops.
  requireFailure .resource .declarationAudit
    (checkPacketDetailedWithPolicy .totalPool env { limits with maxAuditSteps := 32 }
      arithmetic packet)
  let wrong := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat)
    (mkApp2 (mkConst ``Nat.add) (mkNatLit 2) (mkNatLit 2)) (mkNatLit 5)
  requireFailure .rejected .finalProof
    (checkPacketDetailedWithPolicy .totalPool env limits wrong packet)
  -- This separate cold traversal does not inherit the packet's visited cache.
  -- Use the existing production audit allowance for its setup, then reuse only
  -- its actually returned cache in the unseen-dependency rejection probes.
  let warm ← unwrap (auditNames checked.env
    { remaining := ({} : Limits).maxAuditSteps } [root])
  match auditNames checked.env warm [root,badUnsafe] with
  | .error failure =>
    unless failure.kind == .audit && failure.message == "unsafe dependency" do
      throw (IO.userError s!"wrong unsafe cache rejection: {failure}")
  | .ok _ => throw (IO.userError "unseen unsafe dependency accepted")
  match auditNames checked.env warm [root,`AuditCacheFixture.missing] with
  | .error failure =>
    unless failure.kind == .audit && failure.message == "missing dependency" do
      throw (IO.userError s!"wrong missing cache rejection: {failure}")
  | .ok _ => throw (IO.userError "unseen missing dependency accepted")
  -- The shared safe prefix must not hide a newly reached unchecked dependency.
  for (dependency, kind) in [(badAxiom, "unapproved axiom")] do
    let name := `AuditCachePacket.badTail
    let tail := theoremData name
      (.letE `prior arithmetic (mkConst root) (mkConst dependency) false)
    let encoded ← unwrap (if shared then encodePacket (declarations ++ [tail]) (mkConst name)
      else encodeTreePacket (declarations ++ [tail]) (mkConst name))
    let result := checkPacketDetailedWithPolicy .totalPool env limits arithmetic encoded
    requireFailure .audit .declarationAudit result
    match result with
    | .error failure =>
      unless failure.failure.message == kind do
        throw (IO.userError s!"wrong dependency rejection: {repr failure}")
    | .ok _ => throw (IO.userError "unchecked dependency accepted")

private def requireAuditFailure (message : String)
    (result : Except Failure AuditState) : IO Unit := do
  match result with
  | .error failure =>
    unless failure.message == message do
      throw (IO.userError s!"wrong audit failure: {failure}")
  | .ok _ => throw (IO.userError "audit unexpectedly accepted")

private def runQueueCases (base : Kernel.Environment) : IO Unit := do
  let d := `AuditQueueFixture.D
  let l := `AuditQueueFixture.L
  let r := `AuditQueueFixture.R
  let top := `AuditQueueFixture.Top
  let definition (name : Name) (value : Expr) : Declaration := .defnDecl {
    name, levelParams := [], type := .sort 1, value,
    hints := .regular 0, safety := .safe }
  let mut env := base
  for declaration in [definition d (.sort 0), definition l (mkConst d),
      definition r (mkConst d),
      definition top (.letE `shared (.sort 1) (mkConst l) (mkConst r) false)] do
    env ← unwrap (forceDeclaration env 10000000 512 declaration)
  -- This independently specified diamond has exactly four first-time visits.
  let complete ← unwrap (auditNames env { remaining := 4 } [top])
  for name in [d,l,r,top] do
    unless complete.seen.contains name do throw (IO.userError s!"omitted diamond node: {name}")
  requireAuditFailure "audit steps" (auditNames env { remaining := 3 } [top])
  let first ← unwrap (auditNames env { remaining := 4 } [d])
  let _ ← unwrap (auditNames env first [top])
  -- Already pending duplicates are retained, and a seen pop still needs fuel.
  requireAuditFailure "audit steps" (auditNames env { remaining := 2 } [l,d])
  let _ ← unwrap (auditNames env { remaining := 3 } [l,d])
  let exhausted ← unwrap (auditNames env { remaining := 2 } [d,d])
  requireAuditFailure "audit steps" (auditNames env exhausted [d])
  let _ ← unwrap (auditNames env exhausted [])
  pure ()

run_cmd do
  let env := (← getEnv).toKernelEnv
  runQueueCases env
  for shared in [false, true] do runCases env shared
  logInfo "Audit pruning: shared arithmetic proofs, wrong result, unseen unsafe/axiom dependencies and aggregate budget checked"

end GradingAuditPruningTests
