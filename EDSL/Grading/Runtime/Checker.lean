/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Runtime.Packet
import EDSL.Grading.Runtime.Audit

/-! Proof-packet admission/checking, using only the options-independent checked
kernel declaration API. Candidate code is never compiled or evaluated. Each call
starts from its caller's immutable trusted snapshot; no candidate state is global.
Heartbeat ceilings accumulate across all kernel additions in a packet. These
limits are admission policy, not a service sandbox or an allocation/latency proof.

Safe opaque bodies are audited logically. Source `partial def` may lower to a safe
opaque logical default body: metadata cannot reconstruct source provenance or a
compiled runtime implementation. Actual unsafe/partial metadata is rejected.
Simple nonnested inductive groups are supported; nested inductives and mutual
definition payloads are outside this protocol version. -/
namespace EDSLGrader.Runtime

open Lean

def kernelFailure : Kernel.Exception → Failure
  | .unknownConstant .. => ⟨.rejected, "kernel unknownConstant"⟩
  | .alreadyDeclared .. => ⟨.rejected, "kernel alreadyDeclared"⟩
  | .declTypeMismatch .. => ⟨.rejected, "kernel declTypeMismatch"⟩
  | .declHasMVars .. => ⟨.rejected, "kernel declHasMVars"⟩
  | .declHasFVars .. => ⟨.rejected, "kernel declHasFVars"⟩
  | .funExpected .. => ⟨.rejected, "kernel funExpected"⟩
  | .typeExpected .. => ⟨.rejected, "kernel typeExpected"⟩
  | .letTypeMismatch .. => ⟨.rejected, "kernel letTypeMismatch"⟩
  | .exprTypeMismatch .. => ⟨.rejected, "kernel exprTypeMismatch"⟩
  | .appTypeMismatch .. => ⟨.rejected, "kernel appTypeMismatch"⟩
  | .invalidProj .. => ⟨.rejected, "kernel invalidProj"⟩
  | .thmTypeIsNotProp .. => ⟨.rejected, "kernel thmTypeIsNotProp"⟩
  | .other _ => ⟨.rejected, "kernel declaration rejected"⟩
  | .deterministicTimeout => ⟨.resource, "kernel heartbeat limit"⟩
  | .excessiveMemory => ⟨.resource, "kernel memory limit"⟩
  | .deepRecursion => ⟨.resource, "kernel recursion limit"⟩
  | .interrupted => ⟨.resource, "kernel interrupted"⟩

/-- No Options or compiler/evaluator APIs occur at the trust boundary. Zero is
disallowed because kernel APIs can interpret zero budgets as unbounded. -/
def forceDeclaration (env : Kernel.Environment) (heartbeats recDepth : USize)
    (decl : Declaration) : Except Failure Kernel.Environment := do
  if heartbeats == 0 || recDepth == 0 then return ← fail .resource "zero kernel budget"
  (Kernel.Environment.addDeclCore env heartbeats recDepth decl none).mapError kernelFailure

/-- Absolute cumulative ceiling for a checked prefix. Clamping also prevents
a controller indexing error from increasing the caller's total budget. -/
def packetKernelCeiling (budget checks completed : Nat) : Nat :=
  budget / checks * min completed checks

theorem packetKernelCeiling_le (budget checks completed : Nat) :
    packetKernelCeiling budget checks completed ≤ budget := by
  unfold packetKernelCeiling
  exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.min_le_right completed checks))
    (Nat.div_mul_le_self budget checks)

def checkFinal (env : Kernel.Environment) (lim : Limits) (heartbeats : USize)
    (state : AuditState) (expected value : Expr) (freshName : Name) :
    Except Failure AuditState := do
  closed expected
  closed value
  if freshName.isAnonymous || (env.find? freshName).isSome then
    return ← fail .internal "certification name collision"
  let state ← auditExprs env state expected value
  let _ ← forceDeclaration env heartbeats lim.kernelRecDepth (.thmDecl {
    name := freshName, levelParams := [], type := expected, value })
  return state

/-- Root-only wrapper/test API. The supplied name is trusted, not a packet field.
The returned environment discards the scratch theorem used for checking. -/
def checkExpr (env : Kernel.Environment) (lim : Limits) (expected value : Expr)
    (freshName : Name) : Except Failure Checked := do
  let state ← checkFinal env lim lim.kernelHeartbeats
    { remaining := lim.maxAuditSteps } expected value freshName
  return {
    env, value
    declarations := 0
    constants := state.seen.size
    decoderSteps := 0
    auditSteps := lim.maxAuditSteps - state.remaining
    kernelChecks := 1 }

/-- For this protocol every inductive group is required to have no kernel-generated
nested types. The checked insertion is temporary until this check and the audit
both succeed; failed extensions are never returned or reused. -/
def checkInductiveShape (env : Kernel.Environment) (decl : Declaration) : Except Failure Unit := do
  if let .inductDecl _ _ types _ := decl then
    for type in types do
      let some (.inductInfo info) := env.find? type.name
        | return ← fail .internal "checked inductive information missing"
      if info.numNested != 0 then return ← fail .unsupported "nested inductive group"

section
set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-- The operation about to be attempted when a packet check fails. `finalProof`
groups all of `checkFinal`, including its closedness, name, audit and kernel checks. -/
inductive PacketCheckPhase where
  | expected | envelope | kernelBudget | declarationDecode | declarationNames
  | declarationKernel | inductiveShape | declarationAudit | proofDecode | finalProof
  deriving BEq, Repr, Inhabited

/-- Scalar snapshots before the named operation. Decoder and audit steps count
only confirmed successful prefixes, excluding work inside a failed operation;
they are lower bounds, not exact native costs. No candidate state is retained. -/
structure PacketCheckSite where
  phase : PacketCheckPhase
  /-- Zero-based attempted declaration entry; absent at outer and proof stages. -/
  entry : Option Nat := none
  /-- Entries whose decode, kernel insertion, shape check and audit all succeeded. -/
  completedDeclarations : Nat := 0
  decoderSteps : Nat := 0
  auditSteps : Nat := 0
  /-- Planned cumulative ceiling, only for `declarationKernel` and `finalProof`. -/
  kernelCeiling : Option Nat := none
  deriving Repr, Inhabited

structure PacketCheckFailure where
  failure : Failure
  site : PacketCheckSite
  deriving Repr

/-- One packet-wide budget: decoding state, audit state, name count, and kernel
heartbeat quota are carried through every auxiliary declaration and the proof.
Detailed payloads are constructed only on failure; checked prefixes never escape
on error. A failed decoder discards its state, so its steps are not reported. -/
def checkPacketDetailed (env : Kernel.Environment) (lim : Limits) (expected : Expr)
    (input : String) : Except PacketCheckFailure Checked := do
  (closed expected).mapError fun failure =>
    { failure, site := { phase := .expected } }
  let packet ← (Packet.fields lim input).mapError fun failure =>
    { failure, site := { phase := .envelope } }
  let entries := packet.declarations
  let checks := entries.size + 1
  let quota := lim.kernelHeartbeats.toNat / checks
  if quota == 0 || lim.kernelRecDepth == 0 then
    return ← (fail .resource "kernel budget per check").mapError fun failure =>
      { failure, site := { phase := .kernelBudget } }
  let mut checkedEnv := env
  let mut remaining := lim.maxNodes
  let mut names := 0
  let mut audit : AuditState := { remaining := lim.maxAuditSteps }
  let mut kernelChecks := 0
  let mut completedDeclarations := 0
  for entry in entries do
    let (decl, left) ← ((Packet.declaration packet.dialect checkedEnv lim entry).run remaining).mapError
      fun failure => { failure, site := {
        phase := .declarationDecode
        entry := some completedDeclarations
        completedDeclarations
        decoderSteps := lim.maxNodes - remaining
        auditSteps := lim.maxAuditSteps - audit.remaining } }
    remaining := left
    let declared := decl.getNames
    names := names + declared.length
    if names > lim.maxDeclarations then
      return ← (fail .resource "declared constant names").mapError fun failure =>
        { failure, site := {
          phase := .declarationNames
          entry := some completedDeclarations
          completedDeclarations
          decoderSteps := lim.maxNodes - remaining
          auditSteps := lim.maxAuditSteps - audit.remaining } }
    kernelChecks := kernelChecks + 1
    -- The pinned kernel compares against a thread-local cumulative counter;
    -- addDeclCore changes its ceiling without resetting that counter. Prefix
    -- ceilings apportion one total cap rather than reusing its first slice.
    let ceiling := packetKernelCeiling lim.kernelHeartbeats.toNat checks kernelChecks
    let next ← (forceDeclaration checkedEnv (USize.ofNat ceiling)
      lim.kernelRecDepth decl).mapError fun failure =>
        { failure, site := {
          phase := .declarationKernel
          entry := some completedDeclarations
          completedDeclarations
          decoderSteps := lim.maxNodes - remaining
          auditSteps := lim.maxAuditSteps - audit.remaining
          kernelCeiling := some ceiling } }
    (checkInductiveShape next decl).mapError fun failure =>
      { failure, site := {
        phase := .inductiveShape
        entry := some completedDeclarations
        completedDeclarations
        decoderSteps := lim.maxNodes - remaining
        auditSteps := lim.maxAuditSteps - audit.remaining } }
    audit ← (auditNames next audit declared).mapError fun failure =>
      { failure, site := {
        phase := .declarationAudit
        entry := some completedDeclarations
        completedDeclarations
        decoderSteps := lim.maxNodes - remaining
        auditSteps := lim.maxAuditSteps - audit.remaining } }
    checkedEnv := next
    completedDeclarations := completedDeclarations + 1
  let (value, left) ←
    ((Packet.expression packet.dialect checkedEnv lim [] [] packet.proof).run remaining).mapError
      fun failure => { failure, site := {
        phase := .proofDecode
        completedDeclarations
        decoderSteps := lim.maxNodes - remaining
        auditSteps := lim.maxAuditSteps - audit.remaining } }
  let ceiling := packetKernelCeiling lim.kernelHeartbeats.toNat checks checks
  let finalAudit ← (checkFinal checkedEnv lim (USize.ofNat ceiling) audit expected value
    (certificationPrefix.appendCore `proof)).mapError fun failure =>
      { failure, site := {
        phase := .finalProof
        completedDeclarations
        decoderSteps := lim.maxNodes - left
        auditSteps := lim.maxAuditSteps - audit.remaining
        kernelCeiling := some ceiling } }
  return {
    env := checkedEnv
    value
    declarations := entries.size
    constants := finalAudit.seen.size
    decoderSteps := lim.maxNodes - left
    auditSteps := lim.maxAuditSteps - finalAudit.remaining
    kernelChecks := checks }

/-- Compatibility API: the shared detailed checker preserves the original failure. -/
def checkPacket (env : Kernel.Environment) (lim : Limits) (expected : Expr)
    (input : String) : Except Failure Checked :=
  (checkPacketDetailed env lim expected input).mapError (fun f => f.failure)

end

end EDSLGrader.Runtime
