/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.BufferCall.Resources

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.BufferCall
open X86 X86.Sequential

/-- Reuse a verified behavior under a second independently stated contract.
The target can restrict the mathematical domain and require a consequence of
source results. Arguments, complete snapshots and current resource footprints
are identical after translating inputs. Clients must state and review these
mathematical obligations independently of program execution or admission.
Trusted registration still fixes
which specification a grader requires; candidates cannot select it. -/
structure Refinement (source target : Spec) where
  translate : target.Input → source.Input
  arguments : ∀ value, source.arguments (translate value) = target.arguments value
  buffers : ∀ value, source.buffers (translate value) = target.buffers value
  domain : ∀ value, target.domain value → source.domain (translate value)
  result : ∀ value actual, target.domain value →
    source.result (translate value) actual → target.result value actual

namespace Refinement
variable {source middle target : Spec}

def refl (spec : Spec) : Refinement spec spec where
  translate := id
  arguments _ := rfl
  buffers _ := rfl
  domain _ admitted := admitted
  result _ _ _ correct := correct

/-- Refinements compose without executing or inspecting a candidate. -/
def trans (first : Refinement source middle) (second : Refinement middle target) :
    Refinement source target where
  translate value := first.translate (second.translate value)
  arguments value := (first.arguments _).trans (second.arguments value)
  buffers value := (first.buffers _).trans (second.buffers value)
  domain value admitted := first.domain _ (second.domain value admitted)
  result value actual admitted correct := second.result value actual admitted
    (first.result _ actual (second.domain value admitted) correct)

def invocation (r : Refinement source target) (input : Invocation target) : Invocation source :=
  ⟨r.translate input.value, input.returnAddress⟩

/-- Only the logical value changes. The manager, caller, original loan IDs,
return slot, exact code span and complete memory remain the same objects. -/
def resource (r : Refinement source target) (original : Resources target) : Resources source :=
  ⟨original.shared, original.call, r.translate original.value, original.inputLoan⟩

theorem bound (r : Refinement source target) {value : target.Input} {state : State}
    (admitted : Bound target value state) : Bound source (r.translate value) state := by
  intro index argument binding
  apply admitted index argument
  simpa only [r.arguments value] using binding

theorem pre (r : Refinement source target) {bytes : List Byte}
    {input : Invocation target} {initial : State} (admitted : Pre target bytes input initial) :
    Pre source bytes (r.invocation input) initial := by
  refine ⟨r.domain _ admitted.domain, r.bound admitted.arguments, ?_, admitted.code,
    admitted.stack, admitted.returnCanonical, admitted.stackBound, admitted.postStackCanonical⟩
  intro buffer member
  apply admitted.buffers buffer
  simpa only [invocation, r.buffers input.value] using member

theorem post (r : Refinement source target) {input : Invocation target} {initial final : State}
    (domain : target.domain input.value)
    (correct : Post source (r.invocation input) initial final) : Post target input initial final :=
  ⟨r.result _ _ domain correct.result, correct.memory, correct.returnAddress,
    correct.stackPointer, correct.preserved, correct.flags⟩

/-- Exact equivalence retains every complete snapshot and original loan;
refinement neither grants a new permission nor discards an input resource. -/
theorem contract_iff (r : Refinement source target) (original : Resources target)
    (shared : OS.Borrowing.State) :
    ResourceContract (r.resource original) shared ↔ ResourceContract original shared := by
  constructor
  · intro admitted
    refine ⟨admitted.call, ?_, ?_⟩
    · intro buffer member
      exact admitted.buffers buffer (by simpa only [resource, r.buffers original.value] using member)
    · intro buffer member nonempty
      exact admitted.inputs buffer (by simpa only [resource, r.buffers original.value] using member) nonempty
  · intro admitted
    refine ⟨admitted.call, ?_, ?_⟩
    · intro buffer member
      exact admitted.buffers buffer (by simpa only [resource, r.buffers original.value] using member)
    · intro buffer member nonempty
      exact admitted.inputs buffer (by simpa only [resource, r.buffers original.value] using member) nonempty

theorem current_iff (r : Refinement source target) (original : Resources target) (state : State) :
    Current (r.resource original) state ↔ Current original state := by
  constructor
  · intro admitted
    exact ⟨(r.contract_iff original _).mp admitted.contract, admitted.coupled⟩
  · intro admitted
    exact ⟨(r.contract_iff original _).mpr admitted.contract, admitted.coupled⟩

theorem readAllowed_iff (r : Refinement source target) (original : Resources target) (read : Read) :
    ReadAllowed (r.resource original) read ↔ ReadAllowed original read := by
  change (OS.CallResources.ReadAllowed original.call original.shared read ∨
    (DataRead (source.buffers (r.translate original.value)) read ∧
      OS.ArrayResources.ReadPermission original.shared original.call.worker read)) ↔ _
  rw [r.buffers original.value]
  rfl

theorem resourcePre (r : Refinement source target) {bytes : List Byte}
    {original : Resources target} {initial : State}
    (admitted : ResourcePre target bytes original initial) :
    ResourcePre source bytes (r.resource original) initial :=
  ⟨(r.current_iff original initial).mpr admitted.current, admitted.code,
    admitted.entry, admitted.stack, r.domain _ admitted.domain, r.bound admitted.arguments⟩

/-- Reuse universal total correctness, every-prefix current authority, exact
operand-read permissions, return/ABI frames and all independent AF choices.
Useful-domain nonvacuity remains a separate target obligation. -/
theorem semantics (r : Refinement source target) {bytes : List Byte}
    (verified : Grading.ReadOnlySemanticClaim (readOnlyTask source) bytes) :
    Grading.ReadOnlySemanticClaim (readOnlyTask target) bytes := by
  constructor
  · intro input initial admitted
    obtain ⟨executions, policy⟩ := verified.machine (r.invocation input) initial (r.pre admitted)
    refine ⟨?_, policy⟩
    intro choices
    obtain ⟨result, execution, correct⟩ := executions choices
    exact ⟨result, execution, r.post admitted.domain correct⟩
  · intro original initial admitted
    obtain ⟨executions, policy⟩ := verified.resource (r.resource original) initial (r.resourcePre admitted)
    refine ⟨?_, policy.mono (fun state current => (r.current_iff original state).mp current)
      (fun _ read allowed => (r.readAllowed_iff original read).mp allowed)⟩
    intro choices
    obtain ⟨result, execution, correct, current⟩ := executions choices
    exact ⟨result, execution, r.post admitted.domain correct,
      (r.current_iff original result.state).mp current⟩

#print axioms contract_iff
#print axioms readAllowed_iff
#print axioms semantics
end Refinement
end EDSL.BufferCall
