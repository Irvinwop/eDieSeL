/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ByteComparePadding
import EDSL.X86.Sequential.MachineChoices

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

/-- Authenticate any supported exact NOP in current executable memory. Only
the instruction's bytes need fetch authority; apparent operands and bytes
following the instruction impose no premise. Hardware correspondence retains
the existing targetProfile and exact-form support assumptions. -/
theorem NopEncoding.decode_at (before : State) (encoding : NopEncoding)
    (code : CodeAt before.memory before.rip encoding.bytes) :
    decodeAt before = .ok (.nop encoding) := by
  have fetched := code_fetch_transport_of_bound code
    (by cases encoding <;> decide) 0 (by cases encoding <;> decide)
    before rfl (by simp)
  exact decodeAt_transport fetched (NopEncoding.decode_bytes encoding)

/-- Full state and empty operand-read trace for an actual decoded NOP, at any
authenticated code address. No data permission or operand canonicality premise
is introduced. Generic WP, policy and retirement rules apply unchanged. -/
theorem step_nop_context (before : State) (encoding : NopEncoding)
    (code : CodeAt before.memory before.rip encoding.bytes) (choice : Bool) :
    step choice before =
      .ok ⟨.next { before with rip := before.rip + BitVec.ofNat 64 encoding.length }, []⟩ := by
  exact (step_eq_execute choice (NopEncoding.decode_at before encoding code)).trans
    (execute_nop before encoding choice)

/-- The same complete observation for every independent flag-choice vector.
This reuses production registration and Bool execution, without restricting
the vector stream or interpreting the apparent operand address. -/
theorem stepWith_nop_context (before : State) (encoding : NopEncoding)
    (code : CodeAt before.memory before.rip encoding.bytes) (choices : FlagChoices) :
    stepWith choices before =
      .ok ⟨.next { before with rip := before.rip + BitVec.ofNat 64 encoding.length }, []⟩ := by
  rw [stepWith_eq_executeWith choices (NopEncoding.decode_at before encoding code)]
  exact execute_nop before encoding false

end EDSL.X86.Sequential
