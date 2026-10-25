/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Sub64
import EDSL.OS.CallResources
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

/-- Authenticated SUB retains current code/caller loans in the same complete
OS world. A changed RSP gains no authority at the replacement return address. -/
theorem current_subReg64_step {call : OS.CallResources.Call} {shared : OS.CallResources.Shared}
    {before : State} {destination source : Register}
    (current : OS.CallResources.Current call shared before)
    (decoded : decodeAt before = .ok (.subReg64 destination source)) (choice : Bool) :
    ∃ after, step choice before = .ok ⟨.next after, []⟩ ∧
      OS.CallResources.Current call shared after ∧
      Sub64Contract before after destination (before.registers source) 3 := by
  obtain ⟨after, executed, contract⟩ := execute_subReg64_contract before destination source choice
  refine ⟨after, ?_, current.sameMemory contract.memory, contract⟩
  rw [step_eq_execute choice decoded]
  exact executed

theorem current_subImm64_step {call : OS.CallResources.Call} {shared : OS.CallResources.Shared}
    {before : State} {destination : Register} {immediate : Byte}
    (current : OS.CallResources.Current call shared before)
    (decoded : decodeAt before = .ok (.subImm64 destination immediate)) (choice : Bool) :
    ∃ after, step choice before = .ok ⟨.next after, []⟩ ∧
      OS.CallResources.Current call shared after ∧
      Sub64Contract before after destination (immediate.signExtend 64) 4 := by
  obtain ⟨after, executed, contract⟩ := execute_subImm64_contract before destination immediate choice
  refine ⟨after, ?_, current.sameMemory contract.memory, contract⟩
  rw [step_eq_execute choice decoded]
  exact executed

/-- Vector execution uses the same fully defined arithmetic state, retaining
all current authority without assuming uniform or future choice streams. -/
theorem current_subReg64_stepWith {call : OS.CallResources.Call}
    {shared : OS.CallResources.Shared} {before : State} {destination source : Register}
    (current : OS.CallResources.Current call shared before)
    (decoded : decodeAt before = .ok (.subReg64 destination source)) (choices : FlagChoices) :
    ∃ after, stepWith choices before = .ok ⟨.next after, []⟩ ∧
      OS.CallResources.Current call shared after ∧
      Sub64Contract before after destination (before.registers source) 3 := by
  let after := sub64State before destination (before.registers source) 3
  have contract : Sub64Contract before after destination (before.registers source) 3 :=
    sub64State_contract ..
  refine ⟨after, ?_, current.sameMemory contract.memory, contract⟩
  rw [stepWith_eq_executeWith choices decoded, executeWith_subReg64]

theorem current_subImm64_stepWith {call : OS.CallResources.Call}
    {shared : OS.CallResources.Shared} {before : State} {destination : Register} {immediate : Byte}
    (current : OS.CallResources.Current call shared before)
    (decoded : decodeAt before = .ok (.subImm64 destination immediate)) (choices : FlagChoices) :
    ∃ after, stepWith choices before = .ok ⟨.next after, []⟩ ∧
      OS.CallResources.Current call shared after ∧
      Sub64Contract before after destination (immediate.signExtend 64) 4 := by
  let after := sub64State before destination (immediate.signExtend 64) 4
  have contract : Sub64Contract before after destination (immediate.signExtend 64) 4 :=
    sub64State_contract ..
  refine ⟨after, ?_, current.sameMemory contract.memory, contract⟩
  rw [stepWith_eq_executeWith choices decoded, executeWith_subImm64]

end EDSL.X86.Sequential

#print axioms EDSL.X86.Sequential.current_subReg64_step
#print axioms EDSL.X86.Sequential.current_subImm64_step
#print axioms EDSL.X86.Sequential.current_subReg64_stepWith
#print axioms EDSL.X86.Sequential.current_subImm64_stepWith
#audit_edsl
