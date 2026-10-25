import EDSL.X86.Sequential.AndImmediate64
import EDSL.OS.CallResources
import EDSL.OS.ArrayResourcesModel
import EDSL.Audit
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.X86.Sequential
/-- Original resources and the entire OS world persist, including for RSP.
No return from a changed RSP or replacement stack loan is implied. -/
theorem current_andImm64_step {call : OS.CallResources.Call} {shared : OS.CallResources.Shared}
    {before : State} {destination : Register} {immediate : Byte}
    (current : OS.CallResources.Current call shared before)
    (decoded : decodeAt before = .ok (.andImm64 destination immediate)) (af : Bool) :
    ∃ after, step af before = .ok ⟨.next after, []⟩ ∧
      OS.CallResources.Current call shared after ∧
      AndImmediate64Contract before after destination immediate af := by
  exact ⟨_, step_andImm64 decoded af,
    current.sameMemory (andImm64_contract ..).memory, andImm64_contract ..⟩
theorem current_andImm64_stepWith {call : OS.CallResources.Call} {shared : OS.CallResources.Shared}
    {before : State} {destination : Register} {immediate : Byte}
    (current : OS.CallResources.Current call shared before)
    (decoded : decodeAt before = .ok (.andImm64 destination immediate)) (choices : FlagChoices) :
    ∃ after, stepWith choices before = .ok ⟨.next after, []⟩ ∧
      OS.CallResources.Current call shared after ∧
      AndImmediate64Contract before after destination immediate choices.af := by
  exact ⟨_, stepWith_andImm64 decoded choices,
    current.sameMemory (andImm64_contract ..).memory, andImm64_contract ..⟩
theorem array_andImm64_step {call : OS.ArrayResources.Call} {shared : OS.Borrowing.State}
    {before : State} {destination : Register} {immediate : Byte}
    (admitted : OS.ArrayResources.Admission shared call before)
    (decoded : decodeAt before = .ok (.andImm64 destination immediate)) (af : Bool) :
    ∃ after, step af before = .ok ⟨.next after, []⟩ ∧
      OS.ArrayResources.Admission shared call after :=
  ⟨_, step_andImm64 decoded af, admitted.unchangedMemory (andImm64_contract ..).memory⟩
theorem array_andImm64_stepWith {call : OS.ArrayResources.Call} {shared : OS.Borrowing.State}
    {before : State} {destination : Register} {immediate : Byte}
    (admitted : OS.ArrayResources.Admission shared call before)
    (decoded : decodeAt before = .ok (.andImm64 destination immediate)) (choices : FlagChoices) :
    ∃ after, stepWith choices before = .ok ⟨.next after, []⟩ ∧
      OS.ArrayResources.Admission shared call after :=
  ⟨_, stepWith_andImm64 decoded choices,
    admitted.unchangedMemory (andImm64_contract ..).memory⟩
end EDSL.X86.Sequential
#print axioms EDSL.X86.Sequential.current_andImm64_step
#print axioms EDSL.X86.Sequential.current_andImm64_stepWith
#print axioms EDSL.X86.Sequential.array_andImm64_step
#print axioms EDSL.X86.Sequential.array_andImm64_stepWith
#audit_edsl
