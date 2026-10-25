import tests.And64TestBase
import EDSL.Logical64.Domain
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.And64Regression
open X86 Sequential

def rspBytes : List Byte := [0x48,0x83,0xe4,0xf0,0xc3]
def rspBefore : State := Logical64.Domain.initial rspBytes 1 2
def rspAfter (af : Bool) : State := logical64State rspBefore .band .rsp ((0xf0 : Byte).signExtend 64) 4 af

/-- Current original code/caller authority survives arbitrary RSP arithmetic. -/
theorem original_resources_retained (af : Bool) :
    OS.CallResources.Current (Logical64.Domain.call rspBytes)
      (Logical64.Domain.resource rspBytes 1 2).shared (rspAfter af) := by
  have pre := Logical64.Domain.resource_pre rspBytes (by decide) (by decide) 1 2
  exact pre.current.sameMemory (andImm64_contract rspBefore .rsp 0xf0 af).memory

/-- The real AND succeeds, then RET fails at the changed RSP in current RAM. -/
theorem changed_rsp_return_fails (af : Bool) :
    step af rspBefore = .ok ⟨.next (rspAfter af),[]⟩ ∧
      step false (rspAfter af) = .error (.inaccessibleStack 65536) := by
  cases af <;> constructor <;> cbv

/-- Retaining the original world grants no replacement STACK8 read. -/
theorem no_replacement_stack_permission :
    ¬ OS.CallResources.ReadAllowed (Logical64.Domain.call rspBytes)
      (Logical64.Domain.resource rspBytes 1 2).shared ⟨.stack,65536,8⟩ := by
  intro allowed
  have address := allowed.2.1
  contradiction

/-- Even if replacement bytes are physically readable, a machine RET from
that address is not authorized by the original call's read policy. -/
theorem readable_replacement_still_denied {call : OS.CallResources.Call}
    {shared : OS.CallResources.Shared} {before : State} {target : Word}
    (_current : OS.CallResources.Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.legacy .ret))
    (readable : readWord before.memory (before.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true)
    (different : before.registers .rsp ≠ call.stack) (af : Bool) :
    (∃ final, step af before = .ok ⟨.returned final,[⟨.stack,before.registers .rsp,8⟩]⟩) ∧
      ¬ OS.CallResources.ReadAllowed call shared ⟨.stack,before.registers .rsp,8⟩ := by
  constructor
  · rw [step_eq_execute af decoded]
    refine ⟨{ before.writeRegister .rsp (before.registers .rsp + 8) with rip := target }, ?_⟩
    simp [execute, X86.executeInstruction, X86.executeRet, readable, canonicalTarget,
      Instruction.operandReads]
  · intro allowed
    exact different allowed.2.1
end EDSL.Tests.And64Regression
#print axioms EDSL.Tests.And64Regression.original_resources_retained
#print axioms EDSL.Tests.And64Regression.changed_rsp_return_fails
#print axioms EDSL.Tests.And64Regression.no_replacement_stack_permission
#print axioms EDSL.Tests.And64Regression.readable_replacement_still_denied
#audit_edsl
