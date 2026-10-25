import EDSL.X86.Sequential.AndImmediate64
import EDSL.X86.Sequential.Code
import EDSL.Audit
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.X86.Sequential
/-- Complete ordered helper behavior for canonical REX and the /4 selector.
The result still performs the real immediate fetch and has no following fetch. -/
theorem decodeGroup1Imm64At_and {state : State} {rex modrm : Byte}
    (canonicalREX : rex = 0x48 ∨ rex = 0x49)
    (modrmFetch : fetchByte state.memory (state.rip + 2) = .ok modrm)
    (registerOnly : modrm.toNat / 64 = 3) (group : modrm.toNat / 8 % 8 = 4) :
    decodeGroup1Imm64At state rex = do
      return .andImm64 (rexModRMRM rex modrm) (← fetchByte state.memory (state.rip + 3)) := by
  unfold decodeGroup1Imm64At
  split
  · rename_i invalid
    rcases canonicalREX with rfl | rfl <;> simp at invalid
  · simp only [pure_ok]
    rw [modrmFetch, ok_bind]
    simp [registerOnly, group]

/-- Actual top-level decode, including legacy rejection then sequential canonicalREX
refetch. Each premise is a real canonical executable fetch at its ordered byte. -/
theorem decodeAt_andImm64 {state : State} {rex modrm immediate : Byte}
    (canonicalREX : rex = 0x48 ∨ rex = 0x49)
    (fetch0 : fetchByte state.memory state.rip = .ok rex)
    (fetch1 : fetchByte state.memory (state.rip + 1) = .ok 0x83)
    (fetch2 : fetchByte state.memory (state.rip + 2) = .ok modrm)
    (registerOnly : modrm.toNat / 64 = 3) (group : modrm.toNat / 8 % 8 = 4)
    (fetch3 : fetchByte state.memory (state.rip + 3) = .ok immediate) :
    decodeAt state = .ok (.andImm64 (rexModRMRM rex modrm) immediate) := by
  have helper := decodeGroup1Imm64At_and canonicalREX fetch2 registerOnly group
  rw [fetch3, ok_bind, pure_ok] at helper
  have legacy : X86.decodeAt state = .error (.unsupportedOpcode rex) := by
    unfold X86.decodeAt
    rw [fetch0, ok_bind]
    rcases canonicalREX with rfl | rfl <;> cbv
  have dispatch : decodeNewAt state (.unsupportedOpcode rex) = decodeREXWAt state rex := by
    unfold decodeNewAt
    rw [fetch0, ok_bind]
    rcases canonicalREX with rfl | rfl <;> simp [rex32Prefix, rexWPrefix]
  rw [decodeAt, legacy]
  change decodeNewAt state (.unsupportedOpcode rex) = _
  rw [dispatch]
  unfold decodeREXWAt
  rw [fetch1, ok_bind]
  simp only [↓reduceIte]
  exact helper

/-- Unsupported REX.R/X aliases reject before an absent ModRM. -/
theorem decodeGroup1Imm64At_alias (state : State) (rex : Byte)
    (not48 : rex ≠ 0x48) (not49 : rex ≠ 0x49) :
    decodeGroup1Imm64At state rex = .error .unsupportedEncoding := by
  unfold decodeGroup1Imm64At
  rw [ite_eq_left ⟨not48, not49⟩]
  rfl

/-- Memory /4 rejects at ModRM without any immediate/SIB/displacement premise. -/
theorem decodeGroup1Imm64At_memory {state : State} {rex modrm : Byte}
    (_canonicalREX : rex = 0x48 ∨ rex = 0x49)
    (fetch2 : fetchByte state.memory (state.rip + 2) = .ok modrm)
    (memoryForm : modrm.toNat / 64 ≠ 3) :
    decodeGroup1Imm64At state rex = .error .unsupportedEncoding := by
  unfold decodeGroup1Imm64At
  split
  · rfl
  · simp only [pure_ok]
    rw [fetch2, ok_bind]
    rw [ite_eq_left memoryForm]
    rfl

/-- Required immediate faults are retained exactly after a supported selector. -/
theorem decodeGroup1Imm64At_and_fault {state : State} {rex modrm : Byte} {fault : Error}
    (canonicalREX : rex = 0x48 ∨ rex = 0x49)
    (fetch2 : fetchByte state.memory (state.rip + 2) = .ok modrm)
    (registerOnly : modrm.toNat / 64 = 3) (group : modrm.toNat / 8 % 8 = 4)
    (fetch3 : fetchByte state.memory (state.rip + 3) = .error fault) :
    decodeGroup1Imm64At state rex = .error fault := by
  rw [decodeGroup1Imm64At_and canonicalREX fetch2 registerOnly group, fetch3, error_bind]

/-- Relocation inherits production successful-fetch transport and requires no
byte beyond the actual instruction window. This theorem asserts successes only. -/
theorem decodeAt_andImm64_transport {source destination : State} {register : Register} {imm : Byte}
    (transport : SuccessfulFetchTransport source destination)
    (decoded : decodeAt source = .ok (.andImm64 register imm)) :
    decodeAt destination = .ok (.andImm64 register imm) := decodeAt_transport transport decoded
end EDSL.X86.Sequential
#print axioms EDSL.X86.Sequential.decodeAt_andImm64
#print axioms EDSL.X86.Sequential.decodeGroup1Imm64At_and
#print axioms EDSL.X86.Sequential.decodeGroup1Imm64At_alias
#print axioms EDSL.X86.Sequential.decodeGroup1Imm64At_memory
#print axioms EDSL.X86.Sequential.decodeGroup1Imm64At_and_fault
#audit_edsl
