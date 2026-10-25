import tests.And64TestBase
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.And64Regression
open X86 Sequential
/-- The /4 selector is not a GPR field; each actual r/m selects its own bank.
Immediate is symbolic: all 256 byte values are covered, without sampled masks. -/
theorem all_banks (imm : Byte) :
    Sequential.decodeAt (codeState [0x48,0x83,0xe0,imm] 0) = .ok (.andImm64 .rax imm) ∧
    Sequential.decodeAt (codeState [0x48,0x83,0xe1,imm] 0) = .ok (.andImm64 .rcx imm) ∧
    Sequential.decodeAt (codeState [0x48,0x83,0xe2,imm] 0) = .ok (.andImm64 .rdx imm) ∧
    Sequential.decodeAt (codeState [0x48,0x83,0xe3,imm] 0) = .ok (.andImm64 .rbx imm) ∧
    Sequential.decodeAt (codeState [0x48,0x83,0xe4,imm] 0) = .ok (.andImm64 .rsp imm) ∧
    Sequential.decodeAt (codeState [0x48,0x83,0xe5,imm] 0) = .ok (.andImm64 .rbp imm) ∧
    Sequential.decodeAt (codeState [0x48,0x83,0xe6,imm] 0) = .ok (.andImm64 .rsi imm) ∧
    Sequential.decodeAt (codeState [0x48,0x83,0xe7,imm] 0) = .ok (.andImm64 .rdi imm) ∧
    Sequential.decodeAt (codeState [0x49,0x83,0xe0,imm] 0) = .ok (.andImm64 .r8 imm) ∧
    Sequential.decodeAt (codeState [0x49,0x83,0xe1,imm] 0) = .ok (.andImm64 .r9 imm) ∧
    Sequential.decodeAt (codeState [0x49,0x83,0xe2,imm] 0) = .ok (.andImm64 .r10 imm) ∧
    Sequential.decodeAt (codeState [0x49,0x83,0xe3,imm] 0) = .ok (.andImm64 .r11 imm) ∧
    Sequential.decodeAt (codeState [0x49,0x83,0xe4,imm] 0) = .ok (.andImm64 .r12 imm) ∧
    Sequential.decodeAt (codeState [0x49,0x83,0xe5,imm] 0) = .ok (.andImm64 .r13 imm) ∧
    Sequential.decodeAt (codeState [0x49,0x83,0xe6,imm] 0) = .ok (.andImm64 .r14 imm) ∧
    Sequential.decodeAt (codeState [0x49,0x83,0xe7,imm] 0) = .ok (.andImm64 .r15 imm) := by
  repeat' apply And.intro
  all_goals cbv
end EDSL.Tests.And64Regression
#print axioms EDSL.Tests.And64Regression.all_banks
#audit_edsl
