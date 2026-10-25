import tests.And64TestBase
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.And64Regression
open X86 Sequential
/-- Group 0/4/5/7 retain ADD/AND/SUB/CMP behavior at full width. Arithmetic
AF is defined and independent of the supplied logical undefined-flag choice. -/
theorem group_behavior (af : Bool) :
    view .rax af (initial [0x48,0x83,0xc0,1] .rax 0xffffffffffffffff) =
      some (0,0x647,true,4,[]) ∧
    view .rax af (initial [0x48,0x83,0xe0,0xf8] .rax 0x800000010000000f) =
      some (0x8000000100000008,0x682,af,4,[]) ∧
    view .r8 af (initial [0x49,0x83,0xe8,1] .r8 0) =
      some (0xffffffffffffffff,0x687,true,4,[]) ∧
    view .r8 af (initial [0x49,0x83,0xf8,1] .r8 0) =
      some (0,0x687,true,4,[]) ∧
    Sequential.decodeAt (codeState [0x49,0x83,0xc0] 0) = .error .unsupportedEncoding := by
  cases af <;> refine ⟨?_,?_,?_,?_,?_⟩ <;> cbv
end EDSL.Tests.And64Regression
#print axioms EDSL.Tests.And64Regression.group_behavior
#audit_edsl
