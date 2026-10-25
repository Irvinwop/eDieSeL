import tests.And64TestBase
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.And64Regression
open X86 Sequential
theorem not_bit31_sign (af : Bool) : view .rax af (initial [0x48,0x83,0xe0,0xf8] .rax 0x0000000080000008) = some (0x0000000080000008,0x602,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.not_bit31_sign
theorem only_bit63_sign (af : Bool) : view .rax af (initial [0x48,0x83,0xe0,0xf8] .rax 0x8000000000000008) = some (0x8000000000000008,0x682,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.only_bit63_sign
theorem and_not_xor (af : Bool) : view .rax af (initial [0x48,0x83,0xe0,0x01] .rax 0x0000000000000003) = some (0x0000000000000001,0x602,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.and_not_xor
theorem rsp_resource (af : Bool) : view .rsp af (initial [0x48,0x83,0xe4,0xf0] .rsp 0x0000000000002008) = some (0x0000000000002000,0x606,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.rsp_resource
end EDSL.Tests.And64Regression
#audit_edsl
