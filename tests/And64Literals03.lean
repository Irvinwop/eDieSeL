import tests.And64TestBase
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.And64Regression
open X86 Sequential
theorem negative_boundary (af : Bool) : view .rax af (initial [0x48,0x83,0xe0,0x80] .rax 0xffffffffffffffff) = some (0xffffffffffffff80,0x682,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.negative_boundary
theorem minus_one (af : Bool) : view .rax af (initial [0x48,0x83,0xe0,0xff] .rax 0xffffffffffffffff) = some (0xffffffffffffffff,0x686,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.minus_one
theorem zero_mask (af : Bool) : view .rax af (initial [0x48,0x83,0xe0,0x00] .rax 0xffffffffffffffff) = some (0x0000000000000000,0x646,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.zero_mask
theorem lowbyte_parity (af : Bool) : view .rax af (initial [0x48,0x83,0xe0,0xf8] .rax 0x0000000100000008) = some (0x0000000100000008,0x602,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.lowbyte_parity
end EDSL.Tests.And64Regression
#audit_edsl
