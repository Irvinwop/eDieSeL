import tests.And64TestBase
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.And64Regression
open X86 Sequential
theorem frozen_reverse (af : Bool) : view .rdx af (initial [0x48,0x83,0xe2,0xfe] .rdx 0x8000000000000001) = some (0x8000000000000000,0x686,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.frozen_reverse
theorem frozen_fill_zero (af : Bool) : view .rax af (initial [0x48,0x83,0xe0,0xf8] .rax 0x0000000000000007) = some (0x0000000000000000,0x646,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.frozen_fill_zero
theorem frozen_prefix (af : Bool) : view .rsi af (initial [0x48,0x83,0xe6,0xfc] .rsi 0x8000000100000007) = some (0x8000000100000004,0x682,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.frozen_prefix
theorem positive_boundary (af : Bool) : view .rax af (initial [0x48,0x83,0xe0,0x7f] .rax 0xffffffffffffffff) = some (0x000000000000007f,0x602,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.positive_boundary
end EDSL.Tests.And64Regression
#audit_edsl
