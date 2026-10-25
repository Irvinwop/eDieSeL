import tests.And64TestBase
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.And64Regression
open X86 Sequential
theorem frozen_sum (af : Bool) : view .rcx af (initial [0x48,0x83,0xe1,0xf8] .rcx 0x800000010000000f) = some (0x8000000100000008,0x682,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.frozen_sum
theorem full_zero_flag (af : Bool) : view .rcx af (initial [0x48,0x83,0xe1,0xf8] .rcx 0x0000000100000007) = some (0x0000000100000000,0x606,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.full_zero_flag
theorem frozen_extended (af : Bool) : view .r8 af (initial [0x49,0x83,0xe0,0xf8] .r8 0x8000000000000007) = some (0x8000000000000000,0x686,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.frozen_extended
theorem frozen_count_dot (af : Bool) : view .rcx af (initial [0x48,0x83,0xe1,0xfc] .rcx 0xffff000000000003) = some (0xffff000000000000,0x686,af,4,[]) := by
  cases af <;> cbv
#print axioms EDSL.Tests.And64Regression.frozen_count_dot
end EDSL.Tests.And64Regression
#audit_edsl
