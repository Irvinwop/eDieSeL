import tests.And64MaskSplit
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.And64MaskSplitMutants
open X86 Sequential Logical64

def widthBytes : List Byte := EDSL.Tests.And64MaskSplit.bytes.set 9 0x41
def maskBytes : List Byte := EDSL.Tests.And64MaskSplit.bytes.set 12 0xf0

def output (bytes : List Byte) (left right : Word) : Option Word := do
  let result ← (Sequential.run (fun _ => false) 7 (Logical64.Domain.initial bytes left right)).toOption
  return result.state.registers .rax

/-- Distinct, nonzero inputs share bit40; a low32 AND loses that shared bit. -/
theorem bad_width_returns_wrong_high_bit : output widthBytes 0x10000000001 0x10000000002 = some 0 := by cbv
/-- Distinct, nonzero inputs share bit3; -16 removes it and the low3 part cannot restore it. -/
theorem bad_mask_returns_wrong_low_bit : output maskBytes 9 10 = some 0 := by cbv

theorem width_expected_bit : HasBit (0x10000000001 : Word) ⟨40,by decide⟩ ∧
    HasBit (0x10000000002 : Word) ⟨40,by decide⟩ ∧ ¬HasBit (0 : Word) ⟨40,by decide⟩ := by
  unfold HasBit
  decide
theorem mask_expected_bit : HasBit (9 : Word) ⟨3,by decide⟩ ∧
    HasBit (10 : Word) ⟨3,by decide⟩ ∧ ¬HasBit (0 : Word) ⟨3,by decide⟩ := by
  unfold HasBit
  decide

theorem width_result_violates_task : ¬MathematicalResult .intersection
    (0x10000000001 : Word) (0x10000000002 : Word) 0 := by
  intro correct
  exact width_expected_bit.2.2 ((correct ⟨40,by decide⟩).mpr
    ⟨width_expected_bit.1,width_expected_bit.2.1⟩)
theorem mask_result_violates_task : ¬MathematicalResult .intersection (9 : Word) 10 0 := by
  intro correct
  exact mask_expected_bit.2.2 ((correct ⟨3,by decide⟩).mpr
    ⟨mask_expected_bit.1,mask_expected_bit.2.1⟩)
end EDSL.Tests.And64MaskSplitMutants
#print axioms EDSL.Tests.And64MaskSplitMutants.bad_width_returns_wrong_high_bit
#print axioms EDSL.Tests.And64MaskSplitMutants.bad_mask_returns_wrong_low_bit
#print axioms EDSL.Tests.And64MaskSplitMutants.width_result_violates_task
#print axioms EDSL.Tests.And64MaskSplitMutants.mask_result_violates_task
#audit_edsl
