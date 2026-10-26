/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Source.Syntax

set_option autoImplicit false

namespace EDSL.Source.IntegerPromotions

/-! Numeric integer promotion for the admitted small and full int types.
The input's representability proof and the target's explicit numeric bounds
suffice: these theorems assume no source execution or `NoUB` premise. They do
not establish an ABI, storage representation, compiler correspondence, or
support for any other small conversion or integer type.
-/

private theorem rangeBits_le_intBits (target : Target) (source : SmallType) :
    source.rangeBits target ≤ target.intBits := by
  have minimum := target.atLeast16
  have chars := target.charLeShort
  have shorts := target.shortLeInt
  cases source <;> simp only [SmallType.rangeBits] <;> omega

private theorem signed_range_embeddable {target : Target} {source : SmallType}
    (value : Value target (.small source)) (signed : source.isSigned target = true) :
    -target.signedBound ≤ value.toInt ∧ value.toInt < target.signedBound := by
  have bounds := value.property
  simp only [SmallType.lowerBound, SmallType.upperBound, signed, ↓reduceIte] at bounds
  have exponent := Nat.sub_le_sub_right (rangeBits_le_intBits target source) 1
  have power := Nat.pow_le_pow_right (n := 2) (by decide +kernel) exponent
  have inclusion := Int.ofNat_le.mpr power
  change ((2 ^ (source.rangeBits target - 1) : Nat) : Int) ≤
    target.signedBound at inclusion
  change -target.signedBound ≤ value.val ∧ value.val < target.signedBound
  omega

private theorem unsigned_range_embeddable_sint {target : Target} {source : SmallType}
    (value : Value target (.small source)) (unsigned : source.isSigned target = false)
    (narrow : source.rangeBits target < target.intBits) :
    -target.signedBound ≤ value.toInt ∧ value.toInt < target.signedBound := by
  have bounds := value.property
  simp only [SmallType.lowerBound, SmallType.upperBound, unsigned,
    Bool.false_eq_true, ↓reduceIte] at bounds
  have exponent : source.rangeBits target ≤ target.intBits - 1 := by omega
  have power := Nat.pow_le_pow_right (n := 2) (by decide +kernel) exponent
  have inclusion := Int.ofNat_le.mpr power
  change ((2 ^ source.rangeBits target : Nat) : Int) ≤ target.signedBound at inclusion
  have positive : 0 < target.signedBound := Int.natCast_pos.mpr (Nat.two_pow_pos _)
  change -target.signedBound ≤ value.val ∧ value.val < target.signedBound
  omega

private theorem unsigned_range_embeddable_uint {target : Target} {source : SmallType}
    (value : Value target (.small source)) (unsigned : source.isSigned target = false) :
    0 ≤ value.toInt ∧ value.toInt < (target.modulus : Int) := by
  have bounds := value.property
  simp only [SmallType.lowerBound, SmallType.upperBound, unsigned,
    Bool.false_eq_true, ↓reduceIte] at bounds
  have power := Nat.pow_le_pow_right (n := 2) (by decide +kernel)
    (rangeBits_le_intBits target source)
  have inclusion := Int.ofNat_le.mpr power
  change ((2 ^ source.rangeBits target : Nat) : Int) ≤ (target.modulus : Int) at inclusion
  change 0 ≤ value.val ∧ value.val < (target.modulus : Int)
  omega

private theorem promotedType_small (target : Target) (source : SmallType) :
    promotedType target (.small source) =
      if source.isSigned target then .sint
      else if source.rangeBits target < target.intBits then .sint else .uint := by
  have boolean_narrow : 1 < target.intBits := by have minimum := target.atLeast16; omega
  cases source <;> simp [promotedType, SmallType.isSigned, SmallType.rangeBits, boolean_narrow]

/-- Every small value lies in the selected full type's range. This proves
embeddability of its original integer, independently of the promotion map. -/
theorem small_range_embeddable {target : Target} {source : SmallType}
    (value : Value target (.small source)) :
    (promotedType target (.small source)).asIntType.lowerBound target ≤ value.toInt ∧
      value.toInt < (promotedType target (.small source)).asIntType.upperBound target := by
  rw [promotedType_small]
  split
  · exact signed_range_embeddable value ‹source.isSigned target = true›
  · have unsigned : source.isSigned target = false := by
      cases signed : source.isSigned target <;> simp_all
    split
    · exact unsigned_range_embeddable_sint value unsigned
        ‹source.rangeBits target < target.intBits›
    · exact unsigned_range_embeddable_uint value unsigned

/-- Build a full typed value only after proving that the original integer fits.
The uint branch uses `toNat` under a nonnegativity proof, never modulo. -/
private def embedValue {target : Target} (destination : ArithmeticType) (z : Int)
    (bounds : destination.asIntType.lowerBound target ≤ z ∧
      z < destination.asIntType.upperBound target) : Value target destination.asIntType := by
  cases destination with
  | sint => exact ⟨z, bounds⟩
  | uint =>
      exact ⟨z.toNat, by
        change 0 ≤ z ∧ z < (target.modulus : Int) at bounds
        omega⟩

private theorem embedValue_toInt {target : Target} (destination : ArithmeticType) (z : Int)
    (bounds : destination.asIntType.lowerBound target ≤ z ∧
      z < destination.asIntType.upperBound target) :
    (embedValue destination z bounds).toInt = z := by
  cases destination with
  | sint => rfl
  | uint => exact Int.toNat_of_nonneg bounds.1

/-- Promotion preserves the mathematical integer. Full uint/sint branches are
definitionally the identity; small branches embed using their proved ranges. -/
def promoteValue {target : Target} {source : IntType} (value : Value target source) :
    Value target (promotedType target source).asIntType :=
  match source with
  | .uint => value
  | .sint => value
  | .small _ => embedValue _ value.toInt (small_range_embeddable value)

/-- Numeric preservation for every admitted target, type and value. -/
theorem promoteValue_toInt {target : Target} {source : IntType} (value : Value target source) :
    (promoteValue value).toInt = value.toInt := by
  cases source with
  | uint => rfl
  | sint => rfl
  | small _ => exact embedValue_toInt _ _ _

theorem promoteValue_nonnegative_iff {target : Target} {source : IntType}
    (value : Value target source) :
    0 ≤ (promoteValue value).toInt ↔ 0 ≤ value.toInt := by rw [promoteValue_toInt]

theorem promoteValue_negative_iff {target : Target} {source : IntType}
    (value : Value target source) :
    (promoteValue value).toInt < 0 ↔ value.toInt < 0 := by rw [promoteValue_toInt]

theorem promoteValue_zero_iff {target : Target} {source : IntType}
    (value : Value target source) :
    (promoteValue value).toInt = 0 ↔ value.toInt = 0 := by rw [promoteValue_toInt]

theorem promoteValue_nonzero_iff {target : Target} {source : IntType}
    (value : Value target source) :
    (promoteValue value).toInt ≠ 0 ↔ value.toInt ≠ 0 := by rw [promoteValue_toInt]

end EDSL.Source.IntegerPromotions
