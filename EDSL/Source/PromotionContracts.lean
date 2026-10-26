/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.ArithmeticConversions
import EDSL.Source.VCGen
import EDSL.Source.Examples

set_option autoImplicit false

namespace EDSL.Source.PromotionContracts

/-- An admitted input witness independent of future execution. -/
def zeroValue (target : Target) : (ty : IntType) → Value target ty
  | .uint => ⟨0, target.modulus_pos⟩
  | .sint => ⟨0, by have positive := target.signedBound_pos; omega⟩
  | .small ty => ⟨0, by
      have signedPositive : (0 : Int) < (2 ^ (ty.rangeBits target - 1) : Nat) :=
        Int.natCast_pos.mpr (Nat.two_pow_pos _)
      have unsignedPositive : (0 : Int) < (2 ^ ty.rangeBits target : Nat) :=
        Int.natCast_pos.mpr (Nat.two_pow_pos _)
      by_cases signed : ty.isSigned target = true
      · simp only [SmallType.lowerBound, SmallType.upperBound, signed, ↓reduceIte]
        omega
      · simp only [SmallType.lowerBound, SmallType.upperBound, signed]
        omega⟩

def promoteReturn (target : Target) (dialect : Dialect) (source : IntType) :
    Program target [source] (promotedType target source).asIntType :=
  ⟨dialect, .gnuModulo, .promote (.param .here)⟩

/-- For every admitted type/profile and every input, actual source promotion
preserves the mathematical value. The certificate contains no NoUB premise. -/
theorem promoteReturn_certificate (target : Target) (dialect : Dialect) (source : IntType) :
    Certificate (promoteReturn target dialect source) (fun _ => True)
      (fun inputs result => result.toInt = (inputs.get .here).toInt) := by
  refine certificate_of_vc ⟨.cons (zeroValue target source) .nil, trivial⟩ ?_
  intro inputs _
  change (IntegerPromotions.promoteValue (inputs.get .here)).toInt =
    (inputs.get .here).toInt
  exact IntegerPromotions.promoteValue_toInt _

theorem promoteReturn_noUB (target : Target) (dialect : Dialect) (source : IntType) :
    NoUB (promoteReturn target dialect source) (fun _ => True) :=
  (promoteReturn_certificate target dialect source).noUB

theorem two_lt_signedBound (target : Target) : (2 : Int) < target.signedBound := by
  have exponent : 2 ≤ target.intBits - 1 := by
    have minimum := target.atLeast16
    omega
  have power : (4 : Nat) ≤ 2 ^ (target.intBits - 1) :=
    Nat.pow_le_pow_right (n := 2) (i := 2) (by decide) exponent
  change (2 : Int) < ((2 ^ (target.intBits - 1) : Nat) : Int)
  omega

def booleanAdd (target : Target) (dialect : Dialect) :
    Program target [.small .boolean, .small .boolean] .sint :=
  ⟨dialect, .gnuModulo, Expr.usualAdd (.param .here) (.param (.there .here))⟩

/-- Overflow is ruled out from canonical boolean argument ranges and the
minimum admitted int width, rather than assumed as an input condition. -/
theorem booleanAdd_verified (target : Target) (dialect : Dialect) :
    Verifies (booleanAdd target dialect) (fun _ => True)
      (fun inputs result => result.val =
        (inputs.get .here).toInt + (inputs.get (.there .here)).toInt) := by
  intro inputs _
  let left := inputs.get .here
  let right := inputs.get (.there .here)
  let promotedLeft := IntegerPromotions.promoteValue left
  let promotedRight := IntegerPromotions.promoteValue right
  have leftValue : promotedLeft.val = left.toInt :=
    IntegerPromotions.promoteValue_toInt left
  have rightValue : promotedRight.val = right.toInt :=
    IntegerPromotions.promoteValue_toInt right
  have leftBounds := Value.boolean_values left
  have rightBounds := Value.boolean_values right
  have bound := two_lt_signedBound target
  have fits : -target.signedBound ≤ left.toInt + right.toInt ∧
      left.toInt + right.toInt < target.signedBound := by omega
  let result : Value target .sint := ⟨left.toInt + right.toInt, fits⟩
  refine ⟨result, ?_, rfl⟩
  change checkedSigned target .signedAdditionOverflow
    (promotedLeft.val + promotedRight.val) = .defined result
  rw [leftValue, rightValue]
  exact dite_eq_left fits

theorem booleanAdd_certificate (target : Target) (dialect : Dialect) :
    Certificate (booleanAdd target dialect) (fun _ => True)
      (fun inputs result => result.val =
        (inputs.get .here).toInt + (inputs.get (.there .here)).toInt) where
  useful := ⟨.cons (zeroValue target (.small .boolean))
    (.cons (zeroValue target (.small .boolean)) .nil), trivial⟩
  verified := booleanAdd_verified target dialect

theorem booleanAdd_noUB (target : Target) (dialect : Dialect) :
    NoUB (booleanAdd target dialect) (fun _ => True) :=
  (booleanAdd_certificate target dialect).noUB

def unsignedShortAdd (target : Target) (dialect : Dialect) :
    Program target [.small .ushort, .small .ushort]
      (commonType target (.small .ushort) (.small .ushort)) :=
  ⟨dialect, .gnuModulo, Expr.usualAdd (.param .here) (.param (.there .here))⟩

/-- On the selected wide-int profile every pair of unsigned-short values has
an exact signed-int sum. The source's unsigned operands do not force wrapping. -/
theorem unsignedShortAdd32_verified (dialect : Dialect) :
    Verifies (unsignedShortAdd Target.int32 dialect) (fun _ => True)
      (fun inputs result => result.toInt =
        (inputs.get .here).toInt + (inputs.get (.there .here)).toInt) := by
  intro inputs _
  let left := inputs.get .here
  let right := inputs.get (.there .here)
  let promotedLeft := IntegerPromotions.promoteValue left
  let promotedRight := IntegerPromotions.promoteValue right
  have leftValue : promotedLeft.val = left.toInt :=
    IntegerPromotions.promoteValue_toInt left
  have rightValue : promotedRight.val = right.toInt :=
    IntegerPromotions.promoteValue_toInt right
  have leftBounds := left.property
  have rightBounds := right.property
  change 0 ≤ left.toInt ∧ left.toInt < 65536 at leftBounds
  change 0 ≤ right.toInt ∧ right.toInt < 65536 at rightBounds
  have fits : -Target.int32.signedBound ≤ left.toInt + right.toInt ∧
      left.toInt + right.toInt < Target.int32.signedBound := by
    change -2147483648 ≤ left.toInt + right.toInt ∧
      left.toInt + right.toInt < 2147483648
    omega
  let result : Value Target.int32 .sint := ⟨left.toInt + right.toInt, fits⟩
  refine ⟨result, ?_, rfl⟩
  change checkedSigned Target.int32 .signedAdditionOverflow
    (promotedLeft.val + promotedRight.val) = .defined result
  rw [leftValue, rightValue]
  exact dite_eq_left fits

theorem unsignedShortAdd32_certificate (dialect : Dialect) :
    Certificate (unsignedShortAdd Target.int32 dialect) (fun _ => True)
      (fun inputs result => result.toInt =
        (inputs.get .here).toInt + (inputs.get (.there .here)).toInt) where
  useful := ⟨.cons (zeroValue Target.int32 (.small .ushort))
    (.cons (zeroValue Target.int32 (.small .ushort)) .nil), trivial⟩
  verified := unsignedShortAdd32_verified dialect

/-- On equal short/int widths the common type is unsigned int and the sum may
wrap. The independent carry equation still covers every pair of typed inputs. -/
theorem unsignedShortAdd16_verified (dialect : Dialect) :
    Verifies (unsignedShortAdd Target.int16 dialect) (fun _ => True)
      (fun inputs result => ∃ carry : Nat, carry ≤ 1 ∧
        result.toInt + (carry : Int) * (Target.int16.modulus : Int) =
          (inputs.get .here).toInt + (inputs.get (.there .here)).toInt) := by
  intro inputs _
  let left := inputs.get .here
  let right := inputs.get (.there .here)
  let promotedLeft := IntegerPromotions.promoteValue left
  let promotedRight := IntegerPromotions.promoteValue right
  let converted : Inputs Target.int16 [.uint, .uint] :=
    .cons promotedLeft (.cons promotedRight .nil)
  obtain ⟨result, execution, carry, carryBound, sumEquation⟩ :=
    Examples.add_verified Target.int16 dialect converted trivial
  have leftValue : (promotedLeft.val : Int) = left.toInt :=
    IntegerPromotions.promoteValue_toInt left
  have rightValue : (promotedRight.val : Int) = right.toInt :=
    IntegerPromotions.promoteValue_toInt right
  refine ⟨result, execution, carry, carryBound, ?_⟩
  have integerSum := congrArg (fun n : Nat => (n : Int)) sumEquation
  simp only [Int.natCast_add, Int.natCast_mul] at integerSum
  change (result.val : Int) + (carry : Int) * (Target.int16.modulus : Int) =
    (promotedLeft.val : Int) + (promotedRight.val : Int) at integerSum
  change (result.val : Int) + (carry : Int) * (Target.int16.modulus : Int) =
    left.toInt + right.toInt
  omega

theorem unsignedShortAdd16_certificate (dialect : Dialect) :
    Certificate (unsignedShortAdd Target.int16 dialect) (fun _ => True)
      (fun inputs result => ∃ carry : Nat, carry ≤ 1 ∧
        result.toInt + (carry : Int) * (Target.int16.modulus : Int) =
          (inputs.get .here).toInt + (inputs.get (.there .here)).toInt) where
  useful := ⟨.cons (zeroValue Target.int16 (.small .ushort))
    (.cons (zeroValue Target.int16 (.small .ushort)) .nil), trivial⟩
  verified := unsignedShortAdd16_verified dialect

theorem unsignedShortAdd32_noUB (dialect : Dialect) :
    NoUB (unsignedShortAdd Target.int32 dialect) (fun _ => True) :=
  (unsignedShortAdd32_certificate dialect).noUB

theorem unsignedShortAdd16_noUB (dialect : Dialect) :
    NoUB (unsignedShortAdd Target.int16 dialect) (fun _ => True) :=
  (unsignedShortAdd16_certificate dialect).noUB

end EDSL.Source.PromotionContracts
