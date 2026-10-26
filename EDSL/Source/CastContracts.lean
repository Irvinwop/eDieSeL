/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.PromotionContracts

set_option autoImplicit false

namespace EDSL.Source.CastContracts

private theorem zeroValue_toInt (target : Target) (ty : IntType) :
    (PromotionContracts.zeroValue target ty).toInt = 0 := by
  cases ty <;> rfl

def castReturn (target : Target) (dialect : Dialect) (source destination : IntType) :
    Program target [source] destination :=
  ⟨dialect, .gnuModulo, .convert destination (.param .here)⟩

/-- Independent source-cast relation. Non-boolean results satisfy an integer
carry equation; the postcondition contains no cast, evaluator or remainder. -/
def CastResult (target : Target) (destination : IntType) (input output : Int) : Prop :=
  if destination = .small .boolean then
    (input = 0 ∧ output = 0) ∨ (input ≠ 0 ∧ output = 1)
  else destination.lowerBound target ≤ output ∧ output < destination.upperBound target ∧
    ∃ carry : Int, input = output + carry * destination.span target

theorem castValue_result {target : Target} {source : IntType} (destination : IntType)
    (value : Value target source) :
    CastResult target destination value.toInt (IntegerCasts.castValue destination value).toInt := by
  by_cases boolean : destination = .small .boolean
  · subst destination
    have actual := IntegerCasts.castValue_boolean value
    by_cases zero : value.toInt = 0
    · exact Or.inl ⟨zero, by simpa only [ite_eq_left zero] using actual⟩
    · exact Or.inr ⟨zero, by simpa only [ite_eq_right zero] using actual⟩
  · rw [CastResult, ite_eq_right boolean]
    have bounds := (IntegerCasts.castValue destination value).range
    refine ⟨bounds.1, bounds.2, value.toInt / destination.span target -
      (IntegerCasts.castValue destination value).toInt / destination.span target, ?_⟩
    have same := IntegerCasts.castValue_congruent destination value boolean
    have inputSplit := Int.emod_add_ediv_mul value.toInt (destination.span target)
    have outputSplit := Int.emod_add_ediv_mul
      (IntegerCasts.castValue destination value).toInt (destination.span target)
    rw [Int.sub_mul]
    omega

/-- The postcondition refers to mathematical integers, bounds and carries,
not to the evaluator or cast implementation. All typed inputs are admitted. -/
theorem castReturn_certificate (target : Target) (dialect : Dialect)
    (source destination : IntType) :
    Certificate (castReturn target dialect source destination) (fun _ => True)
      (fun inputs result => CastResult target destination
        (inputs.get .here).toInt result.toInt) := by
  refine certificate_of_vc ⟨.cons (PromotionContracts.zeroValue target source) .nil, trivial⟩ ?_
  intro inputs _
  change CastResult target destination (inputs.get .here).toInt
    (IntegerCasts.castValue destination (inputs.get .here)).toInt
  exact castValue_result _ _

theorem castReturn_noUB (target : Target) (dialect : Dialect)
    (source destination : IntType) :
    NoUB (castReturn target dialect source destination) (fun _ => True) :=
  (castReturn_certificate target dialect source destination).noUB

/-- A numeric input condition, not an assumed source-safety property. -/
def FitsIntermediate {target : Target} {source : IntType} (intermediate : IntType)
    (inputs : Inputs target [source]) : Prop :=
  intermediate.lowerBound target ≤ (inputs.get .here).toInt ∧
    (inputs.get .here).toInt < intermediate.upperBound target

def representableRoundTrip (target : Target) (dialect : Dialect)
    (source intermediate : IntType) : Program target [source] source :=
  ⟨dialect, .gnuModulo, .convert source (.convert intermediate (.param .here))⟩

/-- A round trip is lossless on the explicitly representable domain. This does
not assert that arbitrary narrowing can be undone. The domain contains zero. -/
theorem representableRoundTrip_certificate (target : Target) (dialect : Dialect)
    (source intermediate : IntType) :
    Certificate (representableRoundTrip target dialect source intermediate)
      (FitsIntermediate intermediate) (fun inputs result => result = inputs.get .here) := by
  refine certificate_of_vc ⟨.cons (PromotionContracts.zeroValue target source) .nil, ?_⟩ ?_
  · change intermediate.lowerBound target ≤
      (PromotionContracts.zeroValue target source).toInt ∧
        (PromotionContracts.zeroValue target source).toInt < intermediate.upperBound target
    rw [zeroValue_toInt]
    have bounds := (PromotionContracts.zeroValue target intermediate).range
    rwa [zeroValue_toInt] at bounds
  · intro inputs fits
    change IntegerCasts.castValue source
      (IntegerCasts.castValue intermediate (inputs.get .here)) = inputs.get .here
    apply Value.toInt_injective
    have preserved := IntegerCasts.castValue_preserves intermediate (inputs.get .here) fits
    have originalRange := (inputs.get .here).range
    have outer := IntegerCasts.castValue_preserves source
      (IntegerCasts.castValue intermediate (inputs.get .here)) (by
        rw [preserved]
        exact originalRange)
    exact outer.trans preserved

theorem representableRoundTrip_noUB (target : Target) (dialect : Dialect)
    (source intermediate : IntType) :
    NoUB (representableRoundTrip target dialect source intermediate)
      (FitsIntermediate intermediate) :=
  (representableRoundTrip_certificate target dialect source intermediate).noUB

/-- Two explicit unsigned-char casts, followed by the usual promoted addition.
The profile supplies char8/int32 numeric ranges, without claiming a native ABI. -/
def lowByteAdd (dialect : Dialect) : Program Target.int32 [.uint, .uint] .sint :=
  ⟨dialect, .gnuModulo, Expr.usualAdd
    (.convert (.small .uchar) (.param .here))
    (.convert (.small .uchar) (.param (.there .here)))⟩

/-- Independently specified low-byte sum, with an exact bounded int result. -/
def LowByteSum (left right : Value Target.int32 .uint)
    (result : Value Target.int32 .sint) : Prop :=
  result.toInt = left.toInt % 256 + right.toInt % 256 ∧
    0 ≤ result.toInt ∧ result.toInt ≤ 510

private theorem uchar_residue (value : Value Target.int32 .uint) :
    (IntegerCasts.castValue (.small .uchar) value).toInt = value.toInt % 256 := by
  have bounds := (IntegerCasts.castValue (.small .uchar) value).range
  change 0 ≤ (IntegerCasts.castValue (.small .uchar) value).toInt ∧
    (IntegerCasts.castValue (.small .uchar) value).toInt < 256 at bounds
  have congruence := IntegerCasts.castValue_congruent (.small .uchar) value (by decide +kernel)
  change (IntegerCasts.castValue (.small .uchar) value).toInt % 256 =
    value.toInt % 256 at congruence
  rwa [Int.emod_eq_of_lt bounds.1 bounds.2] at congruence

/-- Overflow is discharged from the destination ranges before execution. NoUB
is not an input premise, and the program reuses the shared evaluator and VC. -/
theorem lowByteAdd_verified (dialect : Dialect) :
    Verifies (lowByteAdd dialect) (fun _ => True)
      (fun inputs result => LowByteSum (inputs.get .here) (inputs.get (.there .here)) result) := by
  intro inputs _
  let left := IntegerCasts.castValue (.small .uchar) (inputs.get .here)
  let right := IntegerCasts.castValue (.small .uchar) (inputs.get (.there .here))
  let promotedLeft := IntegerPromotions.promoteValue left
  let promotedRight := IntegerPromotions.promoteValue right
  have leftValue : promotedLeft.val = left.toInt :=
    IntegerPromotions.promoteValue_toInt left
  have rightValue : promotedRight.val = right.toInt :=
    IntegerPromotions.promoteValue_toInt right
  have leftBounds := left.range
  have rightBounds := right.range
  change 0 ≤ left.toInt ∧ left.toInt < 256 at leftBounds
  change 0 ≤ right.toInt ∧ right.toInt < 256 at rightBounds
  have fits : -Target.int32.signedBound ≤ left.toInt + right.toInt ∧
      left.toInt + right.toInt < Target.int32.signedBound := by
    change -2147483648 ≤ left.toInt + right.toInt ∧
      left.toInt + right.toInt < 2147483648
    omega
  let result : Value Target.int32 .sint := ⟨left.toInt + right.toInt, fits⟩
  refine ⟨result, ?_, ?_⟩
  · have promotedFits : -Target.int32.signedBound ≤ promotedLeft.val + promotedRight.val ∧
        promotedLeft.val + promotedRight.val < Target.int32.signedBound := by
      rw [leftValue, rightValue]
      exact fits
    have execution := eval_sadd_defined .gnuModulo inputs
      (.convert .sint (.promote (.convert (.small .uchar) (.param .here))))
      (.convert .sint (.promote (.convert (.small .uchar) (.param (.there .here)))))
      promotedLeft promotedRight rfl rfl promotedFits
    have sameResult : (⟨promotedLeft.val + promotedRight.val, promotedFits⟩ :
        Value Target.int32 .sint) = result := by
      apply Subtype.ext
      change promotedLeft.val + promotedRight.val = left.toInt + right.toInt
      rw [leftValue, rightValue]
    exact execution.trans (congrArg Outcome.defined sameResult)
  · refine ⟨?_, ?_, ?_⟩
    · change left.toInt + right.toInt = _
      change (IntegerCasts.castValue (.small .uchar) (inputs.get .here)).toInt +
        (IntegerCasts.castValue (.small .uchar) (inputs.get (.there .here))).toInt = _
      rw [uchar_residue, uchar_residue]
    · change 0 ≤ left.toInt + right.toInt
      omega
    · change left.toInt + right.toInt ≤ 510
      omega

theorem lowByteAdd_certificate (dialect : Dialect) :
    Certificate (lowByteAdd dialect) (fun _ => True)
      (fun inputs result => LowByteSum (inputs.get .here) (inputs.get (.there .here)) result) where
  useful := ⟨.cons (PromotionContracts.zeroValue Target.int32 .uint)
    (.cons (PromotionContracts.zeroValue Target.int32 .uint) .nil), trivial⟩
  verified := lowByteAdd_verified dialect

theorem lowByteAdd_noUB (dialect : Dialect) :
    NoUB (lowByteAdd dialect) (fun _ => True) :=
  (lowByteAdd_certificate dialect).noUB

end EDSL.Source.CastContracts
