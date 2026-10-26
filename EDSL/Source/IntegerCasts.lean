/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Source.IntegerConversions

set_option autoImplicit false

namespace EDSL.Source.IntType

/-- Size of the mathematical value interval, independent of object storage. -/
def span (target : Target) (ty : IntType) : Int :=
  ty.upperBound target - ty.lowerBound target

theorem lowerBound_lt_upperBound (target : Target) (ty : IntType) :
    ty.lowerBound target < ty.upperBound target := by
  cases ty with
  | uint => exact Int.natCast_pos.mpr target.modulus_pos
  | sint =>
      change -target.signedBound < target.signedBound
      have positive := target.signedBound_pos
      omega
  | small ty =>
      change ty.lowerBound target < ty.upperBound target
      have signedPositive : (0 : Int) < (2 ^ (ty.rangeBits target - 1) : Nat) :=
        Int.natCast_pos.mpr (Nat.two_pow_pos _)
      have unsignedPositive : (0 : Int) < (2 ^ ty.rangeBits target : Nat) :=
        Int.natCast_pos.mpr (Nat.two_pow_pos _)
      unfold SmallType.lowerBound SmallType.upperBound
      split <;> omega

theorem span_pos (target : Target) (ty : IntType) : 0 < ty.span target := by
  have bounds := lowerBound_lt_upperBound target ty
  unfold span
  omega

end EDSL.Source.IntType

namespace EDSL.Source.IntegerCasts

/-! Total mathematical casts for the current integer types and every admitted
value-range profile. Non-boolean destinations use the explicit GNU modulo
policy, including signed destinations; this is not a universal ISO C23 policy.
Boolean conversion tests zero and does not reduce modulo two. These functions
do not model storage, effects, expression evaluation, or source definedness.
-/

/-- The representative in the destination interval. This numeric helper alone
is not boolean conversion; `castValue` handles boolean destinations separately. -/
def canonicalInt (target : Target) (destination : IntType) (z : Int) : Int :=
  destination.lowerBound target +
    (z - destination.lowerBound target) % destination.span target

theorem canonicalInt_range (target : Target) (destination : IntType) (z : Int) :
    destination.lowerBound target ≤ canonicalInt target destination z ∧
      canonicalInt target destination z < destination.upperBound target := by
  have positive := destination.span_pos target
  have lower := Int.emod_nonneg (z - destination.lowerBound target) (Int.ne_of_gt positive)
  have upper := Int.emod_lt_of_pos (z - destination.lowerBound target) positive
  have size : destination.span target =
      destination.upperBound target - destination.lowerBound target := rfl
  unfold canonicalInt
  omega

theorem canonicalInt_congruent (target : Target) (destination : IntType) (z : Int) :
    canonicalInt target destination z % destination.span target =
      z % destination.span target := by
  unfold canonicalInt
  rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]
  congr 1
  omega

/-- Two representatives in one half-open interval with the same residue agree. -/
theorem representative_unique (target : Target) (destination : IntType) {left right : Int}
    (leftRange : destination.lowerBound target ≤ left ∧ left < destination.upperBound target)
    (rightRange : destination.lowerBound target ≤ right ∧ right < destination.upperBound target)
    (sameResidue : left % destination.span target = right % destination.span target) :
    left = right := by
  have shifted :=
    Int.add_emod_eq_add_emod_right (-destination.lowerBound target) sameResidue
  have span := destination.span_pos target
  unfold IntType.span at span shifted
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at shifted
  omega

private def ofInt {target : Target} (destination : IntType) (z : Int)
    (bounds : destination.lowerBound target ≤ z ∧ z < destination.upperBound target) :
    Value target destination :=
  match destination with
  | .uint => ⟨z.toNat, by
      have nonnegative : 0 ≤ z := bounds.1
      have upper : z < (target.modulus : Int) := bounds.2
      omega⟩
  | .sint => ⟨z, bounds⟩
  | .small _ => ⟨z, bounds⟩

private theorem ofInt_toInt {target : Target} (destination : IntType) (z : Int)
    (bounds : destination.lowerBound target ≤ z ∧ z < destination.upperBound target) :
    (ofInt destination z bounds).toInt = z := by
  cases destination with
  | uint => exact Int.toNat_of_nonneg bounds.1
  | sint => rfl
  | small _ => rfl

private def moduloValue {target : Target} (destination : IntType) (z : Int) :
    Value target destination :=
  ofInt destination (canonicalInt target destination z) (canonicalInt_range target destination z)

private theorem moduloValue_toInt {target : Target} (destination : IntType) (z : Int) :
    (moduloValue (target := target) destination z).toInt = canonicalInt target destination z :=
  ofInt_toInt destination _ _

private theorem moduloValue_congruent {target : Target} (destination : IntType) (z : Int) :
    (moduloValue (target := target) destination z).toInt % destination.span target =
      z % destination.span target := by
  rw [moduloValue_toInt]
  exact canonicalInt_congruent target destination z

private def booleanValue {target : Target} (z : Int) : Value target (.small .boolean) :=
  ⟨if z = 0 then 0 else 1, by
    change 0 ≤ (if z = 0 then (0 : Int) else 1) ∧ (if z = 0 then (0 : Int) else 1) < 2
    split <;> omega⟩

/-- Total GNU numeric conversion. The four full-rank branches deliberately
reduce to the existing identities and same-width conversion functions. -/
def castValue {target : Target} {source : IntType} (destination : IntType)
    (value : Value target source) : Value target destination :=
  match source, destination with
  | .uint, .uint => value
  | .sint, .sint => value
  | .uint, .sint => IntegerConversions.unsignedToSigned value
  | .sint, .uint => IntegerConversions.signedToUnsigned value
  | _, .small .boolean => booleanValue value.toInt
  | _, destination => moduloValue destination value.toInt

/-- An implementation-independent numeric contract, stated only in terms of
input/output integers and the destination interval. -/
def CastSpec (target : Target) (destination : IntType) (input output : Int) : Prop :=
  if destination = .small .boolean then output = (if input = 0 then 0 else 1)
  else destination.lowerBound target ≤ output ∧ output < destination.upperBound target ∧
    output % destination.span target = input % destination.span target

theorem castValue_range {target : Target} {source : IntType} (destination : IntType)
    (value : Value target source) :
    destination.lowerBound target ≤ (castValue destination value).toInt ∧
      (castValue destination value).toInt < destination.upperBound target :=
  (castValue destination value).range

theorem castValue_boolean {target : Target} {source : IntType} (value : Value target source) :
    (castValue (.small .boolean) value).toInt = (if value.toInt = 0 then 0 else 1) := by
  cases source <;> rfl

theorem castValue_boolean_eq_zero_iff {target : Target} {source : IntType}
    (value : Value target source) :
    (castValue (.small .boolean) value).toInt = 0 ↔ value.toInt = 0 := by
  rw [castValue_boolean]
  split <;> omega

theorem castValue_boolean_eq_one_iff {target : Target} {source : IntType}
    (value : Value target source) :
    (castValue (.small .boolean) value).toInt = 1 ↔ value.toInt ≠ 0 := by
  rw [castValue_boolean]
  split <;> omega

theorem castValue_boolean_values {target : Target} {source : IntType}
    (value : Value target source) :
    (castValue (.small .boolean) value).toInt = 0 ∨
      (castValue (.small .boolean) value).toInt = 1 :=
  (castValue (.small .boolean) value).boolean_values

theorem castValue_congruent {target : Target} {source : IntType} (destination : IntType)
    (value : Value target source) (nonboolean : destination ≠ .small .boolean) :
    (castValue destination value).toInt % destination.span target =
      value.toInt % destination.span target := by
  cases source with
  | uint =>
      cases destination with
      | uint => rfl
      | sint =>
          have half := target.modulus_eq_twice_signedBound
          have span : IntType.sint.span target = (target.modulus : Int) := by
            change target.signedBound - -target.signedBound = (target.modulus : Int)
            omega
          rw [span]
          exact (IntegerConversions.unsignedToSigned_corresponds value).trans
            (Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr value.isLt)).symm
      | small ty =>
          cases ty <;> first
            | exact False.elim (nonboolean rfl)
            | exact moduloValue_congruent _ _
  | sint =>
      cases destination with
      | uint =>
          change ((IntegerConversions.signedToUnsigned value).val : Int) %
            (target.modulus : Int) = value.val % (target.modulus : Int)
          have bounds := IntegerConversions.signedToUnsigned_range value
          rw [Int.emod_eq_of_lt bounds.1 bounds.2]
          exact (IntegerConversions.signedToUnsigned_corresponds value).symm
      | sint => rfl
      | small ty =>
          cases ty <;> first
            | exact False.elim (nonboolean rfl)
            | exact moduloValue_congruent _ _
  | small ty =>
      cases destination with
      | uint => exact moduloValue_congruent _ _
      | sint => exact moduloValue_congruent _ _
      | small destination =>
          cases destination <;> first
            | exact False.elim (nonboolean rfl)
            | exact moduloValue_congruent _ _

theorem castValue_spec {target : Target} {source : IntType} (destination : IntType)
    (value : Value target source) :
    CastSpec target destination value.toInt (castValue destination value).toInt := by
  unfold CastSpec
  split
  · next boolean => subst destination; exact castValue_boolean value
  · exact ⟨(castValue_range destination value).1, (castValue_range destination value).2,
      castValue_congruent destination value ‹_›⟩

theorem castValue_unique {target : Target} {source : IntType} (destination : IntType)
    (value : Value target source) (candidate : Value target destination)
    (spec : CastSpec target destination value.toInt candidate.toInt) :
    castValue destination value = candidate := by
  apply Value.toInt_injective
  have actual := castValue_spec destination value
  unfold CastSpec at spec actual
  split at spec
  · next boolean => rw [ite_eq_left boolean] at actual; exact actual.trans spec.symm
  · next nonboolean =>
      rw [ite_eq_right nonboolean] at actual
      exact representative_unique target destination ⟨actual.1, actual.2.1⟩
        ⟨spec.1, spec.2.1⟩ (actual.2.2.trans spec.2.2.symm)

theorem castValue_eq_iff {target : Target} {source : IntType} (destination : IntType)
    (value : Value target source) (candidate : Value target destination) :
    castValue destination value = candidate ↔
      CastSpec target destination value.toInt candidate.toInt := by
  constructor
  · intro same
    exact same ▸ castValue_spec destination value
  · exact castValue_unique destination value candidate

theorem castValue_toInt {target : Target} {source : IntType} (destination : IntType)
    (value : Value target source) (nonboolean : destination ≠ .small .boolean) :
    (castValue destination value).toInt = canonicalInt target destination value.toInt :=
  representative_unique target destination (castValue_range destination value)
    (canonicalInt_range target destination value.toInt)
    ((castValue_congruent destination value nonboolean).trans
      (canonicalInt_congruent target destination value.toInt).symm)

/-- Representable inputs keep their mathematical value, also for bool. -/
theorem castValue_preserves {target : Target} {source : IntType} (destination : IntType)
    (value : Value target source)
    (fits : destination.lowerBound target ≤ value.toInt ∧
      value.toInt < destination.upperBound target) :
    (castValue destination value).toInt = value.toInt := by
  by_cases boolean : destination = .small .boolean
  · subst destination
    rw [castValue_boolean]
    change 0 ≤ value.toInt ∧ value.toInt < 2 at fits
    split <;> omega
  · exact representative_unique target destination (castValue_range destination value)
      fits (castValue_congruent destination value boolean)

theorem castValue_self {target : Target} {source : IntType} (value : Value target source) :
    castValue source value = value :=
  Value.toInt_injective (castValue_preserves source value value.range)

/-- Same-width unsigned/signed round trips reuse the existing shared laws.
This does not assert any arbitrary narrowing round trip. -/
theorem castValue_uint_sint_uint {target : Target} (value : Value target .uint) :
    castValue .uint (castValue .sint value) = value :=
  IntegerConversions.signedToUnsigned_unsignedToSigned value

theorem castValue_sint_uint_sint {target : Target} (value : Value target .sint) :
    castValue .sint (castValue .uint value) = value :=
  IntegerConversions.unsignedToSigned_signedToUnsigned value

end EDSL.Source.IntegerCasts
