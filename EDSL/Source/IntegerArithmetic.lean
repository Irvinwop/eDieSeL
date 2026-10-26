/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Source.Eval

set_option autoImplicit false

namespace EDSL.Source.IntegerArithmetic

/-! Arithmetic contracts use mathematical equations and representable operand
ranges. Definedness is proved for the shared primitives; it is never an input
assumption. These laws concern the admitted full int types after promotion,
without extending the source evaluator or asserting a compiler/ABI contract.
-/

/-- Subtraction conserves the operands with at most one borrowed modulus.
In particular, a negative mathematical difference cannot saturate at zero. -/
def UnsignedSubtraction (target : Target) (x y r : Value target .uint) : Prop :=
  ∃ borrow : Nat, borrow ≤ 1 ∧ r.val + y.val = x.val + borrow * target.modulus

/-- Multiplication conserves the entire mathematical product. The carry may
exceed one, unlike the carry of addition or the borrow of subtraction. -/
def UnsignedMultiplication (target : Target) (x y r : Value target .uint) : Prop :=
  ∃ carry : Nat, x.val * y.val = r.val + carry * target.modulus

/-- An independent remainder specification, without division or modulo. -/
def UnsignedRemainder (target : Target) (x y r : Value target .uint) : Prop :=
  0 ≤ r.val ∧ r.val < y.val ∧ ∃ q : Nat, x.val = q * y.val + r.val

/-- The exclusive upper bound is part of the signed overflow boundary. -/
def SignedRange (target : Target) (z : Int) : Prop :=
  -target.signedBound ≤ z ∧ z < target.signedBound

def SignedSubtraction {target : Target} (x y r : Value target .sint) : Prop :=
  r.val = x.val - y.val

def SignedMultiplication {target : Target} (x y r : Value target .sint) : Prop :=
  r.val = x.val * y.val

/-- Truncating quotient/remainder, independently specified by reconstruction,
magnitude, and the dividend's sign. `natAbs` expresses absolute magnitude. -/
def TruncatingDivision (x y q r : Int) : Prop :=
  x = q * y + r ∧ r.natAbs < y.natAbs ∧ (r = 0 ∨ r.sign = x.sign)

def SignedRemainder {target : Target} (x y r : Value target .sint) : Prop :=
  ∃ q : Int, TruncatingDivision x.val y.val q r.val

/-- The one nonzero-divisor exception for representable signed operands. -/
def DivisionOverflowPair {target : Target} (x y : Value target .sint) : Prop :=
  x.val = -target.signedBound ∧ y.val = -1

theorem signedBound_atLeast32768 (target : Target) :
    (32768 : Int) ≤ target.signedBound := by
  have exponent : 15 ≤ target.intBits - 1 := by
    have minimum := target.atLeast16
    omega
  have power := Nat.pow_le_pow_right (n := 2) (by decide +kernel) exponent
  exact Int.ofNat_le.mpr power

theorem unsignedSub_spec (target : Target) (x y : Value target .uint) :
    ∃ r, unsignedSub target x y = .defined r ∧ UnsignedSubtraction target x y r := by
  refine ⟨⟨(x.val + target.modulus - y.val) % target.modulus,
    Nat.mod_lt _ target.modulus_pos⟩, rfl, ?_⟩
  have x_range := x.isLt
  have y_range := y.isLt
  by_cases no_borrow : y.val ≤ x.val
  · refine ⟨0, by omega, ?_⟩
    change (x.val + target.modulus - y.val) % target.modulus + y.val =
      x.val + 0 * target.modulus
    have shifted : x.val + target.modulus - y.val =
        (x.val - y.val) + target.modulus := by omega
    rw [shifted, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · refine ⟨1, by omega, ?_⟩
    change (x.val + target.modulus - y.val) % target.modulus + y.val =
      x.val + 1 * target.modulus
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- The independently specified subtraction result is unique. -/
theorem unsignedSubtraction_unique {target : Target} {x y r s : Value target .uint}
    (r_spec : UnsignedSubtraction target x y r)
    (s_spec : UnsignedSubtraction target x y s) : r = s := by
  obtain ⟨a, a_le, a_eq⟩ := r_spec
  obtain ⟨b, b_le, b_eq⟩ := s_spec
  have r_range := r.isLt
  have s_range := s.isLt
  apply Fin.ext
  have a_cases : a = 0 ∨ a = 1 := by omega
  have b_cases : b = 0 ∨ b = 1 := by omega
  rcases a_cases with rfl | rfl <;> rcases b_cases with rfl | rfl <;>
    simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero] at a_eq b_eq <;> omega

theorem unsignedSub_eq_defined_iff (target : Target) (x y r : Value target .uint) :
    unsignedSub target x y = .defined r ↔ UnsignedSubtraction target x y r := by
  obtain ⟨s, execution, specification⟩ := unsignedSub_spec target x y
  constructor
  · intro result
    have same := Outcome.defined.inj (execution.symm.trans result)
    exact same ▸ specification
  · intro result
    exact unsignedSubtraction_unique specification result ▸ execution

theorem unsignedMul_spec (target : Target) (x y : Value target .uint) :
    ∃ r, unsignedMul target x y = .defined r ∧ UnsignedMultiplication target x y r := by
  refine ⟨⟨(x.val * y.val) % target.modulus, Nat.mod_lt _ target.modulus_pos⟩,
    rfl, (x.val * y.val) / target.modulus, ?_⟩
  simpa only [Nat.mul_comm] using (Nat.mod_add_div (x.val * y.val) target.modulus).symm

theorem unsignedRem_zero (target : Target) (x y : Value target .uint)
    (zero : y.val = 0) : unsignedRem target x y = .undefined .divisionByZero := by
  simp [unsignedRem, zero]

theorem unsignedRem_spec (target : Target) (x y : Value target .uint)
    (nonzero : y.val ≠ 0) :
    ∃ r, unsignedRem target x y = .defined r ∧ UnsignedRemainder target x y r := by
  have bound := Nat.mod_lt x.val (Nat.pos_of_ne_zero nonzero)
  refine ⟨⟨x.val % y.val, Nat.lt_trans bound y.isLt⟩, ?_, Nat.zero_le _, bound,
    x.val / y.val, ?_⟩
  · simp [unsignedRem, nonzero]
  · simpa only [Nat.mul_comm] using (Nat.div_add_mod x.val y.val).symm

private theorem checkedSigned_eq_defined_iff (target : Target) (reason : UBReason)
    (z : Int) (r : Value target .sint) :
    checkedSigned target reason z = .defined r ↔ r.val = z := by
  unfold checkedSigned
  split
  · rename_i fits
    constructor
    · intro same
      exact (congrArg Subtype.val (Outcome.defined.inj same)).symm
    · intro same
      exact congrArg Outcome.defined (Subtype.ext same.symm)
  · rename_i outside
    constructor
    · intro impossible
      cases impossible
    · intro same
      exact False.elim (outside (same ▸ r.property))

theorem signedSub_defined (target : Target) (x y : Value target .sint)
    (fits : SignedRange target (x.val - y.val)) :
    signedSub target x y = .defined ⟨x.val - y.val, fits⟩ :=
  dite_eq_left fits

theorem signedSub_spec (target : Target) (x y : Value target .sint)
    (fits : SignedRange target (x.val - y.val)) :
    ∃ r, signedSub target x y = .defined r ∧ SignedSubtraction x y r :=
  ⟨⟨x.val - y.val, fits⟩, signedSub_defined target x y fits, rfl⟩

theorem signedSub_eq_defined_iff (target : Target) (x y r : Value target .sint) :
    signedSub target x y = .defined r ↔ SignedSubtraction x y r :=
  checkedSigned_eq_defined_iff target .signedSubtractionOverflow _ r

theorem signedSub_overflow (target : Target) (x y : Value target .sint)
    (outside : ¬ SignedRange target (x.val - y.val)) :
    signedSub target x y = .undefined .signedSubtractionOverflow :=
  dite_eq_right outside

theorem signedSub_overflow_iff (target : Target) (x y : Value target .sint) :
    signedSub target x y = .undefined .signedSubtractionOverflow ↔
      ¬ SignedRange target (x.val - y.val) := by
  by_cases fits : SignedRange target (x.val - y.val)
  · rw [signedSub_defined target x y fits]
    simp [fits]
  · simp [signedSub_overflow target x y fits, fits]

theorem signedMul_defined (target : Target) (x y : Value target .sint)
    (fits : SignedRange target (x.val * y.val)) :
    signedMul target x y = .defined ⟨x.val * y.val, fits⟩ :=
  dite_eq_left fits

theorem signedMul_spec (target : Target) (x y : Value target .sint)
    (fits : SignedRange target (x.val * y.val)) :
    ∃ r, signedMul target x y = .defined r ∧ SignedMultiplication x y r :=
  ⟨⟨x.val * y.val, fits⟩, signedMul_defined target x y fits, rfl⟩

theorem signedMul_eq_defined_iff (target : Target) (x y r : Value target .sint) :
    signedMul target x y = .defined r ↔ SignedMultiplication x y r :=
  checkedSigned_eq_defined_iff target .signedMultiplicationOverflow _ r

theorem signedMul_overflow (target : Target) (x y : Value target .sint)
    (outside : ¬ SignedRange target (x.val * y.val)) :
    signedMul target x y = .undefined .signedMultiplicationOverflow :=
  dite_eq_right outside

theorem signedMul_overflow_iff (target : Target) (x y : Value target .sint) :
    signedMul target x y = .undefined .signedMultiplicationOverflow ↔
      ¬ SignedRange target (x.val * y.val) := by
  by_cases fits : SignedRange target (x.val * y.val)
  · rw [signedMul_defined target x y fits]
    simp [fits]
  · simp [signedMul_overflow target x y fits, fits]

/-- A bounded numerator's truncating quotient fits except for minimum / -1.
No upper/lower bound on the nonzero divisor is needed for this number theorem. -/
theorem truncatingQuotient_range (bound : Nat) (x y : Int)
    (x_range : -(bound : Int) ≤ x ∧ x < (bound : Int))
    (nonzero : y ≠ 0)
    (ordinary : ¬ (x = -(bound : Int) ∧ y = -1)) :
    -(bound : Int) ≤ x.tdiv y ∧ x.tdiv y < (bound : Int) := by
  have numerator_abs := Int.natAbs_eq x
  have quotient_abs := Int.natAbs_eq (x.tdiv y)
  have numerator_le : x.natAbs ≤ bound := by omega
  have quotient_le : (x.tdiv y).natAbs ≤ x.natAbs := by
    rw [Int.natAbs_tdiv]
    exact Nat.div_le_self _ _
  by_cases low : x.natAbs < bound
  · omega
  · have minimum : x = -(bound : Int) := by omega
    have not_neg_one : y ≠ -1 := by
      intro same
      exact ordinary ⟨minimum, same⟩
    by_cases one : y = 1
    · subst y
      simpa using x_range
    · have denominator_abs := Int.natAbs_eq y
      have denominator_large : 1 < y.natAbs := by omega
      have numerator_positive : 0 < x.natAbs := by omega
      have quotient_lt : (x.tdiv y).natAbs < x.natAbs := by
        rw [Int.natAbs_tdiv]
        exact Nat.div_lt_self numerator_positive denominator_large
      omega

/-- Any truncating remainder fits the divisor's symmetric range, including
when the numerator's quotient would overflow that range. -/
theorem truncatingRemainder_range (bound : Nat) (x y : Int)
    (y_range : -(bound : Int) ≤ y ∧ y < (bound : Int))
    (nonzero : y ≠ 0) :
    -(bound : Int) ≤ x.tmod y ∧ x.tmod y < (bound : Int) := by
  have denominator_abs := Int.natAbs_eq y
  have denominator_le : y.natAbs ≤ bound := by omega
  have remainder_abs := Int.natAbs_eq (x.tmod y)
  have remainder_lt : (x.tmod y).natAbs < y.natAbs := by
    rw [Int.natAbs_tmod]
    exact Nat.mod_lt _ (Int.natAbs_pos.mpr nonzero)
  omega

theorem truncatingDivision_spec (x y : Int) (nonzero : y ≠ 0) :
    TruncatingDivision x y (x.tdiv y) (x.tmod y) := by
  refine ⟨(Int.tdiv_mul_add_tmod x y).symm, ?_, ?_⟩
  · rw [Int.natAbs_tmod]
    exact Nat.mod_lt _ (Int.natAbs_pos.mpr nonzero)
  · by_cases divides : y ∣ x
    · exact Or.inl (Int.tmod_eq_zero_of_dvd divides)
    · exact Or.inr (by simpa [divides] using Int.sign_tmod x y)

theorem signedDiv_quotient_fits (target : Target) (x y : Value target .sint)
    (nonzero : y.val ≠ 0) (ordinary : ¬ DivisionOverflowPair x y) :
    SignedRange target (x.val.tdiv y.val) :=
  truncatingQuotient_range (2 ^ (target.intBits - 1)) x.val y.val
    x.property nonzero ordinary

/-- The signed minimum divided by negative one is the entire nonzero-divisor
overflow boundary, for every target admitted by `Value`. -/
theorem signedDiv_quotient_fits_iff (target : Target) (x y : Value target .sint)
    (nonzero : y.val ≠ 0) :
    SignedRange target (x.val.tdiv y.val) ↔ ¬ DivisionOverflowPair x y := by
  constructor
  · intro fits overflow
    obtain ⟨minimum, negative_one⟩ := overflow
    have quotient : x.val.tdiv y.val = target.signedBound := by
      simp [minimum, negative_one]
    have upper := fits.2
    rw [quotient] at upper
    omega
  · exact signedDiv_quotient_fits target x y nonzero

theorem signedRem_remainder_fits (target : Target) (x y : Value target .sint)
    (nonzero : y.val ≠ 0) : SignedRange target (x.val.tmod y.val) :=
  truncatingRemainder_range (2 ^ (target.intBits - 1)) x.val y.val y.property nonzero

/-- Defined division and remainder share the same independent mathematical
reconstruction law, and neither execution is assumed. -/
theorem signedDiv_spec (target : Target) (x y : Value target .sint)
    (nonzero : y.val ≠ 0) (ordinary : ¬ DivisionOverflowPair x y) :
    ∃ q, signedDiv target x y = .defined q ∧
      ∃ r : Int, TruncatingDivision x.val y.val q.val r := by
  have fits := signedDiv_quotient_fits target x y nonzero ordinary
  refine ⟨⟨x.val.tdiv y.val, fits⟩, ?_, x.val.tmod y.val,
    truncatingDivision_spec x.val y.val nonzero⟩
  simp [signedDiv, nonzero, checkedSigned, show
    -target.signedBound ≤ x.val.tdiv y.val ∧
      x.val.tdiv y.val < target.signedBound from fits]

theorem signedRem_zero (target : Target) (x y : Value target .sint)
    (zero : y.val = 0) : signedRem target x y = .undefined .divisionByZero := by
  simp [signedRem, zero]

theorem signedRem_quotient_overflow (target : Target) (x y : Value target .sint)
    (nonzero : y.val ≠ 0) (outside : ¬ SignedRange target (x.val.tdiv y.val)) :
    signedRem target x y = .undefined .signedRemainderOverflow := by
  unfold SignedRange at outside
  rw [signedRem, ite_eq_right nonzero, ite_eq_right outside]

theorem signedRem_spec (target : Target) (x y : Value target .sint)
    (nonzero : y.val ≠ 0) (ordinary : ¬ DivisionOverflowPair x y) :
    ∃ r, signedRem target x y = .defined r ∧ SignedRemainder x y r := by
  have quotient_fits := signedDiv_quotient_fits target x y nonzero ordinary
  have remainder_fits := signedRem_remainder_fits target x y nonzero
  refine ⟨⟨x.val.tmod y.val, remainder_fits⟩, ?_, x.val.tdiv y.val,
    truncatingDivision_spec x.val y.val nonzero⟩
  simp [signedRem, nonzero, checkedSigned, show
    -target.signedBound ≤ x.val.tdiv y.val ∧
      x.val.tdiv y.val < target.signedBound from quotient_fits, show
    -target.signedBound ≤ x.val.tmod y.val ∧
      x.val.tmod y.val < target.signedBound from remainder_fits]

theorem signedRem_min_neg_one (target : Target) (x y : Value target .sint)
    (minimum : x.val = -target.signedBound) (negative_one : y.val = -1) :
    signedRem target x y = .undefined .signedRemainderOverflow := by
  have quotient : x.val.tdiv y.val = target.signedBound := by
    simp [minimum, negative_one]
  have outside : ¬ (-target.signedBound ≤ x.val.tdiv y.val ∧
      x.val.tdiv y.val < target.signedBound) := by
    rw [quotient]
    omega
  rw [signedRem, ite_eq_right (by omega : y.val ≠ 0), ite_eq_right outside]

/-- Remainder overflow is exactly the minimum / -1 pair. A zero divisor uses
its own earlier diagnostic, and a representable remainder never hides overflow
of the truncating quotient. -/
theorem signedRem_overflow_iff (target : Target) (x y : Value target .sint) :
    signedRem target x y = .undefined .signedRemainderOverflow ↔
      DivisionOverflowPair x y := by
  by_cases zero : y.val = 0
  · rw [signedRem_zero target x y zero]
    have ordinary : ¬ DivisionOverflowPair x y := by
      intro pair
      have negative_one := pair.2
      omega
    simp [ordinary]
  · by_cases pair : DivisionOverflowPair x y
    · rw [signedRem_min_neg_one target x y pair.1 pair.2]
      simp [pair]
    · obtain ⟨r, execution, _⟩ := signedRem_spec target x y zero pair
      rw [execution]
      simp [pair]

theorem signedRem_defined_iff (target : Target) (x y : Value target .sint) :
    (∃ r, signedRem target x y = .defined r) ↔
      y.val ≠ 0 ∧ ¬ DivisionOverflowPair x y := by
  constructor
  · rintro ⟨r, execution⟩
    constructor
    · intro zero
      rw [signedRem_zero target x y zero] at execution
      cases execution
    · intro pair
      rw [signedRem_min_neg_one target x y pair.1 pair.2] at execution
      cases execution
  · rintro ⟨nonzero, ordinary⟩
    obtain ⟨r, execution, _⟩ := signedRem_spec target x y nonzero ordinary
    exact ⟨r, execution⟩

theorem signedRem_divisionByZero_iff (target : Target) (x y : Value target .sint) :
    signedRem target x y = .undefined .divisionByZero ↔ y.val = 0 := by
  constructor
  · intro zero
    by_cases nonzero : y.val = 0
    · exact nonzero
    · by_cases pair : DivisionOverflowPair x y
      · rw [signedRem_min_neg_one target x y pair.1 pair.2] at zero
        cases zero
      · obtain ⟨r, execution, _⟩ := signedRem_spec target x y nonzero pair
        rw [execution] at zero
        cases zero
  · exact signedRem_zero target x y

theorem signedDiv_min_neg_one (target : Target) (x y : Value target .sint)
    (minimum : x.val = -target.signedBound) (negative_one : y.val = -1) :
    signedDiv target x y = .undefined .signedDivisionOverflow := by
  have quotient : x.val.tdiv y.val = target.signedBound := by
    simp [minimum, negative_one]
  have outside : ¬ (-target.signedBound ≤ x.val.tdiv y.val ∧
      x.val.tdiv y.val < target.signedBound) := by
    rw [quotient]
    omega
  rw [signedDiv, ite_eq_right (by omega : y.val ≠ 0), checkedSigned,
    dite_eq_right outside]

theorem signedDiv_defined_iff (target : Target) (x y : Value target .sint) :
    (∃ q, signedDiv target x y = .defined q) ↔
      y.val ≠ 0 ∧ ¬ DivisionOverflowPair x y := by
  constructor
  · rintro ⟨q, execution⟩
    constructor
    · intro zero
      simp [signedDiv, zero] at execution
    · intro pair
      rw [signedDiv_min_neg_one target x y pair.1 pair.2] at execution
      cases execution
  · rintro ⟨nonzero, ordinary⟩
    obtain ⟨q, execution, _⟩ := signedDiv_spec target x y nonzero ordinary
    exact ⟨q, execution⟩

end EDSL.Source.IntegerArithmetic
