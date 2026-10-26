/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.IntegerArithmetic

set_option autoImplicit false

namespace EDSL.Source.IntegerUnary

/-! Proposed full-rank unary encodings over the existing subtraction primitives.
This numeric layer does not yet add unary source syntax. It assumes the admitted
two's-complement value ranges, without any object-layout or frontend theorem.
Desugared signed negation uses the existing signedSubtractionOverflow diagnostic.
-/

def unsignedZero (target : Target) : Value target .uint :=
  ⟨0, target.modulus_pos⟩

def signedZero (target : Target) : Value target .sint :=
  ⟨0, by
    have bound := IntegerArithmetic.signedBound_atLeast32768 target
    omega⟩

def signedMinusOne (target : Target) : Value target .sint :=
  ⟨-1, by
    have bound := IntegerArithmetic.signedBound_atLeast32768 target
    omega⟩

def unsignedMaximum (target : Target) : Value target .uint :=
  ⟨target.modulus - 1, by have positive := target.modulus_pos; omega⟩

/-- Each helper delegates to an existing primitive, with no alternate evaluator. -/
def unsignedNegate (target : Target) (value : Value target .uint) :
    Outcome (Value target .uint) :=
  unsignedSub target (unsignedZero target) value

def signedNegate (target : Target) (value : Value target .sint) :
    Outcome (Value target .sint) :=
  signedSub target (signedZero target) value

def unsignedComplement (target : Target) (value : Value target .uint) :
    Outcome (Value target .uint) :=
  unsignedSub target (unsignedMaximum target) value

def signedComplement (target : Target) (value : Value target .sint) :
    Outcome (Value target .sint) :=
  signedSub target (signedMinusOne target) value

/-- Independent conservation equation for modular unsigned negation. -/
def UnsignedNegation (target : Target) (input result : Value target .uint) : Prop :=
  ∃ carry : Nat, carry ≤ 1 ∧ result.val + input.val = carry * target.modulus

def SignedNegation {target : Target} (input result : Value target .sint) : Prop :=
  result.val = -input.val

def UnsignedComplement (target : Target) (input result : Value target .uint) : Prop :=
  input.val + result.val = target.modulus - 1

def SignedComplement {target : Target} (input result : Value target .sint) : Prop :=
  input.val + result.val = -1

theorem unsignedNegate_spec (target : Target) (input : Value target .uint) :
    ∃ result, unsignedNegate target input = .defined result ∧
      UnsignedNegation target input result := by
  obtain ⟨result, execution, carry, carry_bound, equation⟩ :=
    IntegerArithmetic.unsignedSub_spec target (unsignedZero target) input
  refine ⟨result, execution, carry, carry_bound, ?_⟩
  change result.val + input.val = 0 + carry * target.modulus at equation
  exact equation.trans (Nat.zero_add _)

theorem unsignedNegate_eq_defined_iff (target : Target)
    (input result : Value target .uint) :
    unsignedNegate target input = .defined result ↔ UnsignedNegation target input result := by
  change unsignedSub target (unsignedZero target) input = .defined result ↔ _
  rw [IntegerArithmetic.unsignedSub_eq_defined_iff]
  change (∃ carry : Nat, carry ≤ 1 ∧
    result.val + input.val = 0 + carry * target.modulus) ↔
    (∃ carry : Nat, carry ≤ 1 ∧ result.val + input.val = carry * target.modulus)
  simp only [Nat.zero_add]

/-- The input-range proof leaves exactly the minimum value as the exception. -/
theorem signedNegate_range_iff (target : Target) (input : Value target .sint) :
    IntegerArithmetic.SignedRange target (-input.val) ↔ input.val ≠ -target.signedBound := by
  have bounds := input.property
  change (-target.signedBound ≤ -input.val ∧ -input.val < target.signedBound) ↔ _
  omega

theorem signedNegate_spec (target : Target) (input : Value target .sint)
    (ordinary : input.val ≠ -target.signedBound) :
    ∃ result, signedNegate target input = .defined result ∧ SignedNegation input result := by
  have fits : IntegerArithmetic.SignedRange target ((signedZero target).val - input.val) := by
    change IntegerArithmetic.SignedRange target (0 - input.val)
    simpa only [Int.zero_sub] using (signedNegate_range_iff target input).mpr ordinary
  obtain ⟨result, execution, equation⟩ :=
    IntegerArithmetic.signedSub_spec target (signedZero target) input fits
  refine ⟨result, execution, ?_⟩
  change result.val = 0 - input.val at equation
  change result.val = -input.val
  omega

theorem signedNegate_eq_defined_iff (target : Target)
    (input result : Value target .sint) :
    signedNegate target input = .defined result ↔ SignedNegation input result := by
  change signedSub target (signedZero target) input = .defined result ↔ _
  rw [IntegerArithmetic.signedSub_eq_defined_iff]
  change result.val = 0 - input.val ↔ result.val = -input.val
  simp only [Int.zero_sub]

/-- This diagnostic follows the existing subtraction encoding; no unary-specific
reason or silent wrapping is added. -/
theorem signedNegate_overflow (target : Target) (input : Value target .sint)
    (minimum : input.val = -target.signedBound) :
    signedNegate target input = .undefined .signedSubtractionOverflow := by
  apply IntegerArithmetic.signedSub_overflow target (signedZero target) input
  have outside : ¬ IntegerArithmetic.SignedRange target (-input.val) := by
    rw [signedNegate_range_iff]
    exact fun ordinary => ordinary minimum
  simpa only [signedZero, Int.zero_sub] using outside

theorem signedNegate_defined_iff (target : Target) (input : Value target .sint) :
    (∃ result, signedNegate target input = .defined result) ↔
      input.val ≠ -target.signedBound := by
  constructor
  · rintro ⟨result, execution⟩ minimum
    rw [signedNegate_overflow target input minimum] at execution
    cases execution
  · intro ordinary
    obtain ⟨result, execution, _⟩ := signedNegate_spec target input ordinary
    exact ⟨result, execution⟩

theorem signedNegate_overflow_iff (target : Target) (input : Value target .sint) :
    signedNegate target input = .undefined .signedSubtractionOverflow ↔
      input.val = -target.signedBound := by
  constructor
  · intro execution
    by_cases minimum : input.val = -target.signedBound
    · exact minimum
    · obtain ⟨result, defined⟩ := (signedNegate_defined_iff target input).mpr minimum
      rw [defined] at execution
      cases execution
  · exact signedNegate_overflow target input

/-- All unsigned inputs have an exact complement; no borrow or wrap is needed. -/
theorem unsignedComplement_spec (target : Target) (input : Value target .uint) :
    ∃ result, unsignedComplement target input = .defined result ∧
      UnsignedComplement target input result := by
  have input_range := input.isLt
  have positive := target.modulus_pos
  let result : Value target .uint := ⟨target.modulus - 1 - input.val, by omega⟩
  refine ⟨result, ?_, ?_⟩
  · apply (IntegerArithmetic.unsignedSub_eq_defined_iff target
      (unsignedMaximum target) input result).mpr
    refine ⟨0, by omega, ?_⟩
    change target.modulus - 1 - input.val + input.val = target.modulus - 1 + 0 * target.modulus
    omega
  · change input.val + (target.modulus - 1 - input.val) = target.modulus - 1
    omega

theorem unsignedComplement_eq_defined_iff (target : Target)
    (input result : Value target .uint) :
    unsignedComplement target input = .defined result ↔ UnsignedComplement target input result := by
  obtain ⟨actual, execution, equation⟩ := unsignedComplement_spec target input
  constructor
  · intro same
    have result_same : actual = result := Outcome.defined.inj (execution.symm.trans same)
    exact result_same ▸ equation
  · intro result_equation
    have same : actual = result := by
      apply Fin.ext
      change input.val + actual.val = target.modulus - 1 at equation
      change input.val + result.val = target.modulus - 1 at result_equation
      omega
    exact same ▸ execution

/-- The mathematical signed complement lies in range for every representable
input, including MIN. It does not share signed negation's exceptional input. -/
theorem signedComplement_spec (target : Target) (input : Value target .sint) :
    ∃ result, signedComplement target input = .defined result ∧ SignedComplement input result := by
  have bounds := input.property
  have fits : IntegerArithmetic.SignedRange target ((signedMinusOne target).val - input.val) := by
    change -target.signedBound ≤ -1 - input.val ∧ -1 - input.val < target.signedBound
    omega
  obtain ⟨result, execution, equation⟩ :=
    IntegerArithmetic.signedSub_spec target (signedMinusOne target) input fits
  refine ⟨result, execution, ?_⟩
  change result.val = -1 - input.val at equation
  change input.val + result.val = -1
  omega

theorem signedComplement_eq_defined_iff (target : Target)
    (input result : Value target .sint) :
    signedComplement target input = .defined result ↔ SignedComplement input result := by
  change signedSub target (signedMinusOne target) input = .defined result ↔ _
  rw [IntegerArithmetic.signedSub_eq_defined_iff]
  change result.val = -1 - input.val ↔ input.val + result.val = -1
  omega

end EDSL.Source.IntegerUnary
