/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Unary
import EDSL.Source.ComplementBits
import EDSL.Source.PromotionContracts

set_option autoImplicit false

namespace EDSL.Source.UnaryContracts

/-- Independent numeric exclusion, including small signed types whose promoted
range has the same minimum. It mentions neither execution nor source safety. -/
def NegationAdmitted (target : Target) (kind : ArithmeticType) (input : Int) : Prop :=
  match kind with
  | .sint => input ≠ -target.signedBound
  | .uint => True

def NegationResult (target : Target) (kind : ArithmeticType) (input result : Int) : Prop :=
  match kind with
  | .sint => result = -input
  | .uint => ∃ carry : Nat, carry ≤ 1 ∧ result + input = (carry : Int) * (target.modulus : Int)

/-- Independent retained-value-bit specification; no subtraction occurs here. -/
def ComplementResult (target : Target) (kind : ArithmeticType) (input result : Int) : Prop :=
  match kind with
  | .sint => ComplementBits.IntBits target.intBits input result
  | .uint => ComplementBits.NatBits target.intBits input.toNat result.toNat

/-- One reusable client for every admitted unary operation, source type and dialect. -/
def unaryReturn (target : Target) (dialect : Dialect) (operation : UnaryOp)
    (source : IntType) : Program target [source] (unaryType target dialect operation source) :=
  ⟨dialect, .gnuModulo, Expr.unary dialect operation (.param .here)⟩

def Admitted {target : Target} {source : IntType} (operation : UnaryOp)
    (inputs : Inputs target [source]) : Prop :=
  match operation with
  | .minus => NegationAdmitted target (promotedType target source) (inputs.get .here).toInt
  | _ => True

/-- Arithmetic value/carry and per-bit relations, with a zero/nonzero logical
contract. None calls a unary helper, cast implementation, or source evaluator. -/
def Result (target : Target) (source : IntType) (operation : UnaryOp)
    (input result : Int) : Prop :=
  match operation with
  | .plus => result = input
  | .minus => NegationResult target (promotedType target source) input result
  | .complement => ComplementResult target (promotedType target source) input result
  | .logicalNot => (input = 0 ∧ result = 1) ∨ (input ≠ 0 ∧ result = 0)

theorem unaryReturn_supported (target : Target) (dialect : Dialect)
    (operation : UnaryOp) (source : IntType) :
    (unaryReturn target dialect operation source).body.Supported :=
  Expr.firstUnsupported_unary dialect operation (.param .here)

theorem promotedNegate_spec (target : Target) (kind : ArithmeticType)
    (input : Value target kind.asIntType)
    (ordinary : NegationAdmitted target kind input.toInt) :
    ∃ result, EDSL.Source.promotedNegate target kind input = .defined result ∧
      NegationResult target kind input.toInt result.toInt := by
  cases kind with
  | sint => exact IntegerUnary.signedNegate_spec target input ordinary
  | uint =>
      obtain ⟨result, execution, carry, carry_bound, equation⟩ :=
        IntegerUnary.unsignedNegate_spec target input
      refine ⟨result, execution, carry, carry_bound, ?_⟩
      change (result.val : Int) + (input.val : Int) = (carry : Int) * (target.modulus : Int)
      have integers := congrArg (fun value : Nat => (value : Int)) equation
      rw [Int.natCast_add, Int.natCast_mul] at integers
      exact integers

theorem promotedComplement_spec (target : Target) (kind : ArithmeticType)
    (input : Value target kind.asIntType) :
    ∃ result, EDSL.Source.promotedComplement target kind input = .defined result ∧
      ComplementResult target kind input.toInt result.toInt := by
  cases kind with
  | sint =>
      obtain ⟨result, execution, equation⟩ := IntegerUnary.signedComplement_spec target input
      exact ⟨result, execution, ComplementBits.signed_value_bits target input result equation⟩
  | uint =>
      obtain ⟨result, execution, equation⟩ := IntegerUnary.unsignedComplement_spec target input
      exact ⟨result, execution, ComplementBits.unsigned_value_bits target input result equation⟩

theorem unaryReturn_verified (target : Target) (dialect : Dialect)
    (operation : UnaryOp) (source : IntType) :
    Verifies (unaryReturn target dialect operation source) (Admitted operation)
      (fun inputs result => Result target source operation (inputs.get .here).toInt result.toInt) := by
  intro inputs permitted
  let input := inputs.get .here
  let promoted := IntegerPromotions.promoteValue input
  have preserved : promoted.toInt = input.toInt := IntegerPromotions.promoteValue_toInt input
  cases operation with
  | plus =>
      refine ⟨promoted, ?_, preserved⟩
      rw [eval_of_supported _ _ (unaryReturn_supported target dialect .plus source)]
      rfl
  | minus =>
      have ordinary : NegationAdmitted target (promotedType target source) promoted.toInt := by
        rw [preserved]
        exact permitted
      obtain ⟨result, execution, specification⟩ :=
        promotedNegate_spec target (promotedType target source) promoted ordinary
      refine ⟨result, ?_, ?_⟩
      · rw [eval_of_supported _ _ (unaryReturn_supported target dialect .minus source)]
        change evalExpr .gnuModulo inputs (Expr.unaryMinus (.param .here)) = .defined result
        rw [eval_unaryMinus]
        exact execution
      · change NegationResult target (promotedType target source) input.toInt result.toInt
        rw [preserved] at specification
        exact specification
  | complement =>
      obtain ⟨result, execution, specification⟩ :=
        promotedComplement_spec target (promotedType target source) promoted
      refine ⟨result, ?_, ?_⟩
      · rw [eval_of_supported _ _ (unaryReturn_supported target dialect .complement source)]
        change evalExpr .gnuModulo inputs (Expr.unaryComplement (.param .here)) = .defined result
        rw [eval_unaryComplement]
        exact execution
      · change ComplementResult target (promotedType target source) input.toInt result.toInt
        rw [preserved] at specification
        exact specification
  | logicalNot =>
      obtain ⟨result, execution, observed⟩ :=
        eval_logicalNot_defined dialect .gnuModulo inputs (.param .here) input rfl
      refine ⟨result, ?_, ?_⟩
      · rw [eval_of_supported _ _ (unaryReturn_supported target dialect .logicalNot source)]
        exact execution
      · change (input.toInt = 0 ∧ result.toInt = 1) ∨ (input.toInt ≠ 0 ∧ result.toInt = 0)
        by_cases zero : input.toInt = 0
        · rw [ite_eq_left zero] at observed
          exact Or.inl ⟨zero, observed⟩
        · rw [ite_eq_right zero] at observed
          exact Or.inr ⟨zero, observed⟩

private theorem zeroValue_toInt (target : Target) (source : IntType) :
    (PromotionContracts.zeroValue target source).toInt = 0 := by
  cases source <;> rfl

theorem unaryReturn_certificate (target : Target) (dialect : Dialect)
    (operation : UnaryOp) (source : IntType) :
    Certificate (unaryReturn target dialect operation source) (Admitted operation)
      (fun inputs result => Result target source operation (inputs.get .here).toInt result.toInt) where
  useful := by
    refine ⟨.cons (PromotionContracts.zeroValue target source) .nil, ?_⟩
    cases operation with
    | plus => trivial
    | complement => trivial
    | logicalNot => trivial
    | minus =>
        change NegationAdmitted target (promotedType target source)
          (PromotionContracts.zeroValue target source).toInt
        rw [zeroValue_toInt]
        cases promotedType target source with
        | uint => trivial
        | sint =>
            change (0 : Int) ≠ -target.signedBound
            have positive := IntegerArithmetic.signedBound_atLeast32768 target
            omega
  verified := unaryReturn_verified target dialect operation source

theorem unaryReturn_noUB (target : Target) (dialect : Dialect)
    (operation : UnaryOp) (source : IntType) :
    NoUB (unaryReturn target dialect operation source) (Admitted operation) :=
  (unaryReturn_certificate target dialect operation source).noUB

/-- A numeric boundary for the already selected arithmetic kind. -/
theorem promotedNegate_minimum (target : Target) (kind : ArithmeticType)
    (input : Value target kind.asIntType) (signed : kind = .sint)
    (minimum : input.toInt = -target.signedBound) :
    EDSL.Source.promotedNegate target kind input = .undefined .signedSubtractionOverflow := by
  cases kind with
  | sint => exact IntegerUnary.signedNegate_overflow target input minimum
  | uint => cases signed

/-- This witness law also applies to small signed types when their promoted
value equals MIN; small source type alone does not justify safe negation. -/
theorem unaryMinus_minimum_undefined (target : Target) (dialect : Dialect)
    (source : IntType) (input : Value target source)
    (signed : promotedType target source = .sint)
    (minimum : input.toInt = -target.signedBound) :
    eval (unaryReturn target dialect .minus source) (.cons input .nil) =
      .undefined .signedSubtractionOverflow := by
  rw [eval_of_supported _ _ (unaryReturn_supported target dialect .minus source)]
  change evalExpr .gnuModulo (.cons input .nil) (Expr.unaryMinus (.param .here)) = _
  rw [eval_unaryMinus]
  apply promotedNegate_minimum target (promotedType target source)
    (IntegerPromotions.promoteValue input) signed
  rw [IntegerPromotions.promoteValue_toInt]
  exact minimum

theorem unaryMinus_minimum_not_verified (target : Target) (dialect : Dialect)
    (source : IntType) (input : Value target source)
    (signed : promotedType target source = .sint) (minimum : input.toInt = -target.signedBound)
    (post : Inputs target [source] → Value target (unaryType target dialect .minus source) → Prop) :
    ¬ Verifies (unaryReturn target dialect .minus source) (fun _ => True) post := by
  intro verified
  obtain ⟨result, execution, _⟩ := verified (.cons input .nil) trivial
  rw [unaryMinus_minimum_undefined target dialect source input signed minimum] at execution
  cases execution

theorem unaryMinus_minimum_not_certified (target : Target) (dialect : Dialect)
    (source : IntType) (input : Value target source)
    (signed : promotedType target source = .sint) (minimum : input.toInt = -target.signedBound)
    (post : Inputs target [source] → Value target (unaryType target dialect .minus source) → Prop) :
    ¬ Certificate (unaryReturn target dialect .minus source) (fun _ => True) post := by
  intro certificate
  exact unaryMinus_minimum_not_verified target dialect source input signed minimum post
    certificate.verified

def signedMinimum (target : Target) : Value target .sint :=
  ⟨-target.signedBound, by
    have positive := IntegerArithmetic.signedBound_atLeast32768 target
    omega⟩

/-- An unconditional rejection on full signed int for every admitted profile. -/
theorem signedMinus_all_inputs_not_certified (target : Target) (dialect : Dialect)
    (post : Inputs target [.sint] → Value target .sint → Prop) :
    ¬ Certificate (unaryReturn target dialect .minus .sint) (fun _ => True) post :=
  unaryMinus_minimum_not_certified target dialect .sint (signedMinimum target) rfl rfl post

end EDSL.Source.UnaryContracts
