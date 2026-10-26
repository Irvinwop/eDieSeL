/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Certificate

set_option autoImplicit false

namespace EDSL.Source.Division

/-- An independent quotient specification, stated without division or remainder.
The result type supplies its unsigned representability bound separately. -/
def QuotientInterval (target : Target) (numerator denominator result : Value target .uint) :
    Prop :=
  result.val * denominator.val ≤ numerator.val ∧
    numerator.val < (result.val + 1) * denominator.val

/-- All representable numerators and every nonzero representable denominator. -/
def NonzeroDenominator {target : Target} (inputs : Inputs target [.uint, .uint]) : Prop :=
  (inputs.get (.there .here)).val ≠ 0

/-- `return numerator / denominator;` in the shared pure fragment. -/
def quotient (target : Target) (dialect : Dialect) : Program target [.uint, .uint] .uint :=
  ⟨dialect, .gnuModulo, .udiv (.param .here) (.param (.there .here))⟩

theorem quotient_verified (target : Target) (dialect : Dialect) :
    Verifies (quotient target dialect) NonzeroDenominator
      (fun inputs result => QuotientInterval target
        (inputs.get .here) (inputs.get (.there .here)) result) := by
  intro inputs permitted
  let numerator := inputs.get .here
  let denominator := inputs.get (.there .here)
  have nonzero : denominator.val ≠ 0 := permitted
  refine ⟨⟨numerator.val / denominator.val,
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) numerator.isLt⟩, ?_, ?_⟩
  · simp [eval, quotient, evalExpr, ExpressionCore.evalOutcome, ExpressionCore.evalCore, bind, Outcome.andThen, unsignedDiv,
      numerator, denominator, nonzero]
  · exact ⟨Nat.div_mul_le_self _ _, by
      simpa [Nat.mul_comm] using
        Nat.lt_mul_div_succ numerator.val (Nat.pos_of_ne_zero nonzero)⟩

theorem quotient_noUB (target : Target) (dialect : Dialect) :
    NoUB (quotient target dialect) NonzeroDenominator :=
  (quotient_verified target dialect).noUB

theorem modulus_gt_one (target : Target) : 1 < target.modulus := by
  apply Nat.one_lt_two_pow
  have minimum := target.atLeast16
  omega

def one (target : Target) : Value target .uint := ⟨1, modulus_gt_one target⟩

def zero (target : Target) : Value target .uint := ⟨0, target.modulus_pos⟩

/-- The nonzero-denominator domain is inhabited independently of the evaluator. -/
theorem quotient_certificate (target : Target) (dialect : Dialect) :
    Certificate (quotient target dialect) NonzeroDenominator
      (fun inputs result => QuotientInterval target
        (inputs.get .here) (inputs.get (.there .here)) result) where
  useful := ⟨.cons (zero target) (.cons (one target) .nil), by
    change (1 : Nat) ≠ 0
    omega⟩
  verified := quotient_verified target dialect

/-- A deliberately incorrect quotient implementation: the unsigned increment
wraps before division. It uses only defined source operations on the same domain. -/
def wrappedIncrement (target : Target) (dialect : Dialect) :
    Program target [.uint, .uint] .uint :=
  ⟨dialect, .gnuModulo, .udiv (.uadd (.param .here) (.literal (one target)))
    (.param (.there .here))⟩

/-- Functional incorrectness does not prevent defined completion. -/
theorem wrappedIncrement_noUB (target : Target) (dialect : Dialect) :
    NoUB (wrappedIncrement target dialect) NonzeroDenominator := by
  intro inputs permitted
  let numerator := inputs.get .here
  let denominator := inputs.get (.there .here)
  have nonzero : denominator.val ≠ 0 := permitted
  let incremented : Value target .uint :=
    ⟨(numerator.val + 1) % target.modulus, Nat.mod_lt _ target.modulus_pos⟩
  refine ⟨⟨incremented.val / denominator.val,
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) incremented.isLt⟩, ?_⟩
  simp [eval, wrappedIncrement, evalExpr, ExpressionCore.evalOutcome, ExpressionCore.evalCore, bind, pure, Outcome.andThen, unsignedAdd,
    unsignedDiv, one, numerator, denominator, incremented, nonzero]

def maximum (target : Target) : Value target .uint :=
  ⟨target.modulus - 1, by have positive := target.modulus_pos; omega⟩

/-- The counterexample is UINT_MAX with denominator one at every admitted width. -/
def counterexample (target : Target) : Inputs target [.uint, .uint] :=
  .cons (maximum target) (.cons (one target) .nil)

theorem counterexample_admitted (target : Target) :
    NonzeroDenominator (counterexample target) := by
  change (1 : Nat) ≠ 0
  omega

theorem wrappedIncrement_counterexample_defined (target : Target) (dialect : Dialect) :
    eval (wrappedIncrement target dialect) (counterexample target) = .defined (zero target) := by
  have wraps : target.modulus - 1 + 1 = target.modulus := by
    have positive := target.modulus_pos
    omega
  change unsignedDiv target
    ⟨(target.modulus - 1 + 1) % target.modulus, Nat.mod_lt _ target.modulus_pos⟩
    (one target) = .defined (zero target)
  simp [unsignedDiv, one, zero, wraps]

theorem counterexample_violates_contract (target : Target) :
    ¬ QuotientInterval target
      ((counterexample target).get .here)
      ((counterexample target).get (.there .here)) (zero target) := by
  intro interval
  have upper : target.modulus - 1 < 1 := by
    change 0 * 1 ≤ target.modulus - 1 ∧
      target.modulus - 1 < (0 + 1) * 1 at interval
    exact interval.2
  have large := modulus_gt_one target
  omega

theorem wrappedIncrement_not_verified (target : Target) (dialect : Dialect) :
    ¬ Verifies (wrappedIncrement target dialect) NonzeroDenominator
      (fun inputs result => QuotientInterval target
        (inputs.get .here) (inputs.get (.there .here)) result) := by
  intro verified
  obtain ⟨result, execution, specification⟩ :=
    verified (counterexample target) (counterexample_admitted target)
  have same : zero target = result := Outcome.defined.inj
    ((wrappedIncrement_counterexample_defined target dialect).symm.trans execution)
  exact counterexample_violates_contract target (same ▸ specification)

theorem wrappedIncrement_not_certified (target : Target) (dialect : Dialect) :
    ¬ Certificate (wrappedIncrement target dialect) NonzeroDenominator
      (fun inputs result => QuotientInterval target
        (inputs.get .here) (inputs.get (.there .here)) result) := by
  intro certificate
  exact wrappedIncrement_not_verified target dialect certificate.verified

end EDSL.Source.Division
