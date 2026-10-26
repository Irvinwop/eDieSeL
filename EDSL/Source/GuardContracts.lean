/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.VCGen
import EDSL.Source.Division
import EDSL.Source.IntegerArithmetic

set_option autoImplicit false

namespace EDSL.Source.GuardContracts

/-! All-input clients of the shared source evaluator. The guards are core bool
expressions; dialect metadata does not assert that C and C++ source logical
expressions have the same type. Literals below are representable numeric values,
without a parser, unary-negation, object-storage, or native-execution claim.
-/

def signedZero (target : Target) : Value target .sint :=
  ⟨0, by have bound := IntegerArithmetic.signedBound_atLeast32768 target; omega⟩

def signedMinimum (target : Target) : Value target .sint :=
  ⟨-target.signedBound, by
    have bound := IntegerArithmetic.signedBound_atLeast32768 target
    omega⟩

def signedNegativeOne (target : Target) : Value target .sint :=
  ⟨-1, by have bound := IntegerArithmetic.signedBound_atLeast32768 target; omega⟩

def unsignedGuard (target : Target) : Expr target [.uint, .uint] (.small .boolean) :=
  .compare .ne .uint (.param (.there .here)) (.literal (Division.zero target))

def signedNonzeroGuard (target : Target) : Expr target [.sint, .sint] (.small .boolean) :=
  .compare .ne .sint (.param (.there .here)) (.literal (signedZero target))

/-- `d != 0 && (n != MIN || d != -1)`, using only comparisons and lazy selects.
Both logical intermediate results have the core canonical bool type. -/
def signedGuard (target : Target) : Expr target [.sint, .sint] (.small .boolean) :=
  .select (signedNonzeroGuard target)
    (.select (.compare .ne .sint (.param .here) (.literal (signedMinimum target)))
      (.literal (booleanValue true))
      (.compare .ne .sint (.param (.there .here)) (.literal (signedNegativeOne target))))
    (.literal (booleanValue false))

def guardedUnsigned (target : Target) (dialect : Dialect) :
    Program target [.uint, .uint] .uint :=
  ⟨dialect, .gnuModulo, .select (unsignedGuard target)
    (.udiv (.param .here) (.param (.there .here))) (.literal (Division.zero target))⟩

def guardedSigned (target : Target) (dialect : Dialect) :
    Program target [.sint, .sint] .sint :=
  ⟨dialect, .gnuModulo, .select (signedGuard target)
    (.sdiv (.param .here) (.param (.there .here))) (.literal (signedZero target))⟩

/-- A synthetic negative control: the nonzero check misses MIN / -1. -/
def nonzeroGuardedSigned (target : Target) (dialect : Dialect) :
    Program target [.sint, .sint] .sint :=
  ⟨dialect, .gnuModulo, .select (signedNonzeroGuard target)
    (.sdiv (.param .here) (.param (.there .here))) (.literal (signedZero target))⟩

/-- These statements scan the original complete bodies, including both arms. -/
theorem guardedUnsigned_supported (target : Target) (dialect : Dialect) :
    (guardedUnsigned target dialect).body.Supported := rfl

theorem guardedSigned_supported (target : Target) (dialect : Dialect) :
    (guardedSigned target dialect).body.Supported := rfl

theorem nonzeroGuardedSigned_supported (target : Target) (dialect : Dialect) :
    (nonzeroGuardedSigned target dialect).body.Supported := rfl

/-- A zero denominator returns zero; otherwise the quotient is specified by an
independent multiplication interval, without evaluating a division in the post. -/
def UnsignedResult {target : Target} (inputs : Inputs target [.uint, .uint])
    (result : Value target .uint) : Prop :=
  if (inputs.get (.there .here)).val = 0 then result.val = 0
  else Division.QuotientInterval target (inputs.get .here) (inputs.get (.there .here)) result

/-- Exceptional inputs return zero; all other inputs satisfy reconstruction,
remainder magnitude, and dividend-sign constraints. No division occurs here. -/
def SignedResult {target : Target} (inputs : Inputs target [.sint, .sint])
    (result : Value target .sint) : Prop :=
  if (inputs.get (.there .here)).val = 0 ∨
      ((inputs.get .here).val = -target.signedBound ∧
        (inputs.get (.there .here)).val = -1) then result.val = 0
  else ∃ remainder : Int, IntegerArithmetic.TruncatingDivision
    (inputs.get .here).val (inputs.get (.there .here)).val result.val remainder

/-- Observations concern the actual raw evaluator, before the program coverage
gate. The comparison law supplies the mathematical meaning of the flag. -/
theorem unsignedGuard_observes (target : Target) (policy : IntegerConversionPolicy)
    (inputs : Inputs target [.uint, .uint]) :
    ∃ flag, evalExpr policy inputs (unsignedGuard target) = .defined flag ∧
      (flag.toInt ≠ 0 ↔ (inputs.get (.there .here)).val ≠ 0) := by
  refine ⟨compareValues .ne (inputs.get (.there .here)) (Division.zero target), rfl, ?_⟩
  simpa [ComparisonOp.Relates, Value.toInt, Division.zero] using
    compareValues_nonzero_iff .ne (inputs.get (.there .here)) (Division.zero target)

theorem signedNonzeroGuard_observes (target : Target) (policy : IntegerConversionPolicy)
    (inputs : Inputs target [.sint, .sint]) :
    ∃ flag, evalExpr policy inputs (signedNonzeroGuard target) = .defined flag ∧
      (flag.toInt ≠ 0 ↔ (inputs.get (.there .here)).val ≠ 0) := by
  refine ⟨compareValues .ne (inputs.get (.there .here)) (signedZero target), rfl, ?_⟩
  exact compareValues_nonzero_iff .ne (inputs.get (.there .here)) (signedZero target)

theorem signedGuard_observes (target : Target) (policy : IntegerConversionPolicy)
    (inputs : Inputs target [.sint, .sint]) :
    ∃ flag, evalExpr policy inputs (signedGuard target) = .defined flag ∧
      (flag.toInt ≠ 0 ↔ (inputs.get (.there .here)).val ≠ 0 ∧
        ¬ IntegerArithmetic.DivisionOverflowPair
          (inputs.get .here) (inputs.get (.there .here))) := by
  let numerator := inputs.get .here
  let denominator := inputs.get (.there .here)
  have denominator_correct :
      (compareValues .ne denominator (signedZero target)).toInt ≠ 0 ↔
        denominator.val ≠ 0 :=
    compareValues_nonzero_iff .ne denominator (signedZero target)
  have numerator_correct :
      (compareValues .ne numerator (signedMinimum target)).toInt ≠ 0 ↔
        numerator.val ≠ -target.signedBound :=
    compareValues_nonzero_iff .ne numerator (signedMinimum target)
  have negative_one_correct :
      (compareValues .ne denominator (signedNegativeOne target)).toInt ≠ 0 ↔
        denominator.val ≠ -1 :=
    compareValues_nonzero_iff .ne denominator (signedNegativeOne target)
  apply (Outcome.requires_iff _ _).mp
  apply (vcExpr_iff policy inputs (signedGuard target) _).mp
  change (if (compareValues .ne denominator (signedZero target)).toInt = 0 then
      ((booleanValue (target := target) false).toInt ≠ 0 ↔ denominator.val ≠ 0 ∧
        ¬ IntegerArithmetic.DivisionOverflowPair numerator denominator)
    else if (compareValues .ne numerator (signedMinimum target)).toInt = 0 then
      ((compareValues .ne denominator (signedNegativeOne target)).toInt ≠ 0 ↔
        denominator.val ≠ 0 ∧ ¬ IntegerArithmetic.DivisionOverflowPair numerator denominator)
    else ((booleanValue (target := target) true).toInt ≠ 0 ↔ denominator.val ≠ 0 ∧
        ¬ IntegerArithmetic.DivisionOverflowPair numerator denominator))
  by_cases denominator_zero : (compareValues .ne denominator (signedZero target)).toInt = 0
  · have zero : denominator.val = 0 := by
      by_cases zero : denominator.val = 0
      · exact zero
      · exact False.elim (denominator_correct.mpr zero denominator_zero)
    simp [denominator_zero, booleanValue_toInt, zero]
  · have nonzero := denominator_correct.mp denominator_zero
    by_cases numerator_minimum :
        (compareValues .ne numerator (signedMinimum target)).toInt = 0
    · have minimum : numerator.val = -target.signedBound := by
        by_cases minimum : numerator.val = -target.signedBound
        · exact minimum
        · exact False.elim (numerator_correct.mpr minimum numerator_minimum)
      simpa [denominator_zero, numerator_minimum,
        IntegerArithmetic.DivisionOverflowPair, minimum, nonzero] using
        negative_one_correct
    · have ordinary := numerator_correct.mp numerator_minimum
      simp [denominator_zero, numerator_minimum, booleanValue_toInt, nonzero,
        IntegerArithmetic.DivisionOverflowPair, ordinary]

/-- The selected unsigned division branch obtains its precondition from the
executed comparison, rather than from the admission predicate. -/
theorem unsignedGuard_branch_safe (target : Target) (policy : IntegerConversionPolicy)
    (inputs : Inputs target [.uint, .uint]) (flag : Value target (.small .boolean))
    (execution : evalExpr policy inputs (unsignedGuard target) = .defined flag)
    (selected : flag.toInt ≠ 0) : (inputs.get (.there .here)).val ≠ 0 := by
  obtain ⟨observed, observed_execution, correct⟩ := unsignedGuard_observes target policy inputs
  have same : observed = flag := Outcome.defined.inj (observed_execution.symm.trans execution)
  exact (same ▸ correct).mp selected

/-- Both nonzero and the sole signed overflow exclusion are local facts of the
executed true branch. The proof uses the actual nested-select guard observation. -/
theorem signedGuard_branch_safe (target : Target) (policy : IntegerConversionPolicy)
    (inputs : Inputs target [.sint, .sint]) (flag : Value target (.small .boolean))
    (execution : evalExpr policy inputs (signedGuard target) = .defined flag)
    (selected : flag.toInt ≠ 0) :
    (inputs.get (.there .here)).val ≠ 0 ∧
      ¬ IntegerArithmetic.DivisionOverflowPair (inputs.get .here) (inputs.get (.there .here)) := by
  obtain ⟨observed, observed_execution, correct⟩ := signedGuard_observes target policy inputs
  have same : observed = flag := Outcome.defined.inj (observed_execution.symm.trans execution)
  exact (same ▸ correct).mp selected

theorem unsignedGuard_zero_iff (target : Target) (policy : IntegerConversionPolicy)
    (inputs : Inputs target [.uint, .uint]) (flag : Value target (.small .boolean))
    (execution : evalExpr policy inputs (unsignedGuard target) = .defined flag) :
    flag.toInt = 0 ↔ (inputs.get (.there .here)).val = 0 := by
  obtain ⟨observed, observed_execution, correct⟩ := unsignedGuard_observes target policy inputs
  have same : observed = flag := Outcome.defined.inj (observed_execution.symm.trans execution)
  rw [same] at correct
  omega

theorem signedGuard_zero_iff (target : Target) (policy : IntegerConversionPolicy)
    (inputs : Inputs target [.sint, .sint]) (flag : Value target (.small .boolean))
    (execution : evalExpr policy inputs (signedGuard target) = .defined flag) :
    flag.toInt = 0 ↔ (inputs.get (.there .here)).val = 0 ∨
      IntegerArithmetic.DivisionOverflowPair (inputs.get .here) (inputs.get (.there .here)) := by
  obtain ⟨observed, observed_execution, correct⟩ := signedGuard_observes target policy inputs
  have same : observed = flag := Outcome.defined.inj (observed_execution.symm.trans execution)
  rw [same] at correct
  simp only [IntegerArithmetic.DivisionOverflowPair] at correct ⊢
  omega

/-- Composition through the original program's coverage preflight and actual
lazy evaluator. An unchosen division is never evaluated. -/
theorem guardedUnsigned_eval (target : Target) (dialect : Dialect)
    (inputs : Inputs target [.uint, .uint]) (flag : Value target (.small .boolean))
    (guard_execution : evalExpr .gnuModulo inputs (unsignedGuard target) = .defined flag) :
    eval (guardedUnsigned target dialect) inputs =
      if flag.toInt = 0 then .defined (Division.zero target)
      else unsignedDiv target (inputs.get .here) (inputs.get (.there .here)) := by
  change ((evalExpr .gnuModulo inputs (unsignedGuard target)).andThen fun value =>
    if value.toInt = 0 then .defined (Division.zero target)
    else unsignedDiv target (inputs.get .here) (inputs.get (.there .here))) = _
  rw [guard_execution]
  rfl

theorem guardedSigned_eval (target : Target) (dialect : Dialect)
    (inputs : Inputs target [.sint, .sint]) (flag : Value target (.small .boolean))
    (guard_execution : evalExpr .gnuModulo inputs (signedGuard target) = .defined flag) :
    eval (guardedSigned target dialect) inputs =
      if flag.toInt = 0 then .defined (signedZero target)
      else signedDiv target (inputs.get .here) (inputs.get (.there .here)) := by
  change ((evalExpr .gnuModulo inputs (signedGuard target)).andThen fun value =>
    if value.toInt = 0 then .defined (signedZero target)
    else signedDiv target (inputs.get .here) (inputs.get (.there .here))) = _
  rw [guard_execution]
  rfl

theorem guardedUnsigned_verified (target : Target) (dialect : Dialect) :
    Verifies (guardedUnsigned target dialect) (fun _ => True) UnsignedResult := by
  intro inputs _
  obtain ⟨flag, guard_execution, _⟩ := unsignedGuard_observes target .gnuModulo inputs
  by_cases selected_false : flag.toInt = 0
  · have denominator_zero :=
      (unsignedGuard_zero_iff target .gnuModulo inputs flag guard_execution).mp selected_false
    refine ⟨Division.zero target, ?_, ?_⟩
    · rw [guardedUnsigned_eval target dialect inputs flag guard_execution,
        ite_eq_left selected_false]
    · simp only [UnsignedResult, denominator_zero, ↓reduceIte, Division.zero]
  · have nonzero :=
      unsignedGuard_branch_safe target .gnuModulo inputs flag guard_execution selected_false
    obtain ⟨result, division_execution, interval⟩ :=
      Division.quotient_verified target dialect inputs nonzero
    change unsignedDiv target (inputs.get .here) (inputs.get (.there .here)) =
      .defined result at division_execution
    refine ⟨result, ?_, ?_⟩
    · rw [guardedUnsigned_eval target dialect inputs flag guard_execution,
        ite_eq_right selected_false]
      exact division_execution
    · simpa only [UnsignedResult, nonzero, ↓reduceIte] using interval

theorem guardedSigned_verified (target : Target) (dialect : Dialect) :
    Verifies (guardedSigned target dialect) (fun _ => True) SignedResult := by
  intro inputs _
  obtain ⟨flag, guard_execution, _⟩ := signedGuard_observes target .gnuModulo inputs
  by_cases selected_false : flag.toInt = 0
  · have exceptional :=
      (signedGuard_zero_iff target .gnuModulo inputs flag guard_execution).mp selected_false
    refine ⟨signedZero target, ?_, ?_⟩
    · rw [guardedSigned_eval target dialect inputs flag guard_execution,
        ite_eq_left selected_false]
    · change (inputs.get (.there .here)).val = 0 ∨
        ((inputs.get .here).val = -target.signedBound ∧
          (inputs.get (.there .here)).val = -1) at exceptional
      simp only [SignedResult, exceptional, ↓reduceIte, signedZero]
  · obtain ⟨nonzero, ordinary⟩ :=
      signedGuard_branch_safe target .gnuModulo inputs flag guard_execution selected_false
    obtain ⟨result, division_execution, reconstruction⟩ :=
      IntegerArithmetic.signedDiv_spec target
        (inputs.get .here) (inputs.get (.there .here)) nonzero ordinary
    refine ⟨result, ?_, ?_⟩
    · rw [guardedSigned_eval target dialect inputs flag guard_execution,
        ite_eq_right selected_false]
      exact division_execution
    · change ¬ ((inputs.get .here).val = -target.signedBound ∧
        (inputs.get (.there .here)).val = -1) at ordinary
      simpa [SignedResult, nonzero, ordinary] using reconstruction

theorem guardedUnsigned_certificate (target : Target) (dialect : Dialect) :
    Certificate (guardedUnsigned target dialect) (fun _ => True) UnsignedResult where
  useful := ⟨.cons (Division.zero target) (.cons (Division.zero target) .nil), True.intro⟩
  verified := guardedUnsigned_verified target dialect

theorem guardedSigned_certificate (target : Target) (dialect : Dialect) :
    Certificate (guardedSigned target dialect) (fun _ => True) SignedResult where
  useful := ⟨.cons (signedZero target) (.cons (signedZero target) .nil), True.intro⟩
  verified := guardedSigned_verified target dialect

theorem guardedUnsigned_noUB (target : Target) (dialect : Dialect) :
    NoUB (guardedUnsigned target dialect) (fun _ => True) :=
  (guardedUnsigned_certificate target dialect).noUB

theorem guardedSigned_noUB (target : Target) (dialect : Dialect) :
    NoUB (guardedSigned target dialect) (fun _ => True) :=
  (guardedSigned_certificate target dialect).noUB

/-- A typed witness available for every admitted target; MIN and -1 are values,
not a claim about source tokens or the parsing of unary minus. -/
def signedExceptionInputs (target : Target) : Inputs target [.sint, .sint] :=
  .cons (signedMinimum target) (.cons (signedNegativeOne target) .nil)

/-- The missing exceptional-pair guard causes actual executed source UB. -/
theorem nonzeroGuardedSigned_min_neg_one (target : Target) (dialect : Dialect) :
    eval (nonzeroGuardedSigned target dialect) (signedExceptionInputs target) =
      .undefined .signedDivisionOverflow := by
  obtain ⟨flag, guard_execution, correct⟩ :=
    signedNonzeroGuard_observes target .gnuModulo (signedExceptionInputs target)
  have selected : flag.toInt ≠ 0 := correct.mpr (by
    change (-1 : Int) ≠ 0
    decide +kernel)
  change ((evalExpr .gnuModulo (signedExceptionInputs target)
    (signedNonzeroGuard target)).andThen fun value =>
      if value.toInt = 0 then .defined (signedZero target)
      else signedDiv target (signedMinimum target) (signedNegativeOne target)) = _
  rw [guard_execution]
  simp only [Outcome.andThen, selected, ↓reduceIte]
  exact IntegerArithmetic.signedDiv_min_neg_one target
    (signedMinimum target) (signedNegativeOne target) rfl rfl

theorem nonzeroGuardedSigned_not_verified (target : Target) (dialect : Dialect)
    (post : Inputs target [.sint, .sint] → Value target .sint → Prop) :
    ¬ Verifies (nonzeroGuardedSigned target dialect) (fun _ => True) post := by
  intro verified
  obtain ⟨result, execution, _⟩ := verified (signedExceptionInputs target) True.intro
  rw [nonzeroGuardedSigned_min_neg_one target dialect] at execution
  cases execution

theorem nonzeroGuardedSigned_not_certified (target : Target) (dialect : Dialect)
    (post : Inputs target [.sint, .sint] → Value target .sint → Prop) :
    ¬ Certificate (nonzeroGuardedSigned target dialect) (fun _ => True) post := by
  intro certificate
  exact nonzeroGuardedSigned_not_verified target dialect post certificate.verified

end EDSL.Source.GuardContracts
