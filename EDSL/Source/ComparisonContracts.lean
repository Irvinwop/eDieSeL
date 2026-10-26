/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Conditions
import EDSL.Source.CastContracts

set_option autoImplicit false

namespace EDSL.Source.ComparisonContracts

/-- One source client for every comparison, integral input pair and dialect. -/
def compareReturn (target : Target) (dialect : Dialect) (operation : ComparisonOp)
    (left right : IntType) : Program target [left, right] dialect.logicalType :=
  ⟨dialect, .gnuModulo, Expr.sourceCompare dialect operation
    (.param .here) (.param (.there .here))⟩

/-- Original integers are related to unique common-type representatives by
independent carry equations, then compared by their mathematical relation.
No cast implementation, evaluator, or candidate-selected result occurs here. -/
def ComparisonResult {target : Target} {left right : IntType} {resultType : IntType}
    (operation : ComparisonOp) (inputs : Inputs target [left, right])
    (result : Value target resultType) : Prop :=
  (result.toInt = 0 ∨ result.toInt = 1) ∧
    ∃ normalizedLeft normalizedRight : Value target (commonType target left right),
      CastContracts.CastResult target (commonType target left right)
        (inputs.get .here).toInt normalizedLeft.toInt ∧
      CastContracts.CastResult target (commonType target left right)
        (inputs.get (.there .here)).toInt normalizedRight.toInt ∧
      (result.toInt = 1 ↔ operation.Relates normalizedLeft.toInt normalizedRight.toInt)

theorem compareReturn_supported (target : Target) (dialect : Dialect)
    (operation : ComparisonOp) (left right : IntType) :
    (compareReturn target dialect operation left right).body.Supported := by
  cases dialect <;> rfl

theorem compareReturn_verified (target : Target) (dialect : Dialect)
    (operation : ComparisonOp) (left right : IntType) :
    Verifies (compareReturn target dialect operation left right) (fun _ => True)
      (ComparisonResult operation) := by
  intro inputs _
  let promotedLeft := IntegerPromotions.promoteValue (inputs.get .here)
  let promotedRight := IntegerPromotions.promoteValue (inputs.get (.there .here))
  let normalizedLeft := IntegerCasts.castValue (commonType target left right) promotedLeft
  let normalizedRight := IntegerCasts.castValue (commonType target left right) promotedRight
  let flag := compareValues operation normalizedLeft normalizedRight
  let result := dialect.logicalValue flag
  refine ⟨result, ?_, Dialect.logicalValue_zero_one dialect flag,
    normalizedLeft, normalizedRight, ?_, ?_, ?_⟩
  · rw [eval_of_supported _ _ (compareReturn_supported target dialect operation left right)]
    change evalExpr .gnuModulo inputs
      (Expr.sourceCompare dialect operation (.param .here) (.param (.there .here))) = .defined result
    rw [Expr.sourceCompare, eval_logicalResult, eval_usualCompare]
    rfl
  · have specification := CastContracts.castValue_result (commonType target left right) promotedLeft
    simpa only [promotedLeft, IntegerPromotions.promoteValue_toInt] using specification
  · have specification := CastContracts.castValue_result (commonType target left right) promotedRight
    simpa only [promotedRight, IntegerPromotions.promoteValue_toInt] using specification
  · exact Dialect.logicalValue_compare_one_iff dialect operation normalizedLeft normalizedRight

theorem compareReturn_certificate (target : Target) (dialect : Dialect)
    (operation : ComparisonOp) (left right : IntType) :
    Certificate (compareReturn target dialect operation left right) (fun _ => True)
      (ComparisonResult operation) where
  useful := ⟨.cons (PromotionContracts.zeroValue target left)
    (.cons (PromotionContracts.zeroValue target right) .nil), trivial⟩
  verified := compareReturn_verified target dialect operation left right

theorem compareReturn_noUB (target : Target) (dialect : Dialect)
    (operation : ComparisonOp) (left right : IntType) :
    NoUB (compareReturn target dialect operation left right) (fun _ => True) :=
  (compareReturn_certificate target dialect operation left right).noUB

end EDSL.Source.ComparisonContracts
