/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Source.IntegerPromotions

set_option autoImplicit false

namespace EDSL.Source

/-! Numeric comparison and language-specific logical result values.
Operands are compared by their mathematical integers. This module performs no
integer promotions or common-type conversions; the source comparison grammar
supplies operands after those steps. Bool's source-value range is exactly 0/1,
independently of any storage width. No source execution, ABI, or frontend
correspondence is assumed or established here.
-/

/-- The canonical source bool corresponding to a Lean Boolean. -/
def booleanValue {target : Target} (flag : Bool) : Value target (.small .boolean) :=
  ⟨if flag then 1 else 0, by
    change 0 ≤ (if flag then (1 : Int) else 0) ∧ (if flag then (1 : Int) else 0) < 2
    cases flag <;> decide +kernel⟩

theorem booleanValue_toInt {target : Target} (flag : Bool) :
    (booleanValue (target := target) flag).toInt = if flag then 1 else 0 := rfl

theorem booleanValue_zero_one {target : Target} (flag : Bool) :
    (booleanValue (target := target) flag).toInt = 0 ∨
      (booleanValue (target := target) flag).toInt = 1 :=
  Value.boolean_values _

theorem booleanValue_one_iff {target : Target} (flag : Bool) :
    (booleanValue (target := target) flag).toInt = 1 ↔ flag = true := by
  rw [booleanValue_toInt]
  cases flag <;> decide +kernel

theorem booleanValue_zero_iff {target : Target} (flag : Bool) :
    (booleanValue (target := target) flag).toInt = 0 ↔ flag = false := by
  rw [booleanValue_toInt]
  cases flag <;> decide +kernel

/-- The mathematical relation specified by each comparison, independent of
the implementation of numeric comparison results. -/
def ComparisonOp.Relates : ComparisonOp → Int → Int → Prop
  | .eq, x, y => x = y
  | .ne, x, y => x ≠ y
  | .lt, x, y => x < y
  | .le, x, y => x ≤ y
  | .gt, x, y => y < x
  | .ge, x, y => y ≤ x

instance ComparisonOp.relatesDecidable (op : ComparisonOp) (x y : Int) :
    Decidable (op.Relates x y) := by
  cases op <;> unfold Relates <;> infer_instance

/-- Compare same-typed values by `toInt`, returning a canonical source bool.
This operation does not perform promotions or choose a common operand type. -/
def compareValues {target : Target} {ty : IntType} (op : ComparisonOp)
    (left right : Value target ty) : Value target (.small .boolean) :=
  booleanValue <| match op with
    | .eq => decide (left.toInt = right.toInt)
    | .ne => decide (left.toInt ≠ right.toInt)
    | .lt => decide (left.toInt < right.toInt)
    | .le => decide (left.toInt ≤ right.toInt)
    | .gt => decide (right.toInt < left.toInt)
    | .ge => decide (right.toInt ≤ left.toInt)

theorem compareValues_zero_one {target : Target} {ty : IntType} (op : ComparisonOp)
    (left right : Value target ty) :
    (compareValues op left right).toInt = 0 ∨ (compareValues op left right).toInt = 1 :=
  Value.boolean_values _

theorem compareValues_one_iff {target : Target} {ty : IntType} (op : ComparisonOp)
    (left right : Value target ty) :
    (compareValues op left right).toInt = 1 ↔ op.Relates left.toInt right.toInt := by
  cases op <;> simp only [compareValues, booleanValue_one_iff, decide_eq_true_eq,
    ComparisonOp.Relates]

theorem compareValues_zero_iff {target : Target} {ty : IntType} (op : ComparisonOp)
    (left right : Value target ty) :
    (compareValues op left right).toInt = 0 ↔ ¬op.Relates left.toInt right.toInt := by
  constructor
  · intro zero related
    exact (by decide +kernel : (0 : Int) ≠ 1)
      (zero.symm.trans ((compareValues_one_iff op left right).mpr related))
  · intro unrelated
    rcases compareValues_zero_one op left right with zero | one
    · exact zero
    · exact False.elim (unrelated ((compareValues_one_iff op left right).mp one))

theorem compareValues_nonzero_iff {target : Target} {ty : IntType} (op : ComparisonOp)
    (left right : Value target ty) :
    (compareValues op left right).toInt ≠ 0 ↔ op.Relates left.toInt right.toInt := by
  constructor
  · intro nonzero
    rcases compareValues_zero_one op left right with zero | one
    · exact False.elim (nonzero zero)
    · exact (compareValues_one_iff op left right).mp one
  · intro related zero
    exact (by decide +kernel : (0 : Int) ≠ 1)
      (zero.symm.trans ((compareValues_one_iff op left right).mpr related))

/-- A source bool is determined by its result-1 observation. -/
theorem compareValues_unique {target : Target} {ty : IntType} (op : ComparisonOp)
    (left right : Value target ty) (result : Value target (.small .boolean))
    (correct : result.toInt = 1 ↔ op.Relates left.toInt right.toInt) :
    result = compareValues op left right := by
  apply Value.toInt_injective
  rcases Value.boolean_values result with zero | one
  · have unrelated : ¬op.Relates left.toInt right.toInt := by
      intro related
      exact (by decide +kernel : (0 : Int) ≠ 1) (zero.symm.trans (correct.mpr related))
    exact zero.trans ((compareValues_zero_iff op left right).mpr unrelated).symm
  · exact one.trans ((compareValues_one_iff op left right).mpr (correct.mp one)).symm

/-- Equality comparisons also determine equality of the typed values. -/
theorem compareValues_eq_one_iff {target : Target} {ty : IntType}
    (left right : Value target ty) :
    (compareValues .eq left right).toInt = 1 ↔ left = right := by
  rw [compareValues_one_iff]
  change left.toInt = right.toInt ↔ left = right
  exact ⟨fun same => Value.toInt_injective same, congrArg Value.toInt⟩

theorem compareValues_ne_one_iff {target : Target} {ty : IntType}
    (left right : Value target ty) :
    (compareValues .ne left right).toInt = 1 ↔ left ≠ right := by
  rw [compareValues_one_iff]
  change left.toInt ≠ right.toInt ↔ left ≠ right
  constructor
  · intro different same
    exact different (congrArg Value.toInt same)
  · intro different same
    exact different (Value.toInt_injective same)

/-- C lifts a bool to int by exactly the existing integer promotion operation;
C++ keeps the bool itself. -/
def Dialect.logicalValue {target : Target} (dialect : Dialect)
    (flag : Value target (.small .boolean)) : Value target dialect.logicalType :=
  match dialect with
  | .gnuC23 => IntegerPromotions.promoteValue flag
  | .gnuCpp26 => flag

theorem Dialect.logicalValue_toInt {target : Target} (dialect : Dialect)
    (flag : Value target (.small .boolean)) :
    (dialect.logicalValue flag).toInt = flag.toInt := by
  cases dialect with
  | gnuC23 => exact IntegerPromotions.promoteValue_toInt flag
  | gnuCpp26 => rfl

theorem Dialect.logicalValue_zero_one {target : Target} (dialect : Dialect)
    (flag : Value target (.small .boolean)) :
    (dialect.logicalValue flag).toInt = 0 ∨ (dialect.logicalValue flag).toInt = 1 := by
  rw [logicalValue_toInt]
  exact Value.boolean_values flag

theorem Dialect.logicalValue_compare_one_iff {target : Target} {ty : IntType}
    (dialect : Dialect) (op : ComparisonOp) (left right : Value target ty) :
    (dialect.logicalValue (compareValues op left right)).toInt = 1 ↔
      op.Relates left.toInt right.toInt := by
  rw [logicalValue_toInt, compareValues_one_iff]

theorem Dialect.logicalValue_compare_zero_iff {target : Target} {ty : IntType}
    (dialect : Dialect) (op : ComparisonOp) (left right : Value target ty) :
    (dialect.logicalValue (compareValues op left right)).toInt = 0 ↔
      ¬op.Relates left.toInt right.toInt := by
  rw [logicalValue_toInt, compareValues_zero_iff]

theorem Dialect.logicalValue_compare_nonzero_iff {target : Target} {ty : IntType}
    (dialect : Dialect) (op : ComparisonOp) (left right : Value target ty) :
    (dialect.logicalValue (compareValues op left right)).toInt ≠ 0 ↔
      op.Relates left.toInt right.toInt := by
  rw [logicalValue_toInt, compareValues_nonzero_iff]

end EDSL.Source
