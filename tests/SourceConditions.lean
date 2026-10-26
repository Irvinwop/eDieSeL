/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Conditions

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.SourceConditions
open EDSL.Source

/-- Project the result value while retaining the actual execution failures. -/
private def observe {target : Target} {ty : IntType} :
    Outcome (Value target ty) → Outcome Int
  | .defined value => .defined value.toInt
  | .undefined reason => .undefined reason
  | .unsupported feature => .unsupported feature

/-- Mixed signed/unsigned comparison uses the converted unsigned value. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.sourceCompare dialect .lt (.literal (ty := .sint) ⟨(-1), by decide +kernel⟩) (.literal (ty := .uint) ⟨1, by decide +kernel⟩)⟩ :
      Program Target.int32 [] dialect.logicalType) .nil) = .defined 0 := by
  cases dialect <;> decide +kernel

/-- Equality sees the same common-type representation at unsigned maximum. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.sourceCompare dialect .eq (.literal (ty := .sint) ⟨(-1), by decide +kernel⟩) (.literal (ty := .uint) ⟨4294967295, by decide +kernel⟩)⟩ :
      Program Target.int32 [] dialect.logicalType) .nil) = .defined 1 := by
  cases dialect <;> decide +kernel

/-- Inequality of equal zero operands is false. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.sourceCompare dialect .ne (.literal (ty := .uint) ⟨0, by decide +kernel⟩) (.literal (ty := .uint) ⟨0, by decide +kernel⟩)⟩ :
      Program Target.int32 [] dialect.logicalType) .nil) = .defined 0 := by
  cases dialect <;> decide +kernel

/-- Non-strict signed order includes the maximum endpoint. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.sourceCompare dialect .le (.literal (ty := .sint) ⟨2147483647, by decide +kernel⟩) (.literal (ty := .sint) ⟨2147483647, by decide +kernel⟩)⟩ :
      Program Target.int32 [] dialect.logicalType) .nil) = .defined 1 := by
  cases dialect <;> decide +kernel

/-- Greater-than must not compare by overflowing signed subtraction. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.sourceCompare dialect .gt (.literal (ty := .sint) ⟨(-2147483648), by decide +kernel⟩) (.literal (ty := .sint) ⟨2147483647, by decide +kernel⟩)⟩ :
      Program Target.int32 [] dialect.logicalType) .nil) = .defined 0 := by
  cases dialect <;> decide +kernel

/-- Greater-or-equal includes the minimum endpoint. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.sourceCompare dialect .ge (.literal (ty := .sint) ⟨(-2147483648), by decide +kernel⟩) (.literal (ty := .sint) ⟨(-2147483648), by decide +kernel⟩)⟩ :
      Program Target.int32 [] dialect.logicalType) .nil) = .defined 1 := by
  cases dialect <;> decide +kernel

/-- Unsigned short fits int32 before common-type comparison. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.sourceCompare dialect .eq (.literal (ty := .small .ushort) ⟨65535, by decide +kernel⟩) (.literal (ty := .sint) ⟨(-1), by decide +kernel⟩)⟩ :
      Program Target.int32 [] dialect.logicalType) .nil) = .defined 0 := by
  cases dialect <;> decide +kernel

/-- At equal short/int widths the comparison selects unsigned int. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.sourceCompare dialect .eq (.literal (ty := .small .ushort) ⟨65535, by decide +kernel⟩) (.literal (ty := .sint) ⟨(-1), by decide +kernel⟩)⟩ :
      Program Target.int16 [] dialect.logicalType) .nil) = .defined 1 := by
  cases dialect <;> decide +kernel

/-- Comparison is eager even when the left operand is false as a truth value. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo,
      Expr.sourceCompare dialect .lt
        (.literal (ty := .uint) ⟨0, by decide +kernel⟩)
        (.udiv (.literal (ty := .uint) ⟨1, by decide +kernel⟩)
          (.literal (ty := .uint) ⟨0, by decide +kernel⟩))⟩ :
      Program Target.int32 [] dialect.logicalType) .nil) = .undefined .divisionByZero := by
  cases dialect <;> decide +kernel

/-- An unsigned comparison against zero must still execute its failing left operand. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo,
      Expr.sourceCompare dialect .lt
        (.udiv (.literal (ty := .uint) ⟨1, by decide +kernel⟩)
          (.literal (ty := .uint) ⟨0, by decide +kernel⟩))
        (.literal (ty := .uint) ⟨0, by decide +kernel⟩)⟩ :
      Program Target.int32 [] dialect.logicalType) .nil) = .undefined .divisionByZero := by
  cases dialect <;> decide +kernel

/-- AND skips a fully modeled division-by-zero right operand when left is zero. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.logicalAnd dialect (.literal (ty := .uint) ⟨0, by decide +kernel⟩) (.udiv (.literal (ty := .uint) ⟨1, by decide +kernel⟩) (.literal (ty := .uint) ⟨0, by decide +kernel⟩))⟩ :
      Program Target.int32 [] dialect.logicalType) .nil) = .defined 0 := by
  cases dialect <;> decide +kernel

/-- OR treats an even negative value as true and skips division by zero. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.logicalOr dialect (.literal (ty := .sint) ⟨(-2), by decide +kernel⟩) (.sdiv (.literal (ty := .sint) ⟨1, by decide +kernel⟩) (.literal (ty := .sint) ⟨0, by decide +kernel⟩))⟩ :
      Program Target.int32 [] dialect.logicalType) .nil) = .defined 1 := by
  cases dialect <;> decide +kernel

/-- AND evaluates a selected failing right operand. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.logicalAnd dialect (.literal (ty := .uint) ⟨2, by decide +kernel⟩) (.udiv (.literal (ty := .uint) ⟨1, by decide +kernel⟩) (.literal (ty := .uint) ⟨0, by decide +kernel⟩))⟩ :
      Program Target.int32 [] dialect.logicalType) .nil) = .undefined .divisionByZero := by
  cases dialect <;> decide +kernel

/-- OR evaluates its right operand after false. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.logicalOr dialect (.literal (ty := .uint) ⟨0, by decide +kernel⟩) (.udiv (.literal (ty := .uint) ⟨1, by decide +kernel⟩) (.literal (ty := .uint) ⟨0, by decide +kernel⟩))⟩ :
      Program Target.int32 [] dialect.logicalType) .nil) = .undefined .divisionByZero := by
  cases dialect <;> decide +kernel

/-- A failure in the condition is not repaired by identical safe arms. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, .select (Expr.truth (.udiv (.literal (ty := .uint) ⟨1, by decide +kernel⟩) (.literal (ty := .uint) ⟨0, by decide +kernel⟩))) (.literal (ty := .uint) ⟨7, by decide +kernel⟩) (.literal (ty := .uint) ⟨7, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .uint) .nil) = .undefined .divisionByZero := by
  cases dialect <;> decide +kernel

/-- A source conditional skips the unselected modeled-UB arm. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.conditional (target := Target.int32) dialect (.literal (ty := .sint) ⟨2, by decide +kernel⟩) (.literal (ty := .sint) ⟨42, by decide +kernel⟩) (.sdiv (.literal (ty := .sint) ⟨1, by decide +kernel⟩) (.literal (ty := .sint) ⟨0, by decide +kernel⟩))⟩ :
      Program Target.int32 [] (conditionalType Target.int32 dialect .sint .sint)) .nil) = .defined 42 := by
  cases dialect <;> decide +kernel

/-- Reversing selection executes the modeled-UB arm. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.conditional (target := Target.int32) dialect (.literal (ty := .sint) ⟨0, by decide +kernel⟩) (.literal (ty := .sint) ⟨42, by decide +kernel⟩) (.sdiv (.literal (ty := .sint) ⟨1, by decide +kernel⟩) (.literal (ty := .sint) ⟨0, by decide +kernel⟩))⟩ :
      Program Target.int32 [] (conditionalType Target.int32 dialect .sint .sint)) .nil) = .undefined .divisionByZero := by
  cases dialect <;> decide +kernel

/-- Both conditional arm types determine the unsigned result before selection. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.conditional (target := Target.int32) dialect (.literal (ty := .small .boolean) ⟨1, by decide +kernel⟩) (.literal (ty := .sint) ⟨(-1), by decide +kernel⟩) (.literal (ty := .uint) ⟨0, by decide +kernel⟩)⟩ :
      Program Target.int32 [] (conditionalType Target.int32 dialect .sint .uint)) .nil) = .defined 4294967295 := by
  cases dialect <;> decide +kernel

/-- Program coverage rejects an unsupported right arm even when AND would skip it. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, Expr.logicalAnd dialect (.literal (ty := .uint) ⟨0, by decide +kernel⟩) (.unsupported (ty := .uint) .memoryAccess)⟩ :
      Program Target.int32 [] dialect.logicalType) .nil) = .unsupported .memoryAccess := by
  cases dialect <;> decide +kernel

/-- Coverage validation precedes execution diagnostics for incomplete programs. -/
example (dialect : Dialect) :
    observe (eval (⟨dialect, .gnuModulo, .uadd (.udiv (.literal (ty := .uint) ⟨1, by decide +kernel⟩) (.literal (ty := .uint) ⟨0, by decide +kernel⟩)) (.unsupported .memoryAccess)⟩ :
      Program Target.int32 [] .uint) .nil) = .unsupported .memoryAccess := by
  cases dialect <;> decide +kernel

/-- Prvalue uchar arms undergo C's arithmetic conversion. -/
example :
    eval (⟨.gnuC23, .gnuModulo,
      Expr.conditional (target := Target.int32) .gnuC23 (.literal (ty := .sint) ⟨1, by decide +kernel⟩)
        (.literal (ty := .small .uchar) ⟨255, by decide +kernel⟩) (.literal (ty := .small .uchar) ⟨127, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .sint) .nil = .defined ⟨255, by decide +kernel⟩ := by
  decide +kernel

/-- C++ preserves matching uchar prvalue arm types. -/
example :
    eval (⟨.gnuCpp26, .gnuModulo,
      Expr.conditional (target := Target.int32) .gnuCpp26 (.literal (ty := .sint) ⟨1, by decide +kernel⟩)
        (.literal (ty := .small .uchar) ⟨255, by decide +kernel⟩) (.literal (ty := .small .uchar) ⟨127, by decide +kernel⟩)⟩ :
      Program Target.int32 [] (.small .uchar)) .nil = .defined ⟨255, by decide +kernel⟩ := by
  decide +kernel

/-- Logical C results are int, including a sum outside the bool range. -/
example :
    eval (⟨.gnuC23, .gnuModulo,
      .sadd (Expr.sourceCompare .gnuC23 .eq (.literal (ty := .uint) ⟨1, by decide +kernel⟩) (.literal (ty := .uint) ⟨1, by decide +kernel⟩))
        (Expr.sourceCompare .gnuC23 .lt (.literal (ty := .uint) ⟨1, by decide +kernel⟩) (.literal (ty := .uint) ⟨2, by decide +kernel⟩))⟩ :
      Program Target.int32 [] .sint) .nil = .defined ⟨2, by decide +kernel⟩ := by
  decide +kernel

/-- A C++ comparison has bool type before an explicit promotion. -/
example :
    eval (⟨.gnuCpp26, .gnuModulo,
      Expr.sourceCompare .gnuCpp26 .lt (.literal (ty := .sint) ⟨(-1), by decide +kernel⟩) (.literal (ty := .sint) ⟨0, by decide +kernel⟩)⟩ :
      Program Target.int32 [] (.small .boolean)) .nil = .defined ⟨1, by decide +kernel⟩ := by
  decide +kernel

private def skippedUnknown : Program Target.int32 [] .uint :=
  ⟨.gnuC23, .gnuModulo, .select (.literal (ty := .small .boolean) ⟨0, by decide +kernel⟩) (.unsupported .memoryAccess) (.literal (ty := .uint) ⟨7, by decide +kernel⟩)⟩

/-- Raw execution chooses one arm; structural coverage is a separate phase. -/
example : evalExpr .gnuModulo (.nil : Inputs Target.int32 []) skippedUnknown.body =
    .defined ⟨7, by decide +kernel⟩ := by
  decide +kernel

example : vcExpr .gnuModulo (.nil : Inputs Target.int32 []) skippedUnknown.body
    (fun value => value.val = 7) := by
  change (7 : Nat) = 7
  rfl

/-- The public program evaluator enforces coverage of the complete body. -/
example : eval skippedUnknown .nil = .unsupported .memoryAccess := rfl

/-- Raw branch success cannot be packaged as a public supported certificate. -/
example (post : Inputs Target.int32 [] → Value Target.int32 .uint → Prop) :
    ¬ Certificate skippedUnknown (fun _ => True) post :=
  no_certificate_with_unsupported skippedUnknown (fun _ => True) post .memoryAccess rfl

end EDSL.Tests.SourceConditions
