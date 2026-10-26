/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Unary

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.SourceUnary
open EDSL.Source

/-- Observe public program evaluation without hiding coverage or UB outcomes. -/
private def observe {target : Target} {ty : IntType} :
    Outcome (Value target ty) → Outcome Int
  | .defined value => .defined value.toInt
  | .undefined reason => .undefined reason
  | .unsupported feature => .unsupported feature

private def run {target : Target} {ty : IntType}
    (dialect : Dialect) (body : Expr target [] ty) : Outcome Int :=
  observe (eval ⟨dialect, .gnuModulo, body⟩ .nil)

private def true32 : Expr Target.int32 [] (.small .boolean) :=
  Expr.literal ⟨1, by decide +kernel⟩
private def false32 : Expr Target.int32 [] (.small .boolean) :=
  Expr.literal ⟨0, by decide +kernel⟩
private def min32 : Expr Target.int32 [] .sint :=
  Expr.literal ⟨-2147483648, by decide +kernel⟩
private def max32 : Expr Target.int32 [] .sint :=
  Expr.literal ⟨2147483647, by decide +kernel⟩
private def umax32 : Expr Target.int32 [] .uint :=
  Expr.literal ⟨4294967295, by decide +kernel⟩
private def ucharMax32 : Expr Target.int32 [] (.small .uchar) :=
  Expr.literal ⟨255, by decide +kernel⟩

/-- Unary plus promotes bool to int, and is not a bool-typed identity. -/
example (dialect : Dialect) :
    run (ty := .sint) dialect (Expr.unary dialect .plus true32) = .defined 1 := by
  cases dialect <;> decide +kernel

/-- Negating true happens after promotion, so the result is signed minus one. -/
example (dialect : Dialect) :
    run (ty := .sint) dialect true32.unaryMinus = .defined (-1) := by
  cases dialect <;> decide +kernel

/-- Complementing true flips the promoted int bits rather than bool's range. -/
example (dialect : Dialect) :
    run (ty := .sint) dialect (Expr.unary dialect .complement true32) = .defined (-2) := by
  cases dialect <;> decide +kernel

/-- Logical negation returns one exactly for zero, in the dialect's result type. -/
example (dialect : Dialect) :
    run (target := Target.int32) (ty := dialect.logicalType) dialect
      ((Expr.literal (ty := .sint) ⟨0, by decide +kernel⟩).logicalNot dialect) = .defined 1 := by
  cases dialect <;> decide +kernel

/-- A nonzero even integer is true, not false by reduction modulo two. -/
example (dialect : Dialect) :
    run (target := Target.int32) (ty := dialect.logicalType) dialect
      ((Expr.literal (ty := .sint) ⟨2, by decide +kernel⟩).logicalNot dialect) = .defined 0 := by
  cases dialect <;> decide +kernel

/-- Negative nonzero integers are true as well. -/
example (dialect : Dialect) :
    run (target := Target.int32) (ty := dialect.logicalType) dialect
      ((Expr.literal (ty := .sint) ⟨-2, by decide +kernel⟩).logicalNot dialect) = .defined 0 := by
  cases dialect <;> decide +kernel

/-- Double negation normalizes truth even when C and C++ use different types. -/
example (dialect : Dialect) :
    run (target := Target.int32) (ty := dialect.logicalType) dialect
      (((Expr.literal (ty := .sint) ⟨-2, by decide +kernel⟩).logicalNot dialect).logicalNot dialect) =
        .defined 1 := by
  cases dialect <;> decide +kernel

/-- Unsigned negation wraps at both nonzero endpoints, while zero stays zero. -/
example (dialect : Dialect) :
    run (target := Target.int32) (ty := .uint) dialect
      (.unaryMinus (Expr.literal (ty := .uint) ⟨0, by decide +kernel⟩)) = .defined 0 ∧
    run (target := Target.int32) (ty := .uint) dialect
      (.unaryMinus (Expr.literal (ty := .uint) ⟨1, by decide +kernel⟩)) = .defined 4294967295 ∧
    run dialect umax32.unaryMinus = .defined 1 := by
  cases dialect <;> decide +kernel

/-- The unrepresentable signed negation remains UB, not unsigned wrapping. -/
example (dialect : Dialect) :
    run dialect min32.unaryMinus = .undefined .signedSubtractionOverflow := by
  cases dialect <;> decide +kernel

/-- The value adjacent to signed minimum can be negated to signed maximum. -/
example (dialect : Dialect) :
    run (target := Target.int32) dialect
      (.unaryMinus (Expr.literal (ty := .sint) ⟨-2147483647, by decide +kernel⟩)) =
        .defined 2147483647 := by
  cases dialect <;> decide +kernel

/-- The positive maximum also has a representable negative. -/
example (dialect : Dialect) :
    run dialect max32.unaryMinus = .defined (-2147483647) := by
  cases dialect <;> decide +kernel

/-- Signed complement is defined at MIN; negating MIN first would fail. -/
example (dialect : Dialect) :
    run dialect min32.unaryComplement = .defined 2147483647 := by
  cases dialect <;> decide +kernel

/-- Signed complement is defined at MAX; adding one before negation would fail. -/
example (dialect : Dialect) :
    run dialect max32.unaryComplement = .defined (-2147483648) := by
  cases dialect <;> decide +kernel

/-- Byte operands operate at int width after promotion, without byte wrapping. -/
example (dialect : Dialect) :
    run (ty := .sint) dialect ucharMax32.unaryPlus = .defined 255 ∧
    run (ty := .sint) dialect ucharMax32.unaryMinus = .defined (-255) ∧
    run (ty := .sint) dialect ucharMax32.unaryComplement = .defined (-256) := by
  cases dialect <;> decide +kernel

/-- Unsigned short fits int32, so both unary results are signed. -/
example (dialect : Dialect) :
    run (target := Target.int32) (ty := .sint) dialect
      (.unaryMinus (Expr.literal (ty := .small .ushort) ⟨65535, by decide +kernel⟩)) = .defined (-65535) ∧
    run (target := Target.int32) (ty := .sint) dialect
      (.unaryComplement (Expr.literal (ty := .small .ushort) ⟨65535, by decide +kernel⟩)) =
        .defined (-65536) := by
  cases dialect <;> decide +kernel

/-- Equal short/int widths select unsigned int promotion and modular negation. -/
example (dialect : Dialect) :
    run (target := Target.int16) (ty := .uint) dialect
      (.unaryMinus (Expr.literal (ty := .small .ushort) ⟨65535, by decide +kernel⟩)) = .defined 1 ∧
    run (target := Target.int16) (ty := .uint) dialect
      (.unaryComplement (Expr.literal (ty := .small .ushort) ⟨65535, by decide +kernel⟩)) = .defined 0 := by
  cases dialect <;> decide +kernel

/-- Unsigned complement reverses both endpoints in the full promoted range. -/
example (dialect : Dialect) :
    run (target := Target.int32) (ty := .uint) dialect
      (.unaryComplement (Expr.literal (ty := .uint) ⟨0, by decide +kernel⟩)) = .defined 4294967295 ∧
    run dialect umax32.unaryComplement = .defined 0 := by
  cases dialect <;> decide +kernel

/-- Every unary operator evaluates its operand and propagates its division UB. -/
example (dialect : Dialect) (operation : UnaryOp) :
    run (target := Target.int32) dialect
      (Expr.unary dialect operation
        (.udiv (Expr.literal (ty := .uint) ⟨1, by decide +kernel⟩)
          (Expr.literal (ty := .uint) ⟨0, by decide +kernel⟩))) = .undefined .divisionByZero := by
  cases dialect <;> cases operation <;> decide +kernel

/-- Public coverage rejects a marker under every unary helper before execution. -/
example (dialect : Dialect) (operation : UnaryOp) :
    run (target := Target.int32) dialect
      (Expr.unary dialect operation (.unsupported (ty := .sint) .memoryAccess)) =
        .unsupported .memoryAccess := by
  cases dialect <;> cases operation <;> decide +kernel

/-- A lazy conditional may safely skip a fully modeled negation-overflow arm. -/
example (dialect : Dialect) :
    run dialect (.select false32 min32.unaryMinus
      (Expr.literal (ty := .sint) ⟨7, by decide +kernel⟩)) = .defined 7 := by
  cases dialect <;> decide +kernel

/-- Selecting the same supported arm exposes its signed-negation UB. -/
example (dialect : Dialect) :
    run dialect (.select true32 min32.unaryMinus
      (Expr.literal (ty := .sint) ⟨7, by decide +kernel⟩)) = .undefined .signedSubtractionOverflow := by
  cases dialect <;> decide +kernel

/-- C's int result composes with arithmetic; C++'s bool composes as a condition. -/
example :
    run .gnuC23 (.sadd (false32.logicalNot .gnuC23) (false32.logicalNot .gnuC23)) = .defined 2 ∧
    run .gnuCpp26 (.select (true32.logicalNot .gnuCpp26)
      (Expr.literal (ty := .sint) ⟨5, by decide +kernel⟩)
      (Expr.literal (ty := .sint) ⟨7, by decide +kernel⟩)) = .defined 7 := by
  decide +kernel

end EDSL.Tests.SourceUnary
