/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.ArithmeticConversions

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.SourceArithmetic
open EDSL.Source

/-- Unsigned subtraction wraps rather than saturating. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .usub (.literal (ty := .uint) ⟨0, by decide +kernel⟩) (.literal (ty := .uint) ⟨1, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .uint) .nil = .defined ⟨4294967295, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Signed subtraction preserves a negative result. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .ssub (.literal (ty := .sint) ⟨0, by decide +kernel⟩) (.literal (ty := .sint) ⟨1, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .sint) .nil = .defined ⟨-1, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Subtracting one at the signed minimum is UB. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .ssub (.literal (ty := .sint) ⟨(-2147483648), by decide +kernel⟩) (.literal (ty := .sint) ⟨1, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .sint) .nil = .undefined .signedSubtractionOverflow := by
  simp only [eval]
  decide +kernel

/-- Unsigned multiplication may require more than one wrap. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .umul (.literal (ty := .uint) ⟨4294967295, by decide +kernel⟩) (.literal (ty := .uint) ⟨4294967295, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .uint) .nil = .defined ⟨1, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Signed multiplication retains the mathematical sign. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .smul (.literal (ty := .sint) ⟨(-2), by decide +kernel⟩) (.literal (ty := .sint) ⟨3, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .sint) .nil = .defined ⟨-6, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- The signed minimum times minus one is unrepresentable. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .smul (.literal (ty := .sint) ⟨(-2147483648), by decide +kernel⟩) (.literal (ty := .sint) ⟨(-1), by decide +kernel⟩)⟩ :
      Program Target.int32 [] .sint) .nil = .undefined .signedMultiplicationOverflow := by
  simp only [eval]
  decide +kernel

/-- Unsigned-short operands promote to signed int before multiplying. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, Expr.usualMul (.literal (ty := .small .ushort) ⟨65535, by decide +kernel⟩) (.literal (ty := .small .ushort) ⟨65535, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .sint) .nil = .undefined .signedMultiplicationOverflow := by
  simp only [eval]
  decide +kernel

/-- Equal short and int widths select unsigned multiplication. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, Expr.usualMul (.literal (ty := .small .ushort) ⟨65535, by decide +kernel⟩) (.literal (ty := .small .ushort) ⟨65535, by decide +kernel⟩)⟩ :
      Program Target.int16 [] .uint) .nil = .defined ⟨1, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Unsigned remainder retains the ordinary nonnegative divisor bound. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .urem (.literal (ty := .uint) ⟨4294967295, by decide +kernel⟩) (.literal (ty := .uint) ⟨3, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .uint) .nil = .defined ⟨0, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Remainder by zero is UB, despite total host arithmetic. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .urem (.literal (ty := .uint) ⟨7, by decide +kernel⟩) (.literal (ty := .uint) ⟨0, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .uint) .nil = .undefined .divisionByZero := by
  simp only [eval]
  decide +kernel

/-- Signed remainder follows the dividend sign, rather than Euclidean modulo. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .srem (.literal (ty := .sint) ⟨(-7), by decide +kernel⟩) (.literal (ty := .sint) ⟨3, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .sint) .nil = .defined ⟨-1, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- A negative divisor does not negate the positive dividend remainder. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .srem (.literal (ty := .sint) ⟨7, by decide +kernel⟩) (.literal (ty := .sint) ⟨(-3), by decide +kernel⟩)⟩ :
      Program Target.int32 [] .sint) .nil = .defined ⟨1, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- An unrepresentable quotient makes signed remainder UB even if it is zero. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .srem (.literal (ty := .sint) ⟨(-2147483648), by decide +kernel⟩) (.literal (ty := .sint) ⟨(-1), by decide +kernel⟩)⟩ :
      Program Target.int32 [] .sint) .nil = .undefined .signedRemainderOverflow := by
  simp only [eval]
  decide +kernel

/-- Zero is rejected before considering quotient representability. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .srem (.literal (ty := .sint) ⟨(-2147483648), by decide +kernel⟩) (.literal (ty := .sint) ⟨0, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .sint) .nil = .undefined .divisionByZero := by
  simp only [eval]
  decide +kernel

/-- Promotion moves the signed-short boundary into a representable int quotient. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, Expr.usualRem (.literal (ty := .small .sshort) ⟨(-32768), by decide +kernel⟩) (.literal (ty := .small .sshort) ⟨(-1), by decide +kernel⟩)⟩ :
      Program Target.int32 [] .sint) .nil = .defined ⟨0, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- At equal short and int widths the same quotient overflows. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, Expr.usualRem (.literal (ty := .small .sshort) ⟨(-32768), by decide +kernel⟩) (.literal (ty := .small .sshort) ⟨(-1), by decide +kernel⟩)⟩ :
      Program Target.int16 [] .sint) .nil = .undefined .signedRemainderOverflow := by
  simp only [eval]
  decide +kernel

/-- An outer unsigned cast cannot repair signed multiplication overflow. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .convert .uint (.smul (.literal (ty := .sint) ⟨2147483647, by decide +kernel⟩) (.literal (ty := .sint) ⟨2, by decide +kernel⟩))⟩ :
      Program Target.int32 [] .uint) .nil = .undefined .signedMultiplicationOverflow := by
  simp only [eval]
  decide +kernel

/-- Boolean subtraction is performed in int, not in the boolean input range. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, Expr.usualSub (.literal (ty := .small .boolean) ⟨0, by decide +kernel⟩) (.literal (ty := .small .boolean) ⟨1, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .sint) .nil = .defined ⟨-1, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- New arithmetic support retains unsupported operand failures. -/
example (dialect : Dialect) (target : Target) :
    eval (⟨dialect, .gnuModulo,
      .umul (.literal ⟨0, target.modulus_pos⟩) (.unsupported .memoryAccess)⟩ :
      Program target [] .uint) .nil = .unsupported .memoryAccess := rfl


/-- Subtracting the signed minimum from itself must not negate it in source int. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .ssub (.literal (ty := .sint) ⟨(-2147483648), by decide +kernel⟩) (.literal (ty := .sint) ⟨(-2147483648), by decide +kernel⟩)⟩ :
      Program Target.int32 [] .sint) .nil = .defined ⟨0, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- An unsigned remainder can be nonzero. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, .urem (.literal (ty := .uint) ⟨7, by decide +kernel⟩) (.literal (ty := .uint) ⟨3, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .uint) .nil = .defined ⟨1, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Mixed subtraction converts the negative operand before subtraction. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, Expr.usualSub (.literal (ty := .uint) ⟨0, by decide +kernel⟩) (.literal (ty := .sint) ⟨(-1), by decide +kernel⟩)⟩ :
      Program Target.int32 [] .uint) .nil = .defined ⟨1, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Mixed multiplication selects unsigned arithmetic before checking the result. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, Expr.usualMul (.literal (ty := .sint) ⟨2147483647, by decide +kernel⟩) (.literal (ty := .uint) ⟨2, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .uint) .nil = .defined ⟨4294967294, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Mixed remainder converts a negative dividend before dividing. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo, Expr.usualRem (.literal (ty := .sint) ⟨(-7), by decide +kernel⟩) (.literal (ty := .uint) ⟨3, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .uint) .nil = .defined ⟨0, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

end EDSL.Tests.SourceArithmetic
