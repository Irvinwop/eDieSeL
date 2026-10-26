/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.PromotionContracts

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.SourcePromotions
open EDSL.Source

private def small (target : Target) (ty : SmallType) (n : Int)
    (fits : ty.lowerBound target ≤ n ∧ n < ty.upperBound target) :
    Expr target [] (.small ty) := .literal ⟨n, fits⟩

/-- Boolean arithmetic occurs in int, not in the two-value input range. -/
example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.usualAdd (small Target.int32 .boolean 1 (by decide +kernel))
        (small Target.int32 .boolean 1 (by decide +kernel))⟩ .nil =
      .defined ⟨2, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- These operands promote to signed int; adding in ushort first would wrap. -/
example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.usualAdd (small Target.int32 .ushort 65535 (by decide +kernel))
        (small Target.int32 .ushort 65535 (by decide +kernel))⟩ .nil =
      .defined ⟨131070, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Equal short/int widths require unsigned-int promotion and wrapping. -/
example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.usualAdd (small Target.int16 .ushort 65535 (by decide +kernel))
        (small Target.int16 .ushort 65535 (by decide +kernel))⟩ .nil =
      .defined ⟨65534, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Promotion depends on the whole source type, not this small operand's value. -/
example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.usualAdd (small Target.int16 .ushort 1 (by decide +kernel))
        (.literal (ty := .sint) ⟨-2, by decide +kernel⟩)⟩ .nil =
      .defined ⟨65535, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- An abstract value-range profile with equal char/short/int widths.
This asserts no native ABI or object representation correspondence. -/
private def signedChar16 : Target where
  intBits := 16
  atLeast16 := by decide +kernel
  charBits := 16
  charAtLeast8 := by decide +kernel
  shortBits := 16
  shortAtLeast16 := by decide +kernel
  charLeShort := by decide +kernel
  shortLeInt := by decide +kernel
  plainCharSigned := true

private def unsignedChar16 : Target := { signedChar16 with plainCharSigned := false }

/-- Rank remains below int even at equal width: signed char promotes to int,
and adding one at its maximum causes actual signed-int overflow. -/
example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.usualAdd (small signedChar16 .plainChar 32767 (by decide +kernel))
        (.literal (ty := .sint) ⟨1, by decide +kernel⟩)⟩ .nil =
      .undefined .signedAdditionOverflow := by
  simp only [eval]
  decide +kernel

/-- The unsigned plain-char policy changes promotion and the common arithmetic
operation; it is not silently treated as the signed-char case. -/
example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.usualAdd (small unsignedChar16 .plainChar 65535 (by decide +kernel))
        (.literal (ty := .sint) ⟨1, by decide +kernel⟩)⟩ .nil =
      .defined ⟨0, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Promotion does not hide unsupported operand evaluation. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      Expr.promote (.unsupported (ty := .small .ushort) .memoryAccess)⟩ :
      Program Target.int32 [] .sint) .nil = .unsupported .memoryAccess := rfl

/-- A small cast composes with promotion through the shared evaluator. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      Expr.promote (.convert (.small .ushort)
        (.literal (ty := .sint) ⟨1, by decide +kernel⟩))⟩ :
      Program Target.int32 [] .sint) .nil = .defined ⟨1, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Identity promotion of a full int cannot repair UB in its operand. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      Expr.promote (.sadd (.literal ⟨2147483647, by decide +kernel⟩)
        (.literal ⟨1, by decide +kernel⟩))⟩ :
      Program Target.int32 [] .sint) .nil = .undefined .signedAdditionOverflow := by
  simp only [eval]
  decide +kernel

/-- An admitted numeric profile between the two common fixture widths. -/
private def int17 : Target :=
  { Target.int16 with
    intBits := 17
    atLeast16 := by decide +kernel
    shortLeInt := by decide +kernel }

/-- Representable promoted operands do not imply representable arithmetic:
unsigned short promotes to int here, whose maximum is exactly 65535. -/
example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.usualAdd (small int17 .ushort 65535 (by decide +kernel))
        (small int17 .ushort 1 (by decide +kernel))⟩ .nil =
      .undefined .signedAdditionOverflow := by
  simp only [eval]
  decide +kernel

/-- Division overflow is checked in the promoted type, not at short width. -/
example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.usualDiv (small Target.int32 .sshort (-32768) (by decide +kernel))
        (small Target.int32 .sshort (-1) (by decide +kernel))⟩ .nil =
      .defined ⟨32768, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.usualDiv (small Target.int16 .sshort (-32768) (by decide +kernel))
        (small Target.int16 .sshort (-1) (by decide +kernel))⟩ .nil =
      .undefined .signedDivisionOverflow := by
  simp only [eval]
  decide +kernel

end EDSL.Tests.SourcePromotions
