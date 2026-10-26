/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Eval

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.SourceCasts
open EDSL.Source

/-- Bool conversion tests truth, rather than keeping the low bit. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      .convert (.small .boolean) (.literal (ty := .uint) ⟨2, by decide +kernel⟩)⟩ :
      Program Target.int32 [] (.small .boolean)) .nil =
      .defined ⟨1, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- A negative even integer is nonzero, despite having a zero low bit. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      .convert (.small .boolean) (.literal (ty := .sint) ⟨-256, by decide +kernel⟩)⟩ :
      Program Target.int32 [] (.small .boolean)) .nil =
      .defined ⟨1, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      .convert (.small .boolean) (.literal (ty := .sint) ⟨0, by decide +kernel⟩)⟩ :
      Program Target.int32 [] (.small .boolean)) .nil =
      .defined ⟨0, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Cross-width unsigned conversion wraps at the destination width. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      .convert (.small .uchar) (.literal (ty := .uint) ⟨300, by decide +kernel⟩)⟩ :
      Program Target.int32 [] (.small .uchar)) .nil =
      .defined ⟨44, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- The signed upper boundary maps to the minimum under the selected GNU policy. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      .convert (.small .schar) (.literal (ty := .sint) ⟨128, by decide +kernel⟩)⟩ :
      Program Target.int32 [] (.small .schar)) .nil =
      .defined ⟨-128, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Unsigned narrowing of a negative value is a residue, not a clamp at zero. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      .convert (.small .uchar) (.literal (ty := .sint) ⟨-1, by decide +kernel⟩)⟩ :
      Program Target.int32 [] (.small .uchar)) .nil =
      .defined ⟨255, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

private def unsignedPlainChar : Target := { Target.int32 with plainCharSigned := false }

/-- Plain char has its own explicit signedness profile. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      .convert (.small .plainChar) (.literal (ty := .uint) ⟨255, by decide +kernel⟩)⟩ :
      Program Target.int32 [] (.small .plainChar)) .nil =
      .defined ⟨-1, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      .convert (.small .plainChar) (.literal (ty := .uint) ⟨255, by decide +kernel⟩)⟩ :
      Program unsignedPlainChar [] (.small .plainChar)) .nil =
      .defined ⟨255, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Widening a signed small value preserves its mathematical sign. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      .convert .sint (.literal (ty := .small .schar) ⟨-128, by decide +kernel⟩)⟩ :
      Program Target.int32 [] .sint) .nil =
      .defined ⟨-128, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Narrowing loses information: widening afterward cannot restore the input. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      .convert .uint (.convert (.small .uchar)
        (.literal (ty := .uint) ⟨300, by decide +kernel⟩))⟩ :
      Program Target.int32 [] .uint) .nil =
      .defined ⟨44, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- A well-defined cast cannot repair signed overflow in its operand. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      .convert (.small .uchar)
        (.sadd (.literal ⟨2147483647, by decide +kernel⟩)
          (.literal ⟨1, by decide +kernel⟩))⟩ :
      Program Target.int32 [] (.small .uchar)) .nil =
      .undefined .signedAdditionOverflow := by
  simp only [eval]
  decide +kernel

/-- Cast support does not introduce support for an unimplemented operand. -/
example (dialect : Dialect) (target : Target) (source destination : IntType) :
    eval (⟨dialect, .gnuModulo,
      .convert destination (.unsupported (ty := source) .memoryAccess)⟩ :
      Program target [] destination) .nil = .unsupported .memoryAccess := rfl

/-- An admitted nonstandard range profile: int17/short17/char9. -/
private def char9 : Target where
  intBits := 17
  atLeast16 := by decide +kernel
  charBits := 9
  charAtLeast8 := by decide +kernel
  shortBits := 17
  shortAtLeast16 := by decide +kernel
  charLeShort := by decide +kernel
  shortLeInt := by decide +kernel
  plainCharSigned := true

/-- Casts use profile bounds rather than assuming eight-bit characters. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      .convert (.small .schar) (.literal (ty := .sint) ⟨256, by decide +kernel⟩)⟩ :
      Program char9 [] (.small .schar)) .nil =
      .defined ⟨-256, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- A requested cast is distinct from value-preserving promotion. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      .convert .sint (.literal (ty := .small .ushort) ⟨65535, by decide +kernel⟩)⟩ :
      Program Target.int16 [] .sint) .nil =
      .defined ⟨-1, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- An intermediate narrowing can change the truth value seen by a later cast. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      .convert (.small .boolean) (.convert (.small .uchar)
        (.literal (ty := .sint) ⟨256, by decide +kernel⟩))⟩ :
      Program Target.int32 [] (.small .boolean)) .nil =
      .defined ⟨0, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

end EDSL.Tests.SourceCasts
