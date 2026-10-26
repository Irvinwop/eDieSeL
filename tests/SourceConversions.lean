/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.ConversionContracts

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.SourceConversions
open EDSL.Source

private def signed (n : Int) (fits : -Target.int32.signedBound ≤ n ∧
    n < Target.int32.signedBound) : Expr Target.int32 [] .sint := .literal ⟨n, fits⟩
private def unsigned (n : Nat) (fits : n < Target.int32.modulus) :
    Expr Target.int32 [] .uint := .literal ⟨n, fits⟩

/-- Mixed arithmetic converts before the operation; signed arithmetic at this
boundary would instead overflow. Both operand orders exercise normalization. -/
example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.usualAdd (signed 2147483647 (by decide +kernel))
        (unsigned 1 (by decide +kernel))⟩ .nil =
      .defined ⟨2147483648, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.usualAdd (unsigned 1 (by decide +kernel))
        (signed 2147483647 (by decide +kernel))⟩ .nil =
      .defined ⟨2147483648, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- The negative numerator becomes UINT_MAX before unsigned division. -/
example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.usualDiv (signed (-1) (by decide +kernel))
        (unsigned 2 (by decide +kernel))⟩ .nil =
      .defined ⟨2147483647, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- Converting a negative denominator preserves operand order. -/
example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.usualDiv (unsigned 2 (by decide +kernel))
        (signed (-1) (by decide +kernel))⟩ .nil =
      .defined ⟨0, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- An outer cast cannot repair UB in its operand. -/
example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.convert .uint (Expr.usualAdd
        (signed 2147483647 (by decide +kernel)) (signed 1 (by decide +kernel)))⟩ .nil =
      .undefined .signedAdditionOverflow := by
  simp only [eval]
  decide +kernel

/-- Conversion after defined unsigned arithmetic is not signed-add overflow. -/
example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.convert .sint (Expr.usualAdd
        (signed 2147483647 (by decide +kernel)) (unsigned 1 (by decide +kernel)))⟩ .nil =
      .defined ⟨-2147483648, by decide +kernel⟩ := by
  simp only [eval]
  decide +kernel

/-- The converted signed zero still causes actual division-by-zero UB. -/
example (dialect : Dialect) :
    eval ⟨dialect, .gnuModulo,
      Expr.usualDiv (unsigned 2 (by decide +kernel))
        (signed 0 (by decide +kernel))⟩ .nil =
      .undefined .divisionByZero := by
  simp only [eval]
  decide +kernel

/-- A conversion does not hide missing semantics. -/
example (dialect : Dialect) :
    eval (⟨dialect, .gnuModulo,
      Expr.convert .uint (.unsupported (ty := .sint) .memoryAccess)⟩ :
      Program Target.int32 [] .uint) .nil = .unsupported .memoryAccess := rfl

end EDSL.Tests.SourceConversions
