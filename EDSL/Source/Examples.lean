/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Source.Semantics

set_option autoImplicit false

namespace EDSL.Source.Examples

/-- An arithmetic specification without the evaluator's modulo operation:
the mathematical sum differs from the returned value by at most one modulus.
The result's type separately enforces `0 ≤ result < 2^intBits`. -/
def ModularSum (target : Target) (x y result : Value target .uint) : Prop :=
  ∃ carry : Nat, carry ≤ 1 ∧ result.val + carry * target.modulus = x.val + y.val

def add (target : Target) (dialect : Dialect) : Program target [.uint, .uint] .uint :=
  ⟨dialect, .gnuModulo, .uadd (.param .here) (.param (.there .here))⟩

/-- All externally supplied parameter values, all admitted widths, both dialects.
There is no caller UB-freedom premise or input range restriction beyond typing. -/
theorem add_verified (target : Target) (dialect : Dialect) :
    Verifies (add target dialect) (fun _ => True)
      (fun inputs result => ModularSum target
        (inputs.get .here) (inputs.get (.there .here)) result) := by
  intro inputs _
  let x := inputs.get .here
  let y := inputs.get (.there .here)
  refine ⟨⟨(x.val + y.val) % target.modulus,
    Nat.mod_lt _ target.modulus_pos⟩, rfl, ?_⟩
  refine ⟨(x.val + y.val) / target.modulus, ?_, ?_⟩
  · have hx := x.isLt
    have hy := y.isLt
    have small : x.val + y.val < 2 * target.modulus := by omega
    have carry_lt : (x.val + y.val) / target.modulus < 2 :=
      (Nat.div_lt_iff_lt_mul target.modulus_pos).2 small
    omega
  · exact Nat.mod_add_div' _ _

theorem add_noUB (target : Target) (dialect : Dialect) :
    NoUB (add target dialect) (fun _ => True) := (add_verified target dialect).noUB

/-- A zero divisor is UB for every numerator, rather than Lean's total quotient. -/
def divideByZero (target : Target) (dialect : Dialect) : Program target [.uint] .uint :=
  ⟨dialect, .gnuModulo, .udiv (.param .here) (.literal ⟨0, target.modulus_pos⟩)⟩

theorem divideByZero_undefined (target : Target) (dialect : Dialect)
    (inputs : Inputs target [.uint]) :
    eval (divideByZero target dialect) inputs = .undefined .divisionByZero := rfl

def overflowingAdd (dialect : Dialect) : Program Target.int32 [] .sint :=
  ⟨dialect, .gnuModulo, .sadd
    (.literal ⟨2147483647, by decide +kernel⟩)
    (.literal ⟨1, by decide +kernel⟩)⟩

/-- The positive signed boundary does not silently wrap. -/
theorem overflowingAdd_undefined (dialect : Dialect) :
    eval (overflowingAdd dialect) .nil = .undefined .signedAdditionOverflow := by
  simp only [eval, overflowingAdd]
  decide +kernel

def underflowingAdd (dialect : Dialect) : Program Target.int32 [] .sint :=
  ⟨dialect, .gnuModulo, .sadd
    (.literal ⟨-2147483648, by decide +kernel⟩)
    (.literal ⟨-1, by decide +kernel⟩)⟩

theorem underflowingAdd_undefined (dialect : Dialect) :
    eval (underflowingAdd dialect) .nil = .undefined .signedAdditionOverflow := by
  simp only [eval, underflowingAdd]
  decide +kernel

def overflowingDiv (dialect : Dialect) : Program Target.int32 [] .sint :=
  ⟨dialect, .gnuModulo, .sdiv
    (.literal ⟨-2147483648, by decide +kernel⟩)
    (.literal ⟨-1, by decide +kernel⟩)⟩

/-- `INT_MIN / -1` is UB even though its mathematical quotient exists. -/
theorem overflowingDiv_undefined (dialect : Dialect) :
    eval (overflowingDiv dialect) .nil = .undefined .signedDivisionOverflow := by
  simp only [eval, overflowingDiv]
  decide +kernel

def negativeDiv (dialect : Dialect) : Program Target.int32 [] .sint :=
  ⟨dialect, .gnuModulo, .sdiv
    (.literal ⟨-7, by decide +kernel⟩)
    (.literal ⟨3, by decide +kernel⟩)⟩

/-- Truncation toward zero differs from Euclidean/floor division on this input. -/
theorem negativeDiv_defined (dialect : Dialect) :
    eval (negativeDiv dialect) .nil =
      .defined ⟨-2, by decide +kernel⟩ := by
  simp only [eval, negativeDiv]
  decide +kernel

/-- An unsupported subexpression cannot disappear behind a supported addition. -/
def unsupportedReturn (target : Target) (dialect : Dialect) : Program target [] .uint :=
  ⟨dialect, .gnuModulo, .uadd (.literal ⟨0, target.modulus_pos⟩) (.unsupported .memoryAccess)⟩

theorem unsupportedReturn_outcome (target : Target) (dialect : Dialect) :
    eval (unsupportedReturn target dialect) .nil = .unsupported .memoryAccess := rfl

theorem unsupportedReturn_not_noUB (target : Target) (dialect : Dialect) :
    ¬ NoUB (unsupportedReturn target dialect) (fun _ => True) := by
  intro safe
  obtain ⟨value, execution⟩ := safe .nil trivial
  cases execution

end EDSL.Source.Examples
