/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.WordMath.Triangular32

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.WordMath

/-- Natural conservation and parity, with no execution or admission premise. -/
structure TriangularCountdown (original accumulated remaining : Nat) : Prop where
  remaining_le : remaining ≤ original
  even : remaining % 2 = 0
  balance : accumulated + triangular remaining = triangular original

namespace TriangularCountdown

theorem start_even (original : Nat) (even : original % 2 = 0) :
    TriangularCountdown original 0 original :=
  ⟨Nat.le_refl _, even, by simp only [Nat.zero_add]⟩

/-- The n=1 early-return state is included: its remaining count is zero. -/
theorem start_odd (original : Nat) (odd : original % 2 = 1) :
    TriangularCountdown original original (original - 1) := by
  have positive : 0 < original := by omega
  have recurrence := triangular_pred original positive
  exact ⟨by omega, by omega, by omega⟩

theorem enough {original accumulated remaining : Nat}
    (invariant : TriangularCountdown original accumulated remaining)
    (positive : 0 < remaining) : 2 ≤ remaining := by
  have even := invariant.even
  omega

/-- One mathematical two-at-a-time update, including the last update to zero. -/
theorem step {original accumulated remaining : Nat}
    (invariant : TriangularCountdown original accumulated remaining)
    (enough : 2 ≤ remaining) :
    TriangularCountdown original (accumulated + (2 * remaining - 1)) (remaining - 2) := by
  refine ⟨?_, ?_, triangular_budget_two _ _ _ enough invariant.balance⟩
  · have bound := invariant.remaining_le
    omega
  · have even := invariant.even
    omega

theorem rank_step {remaining : Nat} (enough : 2 ≤ remaining) :
    (remaining - 2) / 2 + 1 = remaining / 2 := by omega

theorem rank_decreases {remaining : Nat} (enough : 2 ≤ remaining) :
    (remaining - 2) / 2 < remaining / 2 := by omega

theorem entry_rank {original remaining : Nat} (bound : remaining ≤ original) :
    remaining / 2 < original / 2 + 1 := by omega

theorem finish {original accumulated remaining : Nat}
    (invariant : TriangularCountdown original accumulated remaining)
    (zero : remaining = 0) : accumulated = triangular original := by
  simpa only [zero, triangular_zero, Nat.add_zero] using invariant.balance

theorem unsigned_bounds {original accumulated remaining : Nat}
    (invariant : TriangularCountdown original accumulated remaining)
    (originalBound : original < 2^32) :
    remaining < 2^32 ∧ accumulated < 2^63 := by
  have resultBound := triangular_u32_lt63 originalBound
  have remainingBound := invariant.remaining_le
  have balance := invariant.balance
  omega

theorem updated_bound {original accumulated remaining : Nat}
    (invariant : TriangularCountdown original accumulated remaining)
    (originalBound : original < 2^32) (enough : 2 ≤ remaining) :
    accumulated + (2 * remaining - 1) < 2^63 := by
  exact ((invariant.step enough).unsigned_bounds originalBound).2

/-- Establish fit BEFORE interpreting the LEA's intermediate sum as a Nat. -/
theorem lea_sum_bound {original accumulated remaining : Nat}
    (invariant : TriangularCountdown original accumulated remaining)
    (originalBound : original < 2^32) (enough : 2 ≤ remaining) :
    accumulated + 2 * remaining < 2^64 := by
  have bound := invariant.updated_bound originalBound enough
  omega

end TriangularCountdown

/-- Generic scaled addition followed by signed-byte -1, with unsigned fit.
This is word arithmetic, not an instruction interpreter or memory assertion. -/
theorem add_twice_minus_one_toNat (accumulated remaining : BitVec 64)
    (positive : 0 < remaining.toNat)
    (fit : accumulated.toNat + 2 * remaining.toNat < 2^64) :
    (accumulated + (remaining <<< 1) + (0xff : BitVec 8).signExtend 64).toNat =
      accumulated.toNat + (2 * remaining.toNat - 1) := by
  have doubleBound : remaining.toNat * 2 < 2^64 := by omega
  have shifted : (remaining <<< 1).toNat = 2 * remaining.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (remaining.toNat * 2) % 2^64 = 2 * remaining.toNat
    rw [Nat.mod_eq_of_lt doubleBound, Nat.mul_comm]
  have sum : (accumulated + (remaining <<< 1)).toNat =
      accumulated.toNat + 2 * remaining.toNat := by
    rw [BitVec.toNat_add, shifted, Nat.mod_eq_of_lt fit]
  have ordered : (1 : BitVec 64) ≤ accumulated + (remaining <<< 1) := by
    change (1 : Nat) ≤ (accumulated + (remaining <<< 1)).toNat
    rw [sum]
    omega
  have negativeOne : (0xff : BitVec 8).signExtend 64 = -(1 : BitVec 64) := by decide
  calc
    _ = ((accumulated + (remaining <<< 1)) - 1).toNat := by
      rw [negativeOne, BitVec.add_neg_eq_sub]
    _ = (accumulated + (remaining <<< 1)).toNat - 1 := BitVec.toNat_sub_of_le ordered
    _ = _ := by rw [sum]; omega

/-- Exact word update and strict rank decrease for every admissible budget.
The actual SUB flags are handled separately by the production SUB64 rules. -/
theorem TriangularCountdown.word_step {original : Nat}
    (accumulated remaining : BitVec 64)
    (invariant : TriangularCountdown original accumulated.toNat remaining.toNat)
    (originalBound : original < 2^32) (enough : 2 ≤ remaining.toNat) :
    let nextAccumulated := accumulated + (remaining <<< 1) + (0xff : BitVec 8).signExtend 64
    let nextRemaining := remaining - (2 : BitVec 8).signExtend 64
    TriangularCountdown original nextAccumulated.toNat nextRemaining.toNat ∧
      nextRemaining.toNat / 2 < remaining.toNat / 2 := by
  have sum := add_twice_minus_one_toNat accumulated remaining (by omega)
    (invariant.lea_sum_bound originalBound enough)
  have decrement : (remaining - (2 : BitVec 8).signExtend 64).toNat = remaining.toNat - 2 := by
    change (remaining - 2).toNat = remaining.toNat - 2
    exact BitVec.toNat_sub_of_le (show (2 : BitVec 64) ≤ remaining from enough)
  dsimp only
  rw [sum, decrement]
  exact ⟨invariant.step enough, TriangularCountdown.rank_decreases enough⟩

end EDSL.WordMath

-- These audit commands are proposed for the parent; none has been run here.
#print axioms EDSL.WordMath.TriangularCountdown.step
#print axioms EDSL.WordMath.add_twice_minus_one_toNat
#print axioms EDSL.WordMath.TriangularCountdown.word_step
