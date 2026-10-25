/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.WordMath.BinarySearch

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Word arithmetic for the shared half-open binary-search interval rules.
The midpoint is computed by subtracting before shifting; no signed-range
restriction or non-overflowing sum of the endpoints is assumed. These results
are independent of any instruction, compiler, machine state or program. -/
namespace EDSL.WordMath.BinarySearch

/-- The unsigned subtract/shift/add expression, at any width including zero. -/
def wordMidpoint {width : Nat} (low high : BitVec width) : BitVec width :=
  low + ((high - low) >>> 1)

/-- Under the interval ordering, unsigned subtraction and the final addition
both agree exactly with natural arithmetic. Endpoint sums may overflow. -/
theorem wordMidpoint_toNat {width : Nat} (low high : BitVec width)
    (ordered : low.toNat ≤ high.toNat) :
    (wordMidpoint low high).toNat = midpoint low.toNat high.toNat := by
  have words : low ≤ high := ordered
  have half : ((high - low) >>> 1).toNat = (high.toNat - low.toNat) / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_sub_of_le words]
  have highBound := high.isLt
  have noOverflow : low.toNat + ((high - low) >>> 1).toNat < 2 ^ width := by
    rw [half]
    omega
  rw [wordMidpoint, BitVec.toNat_add, Nat.mod_eq_of_lt noOverflow, half]
  rfl

/-- An active half-open word interval contains the computed midpoint. -/
theorem wordMidpoint_bounds {width : Nat} (low high : BitVec width)
    (active : low.toNat < high.toNat) :
    low.toNat ≤ (wordMidpoint low high).toNat ∧
      (wordMidpoint low high).toNat < high.toNat := by
  rw [wordMidpoint_toNat low high (Nat.le_of_lt active)]
  exact midpoint_bounds active

/-- Advancing past an active midpoint cannot wrap, including at a maximal
representable high endpoint. No extra input-size bound is required. -/
theorem wordMidpoint_successor_toNat {width : Nat} (low high : BitVec width)
    (active : low.toNat < high.toNat) :
    (wordMidpoint low high + 1).toNat =
      midpoint low.toNat high.toNat + 1 := by
  have positive : 0 < width := by
    have lowBound := low.isLt
    have highBound := high.isLt
    by_cases zero : width = 0
    · simp only [zero, Nat.pow_zero] at lowBound highBound
      omega
    · omega
  have upper := (wordMidpoint_bounds low high active).2
  have highBound := high.isLt
  have safe : (wordMidpoint low high).toNat + 1 < 2 ^ width := by omega
  have one : (1 : BitVec width).toNat = 1 := by
    change (1#width).toNat = 1
    exact BitVec.toNat_one positive
  rw [BitVec.toNat_add, one,
    Nat.mod_eq_of_lt safe, wordMidpoint_toNat low high (Nat.le_of_lt active)]

/-- The two branch updates retain the same strict natural interval ranks. -/
theorem wordMidpoint_ranks {width : Nat} (low high : BitVec width)
    (active : low.toNat < high.toNat) :
    high.toNat - (wordMidpoint low high + 1).toNat < high.toNat - low.toNat ∧
      (wordMidpoint low high).toNat - low.toNat < high.toNat - low.toNat := by
  rw [wordMidpoint_successor_toNat low high active,
    wordMidpoint_toNat low high (Nat.le_of_lt active)]
  exact ⟨advance_low_rank active, retreat_high_rank active⟩

#print axioms wordMidpoint_toNat
#print axioms wordMidpoint_bounds
#print axioms wordMidpoint_successor_toNat
#print axioms wordMidpoint_ranks
end EDSL.WordMath.BinarySearch
#audit_edsl
