/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

/-! Mathematical interval rules for unsigned binary search. They specify any
matching index, including duplicate values, or absence from the complete input.
They supply loop invariants and decreasing ranks; instruction execution,
address bounds, input snapshots and current memory authority are separate. -/
namespace EDSL.WordMath.BinarySearch

/-- Nondecreasing order on precisely the admitted finite input. -/
def Sorted (values : Nat → Nat) (size : Nat) : Prop :=
  ∀ i j, i ≤ j → j < size → values i ≤ values j

/-- The excluded prefix and suffix cannot contain a match. -/
structure Invariant (values : Nat → Nat) (key size low high : Nat) : Prop where
  low_le_high : low ≤ high
  high_le_size : high ≤ size
  excluded_low : ∀ i, i < low → values i < key
  excluded_high : ∀ i, high ≤ i → i < size → key < values i

/-- Independent result relation: any equal input position, or genuine absence. -/
def Correct (values : Nat → Nat) (key size : Nat) : Option Nat → Prop
  | some index => index < size ∧ values index = key
  | none => ∀ index, index < size → values index ≠ key

/-- Natural arithmetic avoids overflow in the midpoint's mathematical rule. -/
def midpoint (low high : Nat) : Nat := low + (high - low) / 2

theorem midpoint_bounds {low high : Nat} (active : low < high) :
    low ≤ midpoint low high ∧ midpoint low high < high := by
  simp only [midpoint]
  omega

theorem initial (values : Nat → Nat) (key size : Nat) :
    Invariant values key size 0 size := by
  constructor
  · omega
  · omega
  · intro i hi
    omega
  · intro i hi bound
    omega

theorem matches_remain {values : Nat → Nat} {key size low high : Nat}
    (inv : Invariant values key size low high) {index : Nat}
    (bound : index < size) (equal : values index = key) :
    low ≤ index ∧ index < high := by
  constructor
  · by_cases inside : low ≤ index
    · exact inside
    · have before : index < low := by omega
      have excluded := inv.excluded_low index before
      omega
  · by_cases inside : index < high
    · exact inside
    · have after : high ≤ index := by omega
      have excluded := inv.excluded_high index after bound
      omega

theorem advance_low {values : Nat → Nat} {key size low high : Nat}
    (ordered : Sorted values size) (inv : Invariant values key size low high)
    (active : low < high) (below : values (midpoint low high) < key) :
    Invariant values key size (midpoint low high + 1) high := by
  obtain ⟨lower, upper⟩ := midpoint_bounds active
  have middle_size : midpoint low high < size := Nat.lt_of_lt_of_le upper inv.high_le_size
  refine ⟨by omega, inv.high_le_size, ?_, inv.excluded_high⟩
  intro i bound
  have before : i ≤ midpoint low high := by omega
  exact Nat.lt_of_le_of_lt (ordered i (midpoint low high) before middle_size) below

theorem retreat_high {values : Nat → Nat} {key size low high : Nat}
    (ordered : Sorted values size) (inv : Invariant values key size low high)
    (active : low < high) (above : key < values (midpoint low high)) :
    Invariant values key size low (midpoint low high) := by
  obtain ⟨lower, upper⟩ := midpoint_bounds active
  refine ⟨lower, Nat.le_trans (Nat.le_of_lt upper) inv.high_le_size, inv.excluded_low, ?_⟩
  intro i after bound
  exact Nat.lt_of_lt_of_le above (ordered (midpoint low high) i after bound)

theorem found {values : Nat → Nat} {key size low high : Nat}
    (inv : Invariant values key size low high) (active : low < high)
    (equal : values (midpoint low high) = key) :
    Correct values key size (some (midpoint low high)) := by
  exact ⟨Nat.lt_of_lt_of_le (midpoint_bounds active).2 inv.high_le_size, equal⟩

theorem exhausted {values : Nat → Nat} {key size low high : Nat}
    (inv : Invariant values key size low high) (empty : low = high) :
    Correct values key size none := by
  intro i bound equal
  obtain ⟨lower, upper⟩ := matches_remain inv bound equal
  omega

theorem advance_low_rank {low high : Nat} (active : low < high) :
    high - (midpoint low high + 1) < high - low := by
  obtain ⟨lower, upper⟩ := midpoint_bounds active
  omega

theorem retreat_high_rank {low high : Nat} (active : low < high) :
    midpoint low high - low < high - low := by
  obtain ⟨lower, upper⟩ := midpoint_bounds active
  omega

#print axioms midpoint_bounds
#print axioms initial
#print axioms matches_remain
#print axioms advance_low
#print axioms retreat_high
#print axioms found
#print axioms exhausted
#print axioms advance_low_rank
#print axioms retreat_high_rank
end EDSL.WordMath.BinarySearch
#audit_edsl
