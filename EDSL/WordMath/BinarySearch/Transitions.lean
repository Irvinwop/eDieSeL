/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.WordMath.BinarySearch.Word

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Word-index transitions for the shared half-open binary-search invariant.
A client supplies the actual loaded midpoint value and comparison branch.
The rules preserve exclusion over the entire admitted input and prove the
independent match-or-absent relation. Memory and caller authority remain
obligations of the machine-code proof. -/
namespace EDSL.WordMath.BinarySearch

/-- The low branch updates the word register with no wrap, while retaining
the original sorted-input invariant and the complete excluded suffix. -/
theorem advance_low_word {width : Nat} {values : Nat → Nat}
    {key size : Nat} {low high : BitVec width}
    (sorted : Sorted values size)
    (inv : Invariant values key size low.toNat high.toNat)
    (active : low.toNat < high.toNat)
    (below : values (wordMidpoint low high).toNat < key) :
    Invariant values key size (wordMidpoint low high + 1).toNat high.toNat := by
  rw [wordMidpoint_successor_toNat low high active]
  apply advance_low sorted inv active
  rw [wordMidpoint_toNat low high (Nat.le_of_lt active)] at below
  exact below

/-- The high branch uses the actual computed word midpoint as its new
exclusive upper bound; no input element outside the interval is forgotten. -/
theorem retreat_high_word {width : Nat} {values : Nat → Nat}
    {key size : Nat} {low high : BitVec width}
    (sorted : Sorted values size)
    (inv : Invariant values key size low.toNat high.toNat)
    (active : low.toNat < high.toNat)
    (above : key < values (wordMidpoint low high).toNat) :
    Invariant values key size low.toNat (wordMidpoint low high).toNat := by
  rw [wordMidpoint_toNat low high (Nat.le_of_lt active)]
  apply retreat_high sorted inv active
  rw [wordMidpoint_toNat low high (Nat.le_of_lt active)] at above
  exact above

/-- An equal midpoint returns an in-range match, allowing duplicate values
and imposing no unnecessary earliest-match condition. -/
theorem found_word {width : Nat} {values : Nat → Nat}
    {key size : Nat} {low high : BitVec width}
    (inv : Invariant values key size low.toNat high.toNat)
    (active : low.toNat < high.toNat)
    (equal : values (wordMidpoint low high).toNat = key) :
    Correct values key size (some (wordMidpoint low high).toNat) := by
  rw [wordMidpoint_toNat low high (Nat.le_of_lt active)]
  apply found inv active
  rw [wordMidpoint_toNat low high (Nat.le_of_lt active)] at equal
  exact equal

/-- The machine's unsigned low >= high exit test establishes absence.
The invariant itself supplies the opposite bound, including empty inputs. -/
theorem exhausted_word {width : Nat} {values : Nat → Nat}
    {key size : Nat} {low high : BitVec width}
    (inv : Invariant values key size low.toNat high.toNat)
    (done : high.toNat ≤ low.toNat) :
    Correct values key size none := by
  exact exhausted inv (Nat.le_antisymm inv.low_le_high done)

#print axioms advance_low_word
#print axioms retreat_high_word
#print axioms found_word
#print axioms exhausted_word
end EDSL.WordMath.BinarySearch
#audit_edsl
