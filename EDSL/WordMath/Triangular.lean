/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0

-/
import Init

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.WordMath

/-- Natural triangular number, before any word truncation. -/
def triangular (n : Nat) : Nat := n * (n + 1) / 2

/-- The contract does not mention a program or its implementation. -/
def TriangularModulo (n : Nat) (result : BitVec 64) : Prop :=
  result.toNat = triangular n % 2^64

theorem triangular_zero : triangular 0 = 0 := rfl

theorem triangular_succ (n : Nat) :
    triangular (n + 1) = triangular n + (n + 1) := by
  have numerator : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, Nat.two_mul]
    omega
  change ((n + 1) * (n + 1 + 1)) / 2 = n * (n + 1) / 2 + (n + 1)
  rw [numerator, Nat.add_mul_div_left _ _ (by decide)]

theorem triangular_pred (n : Nat) (positive : 0 < n) :
    triangular n = triangular (n - 1) + n := by
  have split : n = (n - 1) + 1 := by omega
  simpa only [← split] using triangular_succ (n - 1)

/-- Two-at-a-time countdown recurrence; no parity restriction is needed. -/
theorem triangular_two (n : Nat) (enough : 2 ≤ n) :
    triangular n = triangular (n - 2) + (2 * n - 1) := by
  have one := triangular_pred n (by omega)
  have two := triangular_pred (n - 1) (by omega)
  have reduced : n - 1 - 1 = n - 2 := by omega
  rw [reduced] at two
  omega

/-- Avoids reasoning about divisibility afresh at each polynomial use. -/
theorem triangular_double (n : Nat) : 2 * triangular n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n induction =>
    change 2 * triangular (n + 1) = (n + 1) * (n + 1 + 1)
    rw [triangular_succ]
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, Nat.two_mul]
      at induction ⊢
    omega

/-- Natural countdown-budget conservation, reusable by loop invariants. -/
theorem triangular_budget_two (total accumulated remaining : Nat)
    (enough : 2 ≤ remaining)
    (balance : accumulated + triangular remaining = total) :
    accumulated + (2 * remaining - 1) + triangular (remaining - 2) = total := by
  have recurrence := triangular_two remaining enough
  omega

/-- The reduced quadratic numerator balances the desired value and the
quantity removed. This also establishes that natural subtraction is exact. -/
theorem triangular_quadratic_balance (n : Nat) :
    (n - 1) * (n - 1) + n =
      triangular n + (n - 2) * (n - 1) / 2 := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ k =>
      have doubled := triangular_double k
      have first := triangular_succ k
      have second : triangular (k + 2) = triangular (k + 1) + (k + 2) :=
        triangular_succ (k + 1)
      have firstPred : k + 2 - 1 = k + 1 := by omega
      have secondPred : k + 2 - 2 = k := by omega
      change (k + 2 - 1) * (k + 2 - 1) + (k + 2) =
        triangular (k + 2) + (k + 2 - 2) * (k + 2 - 1) / 2
      rw [firstPred, secondPred]
      change (k + 1) * (k + 1) + (k + 2) = triangular (k + 2) + triangular k
      rw [second, first]
      simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, Nat.two_mul]
        at doubled ⊢
      omega

theorem triangular_quadratic (n : Nat) :
    (n - 1) * (n - 1) + n - ((n - 2) * (n - 1) / 2) = triangular n := by
  have balance := triangular_quadratic_balance n
  omega

theorem triangularModulo_ofNat (n : Nat) :
    TriangularModulo n (BitVec.ofNat 64 (triangular n)) := rfl

theorem triangularModulo_unique {n : Nat} {first second : BitVec 64}
    (left : TriangularModulo n first) (right : TriangularModulo n second) : first = second := by
  exact BitVec.eq_of_toNat_eq (left.trans right.symm)

theorem triangularModulo_exists_unique (n : Nat) :
    ∃ result : BitVec 64, TriangularModulo n result ∧
      ∀ other, TriangularModulo n other → other = result :=
  ⟨_, triangularModulo_ofNat n, fun _ proof =>
    triangularModulo_unique proof (triangularModulo_ofNat n)⟩

end EDSL.WordMath

#print axioms EDSL.WordMath.triangular_succ
#print axioms EDSL.WordMath.triangular_two
#print axioms EDSL.WordMath.triangular_double
#print axioms EDSL.WordMath.triangular_quadratic_balance
#print axioms EDSL.WordMath.triangularModulo_exists_unique
