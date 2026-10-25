/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0

-/
import EDSL.WordMath.Triangular

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.WordMath

/-- Unsigned 32-bit factors fit in a 64-bit product. This does not imply
that the same product fits the SIGNED 64-bit interval. -/
theorem nat_u32_mul_lt64 {left right : Nat}
    (leftBound : left < 2^32) (rightBound : right < 2^32) : left * right < 2^64 := by
  calc
    left * right < (2^32) * (2^32) :=
      Nat.mul_lt_mul_of_lt_of_lt leftBound rightBound
    _ = 2^64 := by decide

theorem u32_widen_mul_toNat (left right : BitVec 32) :
    (left.setWidth 64 * right.setWidth 64).toNat = left.toNat * right.toNat := by
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
  exact Nat.mod_eq_of_lt (nat_u32_mul_lt64 left.isLt right.isLt)

/-- One factor is below 2^32 and the successor factor may equal 2^32. -/
theorem nat_u32_successor_product_lt64 {n : Nat} (bound : n < 2^32) :
    n * (n + 1) < 2^64 := by
  calc
    n * (n + 1) < (2^32) * (2^32) :=
      Nat.mul_lt_mul_of_lt_of_le bound (by omega) (by decide)
    _ = 2^64 := by decide

theorem triangular_u32_lt63 {n : Nat} (bound : n < 2^32) : triangular n < 2^63 := by
  have product := nat_u32_successor_product_lt64 bound
  have doubled := triangular_double n
  omega

/-- The first square-plus-input addition also fits UNSIGNED 64 bits. -/
theorem u32_quadratic_sum_lt64 {n : Nat} (bound : n < 2^32) (positive : 0 < n) :
    (n - 1) * (n - 1) + n < 2^64 := by
  have smaller : (n - 1) * (n - 1) ≤ n * (n - 1) :=
    Nat.mul_le_mul_right (n - 1) (by omega)
  have expanded : n * (n - 1) + n = n * n := by
    calc
      n * (n - 1) + n = n * (n - 1 + 1) := by simp [Nat.mul_add]
      _ = n * n := by rw [show n - 1 + 1 = n by omega]
  have square := nat_u32_mul_lt64 bound bound
  omega

/-- n=1 wraps n-2 to UINT32_MAX, but the companion factor n-1 is zero.
For n≥2 the decrement is exact; neither case assumes a full64 input binding. -/
theorem wrapped_u32_pred2_product {n : Nat} (bound : n < 2^32) (positive : 0 < n) :
    ((2^32 + n - 2) % 2^32) * (n - 1) = (n - 2) * (n - 1) := by
  by_cases enough : 2 ≤ n
  · have exactDecrement : (2^32 + n - 2) % 2^32 = n - 2 := by omega
    rw [exactDecrement]
  · have one : n = 1 := by omega
    simp [one]

theorem add_negative_two32 (value : BitVec 32) :
    value + (0xfe : BitVec 8).signExtend 32 = value - 2 := by
  have negativeImmediate : (0xfe : BitVec 8).signExtend 32 = -(2 : BitVec 32) := by decide
  rw [negativeImmediate, BitVec.add_neg_eq_sub]

/-- A mathematical word expression for the reduced polynomial. It is not the
specification, decoder, executor, or a claimed model of a whole program. -/
def reducedTriangular32 (input : BitVec 32) : BitVec 64 :=
  if input = 0 then 0 else
    let predecessor := (input - 1).setWidth 64
    let decremented := (input - 2).setWidth 64
    predecessor * predecessor + input.setWidth 64 - ((decremented * predecessor) >>> 1)

/-- Universal word bridge. The result is exact even at UINT32_MAX;
all intermediate unsigned fit proofs precede the logical right shift. -/
theorem reducedTriangular32_toNat (input : BitVec 32) :
    (reducedTriangular32 input).toNat = triangular input.toNat := by
  by_cases zero : input = 0
  · simp [reducedTriangular32, zero, triangular]
  · have positive : 0 < input.toNat := by
      have notZero : input.toNat ≠ 0 := by
        intro bad
        apply zero
        apply BitVec.eq_of_toNat_eq
        simpa using bad
      omega
    have predecessorValue : (input - 1).toNat = input.toNat - 1 := by
      apply BitVec.toNat_sub_of_le
      change (1 : Nat) ≤ input.toNat
      omega
    have decrementedValue : (input - 2).toNat = (2^32 + input.toNat - 2) % 2^32 := by
      rw [BitVec.toNat_sub]
      have literal : (2 : BitVec 32).toNat = 2 := by decide
      rw [literal]
      congr 1
      omega
    let predecessor := (input - 1).setWidth 64
    let decremented := (input - 2).setWidth 64
    let wide := input.setWidth 64
    have square : (predecessor * predecessor).toNat =
        (input.toNat - 1) * (input.toNat - 1) := by
      change (((input - 1).setWidth 64) * ((input - 1).setWidth 64)).toNat = _
      rw [u32_widen_mul_toNat, predecessorValue]
    have product : (decremented * predecessor).toNat =
        (input.toNat - 2) * (input.toNat - 1) := by
      change (((input - 2).setWidth 64) * ((input - 1).setWidth 64)).toNat = _
      rw [u32_widen_mul_toNat, decrementedValue, predecessorValue]
      exact wrapped_u32_pred2_product input.isLt positive
    have wideValue : wide.toNat = input.toNat :=
      BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)
    have sum : (predecessor * predecessor + wide).toNat =
        (input.toNat - 1) * (input.toNat - 1) + input.toNat := by
      rw [BitVec.toNat_add, square, wideValue]
      exact Nat.mod_eq_of_lt (u32_quadratic_sum_lt64 input.isLt positive)
    have half : ((decremented * predecessor) >>> 1).toNat =
        (input.toNat - 2) * (input.toNat - 1) / 2 := by
      simp only [BitVec.toNat_ushiftRight, product, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have balance := triangular_quadratic_balance input.toNat
    have ordered : ((decremented * predecessor) >>> 1) ≤ predecessor * predecessor + wide := by
      change ((decremented * predecessor) >>> 1).toNat ≤
        (predecessor * predecessor + wide).toNat
      rw [half, sum]
      omega
    simp only [reducedTriangular32, zero, ↓reduceIte]
    change (predecessor * predecessor + wide - ((decremented * predecessor) >>> 1)).toNat = _
    rw [BitVec.toNat_sub_of_le ordered, sum, half]
    exact triangular_quadratic input.toNat

theorem reducedTriangular32_contract (input : BitVec 32) :
    TriangularModulo input.toNat (reducedTriangular32 input) := by
  change (reducedTriangular32 input).toNat = triangular input.toNat % 2^64
  rw [reducedTriangular32_toNat, Nat.mod_eq_of_lt]
  have bound := triangular_u32_lt63 input.isLt
  omega

end EDSL.WordMath

#print axioms EDSL.WordMath.u32_widen_mul_toNat
#print axioms EDSL.WordMath.triangular_u32_lt63
#print axioms EDSL.WordMath.wrapped_u32_pred2_product
#print axioms EDSL.WordMath.reducedTriangular32_toNat
#print axioms EDSL.WordMath.reducedTriangular32_contract
