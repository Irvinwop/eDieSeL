/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Source.Syntax

set_option autoImplicit false

namespace EDSL.Source.Target

theorem signedBound_pos (target : Target) : 0 < target.signedBound :=
  Int.natCast_pos.mpr (Nat.two_pow_pos _)

theorem modulus_eq_twice_signedBound (target : Target) :
    (target.modulus : Int) = 2 * target.signedBound := by
  have width : target.intBits = (target.intBits - 1) + 1 := by
    have minimum := target.atLeast16
    omega
  have power : (2 ^ target.intBits : Nat) = 2 ^ (target.intBits - 1) * 2 :=
    (congrArg (fun n => (2 : Nat) ^ n) width).trans (Nat.pow_succ _ _)
  change ((2 ^ target.intBits : Nat) : Int) =
    2 * ((2 ^ (target.intBits - 1) : Nat) : Int)
  rw [power, Int.natCast_mul]
  omega

end EDSL.Source.Target

namespace EDSL.Source.IntegerConversions

/-! Same-width two's-complement mathematical maps on the admitted value ranges.
These total number functions do not extend `Expr` or the evaluator, and do not
claim that every ISO C23 implementation chooses this unsigned-to-signed map.
No object representation, ABI, memory effect, or source definedness is modeled.
-/

/-- The signed and unsigned values represent the same residue modulo `2^intBits`.
Their respective ranges are supplied by `Value`, independently of either map. -/
def Corresponds {target : Target} (unsigned : Value target .uint)
    (signed : Value target .sint) : Prop :=
  signed.val % (target.modulus : Int) = (unsigned.val : Int)

/-- Select the representative in `[-signedBound, signedBound)`. -/
def unsignedToSigned {target : Target} (value : Value target .uint) :
    Value target .sint :=
  ⟨if (value.val : Int) < target.signedBound then (value.val : Int)
    else (value.val : Int) - (target.modulus : Int), by
    have half := target.modulus_eq_twice_signedBound
    have positive := target.signedBound_pos
    have upper : (value.val : Int) < (target.modulus : Int) :=
      Int.ofNat_lt.mpr value.isLt
    split <;> omega⟩

/-- Select the nonnegative representative modulo `2^intBits`. -/
def signedToUnsigned {target : Target} (value : Value target .sint) :
    Value target .uint :=
  ⟨(value.val % (target.modulus : Int)).toNat, by
    have positive : (0 : Int) < (target.modulus : Int) :=
      Int.natCast_pos.mpr target.modulus_pos
    have lower := Int.emod_nonneg value.val (Int.ne_of_gt positive)
    have upper := Int.emod_lt_of_pos value.val positive
    omega⟩

theorem unsignedToSigned_range {target : Target} (value : Value target .uint) :
    -target.signedBound ≤ (unsignedToSigned value).val ∧
      (unsignedToSigned value).val < target.signedBound :=
  (unsignedToSigned value).property

theorem signedToUnsigned_range {target : Target} (value : Value target .sint) :
    (0 : Int) ≤ ((signedToUnsigned value).val : Int) ∧
      ((signedToUnsigned value).val : Int) < (target.modulus : Int) :=
  ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (signedToUnsigned value).isLt⟩

private theorem unsigned_remainder {target : Target} (value : Value target .uint) :
    (value.val : Int) % (target.modulus : Int) = (value.val : Int) :=
  Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr value.isLt)

theorem unsignedToSigned_corresponds {target : Target} (value : Value target .uint) :
    Corresponds value (unsignedToSigned value) := by
  unfold Corresponds unsignedToSigned
  dsimp only
  split
  · exact unsigned_remainder value
  · rw [Int.sub_emod_right]
    exact unsigned_remainder value

theorem signedToUnsigned_corresponds {target : Target} (value : Value target .sint) :
    Corresponds (signedToUnsigned value) value := by
  unfold Corresponds signedToUnsigned
  dsimp only
  symm
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (Int.natCast_ne_zero.mpr (Nat.ne_of_gt target.modulus_pos))

/-- Congruence and the signed range identify a unique signed value. -/
theorem signed_unique {target : Target} {unsigned : Value target .uint}
    {left right : Value target .sint}
    (left_ok : Corresponds unsigned left) (right_ok : Corresponds unsigned right) :
    left = right := by
  apply Subtype.ext
  have half := target.modulus_eq_twice_signedBound
  have left_range := left.property
  have right_range := right.property
  have residues : left.val % (target.modulus : Int) =
      right.val % (target.modulus : Int) := left_ok.trans right_ok.symm
  have shifted := Int.add_emod_eq_add_emod_right target.signedBound residues
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at shifted
  omega

/-- Congruence and the unsigned range identify a unique unsigned value. -/
theorem unsigned_unique {target : Target} {signed : Value target .sint}
    {left right : Value target .uint}
    (left_ok : Corresponds left signed) (right_ok : Corresponds right signed) :
    left = right := by
  apply Fin.ext
  have same : (left.val : Int) = (right.val : Int) := left_ok.symm.trans right_ok
  omega

/-- An implementation-independent characterization by congruence and range. -/
theorem unsignedToSigned_eq_iff {target : Target} (unsigned : Value target .uint)
    (signed : Value target .sint) :
    unsignedToSigned unsigned = signed ↔ Corresponds unsigned signed := by
  constructor
  · intro same
    exact same ▸ unsignedToSigned_corresponds unsigned
  · exact signed_unique (unsignedToSigned_corresponds unsigned)

theorem signedToUnsigned_eq_iff {target : Target} (signed : Value target .sint)
    (unsigned : Value target .uint) :
    signedToUnsigned signed = unsigned ↔ Corresponds unsigned signed := by
  constructor
  · intro same
    exact same ▸ signedToUnsigned_corresponds signed
  · exact unsigned_unique (signedToUnsigned_corresponds signed)

theorem signedToUnsigned_unsignedToSigned {target : Target} (value : Value target .uint) :
    signedToUnsigned (unsignedToSigned value) = value :=
  unsigned_unique (signedToUnsigned_corresponds (unsignedToSigned value))
    (unsignedToSigned_corresponds value)

theorem unsignedToSigned_signedToUnsigned {target : Target} (value : Value target .sint) :
    unsignedToSigned (signedToUnsigned value) = value :=
  signed_unique (unsignedToSigned_corresponds (signedToUnsigned value))
    (signedToUnsigned_corresponds value)

/-- Every nonnegative signed value keeps its mathematical value. -/
theorem signedToUnsigned_of_nonnegative {target : Target} (value : Value target .sint)
    (nonnegative : 0 ≤ value.val) :
    ((signedToUnsigned value).val : Int) = value.val := by
  have half := target.modulus_eq_twice_signedBound
  have positive := target.signedBound_pos
  have range := value.property
  have congruence := signedToUnsigned_corresponds value
  unfold Corresponds at congruence
  rw [Int.emod_eq_of_lt nonnegative (by omega)] at congruence
  exact congruence.symm

/-- A low-half unsigned value is representable as a nonnegative signed value. -/
theorem unsignedToSigned_of_low_half {target : Target} (value : Value target .uint)
    (low : (value.val : Int) < target.signedBound) :
    (unsignedToSigned value).val = (value.val : Int) := by
  let signed : Value target .sint :=
    ⟨(value.val : Int), by have positive := target.signedBound_pos; omega⟩
  have same : unsignedToSigned value = signed :=
    (unsignedToSigned_eq_iff value signed).mpr (unsigned_remainder value)
  exact congrArg Subtype.val same

/-- Precisely the low half maps to a nonnegative signed value. -/
theorem unsignedToSigned_nonnegative_iff {target : Target} (value : Value target .uint) :
    0 ≤ (unsignedToSigned value).val ↔ (value.val : Int) < target.signedBound := by
  constructor
  · intro nonnegative
    have preserved := signedToUnsigned_of_nonnegative (unsignedToSigned value) nonnegative
    rw [signedToUnsigned_unsignedToSigned] at preserved
    have range := unsignedToSigned_range value
    omega
  · intro low
    rw [unsignedToSigned_of_low_half value low]
    exact Int.natCast_nonneg _

/-- A negative signed value is moved up by exactly one modulus. -/
theorem signedToUnsigned_of_negative {target : Target} (value : Value target .sint)
    (negative : value.val < 0) :
    ((signedToUnsigned value).val : Int) = value.val + (target.modulus : Int) := by
  have half := target.modulus_eq_twice_signedBound
  have positive := target.signedBound_pos
  have range := value.property
  have shifted : (value.val + (target.modulus : Int)) % (target.modulus : Int) =
      value.val + (target.modulus : Int) :=
    Int.emod_eq_of_lt (by omega) (by omega)
  rw [Int.add_emod_right] at shifted
  have congruence := signedToUnsigned_corresponds value
  unfold Corresponds at congruence
  exact congruence.symm.trans shifted

/-- The unsigned high half maps to a negative value one modulus lower.
The half-way boundary is included, so it maps to the signed minimum. -/
theorem unsignedToSigned_of_high_half {target : Target} (value : Value target .uint)
    (high : target.signedBound ≤ (value.val : Int)) :
    (unsignedToSigned value).val < 0 ∧
      (unsignedToSigned value).val = (value.val : Int) - (target.modulus : Int) := by
  have negative : (unsignedToSigned value).val < 0 := by
    have sign := unsignedToSigned_nonnegative_iff value
    omega
  have offset := signedToUnsigned_of_negative (unsignedToSigned value) negative
  rw [signedToUnsigned_unsignedToSigned] at offset
  exact ⟨negative, by omega⟩

end EDSL.Source.IntegerConversions
