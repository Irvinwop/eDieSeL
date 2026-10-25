/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export.PackedBytes.Views

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Balanced views of finite little-endian byte regions.

Fuel changes the append-tree shape, not the represented bytes. When fuel is
exhausted, ordinary exact-length decoding provides a total fallback. No fuel,
page-size or canonical-value assumption is needed by the semantic theorems.
These ordinary declarations neither authenticate external bytes nor establish
that a concrete packet fits the fixed runtime limits.
-/
namespace EDSLGrader.Export.PackedBytes

/-- Decode by halving regions larger than sixteen bytes while fuel remains.
The right region starts after the low half; excess high digits are discarded
by its recorded byte count. -/
def balancedBytesOfNat : Nat → Nat → Nat → List (BitVec 8)
  | 0, byteCount, value => bytesOfNat byteCount value
  | fuel + 1, byteCount, value =>
      if byteCount ≤ 16 then bytesOfNat byteCount value
      else
        let half := byteCount / 2
        List.append (balancedBytesOfNat fuel half value)
          (balancedBytesOfNat fuel (byteCount - half) (value >>> (8 * half)))

/-- Every fuel value gives exactly the ordinary finite byte decoding.
In particular, the fallback at fuel zero preserves all requested bytes. -/
theorem balancedBytesOfNat_eq_bytesOfNat (fuel byteCount value : Nat) :
    balancedBytesOfNat fuel byteCount value = bytesOfNat byteCount value := by
  induction fuel generalizing byteCount value with
  | zero => rfl
  | succ fuel ih =>
      by_cases short : byteCount ≤ 16
      · simp only [balancedBytesOfNat, ite_eq_left short]
      · simp only [balancedBytesOfNat, ite_eq_right short, ih]
        have partition : byteCount / 2 + (byteCount - byteCount / 2) = byteCount :=
          Nat.add_sub_of_le (Nat.div_le_self byteCount 2)
        have pieces := split_bytesOfNat (byteCount / 2)
          (byteCount - byteCount / 2) value
        rw [partition] at pieces
        exact pieces.symm

/-- Append-tree depth does not change the exact decoded byte count. -/
theorem length_balancedBytesOfNat (fuel byteCount value : Nat) :
    (balancedBytesOfNat fuel byteCount value).length = byteCount := by
  rw [balancedBytesOfNat_eq_bytesOfNat, length_bytesOfNat]

/-- The represented numeric value is precisely the retained low digits. -/
theorem natOfBytes_balancedBytesOfNat (fuel byteCount value : Nat) :
    natOfBytes (balancedBytesOfNat fuel byteCount value) = value % 256 ^ byteCount := by
  rw [balancedBytesOfNat_eq_bytesOfNat, natOfBytes_bytesOfNat]

/-- A balanced view of an encoded list preserves every source byte. -/
theorem balancedBytesOfNat_natOfBytes (fuel : Nat) (bytes : List (BitVec 8)) :
    balancedBytesOfNat fuel bytes.length (natOfBytes bytes) = bytes := by
  rw [balancedBytesOfNat_eq_bytesOfNat, bytesOfNat_natOfBytes]

/-- Byte counts and independently established encoded values suffice to expose
an exact list endpoint. Neither premise is inferred from producer metadata. -/
theorem balancedBytesOfNat_eq_of_encoding
    (fuel byteCount value : Nat) (bytes : List (BitVec 8))
    (length : bytes.length = byteCount) (encoding : natOfBytes bytes = value) :
    balancedBytesOfNat fuel byteCount value = bytes := by
  rw [← length, ← encoding, balancedBytesOfNat_natOfBytes]

/-- Dropping a prefix shifts the packed value and retains the remaining count,
including requests beyond the end. -/
theorem drop_balancedBytesOfNat (fuel count byteCount value : Nat) :
    List.drop count (balancedBytesOfNat fuel byteCount value) =
      balancedBytesOfNat fuel (byteCount - count) (value >>> (8 * count)) := by
  rw [balancedBytesOfNat_eq_bytesOfNat, balancedBytesOfNat_eq_bytesOfNat]
  exact drop_bytesOfNat_shift count byteCount value

/-- Taking a prefix changes only the number of retained digits. -/
theorem take_balancedBytesOfNat (fuel count byteCount value : Nat) :
    List.take count (balancedBytesOfNat fuel byteCount value) =
      balancedBytesOfNat fuel (min count byteCount) value := by
  rw [balancedBytesOfNat_eq_bytesOfNat, balancedBytesOfNat_eq_bytesOfNat]
  exact take_bytesOfNat count byteCount value

/-- A finite interval is the bounded prefix of its shifted suffix.
An out-of-range request does not invent bytes. -/
theorem slice_balancedBytesOfNat (fuel start count byteCount value : Nat) :
    List.take count (List.drop start (balancedBytesOfNat fuel byteCount value)) =
      balancedBytesOfNat fuel (min count (byteCount - start))
        (value >>> (8 * start)) := by
  rw [balancedBytesOfNat_eq_bytesOfNat, balancedBytesOfNat_eq_bytesOfNat]
  exact slice_bytesOfNat start count byteCount value

/-- A split can be exposed without computing a byte-list prefix in the proof. -/
theorem split_balancedBytesOfNat (fuel leftCount rightCount value : Nat) :
    balancedBytesOfNat fuel (leftCount + rightCount) value =
      balancedBytesOfNat fuel leftCount value ++
        balancedBytesOfNat fuel rightCount (value >>> (8 * leftCount)) := by
  rw [balancedBytesOfNat_eq_bytesOfNat, balancedBytesOfNat_eq_bytesOfNat,
    balancedBytesOfNat_eq_bytesOfNat]
  exact split_bytesOfNat leftCount rightCount value

/-- Different fuel choices are extensionally interchangeable. This is an
ordinary equality proof, not a change to kernel conversion or packet limits. -/
theorem balancedBytesOfNat_fuel_eq (leftFuel rightFuel byteCount value : Nat) :
    balancedBytesOfNat leftFuel byteCount value =
      balancedBytesOfNat rightFuel byteCount value := by
  rw [balancedBytesOfNat_eq_bytesOfNat, balancedBytesOfNat_eq_bytesOfNat]

#print axioms balancedBytesOfNat_eq_bytesOfNat
#print axioms length_balancedBytesOfNat
#print axioms natOfBytes_balancedBytesOfNat
#print axioms balancedBytesOfNat_natOfBytes
#print axioms balancedBytesOfNat_eq_of_encoding
#print axioms drop_balancedBytesOfNat
#print axioms take_balancedBytesOfNat
#print axioms slice_balancedBytesOfNat
#print axioms split_balancedBytesOfNat
#print axioms balancedBytesOfNat_fuel_eq

end EDSLGrader.Export.PackedBytes
