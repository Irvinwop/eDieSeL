/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export.PackedBytes
import Init.Data.Nat.Bitwise.Basic

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Shift and region views of the ordinary packed-byte representation.
These facts retain byte counts and the complete input equality obligation. -/
namespace EDSLGrader.Export.PackedBytes

/-- Byte offsets are bit offsets multiplied by eight. -/
theorem shiftRight_bytes (value count : Nat) :
    value >>> (8 * count) = value / 256 ^ count := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- The low region is first in little-endian concatenation. -/
theorem natOfBytes_append_shift (left right : List (BitVec 8)) :
    natOfBytes (left ++ right) =
      natOfBytes left + (natOfBytes right <<< (8 * left.length)) := by
  rw [natOfBytes_append, Nat.shiftLeft_eq, Nat.pow_mul]
  exact congrArg (fun x : Nat => natOfBytes left + x)
    (Nat.mul_comm (256 ^ left.length) (natOfBytes right))

/-- A suffix is a right shift with its remaining byte count. -/
theorem drop_bytesOfNat_shift (count byteCount value : Nat) :
    List.drop count (bytesOfNat byteCount value) =
      bytesOfNat (byteCount - count) (value >>> (8 * count)) := by
  rw [shiftRight_bytes]
  exact drop_bytesOfNat count byteCount value

/-- An interval is a bounded prefix of the shifted suffix, including requests
past the end of the region. No out-of-range byte is invented. -/
theorem slice_bytesOfNat (start count byteCount value : Nat) :
    List.take count (List.drop start (bytesOfNat byteCount value)) =
      bytesOfNat (min count (byteCount - start)) (value >>> (8 * start)) := by
  rw [drop_bytesOfNat_shift, take_bytesOfNat]

/-- Split a decoded region without computing a byte-list prefix in the proof. -/
theorem split_bytesOfNat (leftCount rightCount value : Nat) :
    bytesOfNat (leftCount + rightCount) value =
      bytesOfNat leftCount value ++
        bytesOfNat rightCount (value >>> (8 * leftCount)) := by
  have pieces := List.take_append_drop leftCount (bytesOfNat (leftCount + rightCount) value)
  rw [take_bytesOfNat, drop_bytesOfNat_shift,
    Nat.min_eq_left (Nat.le_add_right leftCount rightCount),
    Nat.add_sub_cancel_left] at pieces
  exact pieces.symm

#print axioms shiftRight_bytes
#print axioms natOfBytes_append_shift
#print axioms drop_bytesOfNat_shift
#print axioms slice_bytesOfNat
#print axioms split_bytesOfNat
end EDSLGrader.Export.PackedBytes
