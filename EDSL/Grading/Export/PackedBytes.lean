/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Init.Data.BitVec.Bootstrap
import Init.Data.List.Nat.TakeDrop
import Init.Data.Nat.Mod

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Little-endian arithmetic for finite byte regions.

The byte count is part of the representation: a Nat alone cannot distinguish
the empty region from a region of zero bytes. Decoding always returns exactly
the requested number of bytes and discards higher digits. These are ordinary
theorems for certificate construction, not trusted input declarations. They
neither authenticate an external file nor replace its independent contract.

The definitions do not prescribe how large Nats are serialized. In particular,
a producer must still satisfy the packet's decimal-literal and expression
bounds; assembling values from smaller limbs does not change those bounds.
-/
namespace EDSLGrader.Export.PackedBytes

/-- Interpret a byte list as one little-endian, unsigned Nat. -/
def natOfBytes : List (BitVec 8) → Nat
  | [] => 0
  | byte :: bytes => byte.toNat + 256 * natOfBytes bytes

/-- Extract exactly the requested count of little-endian bytes, including zeros.
The high digits beyond that count are discarded. -/
def bytesOfNat : Nat → Nat → List (BitVec 8)
  | 0, _ => []
  | byteCount + 1, value =>
      BitVec.ofNat 8 value :: bytesOfNat byteCount (value / 256)

theorem length_bytesOfNat (byteCount value : Nat) :
    (bytesOfNat byteCount value).length = byteCount := by
  induction byteCount generalizing value with
  | zero => rfl
  | succ byteCount ih =>
      simp only [bytesOfNat, List.length_cons, ih]

/-- Removing the lowest digit is division by the byte radix. -/
theorem natOfBytes_cons_div (byte : BitVec 8) (bytes : List (BitVec 8)) :
    natOfBytes (byte :: bytes) / 256 = natOfBytes bytes := by
  change (byte.toNat + 256 * natOfBytes bytes) / 256 = natOfBytes bytes
  rw [Nat.add_mul_div_left _ _ (by decide : 0 < 256),
    Nat.div_eq_of_lt byte.isLt, Nat.zero_add]

/-- The lowest digit is exactly the original byte, with no truncation. -/
theorem natOfBytes_cons_mod (byte : BitVec 8) (bytes : List (BitVec 8)) :
    natOfBytes (byte :: bytes) % 256 = byte.toNat := by
  change (byte.toNat + 256 * natOfBytes bytes) % 256 = byte.toNat
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt byte.isLt]

/-- Decoding an encoded list preserves its length and every byte. -/
theorem bytesOfNat_natOfBytes (bytes : List (BitVec 8)) :
    bytesOfNat bytes.length (natOfBytes bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      change BitVec.ofNat 8 (natOfBytes (byte :: bytes)) ::
        bytesOfNat bytes.length (natOfBytes (byte :: bytes) / 256) = byte :: bytes
      rw [natOfBytes_cons_div, ih]
      apply congrArg (fun digit : BitVec 8 => digit :: bytes)
      apply BitVec.eq_of_toNat_eq
      change natOfBytes (byte :: bytes) % 256 = byte.toNat
      exact natOfBytes_cons_mod byte bytes

/-- Encoding the requested digits retains exactly the low byteCount bytes. -/
theorem natOfBytes_bytesOfNat (byteCount value : Nat) :
    natOfBytes (bytesOfNat byteCount value) = value % 256 ^ byteCount := by
  induction byteCount generalizing value with
  | zero => simp only [bytesOfNat, natOfBytes, Nat.pow_zero, Nat.mod_one]
  | succ byteCount ih =>
      change (BitVec.ofNat 8 value).toNat +
        256 * natOfBytes (bytesOfNat byteCount (value / 256)) =
          value % 256 ^ (byteCount + 1)
      rw [BitVec.toNat_ofNat]
      change value % 256 +
        256 * natOfBytes (bytesOfNat byteCount (value / 256)) =
          value % 256 ^ (byteCount + 1)
      rw [ih, Nat.pow_succ']
      exact (Nat.mod_mul (a := 256) (b := 256 ^ byteCount) (x := value)).symm

theorem natOfBytes_bytesOfNat_of_lt (byteCount value : Nat)
    (canonical : value < 256 ^ byteCount) :
    natOfBytes (bytesOfNat byteCount value) = value := by
  rw [natOfBytes_bytesOfNat, Nat.mod_eq_of_lt canonical]

/-- Every finite byte list has a canonical encoding at its recorded length. -/
theorem natOfBytes_lt (bytes : List (BitVec 8)) :
    natOfBytes bytes < 256 ^ bytes.length := by
  have low := natOfBytes_bytesOfNat bytes.length (natOfBytes bytes)
  rw [bytesOfNat_natOfBytes] at low
  calc
    natOfBytes bytes = natOfBytes bytes % 256 ^ bytes.length := low
    _ < 256 ^ bytes.length := Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 256))

/-- Equality of lengths and encoded values suffices for byte-list equality. -/
theorem eq_of_length_eq_of_natOfBytes_eq (left right : List (BitVec 8))
    (length : left.length = right.length)
    (value : natOfBytes left = natOfBytes right) : left = right := by
  calc
    left = bytesOfNat left.length (natOfBytes left) :=
      (bytesOfNat_natOfBytes left).symm
    _ = bytesOfNat right.length (natOfBytes right) := by rw [length, value]
    _ = right := bytesOfNat_natOfBytes right

/-- Concatenation is a radix shift and addition. This permits independent,
balanced region construction without choosing a concrete limb width. -/
theorem natOfBytes_append (left right : List (BitVec 8)) :
    natOfBytes (left ++ right) =
      natOfBytes left + 256 ^ left.length * natOfBytes right := by
  induction left with
  | nil => simp only [List.nil_append, natOfBytes, List.length_nil, Nat.pow_zero,
      Nat.one_mul, Nat.zero_add]
  | cons byte bytes ih =>
      simp only [List.cons_append, natOfBytes, List.length_cons, ih,
        Nat.pow_succ', Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- Dropping bytes is division by the corresponding radix power.
This also holds beyond the end of the list, where both sides are zero. -/
theorem natOfBytes_drop (count : Nat) (bytes : List (BitVec 8)) :
    natOfBytes (List.drop count bytes) = natOfBytes bytes / 256 ^ count := by
  induction count generalizing bytes with
  | zero => simp only [List.drop_zero, Nat.pow_zero, Nat.div_one]
  | succ count ih =>
      cases bytes with
      | nil => simp only [List.drop_nil, natOfBytes, Nat.zero_div]
      | cons byte bytes =>
          rw [List.drop_succ_cons, ih, Nat.pow_succ',
            ← Nat.div_div_eq_div_mul, natOfBytes_cons_div]

/-- Taking bytes is reduction modulo the corresponding radix power.
This includes requests extending beyond the end of the list. -/
theorem natOfBytes_take (count : Nat) (bytes : List (BitVec 8)) :
    natOfBytes (List.take count bytes) = natOfBytes bytes % 256 ^ count := by
  induction count generalizing bytes with
  | zero => simp only [List.take_zero, natOfBytes, Nat.pow_zero, Nat.mod_one]
  | succ count ih =>
      cases bytes with
      | nil => simp only [List.take_nil, natOfBytes, Nat.zero_mod]
      | cons byte bytes =>
          change byte.toNat + 256 * natOfBytes (List.take count bytes) =
            natOfBytes (byte :: bytes) % 256 ^ (count + 1)
          rw [ih, Nat.pow_succ', Nat.mod_mul,
            natOfBytes_cons_mod, natOfBytes_cons_div]

/-- A source-list suffix can be recovered without retaining its discarded
prefix in the arithmetic representation. -/
theorem bytesOfNat_drop (count : Nat) (bytes : List (BitVec 8)) :
    bytesOfNat (bytes.length - count) (natOfBytes bytes / 256 ^ count) =
      List.drop count bytes := by
  have roundtrip := bytesOfNat_natOfBytes (List.drop count bytes)
  rw [List.length_drop, natOfBytes_drop] at roundtrip
  exact roundtrip

/-- A source-list prefix can be recovered from the low encoded digits. -/
theorem bytesOfNat_take (count : Nat) (bytes : List (BitVec 8)) :
    bytesOfNat (min count bytes.length) (natOfBytes bytes % 256 ^ count) =
      List.take count bytes := by
  have roundtrip := bytesOfNat_natOfBytes (List.take count bytes)
  rw [List.length_take, natOfBytes_take] at roundtrip
  exact roundtrip

/-- Higher Nat digits have no effect on a fixed-width decoded region. -/
theorem bytesOfNat_mod (byteCount value : Nat) :
    bytesOfNat byteCount (value % 256 ^ byteCount) = bytesOfNat byteCount value := by
  have roundtrip := bytesOfNat_natOfBytes (bytesOfNat byteCount value)
  rw [length_bytesOfNat, natOfBytes_bytesOfNat] at roundtrip
  exact roundtrip

/-- Decode a suffix directly by shifting the packed value. -/
theorem drop_bytesOfNat (count byteCount value : Nat) :
    List.drop count (bytesOfNat byteCount value) =
      bytesOfNat (byteCount - count) (value / 256 ^ count) := by
  induction count generalizing byteCount value with
  | zero => simp only [List.drop_zero, Nat.sub_zero, Nat.pow_zero, Nat.div_one]
  | succ count ih =>
      cases byteCount with
      | zero => simp only [bytesOfNat, List.drop_nil, Nat.zero_sub]
      | succ byteCount =>
          simp only [bytesOfNat, List.drop_succ_cons, Nat.succ_sub_succ_eq_sub]
          rw [ih, Nat.pow_succ', ← Nat.div_div_eq_div_mul]

/-- A prefix only changes the number of decoded digits. -/
theorem take_bytesOfNat (count byteCount value : Nat) :
    List.take count (bytesOfNat byteCount value) =
      bytesOfNat (min count byteCount) value := by
  induction count generalizing byteCount value with
  | zero => simp only [List.take_zero, Nat.zero_min, bytesOfNat]
  | succ count ih =>
      cases byteCount with
      | zero => simp only [bytesOfNat, List.take_nil, Nat.min_zero]
      | succ byteCount =>
          simp only [bytesOfNat, List.take_succ_cons, Nat.succ_min_succ, ih]

/-- Prefix extraction with an explicit modulo, for a prefix within the region. -/
theorem take_bytesOfNat_mod (count byteCount value : Nat)
    (within : count ≤ byteCount) :
    List.take count (bytesOfNat byteCount value) =
      bytesOfNat count (value % 256 ^ count) := by
  rw [take_bytesOfNat, Nat.min_eq_left within, bytesOfNat_mod]

#print axioms length_bytesOfNat
#print axioms natOfBytes_cons_div
#print axioms natOfBytes_cons_mod
#print axioms bytesOfNat_natOfBytes
#print axioms natOfBytes_bytesOfNat
#print axioms natOfBytes_bytesOfNat_of_lt
#print axioms natOfBytes_lt
#print axioms eq_of_length_eq_of_natOfBytes_eq
#print axioms natOfBytes_append
#print axioms natOfBytes_drop
#print axioms natOfBytes_take
#print axioms bytesOfNat_drop
#print axioms bytesOfNat_take
#print axioms bytesOfNat_mod
#print axioms drop_bytesOfNat
#print axioms take_bytesOfNat
#print axioms take_bytesOfNat_mod

end EDSLGrader.Export.PackedBytes
