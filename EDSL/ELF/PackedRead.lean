/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionWindow
import EDSL.Grading.Export.PackedBytes.Views
import EDSL.Grading.Export.PackedBytes.Encoding

/-! Arithmetic consumers for the existing bounded ELF reader.

The byte count is explicit, and words need not be canonical at that count.
These adapters preserve the original reader and field contracts. They neither
authenticate an external file nor establish ELF layout, admission, or execution.
There are no environmental assumptions.
-/
namespace EDSL.ELF.PackedRead

open FunctionWindow (Field)
open EDSLGrader.Export

/-- Identify the original reader's little-endian fold, including its order of
multiplication, with the existing packed encoding. -/
theorem foldr_eq_natOfBytes (bytes : List X86.Byte) :
    bytes.foldr (fun byte rest => byte.toNat + rest * 256) 0 =
      PackedBytes.natOfBytes bytes := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
    simp only [List.foldr_cons, PackedBytes.natOfBytes, ih,
      Nat.mul_comm (PackedBytes.natOfBytes bytes) 256]

/-- Closed endpoints use ordinary kernel shift and modulo primitives. -/
def numericValue (word offset width : Nat) : Nat :=
  (word >>> (8 * offset)) % (1 <<< (8 * width))

theorem numericValue_eq_rangeValue (word offset width : Nat) :
    numericValue word offset width = PackedBytes.Encoding.rangeValue word offset width := by
  unfold numericValue PackedBytes.Encoding.rangeValue
  rw [PackedBytes.shiftRight_bytes, Nat.shiftLeft_eq, Nat.pow_mul, Nat.one_mul]

/-- Every offset and width, including zero widths and noncanonical words.
The bound is the reader's exact bound; out-of-range zero-width reads truncate. -/
theorem readNat_bytesOfNat (n word offset width : Nat) :
    readNat (PackedBytes.bytesOfNat n word) offset width =
      if offset + width ≤ n then .ok (numericValue word offset width)
      else .error .truncated := by
  unfold readNat
  rw [PackedBytes.length_bytesOfNat]
  split
  next inside =>
    rw [foldr_eq_natOfBytes, PackedBytes.slice_bytesOfNat,
      Nat.min_eq_left (by omega : width ≤ n - offset),
      PackedBytes.natOfBytes_bytesOfNat]
    rw [numericValue_eq_rangeValue]
    unfold PackedBytes.Encoding.rangeValue
    rw [PackedBytes.shiftRight_bytes]
  next => rfl

/-- A stable arithmetic form of the existing independent field relation. -/
theorem field_holds_iff (n word : Nat) (field : Field) :
    field.Holds (PackedBytes.bytesOfNat n word) ↔
      field.offset + field.width ≤ n ∧
        numericValue word field.offset field.width = field.value := by
  unfold Field.Holds
  rw [PackedBytes.length_bytesOfNat, foldr_eq_natOfBytes]
  constructor
  · rintro ⟨inside, value⟩
    refine ⟨inside, ?_⟩
    rw [PackedBytes.slice_bytesOfNat,
      Nat.min_eq_left (by omega : field.width ≤ n - field.offset),
      PackedBytes.natOfBytes_bytesOfNat] at value
    simpa only [numericValue, Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_mul] using value
  · rintro ⟨inside, value⟩
    refine ⟨inside, ?_⟩
    rw [PackedBytes.slice_bytesOfNat,
      Nat.min_eq_left (by omega : field.width ≤ n - field.offset),
      PackedBytes.natOfBytes_bytesOfNat]
    simpa only [numericValue, Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_mul] using value

/-- Exact bounded equality, with no reduction of the decoded byte list. -/
def checkField (n word : Nat) (field : Field) : Bool :=
  decide (field.offset + field.width ≤ n) &&
    decide (numericValue word field.offset field.width = field.value)

theorem checkField_eq_readNat (n word : Nat) (field : Field) :
    checkField n word field =
      (match readNat (PackedBytes.bytesOfNat n word) field.offset field.width with
      | .ok observed => decide (observed = field.value)
      | .error _ => false) := by
  rw [readNat_bytesOfNat]
  by_cases inside : field.offset + field.width ≤ n <;> simp [checkField, inside]

theorem checkField_eq_true_iff (n word : Nat) (field : Field) :
    checkField n word field = true ↔ field.Holds (PackedBytes.bytesOfNat n word) := by
  rw [field_holds_iff]
  simp only [checkField, Bool.and_eq_true, decide_eq_true_eq]

theorem checkField_sound (n word : Nat) (field : Field)
    (checked : checkField n word field = true) :
    field.Holds (PackedBytes.bytesOfNat n word) :=
  (checkField_eq_true_iff n word field).mp checked

def checkFields (n word : Nat) (fields : List Field) : Bool :=
  fields.all (checkField n word)

/-- Targets the exact expanded expression shared by the two private ELF
checkers. No private declaration name or changed checker API is required. -/
theorem checkFields_eq_readNat_all (n word : Nat) (fields : List Field) :
    checkFields n word fields =
      fields.all (fun field =>
        match readNat (PackedBytes.bytesOfNat n word) field.offset field.width with
        | .ok observed => decide (observed = field.value)
        | .error _ => false) := by
  unfold checkFields
  congr 1
  funext field
  exact checkField_eq_readNat n word field

theorem checkFields_eq_true_iff (n word : Nat) (fields : List Field) :
    checkFields n word fields = true ↔
      ∀ field ∈ fields, field.Holds (PackedBytes.bytesOfNat n word) := by
  simp only [checkFields, List.all_eq_true, checkField_eq_true_iff]

theorem checkFields_sound (n word : Nat) (fields : List Field)
    (checked : checkFields n word fields = true) :
    ∀ field ∈ fields, field.Holds (PackedBytes.bytesOfNat n word) :=
  (checkFields_eq_true_iff n word fields).mp checked

end EDSL.ELF.PackedRead
