/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.PackedRead
import EDSL.ELF.FunctionSymbol

namespace PackedReadConsumer

open EDSL EDSL.ELF EDSL.ELF.FunctionWindow EDSL.ELF.FunctionSymbol
open EDSLGrader.Export
open EDSL.ELF.PackedRead

/- This is a synthetic section row, not a valid file or a bounded Section.
The bytes and the numeric specification below are independently written ELF64
little-endian layout examples. No reader or checker constructs the specification.
In particular, the high fields intentionally do not describe a real mapping. -/
def literalLow32 : List X86.Byte := [
  0x78, 0x56, 0x34, 0x12, 0xef, 0xcd, 0xab, 0x90,
  0x10, 0x32, 0x54, 0x76, 0x98, 0xba, 0xdc, 0xfe,
  0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88,
  0x80, 0x70, 0x60, 0x50, 0x40, 0x30, 0x20, 0x10]
def literalHigh32 : List X86.Byte := [
  0x02, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x80,
  0xd4, 0xc3, 0xb2, 0xa1, 0x0d, 0xf0, 0xad, 0x0b,
  0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11,
  0xef, 0xbe, 0xad, 0xde, 0x00, 0x00, 0x00, 0x00]
def literalRow : List X86.Byte := literalLow32 ++ literalHigh32

def expectedSection : Section :=
  ⟨0x12345678, 0x90abcdef, 0xfedcba9876543210, 0x8877665544332211,
    0x1020304050607080, 0x8000000100000002, 0xa1b2c3d4, 0x0badf00d,
    0x1122334455667788, 0xdeadbeef⟩

-- A 52-byte low limb and a 12-byte high limb; no literal exceeds 128 decimal
-- digits. The final four zero bytes are represented by the count, not the word.
def low52 : Nat :=
  56454352537923236241055213931541536415018483308594671687346888461432265688905180251481393801975400451263348688991502183192184
def high12 : Nat := 16045690981384860484
def rowWord : Nat := low52 + (high12 <<< (8 * 52))
def packedRow : List X86.Byte := PackedBytes.bytesOfNat 64 rowWord

-- This body is exactly the original two private checkers' expanded expression.
def originalReads (file : List X86.Byte) (fields : List Field) : Bool :=
  fields.all (fun field =>
    match readNat file field.offset field.width with
    | .ok observed => decide (observed = field.value)
    | .error _ => false)

private theorem literal_length : literalRow.length = 64 := by
  simp only [literalRow, literalLow32, literalHigh32, List.length_append,
    List.length_cons, List.length_nil]

/-- Independent bytes really satisfy all ten original section-field reads. -/
theorem literal_section_reads : originalReads literalRow (expectedSection.fields 0) = true := by
  unfold originalReads
  simp only [readNat, literal_length]
  decide

/-- Exact byte comparison, including the four trailing zeros, not a digest. -/
theorem packed_eq_literal : packedRow = literalRow := by
  have low : PackedBytes.bytesOfNat 32 rowWord = literalLow32 := by decide
  have high : PackedBytes.bytesOfNat 32 (rowWord >>> (8 * 32)) = literalHigh32 := by decide
  change PackedBytes.bytesOfNat (32 + 32) rowWord = literalLow32 ++ literalHigh32
  rw [PackedBytes.split_bytesOfNat, low, high]

theorem readers_agree (offset width : Nat) :
    readNat packedRow offset width = readNat literalRow offset width := by
  rw [packed_eq_literal]

/-- Small closed arithmetic check: this never unfolds a packed byte list. -/
theorem numeric_section_reads : checkFields 64 rowWord (expectedSection.fields 0) = true := by
  decide

/-- Consumer integration accepts the actual old readNat-all expression using
the generic adapter, rather than deciding that byte-list expression again. -/
theorem packed_original_section_reads :
    originalReads packedRow (expectedSection.fields 0) = true := by
  exact (checkFields_eq_readNat_all 64 rowWord (expectedSection.fields 0)).symm.trans
    numeric_section_reads

theorem all_section_fields_held :
    ∀ field ∈ expectedSection.fields 0, field.Holds packedRow :=
  checkFields_sound 64 rowWord (expectedSection.fields 0) numeric_section_reads

/-- This six-byte read straddles the low52/high12 join; its expected value is
specified directly by the byte pattern at offsets 50 through 55. -/
theorem crossing_limb_read :
    readNat literalRow 50 6 = .ok 0x112233445566 ∧
    readNat packedRow 50 6 = .ok 0x112233445566 := by
  constructor
  · simp only [readNat, literal_length]
    rfl
  · simp only [packedRow, readNat_bytesOfNat]
    rfl

theorem width_zero_and_truncation :
    readNat literalRow 64 0 = .ok 0 ∧
    readNat packedRow 64 0 = .ok 0 ∧
    readNat literalRow 65 0 = .error .truncated ∧
    readNat packedRow 65 0 = .error .truncated ∧
    readNat literalRow 60 5 = .error .truncated ∧
    readNat packedRow 60 5 = .error .truncated := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [readNat, literal_length]
    rfl
  · simp only [packedRow, readNat_bytesOfNat]
    rfl
  · simp only [readNat, literal_length]
    rfl
  · simp only [packedRow, readNat_bytesOfNat]
    rfl
  · simp only [readNat, literal_length]
    rfl
  · simp only [packedRow, readNat_bytesOfNat]
    rfl

/-- Removing zero high bytes changes the reader's contract despite leaving
the integer unchanged. The original literal fixture has all four zero bytes. -/
theorem exact_trailing_zero_count :
    readNat literalRow 60 4 = .ok 0 ∧
    readNat packedRow 60 4 = .ok 0 ∧
    readNat (PackedBytes.bytesOfNat 60 rowWord) 60 4 = .error .truncated := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [readNat, literal_length]
    rfl
  · simp only [packedRow, readNat_bytesOfNat]
    rfl
  · rw [readNat_bytesOfNat]
    rfl

/-- The bridge must reduce low digits modulo the requested width even when
the word is larger than the entire recorded byte region. -/
theorem noncanonical_and_empty :
    readNat (PackedBytes.bytesOfNat 1 65537) 0 1 = .ok 1 ∧
    readNat (PackedBytes.bytesOfNat 0 65537) 0 0 = .ok 0 := by
  constructor <;> rw [readNat_bytesOfNat] <;> rfl

def valueMutant : List Field :=
  ({ expectedSection with size := 0x8000000100000003 } : Section).fields 0
def endianMutant : List Field :=
  ({ expectedSection with flags := 0x1032547698badcfe } : Section).fields 0
def widthMutant : List Field :=
  (expectedSection.fields 0).map (fun field =>
    if field.offset = 48 then { field with width := 7 } else field)

/-- A changed high value, reversed byte order, and a seven-byte declaration
for an eight-byte nonzero field each fail through the original consumer. -/
theorem original_consumer_rejects_mutants :
    originalReads packedRow valueMutant = false ∧
    originalReads packedRow endianMutant = false ∧
    originalReads packedRow widthMutant = false := by
  have value : checkFields 64 rowWord valueMutant = false := by decide
  have endian : checkFields 64 rowWord endianMutant = false := by decide
  have width : checkFields 64 rowWord widthMutant = false := by decide
  exact ⟨(checkFields_eq_readNat_all 64 rowWord valueMutant).symm.trans value,
    (checkFields_eq_readNat_all 64 rowWord endianMutant).symm.trans endian,
    (checkFields_eq_readNat_all 64 rowWord widthMutant).symm.trans width⟩

theorem original_literal_rejects_mutants :
    originalReads literalRow valueMutant = false ∧
    originalReads literalRow endianMutant = false ∧
    originalReads literalRow widthMutant = false := by
  unfold originalReads
  simp only [readNat, literal_length]
  decide

/-- Zero-width equality still checks both its bound and its expected value. -/
theorem numeric_bound_and_zero_mutants :
    checkField 64 rowWord ⟨64, 0, 0⟩ = true ∧
    checkField 64 rowWord ⟨65, 0, 0⟩ = false ∧
    checkField 64 rowWord ⟨64, 0, 1⟩ = false ∧
    checkField 64 rowWord ⟨60, 5, 0⟩ = false := by
  decide

end PackedReadConsumer
