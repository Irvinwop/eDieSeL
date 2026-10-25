/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionSymbol
import EDSL.ELF.PackedRead
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

namespace EDSL.ELF.PackedMetadata
open X86 FunctionSymbol FunctionWindow EDSLGrader.Export
open PackedRead

private def readerFields (file : List Byte) (fields : List Field) : Bool :=
  fields.all fun field => match readNat file field.offset field.width with
    | .ok observed => decide (observed = field.value)
    | .error _ => false

private theorem fields_accepted (count word : Nat) (fields : List Field)
    (arithmetic : checkFields count word fields = true) :
    readerFields (PackedBytes.bytesOfNat count word) fields = true :=
  (checkFields_eq_readNat_all count word fields).symm.trans arithmetic

private theorem tableFields_accepted (count word base : Nat) (rows : List (List Field))
    (bounded : base ≤ count)
    (arithmetic : ∀ fields ∈ rows,
      checkFields (count - base) (word >>> (8 * base)) fields = true) :
    (decide (base ≤ (PackedBytes.bytesOfNat count word).length) &&
      rows.all (fun fields => readerFields
        ((PackedBytes.bytesOfNat count word).drop base) fields)) = true := by
  rw [PackedBytes.length_bytesOfNat, PackedBytes.drop_bytesOfNat_shift]
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true bounded, List.all_eq_true.mpr ?_⟩
  intro fields member
  exact fields_accepted (count - base) (word >>> (8 * base)) fields
    (arithmetic fields member)

private theorem slice_eq_of_encoding (count word offset width : Nat) (bytes : List Byte)
    (inside : width ≤ count - offset) (length : bytes.length = width)
    (encoding : PackedBytes.natOfBytes bytes = numericValue word offset width) :
    ((PackedBytes.bytesOfNat count word).drop offset).take width = bytes := by
  rw [PackedBytes.slice_bytesOfNat, Nat.min_eq_left inside]
  apply PackedBytes.eq_of_length_eq_of_natOfBytes_eq
  · exact (PackedBytes.length_bytesOfNat width (word >>> (8 * offset))).trans length.symm
  · rw [PackedBytes.natOfBytes_bytesOfNat, encoding]
    unfold numericValue
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_mul]


/-- Arithmetic evidence for a complete symbol table and its entire linked
string table. The shape still includes all symbol names and row restrictions. -/
def SymbolsArithmetic (count word : Nat) (sections : List Section)
    (symbols : Symbols) : Prop :=
  symbols.Shape sections ∧
  symbols.strings.bytes.length ≤ count - symbols.strings.sh.offset ∧
  PackedBytes.natOfBytes symbols.strings.bytes =
    numericValue word symbols.strings.sh.offset symbols.strings.bytes.length ∧
  symbols.sh.offset ≤ count ∧
  (symbols.rows.zipIdx.map fun pair => pair.1.fields (pair.2 * 24)).all
    (checkFields (count - symbols.sh.offset) (word >>> (8 * symbols.sh.offset))) = true

/-- All original metadata obligations, with file reads expressed by counted-word
arithmetic. Every section, every symbol row and all string-table bytes remain
covered. The count retains trailing zero bytes independently of the word. -/
def Arithmetic (count word : Nat) (header : Header) (metadata : Metadata) : Prop :=
  metadata.Shape header ∧
  (∀ pair ∈ metadata.sections.zipIdx, pair.1.Bounded count) ∧
  header.sectionOffset ≤ count ∧
  (metadata.sections.zipIdx.map fun pair => pair.1.fields (pair.2 * 64)).all
    (checkFields (count - header.sectionOffset) (word >>> (8 * header.sectionOffset))) = true ∧
  metadata.names.bytes.length ≤ count - metadata.names.sh.offset ∧
  PackedBytes.natOfBytes metadata.names.bytes =
    numericValue word metadata.names.sh.offset metadata.names.bytes.length ∧
  ∀ symbols ∈ metadata.tables, SymbolsArithmetic count word metadata.sections symbols

/-- Reusable bridge to the existing byte-reader checker. This theorem does not
replace the checker or accept a digest, selected window or supplied proof root. -/
theorem accepted (count word : Nat) (header : Header) (metadata : Metadata)
    (evidence : Arithmetic count word header metadata) :
    checkMetadata (PackedBytes.bytesOfNat count word) header metadata = true := by
  obtain ⟨shape, sectionBounds, sectionBase, sectionFields, namesInside,
    namesEncoding, symbolsEvidence⟩ := evidence
  simp only [checkMetadata, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨shape, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · apply List.all_eq_true.mpr
    intro pair member
    exact decide_eq_true (by
      rw [PackedBytes.length_bytesOfNat]
      exact sectionBounds pair member)
  · exact tableFields_accepted count word header.sectionOffset _ sectionBase
      (List.all_eq_true.mp sectionFields)
  · exact slice_eq_of_encoding count word metadata.names.sh.offset
      metadata.names.bytes.length metadata.names.bytes namesInside rfl namesEncoding
  · apply List.all_eq_true.mpr
    intro symbols member
    obtain ⟨symbolShape, stringsInside, stringsEncoding, symbolBase, symbolFields⟩ :=
      symbolsEvidence symbols member
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨symbolShape, ?_⟩, ?_⟩
    · exact slice_eq_of_encoding count word symbols.strings.sh.offset
        symbols.strings.bytes.length symbols.strings.bytes stringsInside rfl stringsEncoding
    · exact tableFields_accepted count word symbols.sh.offset _ symbolBase
        (List.all_eq_true.mp symbolFields)

/-- The same complete checked metadata contract used by ordinary literal files. -/
theorem checked (count word : Nat) (header : Header) (metadata : Metadata)
    (evidence : Arithmetic count word header metadata) :
    CheckedMetadata (PackedBytes.bytesOfNat count word) header metadata :=
  checkMetadata_sound (accepted count word header metadata evidence)

#print axioms accepted
#print axioms checked
end EDSL.ELF.PackedMetadata
#audit_edsl
