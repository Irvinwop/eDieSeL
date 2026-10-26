/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.BinarySearch.Clang.NamedELF

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.BinarySearch.Clang.NamedELF
open X86 ELF.FunctionSymbol OS.AddressSpace

/-- The explicit 64-byte interface is exactly the unchanged default check. -/
theorem checked64 : input.checkWith 64 file name = true := by
  rw [input.checkWith64_eq_check]
  exact checked

theorem symbol_checked :
    check file input.table input.metadata name input.function input.bytes = true := by
  rw [← input.check_eq_symbol]
  exact checked

/-- Full metadata, exact unique symbol contract, all program headers/LOADs,
and the complete file-backed selection; no semantic or resource premise. -/
theorem binding :
    CheckedMetadata file input.table.header input.metadata ∧
    input.function.Contract input.metadata name input.bytes.length ∧
    ELF.FunctionWindow.Layout file input.table ∧
    ELF.FunctionWindow.Selection file input.table.image input.function.window input.bytes :=
  checked_sound symbol_checked

theorem unique_name : input.metadata.matches name = [input.function.occurrence] :=
  binding.2.1.2.2.1

/-- These projections expose the authenticated selection hints for clients.
They do not replace the whole-file `checked` theorem. -/
theorem identity :
    input.function.occurrence.table = 26 ∧ input.function.occurrence.index = 101 ∧
    input.function.occurrence.symbol.nameOffset = 1650 ∧
    input.function.occurrence.symbol.info = 18 ∧ input.function.occurrence.symbol.other = 0 ∧
    input.function.occurrence.symbol.sh = 13 ∧
    input.function.occurrence.symbol.value = 4201072 ∧
    input.function.occurrence.symbol.size = 58 ∧
    input.function.window.address = 4201072 ∧ input.function.window.offset = 6768 ∧
    input.function.window.base = (4201072 : Word) ∧ input.bytes.length = 58 := by
  decide +kernel

theorem file_length : file.length = 44240 := Corpus.V1.Clang.fileLength
theorem bytes_eq : input.bytes = Clang.bytes := rfl
theorem table_eq : input.table = Corpus.V1.Clang.table := rfl
theorem metadata_eq : input.metadata = Corpus.V1.Clang.metadata := rfl
theorem section_eq : input.function.sh = Corpus.V1.Clang.sh13 := rfl

/-- All six selected static-symbol fields hold at the original row in the
complete file. This includes type/binding/visibility and the full extent. -/
theorem symbol_fields :
    ∀ field ∈ input.function.occurrence.symbol.fields
      (Corpus.V1.Clang.symbols26.sh.offset + input.function.occurrence.index * 24),
      field.Holds file := by
  have member : Corpus.V1.Clang.symbols26 ∈ input.metadata.tables := by
    change Corpus.V1.Clang.symbols26 ∈ [Corpus.V1.Clang.symbols05, Corpus.V1.Clang.symbols26]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have row : (input.function.occurrence.symbol, input.function.occurrence.index) ∈
      Corpus.V1.Clang.symbols26.rows.zipIdx := by decide +kernel
  exact (binding.1.tables _ member).2.2 _ row

/-- The defining executable PROGBITS section is the checked original header13. -/
theorem section_fields :
    ∀ field ∈ input.function.sh.fields (input.table.header.sectionOffset + 13 * 64),
      field.Holds file := by
  have member : (input.function.sh, 13) ∈ input.metadata.sections.zipIdx := by decide +kernel
  exact (binding.1.sections _ member).2

theorem source_bytes : (file.drop 6768).take 58 = Clang.bytes := by
  exact binding.2.2.2.source

theorem mapping :
    input.function.window.address = input.function.occurrence.symbol.value ∧
    input.function.occurrence.symbol.size = input.bytes.length ∧
    input.function.sh.kind = 1 ∧ input.function.sh.flags = 6 ∧
    input.function.window.offset = input.function.sh.offset +
      (input.function.occurrence.symbol.value - input.function.sh.address) ∧
    ∃ segment ∈ input.table.image.segments,
      input.function.window.CoveredBy input.bytes.length segment :=
  checked_mapping symbol_checked

theorem executable_permissions :
    ∀ segment ∈ input.table.image.segments,
      segment.permissions.executable = true → segment.permissions = readExecute := by
  decide +kernel

theorem window_checked :
    ELF.FunctionWindow.check file input.table input.function.window input.bytes = true := by
  have accepted := symbol_checked
  unfold check at accepted
  exact (Bool.and_eq_true_iff.mp accepted).2

/-- The same complete byte vector is executable in the modeled installed image.
This does not issue authority, admit a packet, or claim a native installation. -/
theorem installed_code (prior : Space) :
    CodeAt (toMemory (ELF.install file input.table.image prior))
      input.function.window.base input.bytes :=
  ELF.FunctionWindow.checked_code window_checked prior

end EDSL.BinarySearch.Clang.NamedELF
