/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.BinarySearch.Clang.Window
import EDSL.ELF.FunctionSelection
import EDSL.Corpus.V1.ClangLookup

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

/-! Exact named complete-file binding only. This module proves no behavior,
resource witness, attachment, packet admission or source/compiler refinement.
The file, table, metadata and complete code vector are existing public records.
-/
namespace EDSL.BinarySearch.Clang.NamedELF
open X86 ELF.FunctionSymbol

/-- Requested ELF byte name, without its terminating NUL. -/
def name : List Byte :=
  [99,95,98,105,110,97,114,121,95,115,101,97,114,99,104,95,117,51,50]

/-- A selection hint; only `checked` below authenticates it. -/
def symbolIndex : Fin Corpus.V1.Clang.symbols26.rows.length := ⟨101, by decide +kernel⟩

def function : Function :=
  ELF.FunctionSelection.function Corpus.V1.Clang.symbols26 Corpus.V1.Clang.sh13 symbolIndex

def input : ELF.FunctionInput :=
  ELF.FunctionSelection.input Corpus.V1.Clang.table Corpus.V1.Clang.metadata
    Corpus.V1.Clang.symbols26 Corpus.V1.Clang.sh13 symbolIndex Clang.bytes

abbrev file := Corpus.V1.Clang.file

/-- The production default64 checker accepts the original complete file and
unique requested name with all 58 bytes, including its entry prefix and RET.
Whole-file metadata/layout proofs are reused without changing any checker. -/
theorem checked : input.check file name = true := by
  change check Corpus.V1.Clang.file Corpus.V1.Clang.table Corpus.V1.Clang.metadata
    name function Clang.bytes = true
  unfold check
  rw [Corpus.V1.Clang.metadataAccepted]
  unfold ELF.FunctionWindow.check
  have bounded : function.window.offset ≤ 44240 := by decide +kernel
  rw [Corpus.V1.Clang.layoutAccepted, Corpus.V1.Clang.fileDropAt _ bounded]
  simp only [Corpus.V1.Clang.fileLength, ELF.checkCode, X86.fetchByte,
    OS.AddressSpace.toMemory, ELF.install, ELF.segmentCell, Corpus.V1.ClangLookup.fileByte]
  decide +kernel

end EDSL.BinarySearch.Clang.NamedELF
