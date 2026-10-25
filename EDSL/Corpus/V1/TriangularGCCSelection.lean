/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionSelection
import EDSL.Corpus.V1.GCC

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

/-! Data-only authentication of the complete unchanged GCC ELF and complete
named function. The row and section are untrusted hints until `checked`.
This module establishes no execution, compiler or native-loader claim. -/

namespace EDSL.Corpus.V1.TriangularGCCSelection
open X86 ELF.FunctionSymbol

abbrev file := GCC.file

/-- Exact name bytes, excluding the terminating NUL. -/
def name : List Byte := [99,95,116,114,105,97,110,103,117,108,97,114,95,109,111,100,54,52]

/-- The whole declared 60-byte extent, including both padding instructions and
all three returns. These literals are independently extracted from the ELF. -/
def bytes : List Byte := [
  0xf3,0x0f,0x1e,0xfa,0x85,0xff,0x74,0x30,0x89,0xff,0x31,0xc0,
  0x48,0x8d,0x57,0xff,0x40,0xf6,0xc7,0x01,0x74,0x12,0x48,0x89,
  0xf8,0x48,0x89,0xd7,0x48,0x85,0xd2,0x74,0x1a,0x0f,0x1f,0x80,
  0x00,0x00,0x00,0x00,0x48,0x8d,0x44,0x78,0xff,0x48,0x83,0xef,
  0x02,0x75,0xf5,0xc3,0x0f,0x1f,0x40,0x00,0x31,0xc0,0xc3,0xc3]

/-- Static table row 104 and section 14 suggest VA 0x402ec0, file offset
11968 and size 60. The production checker independently authenticates them. -/
def symbolIndex : Fin GCC.symbols27.rows.length := ⟨104, by decide +kernel⟩

def function : Function :=
  ELF.FunctionSelection.function GCC.symbols27 GCC.sh14 symbolIndex

def input : ELF.FunctionInput :=
  ELF.FunctionSelection.input GCC.table GCC.metadata GCC.symbols27 GCC.sh14
    symbolIndex bytes

/-- Whole-file metadata, unique exact name, complete symbol extent, executable
section/LOAD mapping and installed code, under the unchanged default bounds.
Public chunk normalization avoids traversing unrelated preceding file bytes. -/
theorem checked : input.check file name = true := by
  change check GCC.file GCC.table GCC.metadata name function bytes = true
  unfold check
  rw [GCC.metadataAccepted]
  unfold ELF.FunctionWindow.check
  have bounded : function.window.offset ≤ 41016 := by decide +kernel
  rw [GCC.layoutAccepted, GCC.fileDropChunks _ bounded]
  simp only [GCC.fileLength, ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
    ELF.install, ELF.segmentCell, GCC.fileByteChunks]
  decide +kernel

#print axioms checked
end EDSL.Corpus.V1.TriangularGCCSelection
