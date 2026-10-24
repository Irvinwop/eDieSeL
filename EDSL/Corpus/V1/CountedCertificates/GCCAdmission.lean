/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.CountedResources.Image
import EDSL.Corpus.V1.CounterMixedGraphs

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Compiler-local admission for the complete GCC `c_counter_worker` symbol in
the original complete 41016-byte ELF. The table, metadata, function hints and
49-byte proposal below are checked against that file with the original cap 64.
Only the literal requested name is shared with `CounterMixedGraphs`; the named
image and its current resources do not use a compiler-indexed admission root.

The actual same-image manager setup is total for every initial word. Its
ownership, borrowing and atomic gates are retained through the generic image
API. These facts establish modeled admission and present resources, with the
imported protected-resource, coherent scalar RAM, stable translation/no-alias
and represented CPU/CET-off assumptions. They establish no instruction or loop
behavior, progress, physical CPU/OS or compiler refinement, or corpus credit.
-/

namespace EDSL.Corpus.V1.CountedCertificates.GCCAdmission
open X86 OS OS.AddressSpace

/-- Untrusted complete declared extent, including both original RET bytes. -/
def bytes : List Byte :=
  [0xf3,0x0f,0x1e,0xfa,0x85,0xf6,0x74,0x27,0x8d,0x46,0xff,
    0x40,0xf6,0xc6,0x01,0x74,0x0f,0xf0,0x48,0x83,0x07,0x01,
    0x89,0xc6,0x85,0xc0,0x74,0x14,0x0f,0x1f,0x40,0x00,
    0xf0,0x48,0x83,0x07,0x01,0xf0,0x48,0x83,0x07,0x01,
    0x83,0xee,0x02,0x75,0xf1,0xc3,0xc3]

/-- Untrusted symbol, section and file-window hints from the original table. -/
def function : ELF.FunctionSymbol.Function := {
  occurrence := { table := 27, index := 134, symbol := {
    nameOffset := 2056, info := 18, other := 0, sh := 14, value := 4207440, size := 49 } }
  sh := GCC.sh14
  window := { address := 4207440, offset := 13136 } }

/-- Direct compiler-local data; the complete original file remains external. -/
def input : ELF.FunctionInput := {
  table := GCC.table
  metadata := GCC.metadata
  function := function
  bytes := bytes }

/-- Authenticate the exact name, whole extent, original layout and all bytes
against the complete file, using the production explicit-cap checker. -/
theorem checked : input.checkWith 64 GCC.file CounterMixedGraphs.name = true := by
  change ELF.FunctionSymbol.checkWith 64 GCC.file GCC.table GCC.metadata
    CounterMixedGraphs.name function bytes = true
  unfold ELF.FunctionSymbol.checkWith
  rw [GCC.metadataAccepted]
  unfold ELF.FunctionWindow.checkWith
  have offset : function.window.offset = 13136 := rfl
  rw [GCC.layoutAccepted, offset, GCC.fileDropChunks 13136 (by decide +kernel)]
  simp only [GCC.fileLength, ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
    ELF.install, ELF.segmentCell, GCC.fileByteChunks]
  decide +kernel

/-- The provider retains the original complete file, requested name and cap. -/
def named : Counted.NamedImage GCC.file CounterMixedGraphs.name 64 where
  input := input
  checked := checked

/-- Expose the exact callable image independently of compiler dispatchers. -/
theorem image_eq : named.image = (⟨4207440, bytes⟩ : ScalarCall64.Image) := rfl

/-- Every executable segment in this original program table is exactly RX. -/
theorem rx : CountedResources.Image.RX named := by
  change ∀ segment ∈ GCC.table.image.segments,
    segment.permissions.executable = true → segment.permissions = readExecute
  decide +kernel

/-- Kernel reduction of the actual setup gates, with arbitrary old64. -/
theorem total : CountedResources.Image.Total named := by
  intro old
  buffer_resource_kernel_rfl

/-- Current resources come from the actual total generic manager operation. -/
abbrev resources (old : Word) :
    PlainResources.Ready (CountedResources.Image.programSpace named)
      PlainResources.standard old :=
  CountedResources.Image.resources named total old

#print axioms bytes
#print axioms function
#print axioms input
#print axioms checked
#print axioms named
#print axioms image_eq
#print axioms rx
#print axioms total
#print axioms resources

end EDSL.Corpus.V1.CountedCertificates.GCCAdmission
#audit_edsl
