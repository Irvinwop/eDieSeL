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
Compiler-local admission for the complete Clang `c_counter_worker` symbol in
the original complete 44240-byte ELF. The table, metadata, function hints and
86-byte proposal below are checked against that file with the original cap 128.
Only the literal requested name is shared with `CounterMixedGraphs`; the named
image and its current resources do not use a compiler-indexed admission root.

The actual same-image manager setup is total for every initial word. Its
ownership, borrowing and atomic gates are retained through the generic image
API. These facts establish modeled admission and present resources, with the
imported protected-resource, coherent scalar RAM, stable translation/no-alias
and represented CPU/CET-off assumptions. They establish no instruction or loop
behavior, progress, physical CPU/OS or compiler refinement, or corpus credit.
-/

namespace EDSL.Corpus.V1.CountedCertificates.ClangAdmission
open X86 OS OS.AddressSpace

/-- Untrusted complete declared extent, retaining the original NOP13 padding. -/
def bytes : List Byte :=
  [0x85,0xf6,0x74,0x51,0x89,0xf1,0x89,0xf0,0x83,0xe1,0x07,
    0x74,0x11,0x31,0xd2,0x90,0xf0,0x48,0xff,0x07,0xff,0xc2,
    0x39,0xd1,0x75,0xf6,0x89,0xf0,0x29,0xd0,0x83,0xfe,0x08,
    0x72,0x32,0x66,0x66,0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0,
    0xf0,0x48,0xff,0x07,0xf0,0x48,0xff,0x07,
    0xf0,0x48,0xff,0x07,0xf0,0x48,0xff,0x07,
    0xf0,0x48,0xff,0x07,0xf0,0x48,0xff,0x07,
    0xf0,0x48,0xff,0x07,0xf0,0x48,0xff,0x07,
    0x83,0xc0,0xf8,0x75,0xdb,0xc3]

/-- Untrusted symbol, section and file-window hints from the original table. -/
def function : ELF.FunctionSymbol.Function := {
  occurrence := { table := 26, index := 111, symbol := {
    nameOffset := 1823, info := 18, other := 0, sh := 13, value := 4201344, size := 86 } }
  sh := Clang.sh13
  window := { address := 4201344, offset := 7040 } }

/-- Direct compiler-local data; the complete original file remains external. -/
def input : ELF.FunctionInput := {
  table := Clang.table
  metadata := Clang.metadata
  function := function
  bytes := bytes }

/-- Normalize byte reads from the original complete file, including absence
past its end, using only this compiler's file-tail and length evidence. -/
private theorem fileByte (offset : Nat) :
    Clang.file[offset]? = if offset < 44240 then
      (((Clang.chunks.drop (offset / 128)).flatten).drop (offset % 128))[0]? else none := by
  by_cases inside : offset < 44240
  · rw [ite_eq_left inside]
    have dropped := congrArg (fun source : List Byte => source[0]?)
      (Clang.fileDropAt offset (by omega))
    simpa only [List.getElem?_drop, Nat.add_zero] using dropped
  · rw [ite_eq_right inside]
    exact List.getElem?_eq_none (by rw [Clang.fileLength]; omega)

/-- Authenticate the exact name, whole extent, original layout and all bytes
against the complete file, using the production explicit-cap checker. -/
theorem checked : input.checkWith 128 Clang.file CounterMixedGraphs.name = true := by
  change ELF.FunctionSymbol.checkWith 128 Clang.file Clang.table Clang.metadata
    CounterMixedGraphs.name function bytes = true
  unfold ELF.FunctionSymbol.checkWith
  rw [Clang.metadataAccepted]
  unfold ELF.FunctionWindow.checkWith
  have offset : function.window.offset = 7040 := rfl
  rw [Clang.layoutAccepted, offset, Clang.fileDropAt 7040 (by decide +kernel)]
  simp only [Clang.fileLength, ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
    ELF.install, ELF.segmentCell, fileByte]
  decide +kernel

/-- The provider retains the original complete file, requested name and cap. -/
def named : Counted.NamedImage Clang.file CounterMixedGraphs.name 128 where
  input := input
  checked := checked

/-- Expose the exact callable image independently of compiler dispatchers. -/
theorem image_eq : named.image = (⟨4201344, bytes⟩ : ScalarCall64.Image) := rfl

/-- Every executable segment in this original program table is exactly RX. -/
theorem rx : CountedResources.Image.RX named := by
  change ∀ segment ∈ Clang.table.image.segments,
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
#print axioms fileByte
#print axioms checked
#print axioms named
#print axioms image_eq
#print axioms rx
#print axioms total
#print axioms resources

end EDSL.Corpus.V1.CountedCertificates.ClangAdmission
#audit_edsl
