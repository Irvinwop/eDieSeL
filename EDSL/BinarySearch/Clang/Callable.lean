/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.BinarySearch.Clang.NamedELFProperties
import EDSL.BinarySearch.Clang.SortedSingleton
import EDSL.BinarySearch.Clang.Resources
import EDSL.BufferCall.ELFTransport

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.BinarySearch.Clang.Callable
open X86 X86.Sequential OS OS.AddressSpace BufferCall Corpus

attribute [local irreducible] SortedSingleton.ready V1.ByteScanResources.ready

/-- The two named functions were selected from the same complete installed file. -/
theorem installed_same :
    BufferResources.installed NamedELF.file NamedELF.input =
      V1.ByteScanResources.installed SortedSingleton.compiler := rfl

/-- A faster cell view, proved equal to the entire existing resource space.
Both original qwords and all other installed cells and permissions are retained. -/
def fastSpace : Space :=
  BufferResources.freshQWord
    (BufferResources.freshQWord (BufferResources.programSpace NamedELF.file NamedELF.input)
      SortedSingleton.layout.stack SortedSingleton.layout.returnAddress) SortedSingleton.value.base 0x4241

theorem fastSpace_eq : fastSpace = SortedSingleton.resources.shared.resources.space := by
  rw [SortedSingleton.space, V1.ByteScanResources.space]
  unfold fastSpace V1.ByteScanResources.spaceView
  rw [V1.ByteScanResources.programSpace_eq,
    BufferResources.programSpace_eqWith NamedELF.checked64 NamedELF.executable_permissions,
    installed_same]
  rfl

/-- Reindex only via the proved full-space equality; no new world is seeded. -/
def before : BufferResources.Managed :=
  ReadOnlyResources.reindex SortedSingleton.ready.managed fastSpace fastSpace_eq

theorem same : before.shared = SortedSingleton.resources.shared :=
  ReadOnlyResources.reindex_shared SortedSingleton.ready.managed fastSpace fastSpace_eq

/-- Actual checked adoption and shared read loan of the complete 58-byte code.
The original caller and the already-issued four-byte input loan are not replaced. -/
def setup : Except Borrowing.Fault
    (ReadOnlyCalls.Attached before SortedSingleton.resources.call.worker
      ⟨NamedELF.input.function.window.base, NamedELF.input.bytes.length⟩ []) :=
  ReadOnlyCalls.attach before SortedSingleton.layout.codeOwner SortedSingleton.resources.call.worker
    ⟨NamedELF.input.function.window.base, NamedELF.input.bytes.length⟩ []

theorem setup_total : setup.toOption.isSome = true := by
  buffer_resource_kernel_rfl

def attached : ReadOnlyCalls.Attached before SortedSingleton.resources.call.worker
    ⟨NamedELF.input.function.window.base, NamedELF.input.bytes.length⟩ [] :=
  setup.toOption.get setup_total

attribute [local irreducible] attached

theorem attach_checked :
    ReadOnlyCalls.attach before SortedSingleton.layout.codeOwner SortedSingleton.resources.call.worker
      ⟨NamedELF.input.function.window.base, NamedELF.input.bytes.length⟩ [] = .ok attached := by
  buffer_resource_kernel_rfl

/-- Every original installed cell, including unrelated data and permission bits. -/
theorem retainedImage (address : Word) (cell : AddressSpace.Cell)
    (existing : (BufferResources.installed NamedELF.file NamedELF.input).space.cells address = some cell) :
    SortedSingleton.resources.shared.resources.space.cells address = some cell := by
  rw [installed_same] at existing
  exact SortedSingleton.installed_frame existing

/-- Independent universal semantics plus authentic named bytes and useful present
resources, in the original manager and interpreter. No future run is assumed. -/
def certificate : ELFCertificate BinarySearch.spec NamedELF.file NamedELF.name 64 :=
  ELFCertificate.ofRetargetInstalledWith 64 NamedELF.input NamedELF.checked64 Clang.semantics
    NamedELF.executable_permissions (SortedSingleton.pre (fun _ => 0) 0x202 0x4241 rfl)
    same attached retainedImage SortedSingleton.useful

end EDSL.BinarySearch.Clang.Callable
