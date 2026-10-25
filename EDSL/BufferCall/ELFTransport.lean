/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.BufferCall.ELFCertificate
import EDSL.Corpus.ReadOnlyCallTransport

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

/-! Installed-call transport in the existing manager and interpreter. No new
caller, input allocation, authority world, decoder or future execution premise.
The checked attachment changes code authority while preserving all existing
loans, allocations, caller handles, snapshots and the complete current memory. -/

namespace EDSL.BufferCall
open X86 X86.Sequential OS OS.AddressSpace
open Corpus.BufferResources (Managed)

namespace ELFCallTransport
open Corpus.ReadOnlyCallTransport

/-- Exact original caller and buffer identifiers, including unused empty-buffer
IDs. These are constructor identities, not newly issued replacement handles. -/
theorem handles {spec : Spec} (resource : Resources spec) (bytes : List Byte)
    {before : Managed} {entry : Word}
    (attached : Corpus.ReadOnlyCalls.Attached before resource.call.worker
      ⟨entry, bytes.length⟩ []) :
    (retarget resource bytes attached).value = resource.value ∧
    (retarget resource bytes attached).inputLoan = resource.inputLoan ∧
    (retarget resource bytes attached).call.worker = resource.call.worker ∧
    (retarget resource bytes attached).call.stack = resource.call.stack ∧
    (retarget resource bytes attached).call.stackLoan = resource.call.stackLoan ∧
    (retarget resource bytes attached).call.returnAddress = resource.call.returnAddress :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every old live loan survives, even one unrelated to the selected buffers. -/
theorem loans {spec : Spec} (resource : Resources spec) (bytes : List Byte)
    {before : Managed} {entry : Word}
    (attached : Corpus.ReadOnlyCalls.Attached before resource.call.worker
      ⟨entry, bytes.length⟩ []) (same : before.shared = resource.shared)
    {identifier : Nat} {loan : Borrowing.Loan}
    (live : resource.shared.loans identifier = some loan) :
    (retarget resource bytes attached).shared.loans identifier = some loan :=
  attached.loans identifier loan (same.symm ▸ live)

/-- Existing allocation identities are retained in the same authority world. -/
theorem allocations {spec : Spec} (resource : Resources spec) (bytes : List Byte)
    {before : Managed} {entry : Word}
    (attached : Corpus.ReadOnlyCalls.Attached before resource.call.worker
      ⟨entry, bytes.length⟩ []) (same : before.shared = resource.shared)
    {identifier : Nat} {allocation : Ownership.Allocation}
    (live : resource.shared.resources.allocations identifier = some allocation) :
    (retarget resource bytes attached).shared.resources.allocations identifier = some allocation :=
  attached.allocations identifier allocation (same.symm ▸ live)

/-- The actual checked manager history connects the original and final worlds. -/
theorem history {spec : Spec} (resource : Resources spec) (bytes : List Byte)
    {before : Managed} {entry : Word}
    (attached : Corpus.ReadOnlyCalls.Attached before resource.call.worker
      ⟨entry, bytes.length⟩ []) (same : before.shared = resource.shared) :
    Borrowing.History resource.shared (retarget resource bytes attached).shared :=
  same ▸ attached.history

/-- Transport any exact existing loan, without restricting to selected inputs. -/
theorem original_loan {spec : Spec} (resource : Resources spec) (bytes : List Byte)
    {before : Managed} {entry : Word}
    (attached : Corpus.ReadOnlyCalls.Attached before resource.call.worker
      ⟨entry, bytes.length⟩ []) (same : before.shared = resource.shared)
    {identifier : Nat} {region : Region}
    (held : Threads.HasLoan resource.shared resource.call.worker identifier region) :
    Threads.HasLoan (retarget resource bytes attached).shared
      resource.call.worker identifier region :=
  attached.original_loan (same.symm ▸ held)

/-- Custody of the whole installed image survives, including unrelated cells
and their full permissions; there is no projection to executable text. -/
theorem retainedImage {spec : Spec} (resource : Resources spec) (bytes : List Byte)
    {before : Managed} {entry : Word}
    (attached : Corpus.ReadOnlyCalls.Attached before resource.call.worker
      ⟨entry, bytes.length⟩ []) (same : before.shared = resource.shared)
    (image : Space)
    (retained : ∀ address cell, image.cells address = some cell →
      resource.shared.resources.space.cells address = some cell) :
    ∀ address cell, image.cells address = some cell →
      (retarget resource bytes attached).shared.resources.space.cells address = some cell := by
  rw [retarget_space resource bytes attached same]
  exact retained

/-- The actual original caller-slot bytes and EXACT old stack loan survive;
no substitute stack pointer or fresh caller slot is involved. -/
theorem caller_slot {spec : Spec} (resource : Resources spec) (bytes : List Byte)
    {before : Managed} {entry : Word}
    (attached : Corpus.ReadOnlyCalls.Attached before resource.call.worker
      ⟨entry, bytes.length⟩ []) (same : before.shared = resource.shared)
    (contract : ResourceContract resource resource.shared) :
    readWord (toMemory (retarget resource bytes attached).shared.resources.space)
      resource.call.stack = .ok resource.call.returnAddress ∧
    Threads.HasLoan (retarget resource bytes attached).shared resource.call.worker
      resource.call.stackLoan ⟨resource.call.stack, 8⟩ := by
  constructor
  · rw [retarget_space resource bytes attached same]
    exact contract.call.stack
  · exact original_loan resource bytes attached same contract.call.stackLoan

/-- Preserve current snapshots together with each buffer's exact original loan,
without replacing an extent or deriving bytes from a desired program result. -/
theorem inputs {spec : Spec} (resource : Resources spec) (bytes : List Byte)
    {before : Managed} {entry : Word}
    (attached : Corpus.ReadOnlyCalls.Attached before resource.call.worker
      ⟨entry, bytes.length⟩ []) (same : before.shared = resource.shared)
    (contract : ResourceContract resource resource.shared) :
    ∀ buffer ∈ spec.buffers resource.value,
      BufferAt (toMemory (retarget resource bytes attached).shared.resources.space)
        buffer.base buffer.bytes ∧
      (buffer.bytes ≠ [] → Threads.HasLoan (retarget resource bytes attached).shared
        resource.call.worker (resource.inputLoan buffer) buffer.region) := by
  intro buffer member
  constructor
  · rw [retarget_space resource bytes attached same]
    exact contract.buffers buffer member
  · intro nonempty
    exact original_loan resource bytes attached same (contract.inputs buffer member nonempty)

end ELFCallTransport

/-- Join a successful named full-file install to an ALREADY current resource
call. Present code follows from admitted executable bytes and retained text;
retarget_pre supplies current math/arguments/loans. Only RIP changes in the
machine; the original stack slot, return address, input handles and all RAM remain. -/
def ELFLoadedCall.retargetWith {spec : Spec} {file name : List Byte}
    {input : ELF.FunctionInput} {maxBytes : Nat}
    (prior : Space) (loaded : ELF.Loaded)
    (admitted : input.admitWith maxBytes file name prior = .ok loaded)
    {resource : Resources spec} {initial : X86.State} {oldBytes : List Byte}
    (pre : ResourcePre spec oldBytes resource initial)
    {before : Managed} (same : before.shared = resource.shared)
    (attached : Corpus.ReadOnlyCalls.Attached before resource.call.worker
      ⟨input.function.window.base, input.bytes.length⟩ [])
    (text : ELF.FunctionWindow.TextUnchanged (toMemory loaded.space)
      (toMemory resource.shared.resources.space) input.function.window input.bytes.length)
    (retainedImage : ∀ address cell, loaded.space.cells address = some cell →
      resource.shared.resources.space.cells address = some cell) :
    ELFLoadedCall spec file name input maxBytes where
  prior := prior
  loaded := loaded
  admitted := admitted
  resource := Corpus.ReadOnlyCallTransport.retarget resource input.bytes attached
  initial := { initial with rip := input.function.window.base }
  pre := Corpus.ReadOnlyCallTransport.retarget_pre attached same pre
    (ELF.FunctionSymbol.admitted_current_codeWith admitted text)
  entry := rfl
  text := by simpa only [pre.current.coupled] using text
  retainedImage := ELFCallTransport.retainedImage resource input.bytes attached same
    loaded.space retainedImage

/-- A convenient installed-image join. The production successful installation
and current text are derived from the existing checker and ALL retained cells.
The permission premise is explicit; no operation is lowered to weaker semantics. -/
def ELFLoadedCall.retargetInstalledWith {spec : Spec} {file name : List Byte}
    {input : ELF.FunctionInput} {maxBytes : Nat}
    (checked : input.checkWith maxBytes file name = true)
    (permissions : ∀ segment ∈ input.table.image.segments,
      segment.permissions.executable = true → segment.permissions = readExecute)
    {resource : Resources spec} {initial : X86.State} {oldBytes : List Byte}
    (pre : ResourcePre spec oldBytes resource initial)
    {before : Managed} (same : before.shared = resource.shared)
    (attached : Corpus.ReadOnlyCalls.Attached before resource.call.worker
      ⟨input.function.window.base, input.bytes.length⟩ [])
    (retainedImage : ∀ address cell,
      (Corpus.BufferResources.installed file input).space.cells address = some cell →
      resource.shared.resources.space.cells address = some cell) :
    ELFLoadedCall spec file name input maxBytes :=
  retargetWith empty (Corpus.BufferResources.installed file input)
    (Corpus.BufferResources.admittedWith checked) pre same attached
    (Corpus.BufferResources.text_of_retainedWith checked permissions retainedImage) retainedImage

/-- The constructor exposes the existing retarget exactly, so its complete-space,
all-loan, allocation, history and original-handle corollaries apply directly. -/
theorem ELFLoadedCall.retargetWith_resource {spec : Spec} {file name : List Byte}
    {input : ELF.FunctionInput} {maxBytes : Nat}
    (prior : Space) (loaded : ELF.Loaded)
    (admitted : input.admitWith maxBytes file name prior = .ok loaded)
    {resource : Resources spec} {initial : X86.State} {oldBytes : List Byte}
    (pre : ResourcePre spec oldBytes resource initial)
    {before : Managed} (same : before.shared = resource.shared)
    (attached : Corpus.ReadOnlyCalls.Attached before resource.call.worker
      ⟨input.function.window.base, input.bytes.length⟩ [])
    (text : ELF.FunctionWindow.TextUnchanged (toMemory loaded.space)
      (toMemory resource.shared.resources.space) input.function.window input.bytes.length)
    (retainedImage : ∀ address cell, loaded.space.cells address = some cell →
      resource.shared.resources.space.cells address = some cell) :
    (retargetWith prior loaded admitted pre same attached text retainedImage).resource =
      Corpus.ReadOnlyCallTransport.retarget resource input.bytes attached := rfl

/-- Ready for later program instantiation: independent universal semantics,
full named-file checking and useful present resources suffice. No numeral bound
proof, program-specific whole-file solver or assumed successful run is added. -/
def ELFCertificate.ofRetargetInstalledWith (maxBytes : Nat) {spec : Spec}
    {file name : List Byte} (input : ELF.FunctionInput)
    (checked : input.checkWith maxBytes file name = true)
    (semantics : Grading.ReadOnlySemanticClaim (readOnlyTask spec) input.bytes)
    (permissions : ∀ segment ∈ input.table.image.segments,
      segment.permissions.executable = true → segment.permissions = readExecute)
    {resource : Resources spec} {initial : X86.State} {oldBytes : List Byte}
    (pre : ResourcePre spec oldBytes resource initial)
    {before : Managed} (same : before.shared = resource.shared)
    (attached : Corpus.ReadOnlyCalls.Attached before resource.call.worker
      ⟨input.function.window.base, input.bytes.length⟩ [])
    (retainedImage : ∀ address cell,
      (Corpus.BufferResources.installed file input).space.cells address = some cell →
      resource.shared.resources.space.cells address = some cell)
    (useful : spec.useful resource.value) : ELFCertificate spec file name maxBytes :=
  ofLoadedCallWith maxBytes input checked semantics
    (ELFLoadedCall.retargetInstalledWith checked permissions pre same attached retainedImage) useful

end EDSL.BufferCall
