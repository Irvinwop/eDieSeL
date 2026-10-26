/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.BinarySearch.Clang.Callable

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.BinarySearch.Clang.Callable
open X86 X86.Sequential OS OS.AddressSpace BufferCall Corpus

attribute [local irreducible] SortedSingleton.ready V1.ByteScanResources.ready attached

/-- The useful current call selected by the certificate constructor. -/
def loadedCall : ELFLoadedCall BinarySearch.spec NamedELF.file NamedELF.name NamedELF.input 64 :=
  ELFLoadedCall.retargetInstalledWith NamedELF.checked64 NamedELF.executable_permissions
    (SortedSingleton.pre (fun _ => 0) 0x202 0x4241 rfl) same attached retainedImage

theorem loaded_resource : loadedCall.resource =
    ReadOnlyCallTransport.retarget SortedSingleton.resources NamedELF.input.bytes attached := rfl

/-- The complete current memory and all cell permissions remain identical. -/
theorem original_space : loadedCall.resource.shared.resources.space =
    SortedSingleton.original.shared.resources.space := by
  rw [loaded_resource]
  exact (ReadOnlyCallTransport.retarget_space _ _ attached same).trans SortedSingleton.space

/-- The complete original caller and every existing input identifier survive. -/
theorem original_handles :
    loadedCall.resource.value = SortedSingleton.value ∧
    loadedCall.resource.inputLoan = SortedSingleton.resources.inputLoan ∧
    loadedCall.resource.call.worker = SortedSingleton.original.call.worker ∧
    loadedCall.resource.call.stack = SortedSingleton.original.call.stack ∧
    loadedCall.resource.call.stackLoan = SortedSingleton.original.call.stackLoan ∧
    loadedCall.resource.call.returnAddress = SortedSingleton.original.call.returnAddress := by
  rw [loaded_resource]
  exact ELFCallTransport.handles SortedSingleton.resources NamedELF.input.bytes attached

/-- Every loan from before the sorted input preparation remains live. This
includes original code, caller, and the separate original three-byte input. -/
theorem original_loans {identifier : Nat} {loan : Borrowing.Loan}
    (live : SortedSingleton.original.shared.loans identifier = some loan) :
    loadedCall.resource.shared.loans identifier = some loan := by
  rw [loaded_resource]
  exact ELFCallTransport.loans _ _ attached same (SortedSingleton.original_loans live)

/-- The genuinely new exact four-byte loan is retained, with its original ID. -/
theorem sorted_input_held : Threads.HasLoan loadedCall.resource.shared
    SortedSingleton.layout.worker (SortedSingleton.resources.inputLoan SortedSingleton.buffer)
    SortedSingleton.buffer.region := by
  rw [loaded_resource]
  exact ELFCallTransport.original_loan _ _ attached same SortedSingleton.buffer_held

/-- Existing allocation identities, owners, epochs and extents survive.
The checked attachment may add the selected code allocation. -/
theorem original_allocations {identifier : Nat} {allocation : Ownership.Allocation}
    (live : SortedSingleton.original.shared.resources.allocations identifier = some allocation) :
    loadedCall.resource.shared.resources.allocations identifier = some allocation := by
  rw [loaded_resource]
  apply ELFCallTransport.allocations _ _ attached same
  rw [SortedSingleton.original_resources]
  exact live

/-- Actual manager actions connect the initial and final authority states. -/
theorem original_history : Borrowing.History SortedSingleton.original.shared
    loadedCall.resource.shared := by
  rw [loaded_resource]
  exact ReadOnlyResources.history_trans SortedSingleton.checked_history
    (ELFCallTransport.history _ _ attached same)

/-- All installed bytes and permissions survive, including non-code segments. -/
theorem loaded_image (address : Word) (cell : AddressSpace.Cell)
    (present : (BufferResources.installed NamedELF.file NamedELF.input).space.cells address = some cell) :
    loadedCall.resource.shared.resources.space.cells address = some cell :=
  loadedCall.retainedImage address cell present

/-- Caller-slot contents and the exact original stack loan are retained. -/
theorem original_caller :
    readWord (toMemory loadedCall.resource.shared.resources.space)
      SortedSingleton.original.call.stack = .ok SortedSingleton.original.call.returnAddress ∧
    Threads.HasLoan loadedCall.resource.shared SortedSingleton.original.call.worker
      SortedSingleton.original.call.stackLoan ⟨SortedSingleton.original.call.stack, 8⟩ := by
  rw [loaded_resource]
  exact ELFCallTransport.caller_slot _ _ attached same SortedSingleton.contract

/-- Machine state changes only at RIP; registers, flags and complete RAM are
those of the already useful current call. -/
theorem initial_state : loadedCall.initial =
    { SortedSingleton.machine (fun _ => 0) 0x202 0x4241 with
      rip := NamedELF.input.function.window.base } := rfl

theorem useful : BinarySearch.spec.useful loadedCall.resource.value := SortedSingleton.useful

theorem nonvacuous : Grading.ReadOnlyNonvacuous (readOnlyTask BinarySearch.spec)
    NamedELF.input.bytes := certificate.nonvacuous

/-- Universal behavior and every-prefix read policy for this actual loaded
call, derived from the independently proved full binary-search semantics. -/
theorem execution :
    AllExecutions loadedCall.initial (fun result =>
      Post BinarySearch.spec (resourceInput loadedCall.resource) loadedCall.initial result.state ∧
      Current loadedCall.resource result.state) ∧
    Grading.ReadOnlyPolicy loadedCall.initial (Current loadedCall.resource)
      (fun _ read => ReadAllowed loadedCall.resource read) :=
  certificate.resource loadedCall

end EDSL.BinarySearch.Clang.Callable
