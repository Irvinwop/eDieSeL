/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
/- Current-resource preparation only. No behavior of the old ByteScan code or
   named binary-search artifact is asserted. -/
import EDSL.BinarySearch.Contract
import EDSL.Corpus.ReadOnlyInputs
import EDSL.Corpus.V1.ByteScanResources

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

run_cmd do
  let options ← Lean.getOptions
  unless options.getBool `autoImplicit true == false &&
      options.getBool `warningAsError false == true &&
      options.getBool `Elab.async true == false &&
      options.get `maxHeartbeats (0 : Nat) == 300000 &&
      options.get `maxRecDepth (0 : Nat) == 128 do
    throwError "Sorted singleton: effective options differ from required profile"
  Lean.logInfo "EFFECTIVE_OPTIONS autoImplicit=false warningAsError=true Elab.async=false maxHeartbeats=300000 maxRecDepth=128"

namespace EDSL.BinarySearch.Clang.SortedSingleton
open X86 X86.Sequential OS OS.AddressSpace BufferCall
open Corpus

abbrev compiler : V1.ByteScanResources.Compiler := .defaultClang
abbrev original := V1.ByteScanResources.resources compiler
abbrev before := (V1.ByteScanResources.ready compiler).managed
abbrev layout := V1.ByteScanResources.layout

/-- A mathematical input chosen independently of any machine result. -/
def value : BinarySearch.Input := ⟨0x10000, [0x4241], 0x4241⟩
def buffer : Buffer := ⟨value.base, Elements.u32Bytes value.values⟩
def request : ReadOnlyInputs.Request := ⟨layout.dataOwner, ⟨2, 0⟩, buffer⟩

/-- Issue exactly four bytes from the existing initialized padded allocation.
No allocation, store, protection change, caller replacement or seed is made. -/
def setup : Except Borrowing.Fault (ReadOnlyInputs.Result before layout.worker [request]) :=
  ReadOnlyInputs.borrow before layout.worker [request]

-- The production borrow is checked by the kernel at the recorded limits.
theorem setup_total : setup.toOption.isSome = true := by
  buffer_resource_kernel_rfl

def ready : ReadOnlyInputs.Result before layout.worker [request] :=
  setup.toOption.get setup_total

-- Keep projection unification symbolic; the kernel still checks every
-- equality against these same actual definitions at the fixed limits.
attribute [local irreducible] V1.ByteScanResources.ready ready

/-- The selected result is the result of the actual checked input borrow. -/
theorem borrow_checked :
    ReadOnlyInputs.borrow before layout.worker [request] = .ok ready := by
  buffer_resource_kernel_rfl

def resources : Resources BinarySearch.spec where
  shared := ready.managed.shared
  call := original.call
  value := value
  inputLoan _ := (ready.identifiers[0]?).getD 0

/-- No resource-space mutation occurs; the original complete loaded space,
stack and padded payload are identical, including every permission bit. -/
theorem space : resources.shared.resources.space = original.shared.resources.space :=
  congrArg Ownership.World.space ready.resources

theorem original_loan {identifier : Nat} {region : Region}
    (held : Threads.HasLoan original.shared layout.worker identifier region) :
    Threads.HasLoan resources.shared layout.worker identifier region :=
  ready.original_loan held

theorem original_loans {identifier : Nat} {loan : Borrowing.Loan}
    (live : original.shared.loans identifier = some loan) :
    resources.shared.loans identifier = some loan :=
  ready.loans identifier loan live

theorem original_resources : resources.shared.resources = original.shared.resources :=
  ready.resources

theorem checked_history : Borrowing.History original.shared resources.shared :=
  ready.history

theorem buffer_held : Threads.HasLoan resources.shared layout.worker
    (resources.inputLoan buffer) buffer.region :=
  ready.held 0 request rfl (by decide +kernel)

/-- The fourth byte comes from the actual initialized padded qword. It is NOT
covered by the old three-byte loan, and authority comes from the new exact loan. -/
theorem snapshot : BufferAt (toMemory resources.shared.resources.space) buffer.base buffer.bytes := by
  rw [space, V1.ByteScanResources.space]
  refine ⟨by decide +kernel, ?_⟩
  intro index byte present
  match index with
  | 0 | 1 | 2 | 3 =>
    simp [buffer, value, Elements.u32Bytes, Elements.dwordBytes] at present
    subst byte
    rfl
  | index + 4 =>
    simp [buffer, value, Elements.u32Bytes, Elements.dwordBytes] at present

theorem installed_frame {address : Word} {cell : AddressSpace.Cell}
    (existing : (V1.ByteScanResources.installed compiler).space.cells address = some cell) :
    resources.shared.resources.space.cells address = some cell := by
  rw [space]
  exact V1.ByteScanResources.installed_frame compiler existing

/-- This is a current sorted-call contract for the old physical code bytes.
No semantic correctness of that old code for binary search is asserted. -/
theorem contract : ResourceContract resources resources.shared := by
  have old := V1.ByteScanResources.contract compiler
  refine ⟨⟨ready.managed.valid, original_loan old.call.codeLoan,
    original_loan old.call.stackLoan, ?_, ?_, old.call.returnCanonical,
    old.call.stackBound, old.call.postStackCanonical⟩, ?_, ?_⟩
  · change CodeAt (toMemory resources.shared.resources.space) original.call.code original.call.bytes
    rw [space]
    exact old.call.code
  · change readWord (toMemory resources.shared.resources.space) original.call.stack =
      .ok original.call.returnAddress
    rw [space]
    exact old.call.stack
  · intro supplied member
    have same : supplied = buffer := by
      change supplied ∈ [buffer] at member
      simpa only [List.mem_singleton] using member
    subst supplied
    exact snapshot
  · intro supplied member _
    have same : supplied = buffer := by
      change supplied ∈ [buffer] at member
      simpa only [List.mem_singleton] using member
    subst supplied
    exact buffer_held

/-- Sortedness follows from singleton mathematics, not execution or a result. -/
theorem domain : BinarySearch.spec.domain value := by
  constructor
  · change 1 < 2^64
    decide +kernel
  · change WordMath.BinarySearch.Sorted (BinarySearch.sequence value) 1
    intro i j before inside
    have same : i = j := by omega
    subst i
    exact Nat.le_refl _

theorem useful : BinarySearch.spec.useful value := by
  change ([0x4241] : List (BitVec 32)) ≠ []
  decide +kernel

def machine (registers : Register → Word) (flags key : Word) : X86.State where
  registers register := match register with
    | .rsp => layout.stack
    | .rdi => value.base
    | .rsi => 1
    | .rdx => key
    | other => registers other
  flags := flags
  rip := original.call.code
  memory := toMemory resources.shared.resources.space

theorem pre (registers : Register → Word) (flags key : Word)
    (keyBound : key.setWidth 32 = value.key) :
    ResourcePre BinarySearch.spec original.call.bytes resources (machine registers flags key) := by
  refine ⟨⟨contract, rfl⟩, rfl, rfl, rfl, domain, ?_⟩
  intro index argument binding
  obtain ⟨index, indexBound⟩ := index
  match index with
  | 0 | 1 =>
    simp [BinarySearch.spec, resources, value] at binding
    subst argument
    rfl
  | 2 =>
    simp [BinarySearch.spec, resources, value] at binding
    subst argument
    exact keyBound
  | index + 3 => simp at binding

/-- Both old code/caller fields are literally the original issued handles.
The new input loan is separate and must never be described as the old3-byte ID. -/
theorem original_call : resources.call = original.call := rfl

/-- The old exact three-byte input handle remains live alongside the new one. -/
theorem original_input_held : Threads.HasLoan resources.shared layout.worker
    (original.inputLoan V1.ByteScanResources.buffer) V1.ByteScanResources.buffer.region :=
  original_loan (V1.ByteScanResources.buffer_held compiler)

/-- Distinct exact extents cannot be the same current loan identifier. This
uses live authority and functional loan lookup, rather than assigned ID values. -/
theorem input_loan_distinct : resources.inputLoan buffer ≠
    original.inputLoan V1.ByteScanResources.buffer := by
  intro same
  obtain ⟨newLoan, newLive, _, newRegion⟩ := buffer_held
  obtain ⟨oldLoan, oldLive, _, oldRegion⟩ := original_input_held
  rw [same] at newLive
  have equal : newLoan = oldLoan := Option.some.inj (newLive.symm.trans oldLive)
  have regions : buffer.region = V1.ByteScanResources.buffer.region := by
    rw [← newRegion, equal, oldRegion]
  have lengths := congrArg Region.length regions
  change 4 = 3 at lengths
  omega

/-- All allocation identities, owners, epochs and next-allocation metadata
are identical, as a consequence of equality of the complete resource world. -/
theorem original_allocation (identifier : Nat) :
    resources.shared.resources.allocations identifier =
      original.shared.resources.allocations identifier := by
  rw [original_resources]

/-- The private original caller allocation remains authorized in this world. -/
theorem caller_authorized :
    Ownership.authorize resources.shared.resources layout.callerOwner ⟨1, 0⟩ =
      .ok ⟨layout.callerOwner, 0, ⟨layout.stack, 8⟩⟩ := by
  rw [original_resources]
  exact (V1.ByteScanResources.caller_abi compiler (fun _ => 0)).2.2.2

/-- The complete original caller slot and return value are read in the current
unchanged memory. No replacement caller is constructed. -/
theorem caller_slot :
    readWord (toMemory resources.shared.resources.space) resources.call.stack =
      .ok resources.call.returnAddress := contract.call.stack


/-- Only the low 32 bits of the key are constrained; all other registers and
flags supplied to machine are unrestricted by the current precondition. -/
theorem arbitrary_upper_key (registers : Register → Word) (flags : Word)
    (upper : BitVec 32) :
    ResourcePre BinarySearch.spec original.call.bytes resources
      (machine registers flags (upper ++ value.key)) := by
  apply pre
  exact BitVec.setWidth_append_eq_right

/-- A concrete useful current state exists, without an execution hypothesis. -/
theorem useful_current : ∃ initial : X86.State,
    BinarySearch.spec.useful resources.value ∧
      ResourcePre BinarySearch.spec original.call.bytes resources initial :=
  ⟨machine (fun _ => 0) 0x202 (BitVec.ofNat 64 0x4241), useful,
    pre (fun _ => 0) 0x202 (BitVec.ofNat 64 0x4241) rfl⟩

end EDSL.BinarySearch.Clang.SortedSingleton

#print axioms EDSL.BinarySearch.Clang.SortedSingleton.setup_total
#print axioms EDSL.BinarySearch.Clang.SortedSingleton.snapshot
#print axioms EDSL.BinarySearch.Clang.SortedSingleton.contract
#print axioms EDSL.BinarySearch.Clang.SortedSingleton.pre
#audit_edsl

#print axioms EDSL.BinarySearch.Clang.SortedSingleton.input_loan_distinct
#print axioms EDSL.BinarySearch.Clang.SortedSingleton.arbitrary_upper_key
#print axioms EDSL.BinarySearch.Clang.SortedSingleton.useful_current

#print axioms EDSL.BinarySearch.Clang.SortedSingleton.borrow_checked
