/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.WordResources64.Bridge
import EDSL.Grading.StoreReturnValue64.Domain
import EDSL.Audit

namespace EDSL.Tests.DisplacedDataResources
open EDSL X86 X86.Sequential OS
open EDSL.OS.WordResources64

private def bytes : List Byte := [0x48,0x89,0x77,0xf8,0x48,0x8b,0x67,0xf8]

private theorem decoded {call : Call} {shared : Shared} {machine : State}
    (current : Current call shared machine) (codeBytes : call.bytes = bytes)
    (offset : Nat) (inside : offset < bytes.length)
    (pc : machine.rip = call.code + BitVec.ofNat 64 offset)
    {instruction : Sequential.Instruction}
    (literal : Sequential.decodeAt (codeState bytes offset) = .ok instruction) :
    Sequential.decodeAt machine = .ok instruction := by
  have code : CodeAt machine.memory call.code bytes := by
    rw [current.coupled, ← codeBytes]
    exact current.contract.code
  exact decodeAt_transport (code_fetch_transport code (by decide) offset inside machine rfl pc) literal

/-- Exact displaced bytes in arbitrary current worlds store then read back the
actual OS mutation. The same evolved world retains all permissions, complete
outside frame and original caller loan even when the loaded RSP changes. -/
theorem store_load_rsp {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = bytes)
    (entry : before.rip = call.code)
    (pointer : before.registers .rdi + (0xfffffffffffffff8 : Word) = call.targetPointer)
    (different : before.registers .rsi ≠ call.stack) (afStore afLoad : Bool) :
    ∃ evolved middle final,
      Borrowing.mutate shared (.store64 (Threads.principal call.worker) call.ticket
        call.targetPointer (before.registers .rsi)) = .ok (evolved,none) ∧
      step afStore before = .ok ⟨.next middle,[]⟩ ∧
      step afLoad middle = .ok ⟨.next final,[⟨.data,call.targetPointer,8⟩]⟩ ∧
      final.registers .rsp = before.registers .rsi ∧
      Current call evolved final ∧
      Threads.HasLoan evolved call.worker call.codeLoan ⟨call.code,call.bytes.length⟩ ∧
      Threads.HasLoan evolved call.worker call.stackLoan ⟨call.stack,8⟩ ∧
      readWord final.memory call.stack = .ok call.returnAddress ∧
      ¬ReadAllowed call evolved final ⟨.stack,final.registers .rsp,8⟩ ∧
      Borrowing.StoreEffect64 shared evolved call.targetPointer (before.registers .rsi) := by
  have storeDecoded := decoded current codeBytes 0 (by decide) (by simpa using entry)
    (instruction := .storeMem64 (.baseDisp8 .rdi 0xf8) .rsi) (by cbv)
  have intent : Sequential.Instruction.storeIntent64
      (.storeMem64 (.baseDisp8 .rdi 0xf8) .rsi) before =
      some (call.targetPointer,before.registers .rsi) := by
    change some (before.registers .rdi + (0xfffffffffffffff8 : Word),before.registers .rsi) = _
    rw [pointer]
  obtain ⟨evolved,stored,actualStore,currentMiddle,effect,_⟩ :=
    current_store64_step current storeDecoded intent afStore
  let middle := storeAfterLength before evolved 4
  change step afStore before = .ok ⟨.next middle,[]⟩ at actualStore
  change Current call evolved middle at currentMiddle
  have middlePC : middle.rip = call.code + 4 := by simp [middle,storeAfterLength,entry]
  have loadDecoded := decoded currentMiddle codeBytes 4 (by decide) middlePC
    (instruction := .loadMem64 .rsp (.baseDisp8 .rdi 0xf8)) (by cbv)
  have effective : (Address.baseDisp8 .rdi 0xf8).eval middle = call.targetPointer := pointer
  obtain ⟨value,final,actualLoad,assigned,observed,_,_,currentFinal,_,_,_,_⟩ :=
    current_load64_step currentMiddle loadDecoded effective afLoad
  have valueEq : value = before.registers .rsi := by
    apply Except.ok.inj
    exact observed.symm.trans (by rw [currentMiddle.coupled]; exact effect.readback)
  have full := assigned.trans valueEq
  refine ⟨evolved,middle,final,stored,actualStore,actualLoad,full,currentFinal,
    currentFinal.contract.codeLoan,currentFinal.contract.stackLoan,?_,?_,effect⟩
  · rw [currentFinal.coupled]
    exact currentFinal.contract.stack
  · intro allowed
    exact different (full.symm.trans allowed.1)

/-- Real current admission supplies a witness for the two-step theorem; the
argument is arbitrary, and all unconstrained registers/flags remain parameters. -/
theorem admitted_store_load (value : Word) (other : Register → Word) (flags : Word)
    (different : value ≠ (65544 : Word)) (afStore afLoad : Bool) :
    ∃ call shared before evolved middle final,
      Current call shared before ∧
      step afStore before = .ok ⟨.next middle,[]⟩ ∧
      step afLoad middle = .ok ⟨.next final,[⟨.data,262144,8⟩]⟩ ∧
      final.registers .rsp = value ∧ Current call evolved final ∧
      Borrowing.StoreEffect64 shared evolved 262144 value ∧
      Threads.HasLoan evolved call.worker call.stackLoan ⟨65544,8⟩ ∧
      readWord final.memory 65544 = .ok 8192 := by
  let initial := Grading.StoreReturnValue64.Domain.initial bytes value other flags
  let before : State := {initial with registers := fun r =>
    if r = .rdi then 262152 else initial.registers r}
  have current : Current (Grading.StoreReturnValue64.Domain.call bytes)
      (Grading.StoreReturnValue64.Domain.shared bytes) before :=
    (Grading.StoreReturnValue64.Domain.arbitrary_current bytes (by decide) (by decide)
      value other flags).1.sameMemory rfl
  obtain ⟨evolved,middle,final,_,store,load,assigned,after,_,stack,slot,_,effect⟩ :=
    store_load_rsp current rfl rfl
      (by change (262152 : Word) + 0xfffffffffffffff8 = 262144; decide)
      different afStore afLoad
  exact ⟨_,_,before,evolved,middle,final,current,store,load,assigned,after,effect,stack,slot⟩

/-- Readable and writable RAM cannot manufacture owner/epoch authority. -/
theorem stale_and_unowned (value : Word) :
    let s := Grading.StoreReturnValue64.Domain.shared bytes
    canStoreQWord (AddressSpace.toMemory s.resources.space) 262144 = true ∧
    Borrowing.mutate s (.store64 11 ⟨4,1⟩ 262144 value) =
      .error (.ownership .staleEpoch) ∧
    Borrowing.mutate s (.store64 12 ⟨4,0⟩ 262144 value) =
      .error (.ownership .wrongOwner) := by
  exact ⟨rfl,rfl,rfl⟩

/-- An actual live read loan blocks writes through the actual Borrowing gate,
although the underlying mapping still permits the machine store. -/
theorem loan_denied (value : Word) :
    let s := Grading.StoreReturnValue64.Domain.shared bytes
    let borrowed := Borrowing.installLoan s ⟨⟨4,0⟩,11,99,⟨262144,8⟩⟩
    Borrowing.readBorrow s 11 ⟨4,0⟩ 99 ⟨262144,8⟩ = .ok (borrowed,4) ∧
    canStoreQWord (AddressSpace.toMemory borrowed.resources.space) 262144 = true ∧
    Borrowing.mutate borrowed (.store64 11 ⟨4,0⟩ 262144 value) = .error .borrowed := by
  exact ⟨rfl,rfl,rfl⟩

/-- A physically readable displaced operand still cannot satisfy the current
owner policy when its caller principal owns no such allocation. -/
theorem readable_unowned_denied :
    let code : List Byte := [0x48,0x8b,0x47,0]
    let shared := Grading.StoreReturnValue64.Domain.shared code
    let before := Grading.StoreReturnValue64.Domain.initial code
    let wrong : Call := {Grading.StoreReturnValue64.Domain.call code with worker := 11}
    loadQWord before.memory 262144 = .ok 0 ∧
      ¬ReadAllowed wrong shared before ⟨.data,262144,8⟩ := by
  refine ⟨rfl,?_⟩
  intro allowed
  obtain ⟨_,_,allocation,_,authorized,_,_⟩ := allowed
  change Except.error Ownership.Fault.wrongOwner = Except.ok allocation at authorized
  cases authorized

end EDSL.Tests.DisplacedDataResources
#print axioms EDSL.Tests.DisplacedDataResources.store_load_rsp
#print axioms EDSL.Tests.DisplacedDataResources.admitted_store_load
#audit_edsl
