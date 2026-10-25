/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import tests.RexData32Base
import tests.Support.ExceptDecidable
import EDSL.OS.WordResources.Bridge
import EDSL.Grading.Write32.Domain
import EDSL.Grading.Write32.Resources
namespace EDSL.Tests.RexData32Resources
open X86 X86.Sequential OS OS.WordResources
open scoped EDSL.Tests.Support
private def rspCode : List Byte := [0x40,0x8b,0x67,0,0xc3]
-- Actual executable bytes and current resources derive the RSP-changing load.
-- The caller loan remains tied to the original slot, not the loaded machine RSP.
theorem current_rsp {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = rspCode)
    (entry : before.rip = call.code) (pointer : before.registers .rdi = call.targetPointer)
    (af : Bool) :
    ∃ (v : BitVec 32) (after : State),
      Sequential.step af before = .ok ⟨.next after,[⟨.data,call.targetPointer,4⟩]⟩ ∧
      loadDWord before.memory call.targetPointer = .ok v ∧
      after.registers .rsp = v.setWidth 64 ∧ Current call shared after ∧
      (∀ r, r ≠ .rsp → after.registers r = before.registers r) ∧
      after.memory = before.memory ∧ after.flags = before.flags ∧ after.rip = before.rip + 4 ∧
      Threads.HasLoan shared call.worker call.stackLoan ⟨call.stack,8⟩ ∧
      readWord after.memory call.stack = .ok call.returnAddress ∧
      (after.registers .rsp ≠ call.stack →
        ¬Grading.Write32.ReadAllowed call shared after ⟨.stack,after.registers .rsp,8⟩) := by
  have code : CodeAt before.memory call.code rspCode := by
    rw [current.coupled,←codeBytes]
    exact current.contract.code
  have decoded : Sequential.decodeAt before = .ok (.loadMem32Rex .rsp (.baseDisp8 .rdi 0)) :=
    decodeAt_transport (code_fetch_transport code (by decide) 0 (by decide) before rfl
      (by simpa using entry)) (by decide +kernel)
  have effective : (Address.baseDisp8 .rdi 0).eval before = call.targetPointer := by
    simpa [Address.eval] using pointer
  obtain ⟨v,after,actual,assigned,loaded,_,_,next,other,memory,flags,pc⟩ :=
    current_load32Rex_step current decoded effective af
  refine ⟨v,after,actual,loaded,assigned,next,other,memory,flags,pc,
    next.contract.stackLoan,?_,?_⟩
  · rw [next.coupled]
    exact next.contract.stack
  · intro different allowed
    exact different allowed.1

-- A real independently constructed resource world makes the preceding theorem
-- nonvacuous. This also tests that a readable original caller slot survives.
theorem admitted_rsp (af : Bool) :
    ∃ after,
      Sequential.step af (Grading.Write32.Domain.initial rspCode) =
        .ok ⟨.next after,[⟨.data,262144,4⟩]⟩ ∧
      after.registers .rsp = 0 ∧
      Current (Grading.Write32.Domain.call rspCode) (Grading.Write32.Domain.shared rspCode) after ∧
      readWord after.memory 65544 = .ok 8192 ∧
      ¬Grading.Write32.ReadAllowed (Grading.Write32.Domain.call rspCode)
        (Grading.Write32.Domain.shared rspCode) after ⟨.stack,after.registers .rsp,8⟩ := by
  obtain ⟨current,zero,_⟩ := Grading.Write32.Domain.arbitrary_code_current rspCode (by decide) (by decide)
  obtain ⟨v,after,actual,loaded,assigned,next,_,_,_,_,_,stack,denied⟩ :=
    current_rsp current rfl rfl rfl af
  have value : v = 0 := Except.ok.inj (loaded.symm.trans zero)
  have result : after.registers .rsp = 0 := by simpa [value] using assigned
  exact ⟨after,actual,result,next,stack,denied (by simp [result,Grading.Write32.Domain.call])⟩

private def loadCode : List Byte := [0x41,0x8b,6]
private def shared : Shared := Grading.Write32.Domain.shared loadCode
private def call : Call := Grading.Write32.Domain.call loadCode
private def before : State := {Grading.Write32.Domain.initial loadCode with registers := fun r =>
  if r = .r14 then 262144 else (Grading.Write32.Domain.initial loadCode).registers r}
-- Readability and a successful exact machine read cannot manufacture current
-- owner or epoch authority. These are the production ownership/policy gates.
theorem readable_wrong_owner_and_epoch (af : Bool) :
    RexData32.nextView af before (fun f reads => (f.registers .rax,f.rip,f.flags,f.memory,reads)) =
      .ok (0,4099,0x602,before.memory,[⟨.data,262144,4⟩]) ∧
    ¬Grading.Write32.ReadAllowed {call with worker := 11} shared before ⟨.data,262144,4⟩ ∧
    ¬Grading.Write32.ReadAllowed {call with ticket := ⟨4,1⟩} shared before ⟨.data,262144,4⟩ := by
  refine ⟨rfl,?_,?_⟩
  · rintro ⟨_,_,a,_,authorized,_,_⟩
    have denied : Ownership.authorize shared.resources (Threads.principal 11) call.ticket =
        .error .wrongOwner := by rfl
    rw [denied] at authorized
    cases authorized
  · rintro ⟨_,_,a,_,authorized,_,_⟩
    have denied : Ownership.authorize shared.resources (Threads.principal call.worker) ⟨4,1⟩ =
        .error .staleEpoch := by rfl
    rw [denied] at authorized
    cases authorized

private def loan3 : Borrowing.Loan := ⟨⟨4,0⟩,11,11,⟨262144,3⟩⟩
private def loan4 : Borrowing.Loan := ⟨⟨4,0⟩,11,11,⟨262144,4⟩⟩
private def shortLoanWorld : Shared := Borrowing.installLoan shared loan3
private def full : Shared := Borrowing.installLoan shared loan4
private theorem original_outside (i : Nat) (small : i < 4) :
    ¬Borrowing.Subregion ⟨262144,4⟩ (Grading.Domain.loan loadCode i).region := by
  have possibilities : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases possibilities with rfl | rfl | rfl | rfl <;> decide +kernel
-- A real checked three-byte loan does not authorize a four-byte machine read.
theorem partial_loan_denied :
    Borrowing.readBorrow shared 11 ⟨4,0⟩ 11 ⟨262144,3⟩ = .ok (shortLoanWorld,4) ∧
    ¬ArrayResources.ReadPermission shortLoanWorld 10 ⟨.data,262144,4⟩ := by
  refine ⟨rfl,?_⟩
  rintro ⟨i,loan,authorized,fits⟩
  change Borrowing.authorize shortLoanWorld 11 i = .ok loan at authorized
  by_cases small : i < 4
  · have auth : Borrowing.authorize shortLoanWorld 11 i = .ok (Grading.Domain.loan loadCode i) := by
      simp [Borrowing.authorize,shortLoanWorld,Borrowing.installLoan,shared,Grading.Write32.Domain.shared,
        Grading.Domain.shared,small,show i ≠ 4 by omega,Grading.Domain.loan]
    rw [auth] at authorized
    cases authorized
    exact original_outside i small fits
  · by_cases same : i=4
    · subst i
      have auth : Borrowing.authorize shortLoanWorld 11 4 = .ok loan3 := by rfl
      rw [auth] at authorized
      cases authorized
      exact (by decide : ¬Borrowing.Subregion ⟨262144,4⟩ loan3.region) fits
    · have auth : Borrowing.authorize shortLoanWorld 11 i = .error .missingLoan := by
        simp [Borrowing.authorize,shortLoanWorld,Borrowing.installLoan,shared,Grading.Write32.Domain.shared,
          Grading.Domain.shared,small,same]
      rw [auth] at authorized
      cases authorized
-- Completing the same actual loan admits the DATA4 extent; a live loan still
-- blocks exclusive writes through the real Borrowing gate, even same-value stores.
theorem full_loan_and_exclusive_conflict :
    Borrowing.readBorrow shared 11 ⟨4,0⟩ 11 ⟨262144,4⟩ = .ok (full,4) ∧
    ArrayResources.ReadPermission full 10 ⟨.data,262144,4⟩ ∧
    Borrowing.mutate full (.store 11 ⟨4,0⟩ 262144 0) = .error .borrowed := by
  exact ⟨rfl,⟨4,loan4,rfl,by decide⟩,rfl⟩
end EDSL.Tests.RexData32Resources
#audit_edsl
