/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Sub64
import EDSL.Audit
import tests.Support.ExceptDecidable

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.Sub64VectorContinuation
open X86 X86.Sequential
open scoped EDSL.Tests.Support

/- SUB RAX,1; IMUL RAX,RCX; RET. The continuation is vector-only: replacing
it with a Bool continuation loses independent PF/AF/ZF/SF choices. -/
def bytes : List Byte := [0x48,0x83,0xe8,1, 0x48,0x0f,0xaf,0xc1, 0xc3]
def graph : CFG.Graph :=
  ⟨[⟨0,.subImm64 .rax 1,true,2⟩,⟨4,.imulReg64 .rax .rcx,false,1⟩,
    ⟨8,.legacy .ret,false,0⟩],2⟩
def entry : graph.Index := ⟨0,by decide⟩

private def memory : Memory where
  read address :=
    if 0x1000 ≤ address.toNat ∧ address.toNat < 0x1009 then
      bytes[address.toNat - 0x1000]?
    else if 0x2000 ≤ address.toNat ∧ address.toNat < 0x2008 then
      ([0,0x30,0,0,0,0,0,0] : List Byte)[address.toNat - 0x2000]?
    else none
  executable address := decide (0x1000 ≤ address.toNat ∧ address.toNat < 0x1009)

def initial (registers : Register → Word) (flags : Word) : State where
  registers register :=
    if register = .rsp then 0x2000
    else if register = .rax then 7
    else if register = .rcx then 2
    else registers register
  rip := 0x1000
  flags := flags
  memory := memory

private def seed : State := initial (fun _ => 0xfedcba9876543210) 0xad7

private theorem executeWith_ret_read {state : State} {address target : Word}
    (stack : state.registers .rsp = address)
    (loaded : readWord state.memory address = .ok target)
    (canonicalTarget : canonical target = true) (choice : FlagChoices) :
    executeWith state (.legacy .ret) choice =
      .ok ⟨.returned (OS.CallResources.returnAfter state target),[⟨.stack,address,8⟩]⟩ := by
  rw [executeWith_eq_execute state (.legacy .ret) choice rfl]
  simp [execute,X86.executeInstruction,X86.executeRet,Sequential.Instruction.operandReads,
    stack,loaded,canonicalTarget,OS.CallResources.returnAfter]

def Allowed (_ : State) (read : Read) : Prop := read = ⟨.stack,0x2000,8⟩

/-- Independent result of (7 - 1) times 2, the complete return trace and
literal defined CF/OF. No chosen value of any undefined bit is required. -/
def Post (result : Result) : Prop :=
  result.state.registers .rax = 12 ∧ result.state.registers .rsp = 0x2008 ∧
  result.state.rip = 0x3000 ∧ result.instructions = 3 ∧
  result.reads = [⟨.stack,0x2000,8⟩] ∧
  result.state.flags.getLsbD 0 = false ∧ result.state.flags.getLsbD 11 = false ∧
  result.state.flags &&& ~~~arithmeticFlagMask = 0x202

private instance : DecidablePred Post := by
  intro result
  unfold Post
  infer_instance

private instance (contract : X86.VCGen.Contract) [DecidablePred contract] :
    Decidable (X86.VCGen.wpWith graph 0x1000 Allowed 3 entry seed contract) :=
  X86.VCGen.decidableWPWith graph 0x1000 Allowed
    (fun _ read => inferInstanceAs (Decidable (read = ⟨.stack,0x2000,8⟩)))
    3 entry seed contract (fun _ => inferInstance)

/-- Tests the SUB immediate WP with a real vector-only successor, rather
than a RET-only or uniformly chosen continuation. -/
theorem vector_vcg_accepts :
    X86.VCGen.checkChoices graph 0x1000 Allowed 3 entry seed Post = true := by
  decide +kernel

/-- A universal diagonal PF=ZF contract is false. It would pass if a SUB
wrapper accidentally restricted all later choices to one shared Bool. -/
theorem correlated_future_flags_rejected :
    X86.VCGen.checkChoices graph 0x1000 Allowed 3 entry seed
      (fun result => result.state.flags.getLsbD 2 = result.state.flags.getLsbD 6) = false := by
  decide +kernel

theorem authenticated_every_stream (choices : ChoiceStream FlagChoices) :
    ∃ result, runWith choices 3 seed = .ok result ∧ Post result ∧
      result.instructions ≤ 3 ∧ X86.VCGen.CheckedTraceWith Allowed choices seed result := by
  have valid : CFG.Valid bytes graph := CFG.check_sound (by decide +kernel)
  have code : CodeAt seed.memory 0x1000 bytes :=
    ELF.checkCode_sound _ _ _ (by decide +kernel)
  exact X86.VCGen.checked_soundWith (node := entry) valid code rfl vector_vcg_accepts choices

/-- Every full stream, arbitrary scratch registers and incoming flag word.
SUB consumes index zero without using any choice; IMUL uses index one with
four independent bits. Defined CF/OF, every other GPR, nonarithmetic flags,
complete memory, exact retirement and the original stack read are checked.
Expected arithmetic and bit observations do not call a SUB/IMUL helper. -/
theorem arbitrary_choices_and_complete_frame (registers : Register → Word) (flags : Word)
    (choices : ChoiceStream FlagChoices) :
    ∃ result, runWith choices 3 (initial registers flags) = .ok result ∧
      result.state.registers .rax = 12 ∧ result.state.registers .rsp = 0x2008 ∧
      result.state.rip = 0x3000 ∧ result.instructions = 3 ∧
      result.reads = [⟨.stack,0x2000,8⟩] ∧
      result.state.memory = (initial registers flags).memory ∧
      (∀ register, register ≠ .rax → register ≠ .rsp →
        result.state.registers register = (initial registers flags).registers register) ∧
      result.state.flags &&& ~~~arithmeticFlagMask = flags &&& ~~~arithmeticFlagMask ∧
      result.state.flags.getLsbD 0 = false ∧
      result.state.flags.getLsbD 2 = (choices 1).pf ∧
      result.state.flags.getLsbD 4 = (choices 1).af ∧
      result.state.flags.getLsbD 6 = (choices 1).zf ∧
      result.state.flags.getLsbD 7 = (choices 1).sf ∧
      result.state.flags.getLsbD 11 = false := by
  let before := initial registers flags
  let middle := sub64State before .rax 1 4
  let multiplied := imulReg64State middle .rax .rcx (choices 1)
  let final := OS.CallResources.returnAfter multiplied 0x3000
  have valid : CFG.Valid bytes graph := CFG.check_sound (by decide +kernel)
  have code : CodeAt before.memory 0x1000 bytes := by
    change CodeAt memory 0x1000 bytes
    exact ELF.checkCode_sound _ _ _ (by decide +kernel)
  have middleMemory : middle.memory = before.memory :=
    (sub64State_contract before .rax 1 4).memory
  have middlePC : middle.rip = 0x1004 := by
    rw [(sub64State_contract before .rax 1 4).nextPC]
    change (0x1000 : Word) + 4 = 0x1004
    decide +kernel
  have middleRax : middle.registers .rax = 6 := by
    change before.registers .rax - 1 = 6
    have operand : before.registers .rax = 7 := rfl
    rw [operand]
    decide +kernel
  have middleRcx : middle.registers .rcx = 2 := by
    rw [(sub64State_contract before .rax 1 4).registerFrame .rcx (by decide)]
    rfl
  have middleRsp : middle.registers .rsp = 0x2000 := by
    rw [(sub64State_contract before .rax 1 4).registerFrame .rsp (by decide)]
    rfl
  have multipliedMemory : multiplied.memory = before.memory :=
    (imulReg64State_memory middle .rax .rcx (choices 1)).trans middleMemory
  have multipliedPC : multiplied.rip = 0x1008 := by
    rw [imulReg64State_rip,middlePC]
    decide +kernel
  have multipliedRsp : multiplied.registers .rsp = 0x2000 :=
    (imulReg64State_other_register middle .rax .rcx .rsp (choices 1) (by decide)).trans middleRsp
  have product : multiplied.registers .rax = 12 := by
    rw [imulReg64State_destination,middleRax,middleRcx]
    decide +kernel
  have subDecoded : Sequential.decodeAt before = .ok (.subImm64 .rax 1) :=
    valid.decoded code entry before rfl (by rfl)
  have imulDecoded : Sequential.decodeAt middle = .ok (.imulReg64 .rax .rcx) :=
    valid.decoded code ⟨1,by decide⟩ middle middleMemory middlePC
  have retDecoded : Sequential.decodeAt multiplied = .ok (.legacy .ret) :=
    valid.decoded code ⟨2,by decide⟩ multiplied multipliedMemory multipliedPC
  have first : stepWith (choices 0) before = .ok ⟨.next middle,[]⟩ := by
    rw [stepWith_eq_executeWith (choices 0) subDecoded]
    simpa only [show (1 : Byte).signExtend 64 = (1 : Word) from by decide +kernel]
      using executeWith_subImm64 before .rax 1 (choices 0)
  have second : stepWith (choices 1) middle = .ok ⟨.next multiplied,[]⟩ := by
    rw [stepWith_eq_executeWith (choices 1) imulDecoded]
    rfl
  have loaded : readWord multiplied.memory 0x2000 = .ok 0x3000 := by
    rw [multipliedMemory]
    change readWord memory 0x2000 = .ok 0x3000
    decide +kernel
  have third : stepWith (choices 2) multiplied =
      .ok ⟨.returned final,[⟨.stack,0x2000,8⟩]⟩ := by
    rw [stepWith_eq_executeWith (choices 2) retDecoded]
    exact executeWith_ret_read multipliedRsp loaded (by decide +kernel) (choices 2)
  have execution : ExecutesWith choices before ⟨final,3,[⟨.stack,0x2000,8⟩]⟩ :=
    Engine.Executes.next first (Engine.Executes.next second (Engine.Executes.ret third))
  have finalFlags : final.flags = imulFlags64 middle.flags 6 2 (choices 1) := by
    change multiplied.flags = _
    rw [imulReg64State_flags,middleRax,middleRcx]
  have overflow : (6 : Word).smulOverflow 2 = false := by decide +kernel
  have bits : final.flags.getLsbD 0 = false ∧
      final.flags.getLsbD 2 = (choices 1).pf ∧ final.flags.getLsbD 4 = (choices 1).af ∧
      final.flags.getLsbD 6 = (choices 1).zf ∧ final.flags.getLsbD 7 = (choices 1).sf ∧
      final.flags.getLsbD 11 = false := by
    rw [finalFlags]
    simpa only [overflow] using imulFlags64_bits middle.flags 6 2 (choices 1)
  have flagFrame : final.flags &&& ~~~arithmeticFlagMask = flags &&& ~~~arithmeticFlagMask := by
    change multiplied.flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask
    exact (imulReg64State_preserves_flags middle .rax .rcx (choices 1)).trans
      (sub64State_contract before .rax 1 4).flagsFrame
  have finalRax : final.registers .rax = 12 := by
    change multiplied.registers .rax = 12
    exact product
  have finalRsp : final.registers .rsp = 0x2008 := by
    change multiplied.registers .rsp + 8 = 0x2008
    rw [multipliedRsp]
    decide +kernel
  refine ⟨⟨final,3,[⟨.stack,0x2000,8⟩]⟩,
    Engine.run_complete stepWith execution (Nat.le_refl 3),finalRax,finalRsp,rfl,rfl,rfl,
    multipliedMemory,?_,flagFrame,bits⟩
  intro register otherRax otherRsp
  calc
    final.registers register = multiplied.registers register := by
      simp only [final,OS.CallResources.returnAfter,State.writeRegister,ite_eq_right otherRsp]
    _ = middle.registers register :=
      imulReg64State_other_register middle .rax .rcx register (choices 1) otherRax
    _ = before.registers register := (sub64State_contract before .rax 1 4).registerFrame register otherRax

end EDSL.Tests.Sub64VectorContinuation

#print axioms EDSL.Tests.Sub64VectorContinuation.vector_vcg_accepts
#print axioms EDSL.Tests.Sub64VectorContinuation.correlated_future_flags_rejected
#print axioms EDSL.Tests.Sub64VectorContinuation.authenticated_every_stream
#print axioms EDSL.Tests.Sub64VectorContinuation.arbitrary_choices_and_complete_frame
#audit_edsl
