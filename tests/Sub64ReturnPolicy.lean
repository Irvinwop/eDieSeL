/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Sub64
import EDSL.OS.CallResources.Domain
import EDSL.Audit
import tests.Support.ExceptDecidable

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.Sub64ReturnPolicy
open X86 X86.Sequential OS OS.AddressSpace OS.CallResources
open scoped EDSL.Tests.Support

/- The original caller slot is [0x2008,0x2010). Its neighbor at 0x2000
contains duplicate bytes but is never included in the declared caller loan.
The false case retains mapped contents with OS read permission denied. -/
def unbalancedBytes : List Byte := [0x48,0x83,0xec,8,0xc3]
def balancedBytes : List Byte := [0x48,0x83,0xec,8,0x48,0x83,0xc4,8,0xc3]

def supplied (code : List Byte) (readableReplacement : Bool) : Space where
  cells address :=
    if (⟨0x1000,code.length⟩ : Region).Contains address then
      (code[address.toNat - 0x1000]?).map fun byte => ⟨byte,readExecute⟩
    else if (⟨0x2008,8⟩ : Region).Contains address then
      some ⟨(0x3000 : Word).extractLsb' ((address.toNat - 0x2008) * 8) 8,readOnly⟩
    else if (⟨0x2000,8⟩ : Region).Contains address then
      some ⟨(0x3000 : Word).extractLsb' ((address.toNat - 0x2000) * 8) 8,
        if readableReplacement then readOnly else inaccessible⟩
    else none

def declared (code : List Byte) (readableReplacement : Bool) : Domain.Initial :=
  ⟨supplied code readableReplacement,17,29,41,0x1000,code,0x2008,0x3000⟩

private theorem unbalanced_ready (readableReplacement : Bool) :
    Domain.check (declared unbalancedBytes readableReplacement) = true := by
  cases readableReplacement <;> decide +kernel

private theorem balanced_ready : Domain.check (declared balancedBytes false) = true := by
  decide +kernel

private theorem decode_current {code : List Byte} {readableReplacement : Bool}
    {state : State} {instruction : Sequential.Instruction}
    (current : Current (Domain.call (declared code readableReplacement))
      (Domain.shared (declared code readableReplacement)) state)
    (size : code.length ≤ 64) (offset : Nat) (inside : offset < code.length)
    (pc : state.rip = 0x1000 + BitVec.ofNat 64 offset)
    (decoded : Sequential.decodeAt (codeState code offset) = .ok instruction) :
    Sequential.decodeAt state = .ok instruction := by
  have codeAt : CodeAt state.memory 0x1000 code := by
    rw [current.coupled]
    exact current.contract.code
  exact decodeAt_transport (code_fetch_transport codeAt size offset inside state rfl pc) decoded

private theorem lowered_rsp (code : List Byte) (readableReplacement : Bool)
    (registers : Register → Word) (flags : Word) :
    (sub64State (Domain.machine (declared code readableReplacement) registers flags)
      .rsp 8 4).registers .rsp = 0x2000 := by
  change (Domain.machine (declared code readableReplacement) registers flags).registers .rsp - 8 = _
  have original : (Domain.machine (declared code readableReplacement) registers flags).registers .rsp =
      0x2008 := by simp only [Domain.machine,declared,↓reduceIte]
  rw [original]
  decide +kernel

private theorem lowered_pc (code : List Byte) (readableReplacement : Bool)
    (registers : Register → Word) (flags : Word) :
    (sub64State (Domain.machine (declared code readableReplacement) registers flags)
      .rsp 8 4).rip = 0x1004 := by
  rw [(sub64State_contract _ .rsp 8 4).nextPC]
  change (0x1000 : Word) + 4 = 0x1004
  decide +kernel

private theorem execute_ret_read {state : State} {address target : Word}
    (stack : state.registers .rsp = address)
    (loaded : readWord state.memory address = .ok target)
    (canonicalTarget : canonical target = true) (choice : Bool) :
    execute state (.legacy .ret) choice =
      .ok ⟨.returned (returnAfter state target),[⟨.stack,address,8⟩]⟩ := by
  simp [execute,X86.executeInstruction,X86.executeRet,Sequential.Instruction.operandReads,
    stack,loaded,canonicalTarget,returnAfter]

private theorem execute_ret_fault {state : State} {address : Word} {fault : Error}
    (stack : state.registers .rsp = address)
    (loaded : readWord state.memory address = .error fault) (choice : Bool) :
    execute state (.legacy .ret) choice = .error fault := by
  simp [execute,X86.executeInstruction,X86.executeRet,stack,loaded]

private def addEightState (state : State) : State :=
  { state.writeRegister .rsp (state.registers .rsp + 8) with
    rip := state.rip + 4
    flags := addFlags64 state.flags (state.registers .rsp) 8 }

private def balancedBefore (registers : Register → Word) (flags : Word) : State :=
  Domain.machine (declared balancedBytes false) registers flags

private def balancedLowered (registers : Register → Word) (flags : Word) : State :=
  sub64State (balancedBefore registers flags) .rsp 8 4

private def balancedRestored (registers : Register → Word) (flags : Word) : State :=
  addEightState (balancedLowered registers flags)

private theorem execute_add_eight (state : State) (choice : FlagChoices) :
    executeWith state (.addImm64 .rsp 8) choice =
      .ok ⟨.next (addEightState state),[]⟩ := by
  rw [executeWith_eq_execute state (.addImm64 .rsp 8) choice rfl]
  rfl

private theorem current_ret_stepWith {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.legacy .ret))
    (stack : before.registers .rsp = call.stack) (choice : FlagChoices) :
    stepWith choice before = .ok ⟨.returned (returnAfter before call.returnAddress),
      [⟨.stack,call.stack,8⟩]⟩ ∧
    Current call shared (returnAfter before call.returnAddress) ∧
    ReadAllowed call shared ⟨.stack,call.stack,8⟩ ∧
    OperandReadSucceeds before ⟨.stack,call.stack,8⟩ := by
  obtain ⟨actual,kept,allowed,read⟩ := current_ret_step current decoded stack false
  refine ⟨?_,kept,allowed,read⟩
  rw [stepWith_eq_executeWith choice decoded]
  change execute before (.legacy .ret) false = _
  rw [← step_eq_execute false decoded]
  exact actual

private theorem run_three_return {choices : ChoiceStream FlagChoices}
    {before lowered restored final : State} {reads : List Read}
    (first : stepWith (choices 0) before = .ok ⟨.next lowered,[]⟩)
    (second : stepWith (choices 1) lowered = .ok ⟨.next restored,[]⟩)
    (third : stepWith (choices 2) restored = .ok ⟨.returned final,reads⟩) :
    runWith choices 3 before = .ok ⟨final,3,reads⟩ := by
  have execution : ExecutesWith choices before ⟨final,3,reads⟩ :=
    Engine.Executes.next first (Engine.Executes.next second (Engine.Executes.ret third))
  exact Engine.run_complete stepWith execution (Nat.le_refl 3)

private theorem current_sub_state {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.subImm64 .rsp 8)) (choice : FlagChoices) :
    Current call shared (sub64State before .rsp 8 4) := by
  obtain ⟨after,actual,kept,_⟩ := current_subImm64_stepWith current decoded choice
  rw [stepWith_eq_executeWith choice decoded,executeWith_subImm64] at actual
  have same : sub64State before .rsp 8 4 = after :=
    StepResult.next.inj (congrArg Observation.result (Except.ok.inj actual))
  rw [same]
  exact kept

/-- In a nonempty admitted OS world, SUB RSP,8 preserves all original
resources in that very same world. Its changed RSP has neither the original
caller read permission nor the original exact-region stack loan. -/
theorem original_world_survives_without_replacement_authority
    (readableReplacement : Bool) (registers : Register → Word) (flags : Word)
    (choice : FlagChoices) :
    let declaration := declared unbalancedBytes readableReplacement
    let before := Domain.machine declaration registers flags
    ∃ after, stepWith choice before = .ok ⟨.next after,[]⟩ ∧
      Current (Domain.call declaration) (Domain.shared declaration) after ∧
      after.registers .rsp = 0x2000 ∧ after.memory = before.memory ∧
      Threads.HasLoan (Domain.shared declaration) 41 0 ⟨0x1000,unbalancedBytes.length⟩ ∧
      Threads.HasLoan (Domain.shared declaration) 41 1 ⟨0x2008,8⟩ ∧
      readWord after.memory 0x2008 = .ok 0x3000 ∧
      ReadAllowed (Domain.call declaration) (Domain.shared declaration) ⟨.stack,0x2008,8⟩ ∧
      (¬ReadAllowed (Domain.call declaration) (Domain.shared declaration)
        ⟨.stack,after.registers .rsp,8⟩) ∧
      (¬Threads.HasLoan (Domain.shared declaration) 41 1 ⟨after.registers .rsp,8⟩) := by
  let declaration := declared unbalancedBytes readableReplacement
  let before := Domain.machine declaration registers flags
  let after := sub64State before .rsp 8 4
  have current : Current (Domain.call declaration) (Domain.shared declaration) before :=
    Domain.current (Domain.check_sound (unbalanced_ready readableReplacement)) registers flags
  have decoded : Sequential.decodeAt before = .ok (.subImm64 .rsp 8) :=
    decode_current current (by decide) 0 (by decide) (by rfl) (by decide +kernel)
  have actual : stepWith choice before = .ok ⟨.next after,[]⟩ := by
    rw [stepWith_eq_executeWith choice decoded]
    simpa only [show (8 : Byte).signExtend 64 = (8 : Word) from by decide +kernel]
      using executeWith_subImm64 before .rsp 8 choice
  have kept := current_sub_state current decoded choice
  have afterRsp : after.registers .rsp = 0x2000 :=
    lowered_rsp unbalancedBytes readableReplacement registers flags
  have original : readWord after.memory 0x2008 = .ok 0x3000 := by
    rw [kept.coupled]
    exact kept.contract.stack
  refine ⟨after,actual,kept,afterRsp,(sub64State_contract before .rsp 8 4).memory,
    kept.contract.codeLoan,kept.contract.stackLoan,
    original,stackRead_permission kept.contract,?_,?_⟩
  · intro allowed
    have impossible : (0x2000 : Word) = 0x2008 := afterRsp.symm.trans allowed.2.1
    exact (by decide +kernel : (0x2000 : Word) ≠ 0x2008) impossible
  · intro replacementLoan
    obtain ⟨originalLoan,originalLive,_,originalRegion⟩ := kept.contract.stackLoan
    obtain ⟨replacement,replacementLive,_,replacementRegion⟩ := replacementLoan
    have same : replacement = originalLoan :=
      Option.some.inj (replacementLive.symm.trans originalLive)
    have regions : (⟨after.registers .rsp,8⟩ : Region) = ⟨0x2008,8⟩ := by
      apply replacementRegion.symm.trans
      rw [same]
      exact originalRegion
    exact (by decide +kernel : (0x2000 : Word) ≠ 0x2008)
      (afterRsp.symm.trans (congrArg Region.base regions))

/-- Hidden mapped replacement bytes do not satisfy a real RET read. The
original return slot remains usable, but the actual RET faults at 0x2000. -/
theorem inaccessible_replacement_faults (registers : Register → Word) (flags : Word)
    (choices : ChoiceStream FlagChoices) :
    let declaration := declared unbalancedBytes false
    let before := Domain.machine declaration registers flags
    ∃ after, stepWith (choices 0) before = .ok ⟨.next after,[]⟩ ∧
      Current (Domain.call declaration) (Domain.shared declaration) after ∧
      readWord after.memory 0x2008 = .ok 0x3000 ∧
      stepWith (choices 1) after = .error (.inaccessibleStack 0x2000) ∧
      runWith choices 2 before = .error (.inaccessibleStack 0x2000) := by
  let declaration := declared unbalancedBytes false
  let before := Domain.machine declaration registers flags
  let after := sub64State before .rsp 8 4
  have current := Domain.current (Domain.check_sound (unbalanced_ready false)) registers flags
  have decoded : Sequential.decodeAt before = .ok (.subImm64 .rsp 8) :=
    decode_current current (by decide) 0 (by decide) (by rfl) (by decide +kernel)
  have kept := current_sub_state current decoded (choices 0)
  have afterRsp : after.registers .rsp = 0x2000 := lowered_rsp unbalancedBytes false registers flags
  have retDecoded : Sequential.decodeAt after = .ok (.legacy .ret) :=
    decode_current kept (by decide) 4 (by decide)
      (lowered_pc unbalancedBytes false registers flags) (by decide +kernel)
  have first : stepWith (choices 0) before = .ok ⟨.next after,[]⟩ := by
    rw [stepWith_eq_executeWith (choices 0) decoded]
    simpa only [show (8 : Byte).signExtend 64 = (8 : Word) from by decide +kernel]
      using executeWith_subImm64 before .rsp 8 (choices 0)
  have unreadable : readWord after.memory 0x2000 = .error (.inaccessibleStack 0x2000) := by
    rw [(sub64State_contract before .rsp 8 4).memory]
    change readWord (toMemory (supplied unbalancedBytes false)) 0x2000 = _
    decide +kernel
  have second : stepWith (choices 1) after = .error (.inaccessibleStack 0x2000) := by
    rw [stepWith_eq_executeWith (choices 1) retDecoded,
      executeWith_eq_execute after (.legacy .ret) (choices 1) rfl]
    exact execute_ret_fault afterRsp unreadable _
  refine ⟨after,first,kept,?_,second,?_⟩
  · rw [kept.coupled]
    exact kept.contract.stack
  · change Engine.run stepWith choices 2 before = .error (.inaccessibleStack 0x2000)
    rw [Engine.run_next stepWith (fuel := 1) first]
    have tail : Engine.run stepWith (choices.drop 1) 1 after =
        .error (.inaccessibleStack 0x2000) := by
      apply Engine.run_fault stepWith
      simpa only [ChoiceStream.drop,Nat.add_zero] using second
    rw [tail]
    rfl

/-- A readable duplicate even contains the correct target. The machine can
return through it, retaining the same world, but the ACTUAL observed read is
still outside the original-slot caller policy. Numerical target equality
cannot replace that policy or restore the ordinary post-RET RSP. -/
theorem duplicate_returns_but_read_is_forbidden (registers : Register → Word) (flags : Word)
    (choices : ChoiceStream FlagChoices) :
    let declaration := declared unbalancedBytes true
    let before := Domain.machine declaration registers flags
    ∃ after final,
      stepWith (choices 0) before = .ok ⟨.next after,[]⟩ ∧
      Current (Domain.call declaration) (Domain.shared declaration) after ∧
      stepWith (choices 1) after = .ok ⟨.returned final,[⟨.stack,0x2000,8⟩]⟩ ∧
      runWith choices 2 before = .ok ⟨final,2,[⟨.stack,0x2000,8⟩]⟩ ∧
      final.rip = 0x3000 ∧ final.registers .rsp = 0x2008 ∧
      Current (Domain.call declaration) (Domain.shared declaration) final ∧
      final.memory = before.memory ∧
      (¬ReadAllowed (Domain.call declaration) (Domain.shared declaration) ⟨.stack,0x2000,8⟩) := by
  let declaration := declared unbalancedBytes true
  let before := Domain.machine declaration registers flags
  let after := sub64State before .rsp 8 4
  let final := returnAfter after 0x3000
  have current := Domain.current (Domain.check_sound (unbalanced_ready true)) registers flags
  have decoded : Sequential.decodeAt before = .ok (.subImm64 .rsp 8) :=
    decode_current current (by decide) 0 (by decide) (by rfl) (by decide +kernel)
  have first : stepWith (choices 0) before = .ok ⟨.next after,[]⟩ := by
    rw [stepWith_eq_executeWith (choices 0) decoded]
    simpa only [show (8 : Byte).signExtend 64 = (8 : Word) from by decide +kernel]
      using executeWith_subImm64 before .rsp 8 (choices 0)
  have kept := current_sub_state current decoded (choices 0)
  have afterRsp : after.registers .rsp = 0x2000 := lowered_rsp unbalancedBytes true registers flags
  have retDecoded : Sequential.decodeAt after = .ok (.legacy .ret) :=
    decode_current kept (by decide) 4 (by decide)
      (lowered_pc unbalancedBytes true registers flags) (by decide +kernel)
  have loaded : readWord after.memory 0x2000 = .ok 0x3000 := by
    rw [(sub64State_contract before .rsp 8 4).memory]
    change readWord (toMemory (supplied unbalancedBytes true)) 0x2000 = _
    decide +kernel
  have second : stepWith (choices 1) after = .ok ⟨.returned final,[⟨.stack,0x2000,8⟩]⟩ := by
    rw [stepWith_eq_executeWith (choices 1) retDecoded,
      executeWith_eq_execute after (.legacy .ret) (choices 1) rfl]
    exact execute_ret_read afterRsp loaded (by decide +kernel) _
  have execution : ExecutesWith choices before ⟨final,2,[⟨.stack,0x2000,8⟩]⟩ :=
    Engine.Executes.next first (Engine.Executes.ret second)
  have finalRsp : final.registers .rsp = 0x2008 := by
    change after.registers .rsp + 8 = 0x2008
    rw [afterRsp]
    decide +kernel
  refine ⟨after,final,first,kept,second,
    Engine.run_complete stepWith execution (Nat.le_refl 2),rfl,finalRsp,kept.sameMemory rfl,
    (sub64State_contract before .rsp 8 4).memory,?_⟩
  intro allowed
  exact (by decide +kernel : (0x2000 : Word) ≠ 0x2008) allowed.2.1

private def graph : CFG.Graph :=
  ⟨[⟨0,.subImm64 .rsp 8,true,1⟩,⟨4,.legacy .ret,false,0⟩],1⟩
private def entry : graph.Index := ⟨0,by decide⟩
private def retNode : graph.Index := ⟨1,by decide⟩

/-- This is rejection by the real generated SUB+RET WP with the OS caller
read predicate, despite fully authenticated code and a physically successful
return. The independent postcondition is True, so it cannot cause rejection. -/
theorem duplicate_caller_policy_rejected (registers : Register → Word) (flags : Word) :
    let declaration := declared unbalancedBytes true
    let before := Domain.machine declaration registers flags
    CFG.Valid unbalancedBytes graph ∧
      ¬X86.VCGen.wp graph 0x1000
        (fun _ read => ReadAllowed (Domain.call declaration) (Domain.shared declaration) read)
        2 entry before (fun _ => True) := by
  let declaration := declared unbalancedBytes true
  let before := Domain.machine declaration registers flags
  let after := sub64State before .rsp 8 4
  have afterRsp : after.registers .rsp = 0x2000 := lowered_rsp unbalancedBytes true registers flags
  have loaded : readWord after.memory 0x2000 = .ok 0x3000 := by
    rw [(sub64State_contract before .rsp 8 4).memory]
    change readWord (toMemory (supplied unbalancedBytes true)) 0x2000 = _
    decide +kernel
  have returned : execute after (.legacy .ret) false =
      .ok ⟨.returned (returnAfter after 0x3000),[⟨.stack,0x2000,8⟩]⟩ :=
    execute_ret_read afterRsp loaded (by decide +kernel) false
  refine ⟨CFG.check_sound (by decide +kernel),?_⟩
  intro vc
  obtain ⟨next,binding,tail⟩ :=
    (X86.VCGen.wp_subImm64_iff graph 0x1000 _ 1 entry _ (fun _ => True) .rsp 8 rfl).mp vc
  have unique : ∀ index : graph.Index,
      (0x1004 : Word) = 0x1000 + BitVec.ofNat 64 (graph.node index).offset → index = retNode := by
    decide +kernel
  have same := unique next binding
  subst next
  have one := tail false
  change (match execute after (.legacy .ret) false with
    | .error _ => False
    | .ok observation =>
      (∀ read ∈ observation.reads,
        ReadAllowed (Domain.call declaration) (Domain.shared declaration) read) ∧
      match observation.result with
      | .returned _ => True
      | .next middle => ∃ destination,
          middle.rip = 0x1000 + BitVec.ofNat 64 (graph.node destination).offset ∧
          X86.VCGen.wp graph 0x1000
            (fun _ read => ReadAllowed (Domain.call declaration) (Domain.shared declaration) read)
            0 destination middle (fun _ => True)
      | .atomic _ _ | .syscall _ => False) at one
  rw [returned] at one
  have forbidden : ReadAllowed (Domain.call (declared unbalancedBytes true))
      (Domain.shared (declared unbalancedBytes true)) ⟨.stack,0x2000,8⟩ :=
    one.1 _ (by simp)
  exact (by decide +kernel : (0x2000 : Word) ≠ 0x2008) forbidden.2.1

private theorem balanced_prefix (registers : Register → Word) (flags : Word)
    (choices : ChoiceStream FlagChoices) :
    let declaration := declared balancedBytes false
    let before := balancedBefore registers flags
    let lowered := balancedLowered registers flags
    let restored := balancedRestored registers flags
    stepWith (choices 0) before = .ok ⟨.next lowered,[]⟩ ∧
      Current (Domain.call declaration) (Domain.shared declaration) lowered ∧
      lowered.registers .rsp = 0x2000 ∧
      stepWith (choices 1) lowered = .ok ⟨.next restored,[]⟩ ∧
      Current (Domain.call declaration) (Domain.shared declaration) restored ∧
      restored.registers .rsp = 0x2008 ∧ restored.rip = 0x1008 ∧
      restored.memory = before.memory := by
  let declaration := declared balancedBytes false
  let before := balancedBefore registers flags
  let lowered := balancedLowered registers flags
  let restored := balancedRestored registers flags
  have current := Domain.current (Domain.check_sound balanced_ready) registers flags
  have subDecoded : Sequential.decodeAt before = .ok (.subImm64 .rsp 8) :=
    decode_current current (by decide) 0 (by decide) (by rfl) (by decide +kernel)
  have first : stepWith (choices 0) before = .ok ⟨.next lowered,[]⟩ := by
    rw [stepWith_eq_executeWith (choices 0) subDecoded]
    exact executeWith_subImm64 before .rsp 8 (choices 0)
  have currentLowered := current_sub_state current subDecoded (choices 0)
  have loweredRsp : lowered.registers .rsp = 0x2000 := lowered_rsp balancedBytes false registers flags
  have addDecoded : Sequential.decodeAt lowered = .ok (.addImm64 .rsp 8) :=
    decode_current currentLowered (by decide) 4 (by decide)
      (lowered_pc balancedBytes false registers flags) (by decide +kernel)
  have second : stepWith (choices 1) lowered = .ok ⟨.next restored,[]⟩ := by
    rw [stepWith_eq_executeWith (choices 1) addDecoded]
    exact execute_add_eight lowered (choices 1)
  have restoredMemory : restored.memory = lowered.memory := rfl
  have currentRestored : Current (Domain.call declaration) (Domain.shared declaration) restored :=
    currentLowered.sameMemory restoredMemory
  have restoredPC : restored.rip = 0x1008 := by
    change lowered.rip + 4 = 0x1008
    have pc : lowered.rip = 0x1004 := lowered_pc balancedBytes false registers flags
    rw [pc]
    decide +kernel
  have restoredRsp : restored.registers .rsp = 0x2008 := by
    change lowered.registers .rsp + 8 = 0x2008
    rw [loweredRsp]
    decide +kernel
  exact ⟨first,currentLowered,loweredRsp,second,currentRestored,restoredRsp,restoredPC,
    restoredMemory.trans (sub64State_contract before .rsp 8 4).memory⟩

private theorem balanced_complete {choices : ChoiceStream FlagChoices}
    {before lowered restored : State}
    (first : stepWith (choices 0) before = .ok ⟨.next lowered,[]⟩)
    (currentLowered : Current (Domain.call (declared balancedBytes false))
      (Domain.shared (declared balancedBytes false)) lowered)
    (loweredRsp : lowered.registers .rsp = 0x2000)
    (second : stepWith (choices 1) lowered = .ok ⟨.next restored,[]⟩)
    (currentRestored : Current (Domain.call (declared balancedBytes false))
      (Domain.shared (declared balancedBytes false)) restored)
    (restoredRsp : restored.registers .rsp = 0x2008)
    (retDecoded : Sequential.decodeAt restored = .ok (.legacy .ret))
    (restoredMemory : restored.memory = before.memory) :
    let declaration := declared balancedBytes false
    ∃ lowered restored final,
      stepWith (choices 0) before = .ok ⟨.next lowered,[]⟩ ∧
      Current (Domain.call declaration) (Domain.shared declaration) lowered ∧
      lowered.registers .rsp = 0x2000 ∧
      stepWith (choices 1) lowered = .ok ⟨.next restored,[]⟩ ∧
      Current (Domain.call declaration) (Domain.shared declaration) restored ∧
      restored.registers .rsp = 0x2008 ∧
      stepWith (choices 2) restored = .ok ⟨.returned final,[⟨.stack,0x2008,8⟩]⟩ ∧
      runWith choices 3 before = .ok ⟨final,3,[⟨.stack,0x2008,8⟩]⟩ ∧
      final.rip = 0x3000 ∧ final.registers .rsp = 0x2010 ∧
      Current (Domain.call declaration) (Domain.shared declaration) final ∧
      final.memory = before.memory ∧
      ReadAllowed (Domain.call declaration) (Domain.shared declaration) ⟨.stack,0x2008,8⟩ ∧
      OperandReadSucceeds restored ⟨.stack,0x2008,8⟩ := by
  let final := returnAfter restored 0x3000
  have returned := current_ret_stepWith currentRestored retDecoded restoredRsp (choices 2)
  have finalRsp : final.registers .rsp = 0x2010 := by
    change restored.registers .rsp + 8 = 0x2010
    rw [restoredRsp]
    decide +kernel
  exact ⟨lowered,restored,final,first,currentLowered,loweredRsp,second,currentRestored,restoredRsp,
    returned.1,run_three_return first second returned.1,rfl,finalRsp,returned.2.1,
    restoredMemory,returned.2.2.1,returned.2.2.2⟩

/-- Balanced SUB/ADD restores the ORIGINAL slot before the actual RET. The
current code/caller resources survive all three instructions, the original
OS read permission is used, and the legitimate post-return RSP is 0x2010. -/
theorem balanced_adjustment_returns (registers : Register → Word) (flags : Word)
    (choices : ChoiceStream FlagChoices) :
    let declaration := declared balancedBytes false
    let before := Domain.machine declaration registers flags
    ∃ lowered restored final,
      stepWith (choices 0) before = .ok ⟨.next lowered,[]⟩ ∧
      Current (Domain.call declaration) (Domain.shared declaration) lowered ∧
      lowered.registers .rsp = 0x2000 ∧
      stepWith (choices 1) lowered = .ok ⟨.next restored,[]⟩ ∧
      Current (Domain.call declaration) (Domain.shared declaration) restored ∧
      restored.registers .rsp = 0x2008 ∧
      stepWith (choices 2) restored = .ok ⟨.returned final,[⟨.stack,0x2008,8⟩]⟩ ∧
      runWith choices 3 before = .ok ⟨final,3,[⟨.stack,0x2008,8⟩]⟩ ∧
      final.rip = 0x3000 ∧ final.registers .rsp = 0x2010 ∧
      Current (Domain.call declaration) (Domain.shared declaration) final ∧
      final.memory = before.memory ∧
      ReadAllowed (Domain.call declaration) (Domain.shared declaration) ⟨.stack,0x2008,8⟩ ∧
      OperandReadSucceeds restored ⟨.stack,0x2008,8⟩ := by
  let restored := balancedRestored registers flags
  have advance := balanced_prefix registers flags choices
  have retDecoded : Sequential.decodeAt restored = .ok (.legacy .ret) :=
    decode_current advance.2.2.2.2.1 (by decide) 8 (by decide) advance.2.2.2.2.2.2.1 (by decide +kernel)
  exact balanced_complete advance.1 advance.2.1 advance.2.2.1 advance.2.2.2.1
    advance.2.2.2.2.1 advance.2.2.2.2.2.1 retDecoded advance.2.2.2.2.2.2.2

end EDSL.Tests.Sub64ReturnPolicy

#print axioms EDSL.Tests.Sub64ReturnPolicy.original_world_survives_without_replacement_authority
#print axioms EDSL.Tests.Sub64ReturnPolicy.inaccessible_replacement_faults
#print axioms EDSL.Tests.Sub64ReturnPolicy.duplicate_returns_but_read_is_forbidden
#print axioms EDSL.Tests.Sub64ReturnPolicy.duplicate_caller_policy_rejected
#print axioms EDSL.Tests.Sub64ReturnPolicy.balanced_adjustment_returns
#audit_edsl
