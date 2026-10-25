/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.TriangularClangResources
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.Corpus.V1.TriangularClangReturn
open X86 X86.Sequential X86.VCGen
open TriangularClangBody

/-- Extract the terminal actual step from the existing checked trace.
This is an induction on proof evidence, not a second instruction executor. -/
private theorem terminal {Allowed : State → Read → Prop}
    {choices : ChoiceStream FlagChoices} {initial : State} {result : Result}
    (trace : CheckedTraceWith Allowed choices initial result) :
    ∃ count before priorReads reads,
      BlockWith choices initial before count priorReads ∧
      stepWith (choices count) before = .ok ⟨.returned result.state,reads⟩ ∧
      result.instructions = count + 1 ∧ result.reads = priorReads ++ reads := by
  induction trace with
  | @ret choices initial final reads actual _allowed =>
    exact ⟨0,initial,[],reads,Engine.Block.nil,actual,rfl,rfl⟩
  | @next choices initial middle reads result actual _allowed _tail induction =>
    obtain ⟨count,before,priorReads,lastReads,block,last,counted,ordered⟩ := induction
    refine ⟨count+1,before,reads++priorReads,lastReads,Engine.Block.next actual block,?_,?_,?_⟩
    · simpa only [ChoiceStream.drop,Nat.add_comm 1 count,Result.prepend] using last
    · change 1 + result.instructions = count + 1 + 1
      omega
    · simp only [Result.prepend,ordered,List.append_assoc]

private theorem returned_ret {before final : State} {choice : FlagChoices}
    {reads : List Read}
    (actual : stepWith choice before = .ok ⟨.returned final,reads⟩) :
    Sequential.decodeAt before = .ok (.legacy .ret) := by
  cases decoded : Sequential.decodeAt before with
  | error fault =>
    simp only [stepWith,decoded,error_bind] at actual
    cases actual
  | ok instruction =>
    have effect : executeWith before instruction choice = .ok ⟨.returned final,reads⟩ := by
      rwa [stepWith_eq_executeWith choice decoded] at actual
    rcases executeWith_effect before instruction choice with single | ⟨after,next,_reads,_memory⟩
    · rw [executeWith_eq_execute before instruction choice single] at effect
      have onlyRet := execute_returned_only_ret effect rfl
      simp only [onlyRet]
    · rw [next] at effect
      cases effect

/-- The last retired instruction is the actual original RET. Every earlier
instruction has no operand read. Its runtime RSP is the original caller RSP,
and its actual readWord returns precisely the admitted canonical return target.
The index is 3 for zero and 11 for every nonzero low32 input. -/
theorem exact_ret (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec bytes input initial) (choices : ChoiceStream FlagChoices) :
    ∃ result before,
      runWith choices 12 initial = .ok result ∧ Observed input initial result ∧
      BlockWith choices initial before (retired input.value - 1) [] ∧
      Sequential.decodeAt before = .ok (.legacy .ret) ∧
      stepWith (choices (retired input.value - 1)) before =
        .ok ⟨.returned result.state,[stackRead initial]⟩ ∧
      before.registers .rsp = initial.registers .rsp ∧ before.memory = initial.memory ∧
      readWord before.memory (before.registers .rsp) = .ok input.returnAddress ∧
      canonical input.returnAddress = true := by
  obtain ⟨result,actual,observed,trace⟩ := executes input initial pre choices
  obtain ⟨count,before,priorReads,reads,block,last,counted,ordered⟩ := terminal trace
  have decoded := returned_ret last
  have effect : executeWith before (.legacy .ret) (choices count) =
      .ok ⟨.returned result.state,reads⟩ := by
    rwa [stepWith_eq_executeWith (choices count) decoded] at last
  have readList : reads = [⟨.stack,before.registers .rsp,8⟩] :=
    executeWith_reads effect
  rw [observed.2.2.2,readList] at ordered
  have prefixLength := congrArg List.length ordered
  simp only [List.length_singleton,List.length_append] at prefixLength
  have prefixNil : priorReads = [] := List.eq_nil_of_length_eq_zero (by omega)
  have readSame : stackRead initial = ⟨.stack,before.registers .rsp,8⟩ := by
    simpa only [prefixNil,List.nil_append,List.singleton_inj] using ordered
  have rsp : before.registers .rsp = initial.registers .rsp :=
    (congrArg Read.address readSame).symm
  have cost := observed.2.2.1
  have countEq : count = retired input.value - 1 := by omega
  obtain ⟨memory,_code,_rest⟩ := block_residualWith valid block pre.code
    (by simp) (generated_vc input initial pre)
  refine ⟨result,before,actual,observed,?_,decoded,?_,rsp,memory,?_,pre.returnCanonical⟩
  · simpa only [countEq,prefixNil] using block
  · simpa only [countEq,readList,←readSame] using last
  · rw [memory,rsp]
    exact pre.stack

#print axioms exact_ret
end EDSL.Corpus.V1.TriangularClangReturn
#audit_edsl
