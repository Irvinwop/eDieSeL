/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.TriangularGCCClient

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.Corpus.V1.TriangularGCCClient
open X86 X86.Sequential X86.VCGen
open TriangularGCCGraph TriangularGCCBase

def stackRead (initial : State) : Read := ⟨.stack, initial.registers .rsp, 8⟩

/-- Footprints are the production operandReads of every literal graph node. -/
theorem graph_reads (node : graph.Index) (state : State) :
    (graph.node node).instruction.operandReads state =
      if (graph.node node).instruction = .legacy .ret then
        [⟨.stack, state.registers .rsp, 8⟩] else [] := by
  have membership : (graph.node node).instruction ∈ graph.nodes.map CFG.Node.instruction :=
    List.mem_map_of_mem (List.getElem_mem node.isLt)
  generalize chosen : (graph.node node).instruction = instruction at membership ⊢
  simp only [graph, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- The only operand read of every complete Bool execution is the ordered caller slot. -/
theorem reads_bool {input : PureCall.Invocation spec} {initial : State}
    (pre : PureCall.Pre spec bytes input initial) {choices : Choices} {result : Result}
    (execution : Executes choices initial result) : result.reads = [stackRead initial] := by
  let a := annotations input initial pre
  let cert := a.certificate valid
  have binding : CFG.At bytes graph initial.rip valid.entry initial := by
    exact ⟨pre.code, by simp [valid.entry_offset]⟩
  have admitted : a.Inv valid.entry initial := by
    change initial = initial
    rfl
  have start := cert.ghost_start (entry := valid.entry) valid.entry_cutpoint ⟨binding, admitted⟩
  have walk : ∀ {choices : Choices} {first : State} {result : Result},
      Sequential.Cutpoints.Ghost cert first → Executes choices first result →
      result.reads = [stackRead initial] := by
    intro choices first result ghost trace
    induction trace with
    | ret actual =>
      obtain ⟨source, budget, node, interior⟩ := ghost
      have atNode := (a.machineAnnotations valid).binding source budget node _ interior
      have effect := actual
      rw [valid.step_eq_execute atNode.1 node _ rfl atNode.2] at effect
      have isRet := (valid.returned atNode.1 node atNode.2 actual rfl).1
      have footprint := execute_reads effect
      rw [isRet] at footprint
      dsimp only [Instruction.operandReads] at footprint
      have permission := cert.observed_reads_allowed ⟨source, budget, node, interior⟩ actual
        ⟨.stack, _, 8⟩ (by rw [footprint]; exact List.mem_singleton_self _)
      change PureCall.RawRead initial ⟨.stack, _, 8⟩ at permission
      dsimp only [PureCall.RawRead] at permission
      rw [permission.2.1] at footprint
      exact footprint
    | next actual tail induction =>
      have nextGhost := cert.continues_ghost ghost actual rfl
      obtain ⟨source, budget, node, interior⟩ := ghost
      have atNode := (a.machineAnnotations valid).binding source budget node _ interior
      have effect := actual
      rw [valid.step_eq_execute atNode.1 node _ rfl atNode.2] at effect
      have notRet : (graph.node node).instruction ≠ .legacy .ret := by
        intro same
        obtain ⟨final, impossible⟩ := (CFG.execute_returned_iff
          (valid.nodes node).2.2.1 effect).mpr same
        cases impossible
      have footprint := execute_reads effect
      rw [graph_reads] at footprint
      simp only [notRet, ↓reduceIte] at footprint
      simpa only [Result.prepend, footprint, List.nil_append] using induction nextGhost
    | atomic actual tail induction =>
      obtain ⟨source, budget, node, interior⟩ := ghost
      have atNode := (a.machineAnnotations valid).binding source budget node _ interior
      exact False.elim (valid.no_atomic atNode.1 node atNode.2 actual _ _ rfl)
  exact walk start execution

/-- Complete flag vectors retain the same actual ordered read trace, using proved safety. -/
theorem reads_flags {input : PureCall.Invocation spec} {initial : State}
    (pre : PureCall.Pre spec bytes input initial) {choices : ChoiceStream FlagChoices} {result : Result}
    (execution : ExecutesWith choices initial result) : result.reads = [stackRead initial] := by
  obtain ⟨oldChoices, oldExecution⟩ :=
    (nondet_executesWith_iff initial result (safe input initial pre)).mp ⟨choices, execution⟩
  exact reads_bool pre oldExecution

end EDSL.Corpus.V1.TriangularGCCClient

#print axioms EDSL.Corpus.V1.TriangularGCCClient.reads_bool
#print axioms EDSL.Corpus.V1.TriangularGCCClient.reads_flags
