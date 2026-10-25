/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Core
import EDSL.X86.VCGen.Cutpoints
import EDSL.X86.VCGen.Choices
import EDSL.X86.Sequential.Sub64
import EDSL.X86.Sequential.Sub64Resources
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.VCGen
open Sequential

/-- Reusable pure continuation rule for the existing vector WP. The ordinary
successor, remaining fuel, actual retired instruction and independent Post all
remain obligations. This is not a vector cutpoint-loop VCG. -/
theorem wpWith_pure_next_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (initial final : State) (Post : Contract)
    (effect : ∀ choices, executeWith initial (graph.node node).instruction choices =
      .ok ⟨.next final, []⟩) :
    wpWith graph base AllowedRead (fuel + 1) node initial Post ↔
      ∃ next : graph.Index,
        final.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        wpWith graph base AllowedRead fuel next final (fun result => Post (result.prepend 1 [])) := by
  simp [wpWith, effect]
  constructor
  · intro allChoices
    exact allChoices (FlagChoices.uniform false)
  · intro successor _
    exact successor

theorem wp_subReg64_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (state : State) (Post : Contract) (destination source : Register)
    (instruction : (graph.node node).instruction = .subReg64 destination source) :
    let final := sub64State state destination (state.registers source) 3
    wp graph base AllowedRead (fuel + 1) node state Post ↔
      ∃ next : graph.Index,
        final.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        wp graph base AllowedRead fuel next final (fun result => Post (result.prepend 1 [])) := by
  apply wp_pure_next_iff
  intro choice
  rw [instruction, execute_subReg64]

theorem wp_subImm64_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (state : State) (Post : Contract) (destination : Register) (immediate : Byte)
    (instruction : (graph.node node).instruction = .subImm64 destination immediate) :
    let final := sub64State state destination (immediate.signExtend 64) 4
    wp graph base AllowedRead (fuel + 1) node state Post ↔
      ∃ next : graph.Index,
        final.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        wp graph base AllowedRead fuel next final (fun result => Post (result.prepend 1 [])) := by
  apply wp_pure_next_iff
  intro choice
  rw [instruction, execute_subImm64]

theorem wpWith_subReg64_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (state : State) (Post : Contract) (destination source : Register)
    (instruction : (graph.node node).instruction = .subReg64 destination source) :
    let final := sub64State state destination (state.registers source) 3
    wpWith graph base AllowedRead (fuel + 1) node state Post ↔
      ∃ next : graph.Index,
        final.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        wpWith graph base AllowedRead fuel next final (fun result => Post (result.prepend 1 [])) := by
  apply wpWith_pure_next_iff
  intro choices
  rw [instruction, executeWith_subReg64]

theorem wpWith_subImm64_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (state : State) (Post : Contract) (destination : Register) (immediate : Byte)
    (instruction : (graph.node node).instruction = .subImm64 destination immediate) :
    let final := sub64State state destination (immediate.signExtend 64) 4
    wpWith graph base AllowedRead (fuel + 1) node state Post ↔
      ∃ next : graph.Index,
        final.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        wpWith graph base AllowedRead fuel next final (fun result => Post (result.prepend 1 [])) := by
  apply wpWith_pure_next_iff
  intro choices
  rw [instruction, executeWith_subImm64]

namespace Cutpoints

/-- The existing Bool cutpoint rule retains the actual next node, its invariant
and strict dynamic rank descent. SUB contributes no operand-memory read. -/
theorem wp_subReg64_iff (graph : CFG.Graph) (base : Word) (Post : State → Prop)
    (AllowedRead : State → Read → Prop) (Inv : graph.Index → State → Prop)
    (rank : graph.Index → State → Nat) (budget fuel : Nat) (node : graph.Index)
    (state : State) (destination source : Register)
    (instruction : (graph.node node).instruction = .subReg64 destination source) :
    let final := sub64State state destination (state.registers source) 3
    wp graph base Post AllowedRead Inv rank budget (fuel + 1) node state ↔
      ∃ next : graph.Index,
        final.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        if graph.cutpoint next then Inv next final ∧ rank next final < budget
        else wp graph base Post AllowedRead Inv rank budget fuel next final := by
  apply wp_pure_next_iff
  intro choice
  rw [instruction, execute_subReg64]

theorem wp_subImm64_iff (graph : CFG.Graph) (base : Word) (Post : State → Prop)
    (AllowedRead : State → Read → Prop) (Inv : graph.Index → State → Prop)
    (rank : graph.Index → State → Nat) (budget fuel : Nat) (node : graph.Index)
    (state : State) (destination : Register) (immediate : Byte)
    (instruction : (graph.node node).instruction = .subImm64 destination immediate) :
    let final := sub64State state destination (immediate.signExtend 64) 4
    wp graph base Post AllowedRead Inv rank budget (fuel + 1) node state ↔
      ∃ next : graph.Index,
        final.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        if graph.cutpoint next then Inv next final ∧ rank next final < budget
        else wp graph base Post AllowedRead Inv rank budget fuel next final := by
  apply wp_pure_next_iff
  intro choice
  rw [instruction, execute_subImm64]

end Cutpoints
end EDSL.X86.VCGen

#print axioms EDSL.X86.VCGen.wpWith_pure_next_iff
#print axioms EDSL.X86.VCGen.wp_subReg64_iff
#print axioms EDSL.X86.VCGen.wp_subImm64_iff
#print axioms EDSL.X86.VCGen.wpWith_subReg64_iff
#print axioms EDSL.X86.VCGen.wpWith_subImm64_iff
#print axioms EDSL.X86.VCGen.Cutpoints.wp_subReg64_iff
#print axioms EDSL.X86.VCGen.Cutpoints.wp_subImm64_iff
#audit_edsl
