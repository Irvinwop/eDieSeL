import EDSL.X86.VCGen.ChoicesPolicy
import EDSL.X86.VCGen.CutpointPolicy
import EDSL.X86.Sequential.AndImmediate64
import EDSL.Audit
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.X86.VCGen
open Sequential
/-- The successor remains dependent on the current undefined flag. -/
theorem wp_choice_next_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (initial : State) (after : Bool → State) (Post : Contract)
    (effect : ∀ af, execute initial (graph.node node).instruction af = .ok ⟨.next (after af), []⟩) :
    wp graph base AllowedRead (fuel + 1) node initial Post ↔
      ∀ af : Bool, ∃ next : graph.Index,
        (after af).rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        wp graph base AllowedRead fuel next (after af)
          (fun result => Post (result.prepend 1 [])) := by
  simp [wp, effect]
/-- Every current vector and the independent vector continuation are retained. -/
theorem wpWith_choice_next_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (initial : State) (after : FlagChoices → State) (Post : Contract)
    (effect : ∀ choices, executeWith initial (graph.node node).instruction choices =
      .ok ⟨.next (after choices), []⟩) :
    wpWith graph base AllowedRead (fuel + 1) node initial Post ↔
      ∀ choices : FlagChoices, ∃ next : graph.Index,
        (after choices).rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        wpWith graph base AllowedRead fuel next (after choices)
          (fun result => Post (result.prepend 1 [])) := by
  simp [wpWith, effect]
namespace Cutpoints
theorem wp_choice_next_iff (graph : CFG.Graph) (base : Word) (Post : State → Prop)
    (AllowedRead : State → Read → Prop) (Inv : graph.Index → State → Prop)
    (rank : graph.Index → State → Nat) (budget fuel : Nat) (node : graph.Index)
    (initial : State) (after : Bool → State)
    (effect : ∀ af, execute initial (graph.node node).instruction af = .ok ⟨.next (after af), []⟩) :
    wp graph base Post AllowedRead Inv rank budget (fuel + 1) node initial ↔
      ∀ af : Bool, ∃ next : graph.Index,
        (after af).rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        if graph.cutpoint next then
          Inv next (after af) ∧ rank next (after af) < budget
        else wp graph base Post AllowedRead Inv rank budget fuel next (after af) := by
  simp [wp, effect]
end Cutpoints
end EDSL.X86.VCGen
#print axioms EDSL.X86.VCGen.wp_choice_next_iff
#print axioms EDSL.X86.VCGen.wpWith_choice_next_iff
#print axioms EDSL.X86.VCGen.Cutpoints.wp_choice_next_iff
#audit_edsl
