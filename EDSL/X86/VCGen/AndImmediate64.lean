import EDSL.X86.VCGen.ChoiceNext
import EDSL.Audit
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.X86.VCGen
open Sequential
/-- Exact bounded Bool WP over the production AND executor. -/
theorem wp_andImm64_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (initial : State) (destination : Register) (immediate : Byte) (Post : Contract)
    (opcode : (graph.node node).instruction = .andImm64 destination immediate) :
    wp graph base AllowedRead (fuel + 1) node initial Post ↔
      ∀ af : Bool, ∃ next : graph.Index,
        (logical64State initial .band destination (immediate.signExtend 64) 4 af).rip =
          base + BitVec.ofNat 64 (graph.node next).offset ∧
        wp graph base AllowedRead fuel next
          (logical64State initial .band destination (immediate.signExtend 64) 4 af)
          (fun result => Post (result.prepend 1 [])) := by
  apply wp_choice_next_iff
  intro af
  rw [opcode, execute_andImm64]
/-- The complete vector continuation remains wpWith under every current vector. -/
theorem wpWith_andImm64_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (initial : State) (destination : Register) (immediate : Byte) (Post : Contract)
    (opcode : (graph.node node).instruction = .andImm64 destination immediate) :
    wpWith graph base AllowedRead (fuel + 1) node initial Post ↔
      ∀ choices : FlagChoices, ∃ next : graph.Index,
        (logical64State initial .band destination (immediate.signExtend 64) 4 choices.af).rip =
          base + BitVec.ofNat 64 (graph.node next).offset ∧
        wpWith graph base AllowedRead fuel next
          (logical64State initial .band destination (immediate.signExtend 64) 4 choices.af)
          (fun result => Post (result.prepend 1 [])) := by
  apply wpWith_choice_next_iff
  intro choices
  rw [opcode, executeWith_andImm64]
end EDSL.X86.VCGen
#print axioms EDSL.X86.VCGen.wp_andImm64_iff
#print axioms EDSL.X86.VCGen.wpWith_andImm64_iff
#audit_edsl
