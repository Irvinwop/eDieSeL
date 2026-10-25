import EDSL.X86.VCGen.Cutpoints
import EDSL.X86.Sequential.ShortBranch

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.VCGen.Cutpoints
open Sequential

/-- Exactly the original WP successor obligation, with its current dynamic
budget. This abbreviation grants neither a destination nor a cutpoint. -/
abbrev Next (graph : CFG.Graph) (base : Word) (Post : State → Prop)
    (AllowedRead : State → Read → Prop) (Inv : graph.Index → State → Prop)
    (rank : graph.Index → State → Nat) (budget fuel : Nat) (final : State) : Prop :=
  ∃ destination : graph.Index,
    final.rip = base + BitVec.ofNat 64 (graph.node destination).offset ∧
    if graph.cutpoint destination then
      Inv destination final ∧ rank destination final < budget
    else wp graph base Post AllowedRead Inv rank budget fuel destination final

variable (graph : CFG.Graph) (base : Word) (Post : State → Prop)
  (AllowedRead : State → Read → Prop) (Inv : graph.Index → State → Prop)
  (rank : graph.Index → State → Nat) (budget fuel : Nat) (node : graph.Index)
  (state : State)

/-- Select the actual status predicate before expanding the state or executor.
The taken target alone needs canonicality, exactly as in production execution.
The executor equality is universal in AF and has an empty operand-read list. -/
theorem wp_shortBranch_iff (condition : Condition) (displacement : Byte) (taken : Bool)
    (form : ShortBranchForm (graph.node node).instruction condition displacement)
    (selected : condition.holds state.flags = taken)
    (safe : taken = true → canonical (state.rip + 2 + displacement.signExtend 64) = true) :
    wp graph base Post AllowedRead Inv rank budget (fuel + 1) node state ↔
      Next graph base Post AllowedRead Inv rank budget fuel
        { state with rip := if taken then state.rip + 2 + displacement.signExtend 64
                            else state.rip + 2 } := by
  apply wp_pure_next_iff
  intro af
  have effect := execute_shortBranch_context state form
    (by intro actual; exact safe (selected.symm.trans actual)) af
  simpa only [shortBranchTarget, selected] using effect

theorem wp_je_iff (displacement : Byte) (taken : Bool)
    (instruction : (graph.node node).instruction = .je displacement)
    (selected : Condition.holds .equal state.flags = taken)
    (safe : taken = true → canonical (state.rip + 2 + displacement.signExtend 64) = true) :
    wp graph base Post AllowedRead Inv rank budget (fuel + 1) node state ↔
      Next graph base Post AllowedRead Inv rank budget fuel
        { state with rip := if taken then state.rip + 2 + displacement.signExtend 64
                            else state.rip + 2 } :=
  wp_shortBranch_iff graph base Post AllowedRead Inv rank budget fuel node state
    .equal displacement taken (instruction ▸ .equal displacement) selected safe

theorem wp_jcc_iff (condition : Condition) (displacement : Byte) (taken : Bool)
    (instruction : (graph.node node).instruction = .jcc condition displacement)
    (selected : condition.holds state.flags = taken)
    (safe : taken = true → canonical (state.rip + 2 + displacement.signExtend 64) = true) :
    wp graph base Post AllowedRead Inv rank budget (fuel + 1) node state ↔
      Next graph base Post AllowedRead Inv rank budget fuel
        { state with rip := if taken then state.rip + 2 + displacement.signExtend 64
                            else state.rip + 2 } :=
  wp_shortBranch_iff graph base Post AllowedRead Inv rank budget fuel node state
    condition displacement taken (instruction ▸ .generic condition displacement) selected safe

theorem wp_jmp_iff (displacement : Byte)
    (instruction : (graph.node node).instruction = .jmp displacement)
    (safe : canonical (state.rip + 2 + displacement.signExtend 64) = true) :
    wp graph base Post AllowedRead Inv rank budget (fuel + 1) node state ↔
      Next graph base Post AllowedRead Inv rank budget fuel
        { state with rip := state.rip + 2 + displacement.signExtend 64 } := by
  apply wp_pure_next_iff
  intro af
  rw [instruction, execute_jmp]
  simp only [executeShortBranch, safe, ite_true, ok_bind, pure_ok]

#print axioms wp_shortBranch_iff
#print axioms wp_je_iff
#print axioms wp_jcc_iff
#print axioms wp_jmp_iff
end EDSL.X86.VCGen.Cutpoints
