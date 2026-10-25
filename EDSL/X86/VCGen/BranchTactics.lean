import EDSL.X86.VCGen.Branch
import EDSL.X86.VCGen.Tactics

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

namespace EDSL.X86.VCGen
open Sequential
open Lean Elab Tactic

/-- Inspect the real decoded constructor first. Ordinary instructions never
enter branch-lemma elaboration. Only the matching branch family is proposed;
every equality, status choice and canonicality obligation is still checked. -/
elab "vcgen_branch_step" simplify:tactic : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOfArity ``Cutpoints.wp 10 do
    throwError "vcgen_branch_step: expected a cutpoint WP"
  let node ← Lean.Meta.mkAppM ``CFG.Graph.node #[target.getArg! 0, target.getArg! 8]
  let instruction ← Lean.Meta.whnf (← Lean.Meta.mkAppM ``CFG.Node.instruction #[node])
  let selection ← if instruction.isAppOfArity ``Sequential.Instruction.je 1 then
    `(tactic| first
      | refine (Cutpoints.wp_je_iff (taken := true) (instruction := rfl)
          (selected := ?_) (safe := ?_) ..).2 ?_
        · $simplify:tactic; done
        · intro _; $simplify:tactic; done
      | refine (Cutpoints.wp_je_iff (taken := false) (instruction := rfl)
          (selected := ?_) (safe := ?_) ..).2 ?_
        · $simplify:tactic; done
        · intro impossible; cases impossible)
    else if instruction.isAppOfArity ``Sequential.Instruction.jcc 2 then
      `(tactic| first
        | refine (Cutpoints.wp_jcc_iff (taken := true) (instruction := rfl)
            (selected := ?_) (safe := ?_) ..).2 ?_
          · $simplify:tactic; done
          · intro _; $simplify:tactic; done
        | refine (Cutpoints.wp_jcc_iff (taken := false) (instruction := rfl)
            (selected := ?_) (safe := ?_) ..).2 ?_
          · $simplify:tactic; done
          · intro impossible; cases impossible)
    else if instruction.isAppOfArity ``Sequential.Instruction.jmp 1 then
      `(tactic| (
        refine (Cutpoints.wp_jmp_iff (instruction := rfl) (safe := ?_) ..).2 ?_
        · $simplify:tactic; done))
    else throwError "vcgen_branch_step: selected instruction is not a short branch"
  evalTactic selection
  evalTactic (← `(tactic| dsimp only [Cutpoints.Next, Bool.false_eq_true, ite_false, ite_true]))
  evalTactic (← `(tactic| vcgen_factor => $simplify:tactic))
  evalTactic (← `(tactic| vcgen_next))
  evalTactic (← `(tactic| vcgen_cutpoint))

/-- Production block generation with branch selection before record expansion.
Ordinary instructions retain the original generator and universal AF binder. -/
elab "vcgen_branch_block" graph:ident cut:ident simplify:tactic : tactic => do
  let step ← `(tactic| first
    | vcgen_branch_step $simplify:tactic
    | vcgen_block_step $graph:ident $cut:ident $simplify:tactic)
  let mut running := true
  while running do
    let before ← getGoals
    if before.isEmpty then break
    let saved ← saveState
    try
      evalTactic step
      if (← getGoals) == before then running := false
    catch _ =>
      saved.restore
      running := false

end EDSL.X86.VCGen
