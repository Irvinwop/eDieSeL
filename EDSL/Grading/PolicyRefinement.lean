/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.PolicyFor

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading
open X86 X86.Sequential

/-- Transfer the complete read-only policy along a simulation restricted to
old reachable states. Closure under actual new continuing steps establishes
that every new prefix is old reachable, including atomic prefixes. Each next
choice then reproduces the identical old observation, preserving current
resources, actual reads and their pre-state permissions, full memory and
effect restrictions. No agreement outside old reachability is required. -/
theorem ReadOnlyPolicyFor.of_simulatesOn {oldModel newModel : ExecutionModel}
    {initial : State} {Current : State → Prop} {AllowedRead : State → Read → Prop}
    (policy : ReadOnlyPolicyFor oldModel initial Current AllowedRead)
    (simulation : Engine.SimulatesOn (Engine.Reachable oldModel.transition initial)
      newModel.transition oldModel.transition)
    (closed : Engine.ContinuesClosed (Engine.Reachable oldModel.transition initial)
      newModel.transition) :
    ReadOnlyPolicyFor newModel initial Current AllowedRead := by
  have retained : ∀ {choices : ChoiceStream newModel.Choice} {first last : State}
      {count : Nat} {reads : List Read},
      Engine.Block newModel.transition choices first last count reads →
      Engine.Reachable oldModel.transition initial first →
      Engine.Reachable oldModel.transition initial last := by
    intro choices first last count reads block reachable
    induction block with
    | nil => exact reachable
    | next actual tail induction | atomic actual tail induction =>
      exact induction (closed _ _ _ reachable actual _ rfl)
  have start : Engine.Reachable oldModel.transition initial initial := by
    cases oldModel with
    | bool => exact Engine.Reachable.refl step false initial
    | flags => exact Engine.Reachable.refl stepWith (FlagChoices.uniform false) initial
  intro before reachable
  obtain ⟨choices, count, reads, block⟩ := reachable
  have oldReachable := retained block start
  obtain ⟨current, decoded, enabled⟩ := policy before oldReachable
  refine ⟨current, decoded, ?_⟩
  intro choice
  obtain ⟨oldChoice, same⟩ := simulation choice before oldReachable
  obtain ⟨observation, actual, allowed, effect⟩ := enabled oldChoice
  exact ⟨observation, same.symm.trans actual, allowed, effect⟩

/-- Genuine safety of every Bool reachable prefix permits the complete
independent flag-choice policy. This uses the production restricted step
simulation and prefix closure; it does not simulate IMUL globally or restrict
the flags executor to correlated choices. `Current` and `AllowedRead` retain
their original pre-state arguments. -/
theorem ReadOnlyPolicy.flags_of_safe {initial : State}
    {Current : State → Prop} {AllowedRead : State → Read → Prop}
    (policy : ReadOnlyPolicy initial Current AllowedRead) (safe : Safe initial) :
    ReadOnlyPolicyFor .flags initial Current AllowedRead :=
  ReadOnlyPolicyFor.of_simulatesOn (oldModel := .bool) policy
    (stepWith_simulates_step_on_safe safe) (boolReachable_continuesWith safe)

end EDSL.Grading
