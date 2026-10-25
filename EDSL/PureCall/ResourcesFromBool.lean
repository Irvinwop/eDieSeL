/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.PolicyRefinement
import EDSL.PureCall.ResourcesFor

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.PureCall
open X86 X86.Sequential

/-- Reuse a uniformly bounded Bool execution proof and its actual raw policy
under the common complete-flags task. The bound may depend on the admitted
input and initial state, but is uniform over all Bool streams. Actual totality
derives prefix safety; policy is transported at every actual flags prefix and
for every next observation's reads.

The original `Spec`, `Pre`, `Post`, raw caller slot and resource admission are
unchanged. `semantics_of_rawFor` retains the same borrowed caller/code authority
and current OS world, complete memory/permissions, ABI and nonarithmetic flag
frames. Arithmetic correctness grants no read authority. Stable ordinary RAM
and no asynchronous interference remain the existing sequential assumptions.
This theorem supplies no body, ELF, registration or nonvacuity evidence. -/
theorem semantics_of_bounded_bool {spec : Spec} {bytes : List Byte}
    (raw : ∀ input initial, Pre spec bytes input initial →
      ∃ fuel, AllExecutions initial (fun result =>
        Post spec input initial result.state ∧ result.instructions ≤ fuel) ∧
        RawPolicy initial) :
    Grading.ReadOnlySemanticClaimFor .flags (readOnlyTask spec) bytes := by
  apply semantics_of_rawFor .flags
  intro input initial pre
  obtain ⟨fuel, correct, policy⟩ := raw input initial pre
  refine ⟨?_, policy.flags_of_safe correct.safe⟩
  intro choices
  obtain ⟨result, execution, post, _⟩ := allExecutionsWith_of_allExecutions correct choices
  exact ⟨result, execution, post⟩

end EDSL.PureCall
