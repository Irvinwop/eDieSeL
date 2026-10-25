/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.CutpointPolicy
import EDSL.PureCall.ResourcesFromBool

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.VCGen
open Sequential

/-- Preserve the cutpoint bound when applying the existing safe Bool-to-flags
resource bridge. Genuine safety comes from the same total-correctness proof;
the original every-prefix RawPolicy supplies permission. The supplied
annotations are universal proof evidence, outside present-only admission. -/
theorem pureCall_semantics_of_cutpoints_flags
    {profile : CFG.Profile}
    (spec : EDSL.PureCall.Spec) (bytes : List Byte) (graph : CFG.Graph)
    (valid : CFG.Valid bytes graph profile)
    (generated : ∀ input initial, EDSL.PureCall.Pre spec bytes input initial →
      ∃ annotations : Cutpoints.Annotations bytes graph initial.rip
        (EDSL.PureCall.Post spec input initial)
        (fun _ read => EDSL.PureCall.RawRead initial read),
        annotations.Inv valid.entry initial) :
    Grading.ReadOnlySemanticClaimFor .flags (EDSL.PureCall.readOnlyTask spec) bytes := by
  apply EDSL.PureCall.semantics_of_bounded_bool
  intro input initial pre
  obtain ⟨annotations, admitted⟩ := generated input initial pre
  have binding : CFG.At bytes graph initial.rip valid.entry initial := by
    refine ⟨pre.code, ?_⟩
    simp [valid.entry_offset]
  refine ⟨(graph.maxDepth + 1) * (annotations.rank valid.entry initial + 1), ?_⟩
  exact annotations.total_policy valid valid.entry_cutpoint binding admitted

end EDSL.X86.VCGen

#print axioms EDSL.X86.VCGen.pureCall_semantics_of_cutpoints_flags
