/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.TriangularGCCEntry
import EDSL.Corpus.V1.TriangularGCCLoop

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.Corpus.V1.TriangularGCCClient
open X86 X86.Sequential X86.VCGen
open TriangularGCCGraph TriangularGCCBase

/-- All sparse blocks have constructed universal proofs. -/
def annotations (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec bytes input initial) :
    Cutpoints.Annotations bytes graph initial.rip (PureCall.Post spec input initial)
      (fun _ read => PureCall.RawRead initial read) where
  Inv := invariant input initial
  rank := rank input
  blocks cut current isCut binding admitted := by
    rcases cuts cut isCut with same | same
    · subst cut
      have sameState : current = initial := by
        simpa only [invariant, entry, Fin.val_mk, ↓reduceIte] using admitted
      subst current
      exact entryBlock input initial pre
    · subst cut
      have budget : LoopInvariant input initial current := by
        change LoopInvariant input initial current at admitted
        exact admitted
      exact loopBlock input initial pre current binding budget

theorem generated (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec bytes input initial) :
    ∃ a : Cutpoints.Annotations bytes graph initial.rip
      (PureCall.Post spec input initial) (fun _ read => PureCall.RawRead initial read),
      a.Inv valid.entry initial := by
  refine ⟨annotations input initial pre, ?_⟩
  change initial = initial
  rfl

/-- Totality for every Bool stream and the original every-prefix read authority. -/
theorem bounded_raw (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec bytes input initial) :
    AllExecutions initial (fun result => PureCall.Post spec input initial result.state ∧
      result.instructions ≤ 13 * (input.value.toNat / 2 + 2)) ∧ PureCall.RawPolicy initial := by
  let a := annotations input initial pre
  have admitted : a.Inv valid.entry initial := by
    change initial = initial
    rfl
  have binding : CFG.At bytes graph initial.rip valid.entry initial := by
    refine ⟨pre.code, ?_⟩
    simp [valid.entry_offset]
  have total := a.total_policy valid valid.entry_cutpoint binding admitted
  change AllExecutions initial (fun result => PureCall.Post spec input initial result.state ∧
    result.instructions ≤ 13 * (input.value.toNat / 2 + 1 + 1)) ∧ PureCall.RawPolicy initial at total
  simpa only [Nat.add_assoc] using total

/-- Genuine production prefix enabledness follows from total correctness. -/
theorem safe (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec bytes input initial) : Safe initial :=
  (bounded_raw input initial pre).1.safe

/-- Current original resources and all independent undefined-flag vectors. -/
theorem full_flags_semantics :
    Grading.ReadOnlySemanticClaimFor .flags (PureCall.readOnlyTask spec) bytes :=
  pureCall_semantics_of_cutpoints_flags spec bytes graph valid generated

end EDSL.Corpus.V1.TriangularGCCClient

#print axioms EDSL.Corpus.V1.TriangularGCCClient.bounded_raw
#print axioms EDSL.Corpus.V1.TriangularGCCClient.safe
#print axioms EDSL.Corpus.V1.TriangularGCCClient.full_flags_semantics
