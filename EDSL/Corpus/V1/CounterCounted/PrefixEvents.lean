/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterCounted.Admission
import EDSL.Corpus.V1.CounterCohort
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankedPrefix
import EDSL.Audit

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Event authentication and request-count bounds for every actual successful
prefix of an independently admitted counted-call cohort. The proof extends
that same prefix with a ranked completion from its exact lifted cut ghosts.
Each selected bundle's completed proofs authenticate all earlier own events;
nonnegative suffix counts give the independent prefix request bounds.

The finite continuation is constructed, never assumed in admission. Past AF
choices are unrestricted and the original observation list remains intact.
Actual scheduler slots index the subjects; resource actors may coincide.
These conditional modeled results supply no physical CPU/OS, compiler,
fairness, minimum-operation or corpus-admission claim.
-/

namespace EDSL.Corpus.V1.CounterCounted
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

/-- Compose actual executions through their common actual state. -/
private theorem append_actual {before middle final : TSO64.State}
    {left right : List Action} {leftSeen rightSeen : List Observation}
    {profile : Profile} {family : RMWFamily}
    (first : TSO64.schedule before left profile family = .ok (middle, leftSeen))
    (second : TSO64.schedule middle right profile family = .ok (final, rightSeen)) :
    TSO64.schedule before (left ++ right) profile family =
      .ok (final, leftSeen ++ rightSeen) := by
  induction left generalizing before leftSeen with
  | nil =>
    have same : (before, []) = (middle, leftSeen) := Except.ok.inj first
    cases same
    exact second
  | cons action rest ih =>
    obtain ⟨head, tail, stepped, following, same⟩ := schedule_cons_ok first
    cases same
    have appended := ih following
    simp only [List.cons_append, TSO64.schedule, stepped, ok_bind, appended, pure_ok]

variable {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
  {cell : Atomics64.Cell} {before cut : TSO64.State}
  {requests : Spec.Requests before} {actions : List Action}
  {observations : List Observation}

/-- Complete the actual prefix from its exact collectively lifted ghosts.
The prefix need not match future choices. Every suffix offset advances by
all issues of that thread in the original prefix, including peer interleaving.
The witness retains both actual schedules, the exact shared cut ghosts and
both complete collective traces. No desired endpoint is an input. -/
theorem completion_after_prefix
    (proofs : CounterCommon.ProofProvider compiler)
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : TSO64.schedule before actions .ownedOnly .arithmetic =
      .ok (cut, observations))
    (choices : Nat → Nat → Bool) (offset : Nat → Nat) :
    ∃ atCut : (cohort proofs pre).Ghosts before,
      (cohort proofs pre).Current cut atCut ∧
      LiftTrace (cohort proofs pre).Step (ghosts proofs pre) actions observations atCut ∧
      ∃ suffix : (cohort proofs pre).Suffix (before := cut) atCut choices
          (fun tid => offset tid + Mixed.ChoiceTrace.issues tid actions),
        TSO64.schedule before (actions ++ suffix.actions) .ownedOnly .arithmetic =
          .ok (suffix.final, observations ++ suffix.observations) ∧
        LiftTrace (cohort proofs pre).Step (ghosts proofs pre) (actions ++ suffix.actions)
          (observations ++ suffix.observations) suffix.finalGhosts := by
  obtain ⟨atCut, cutCurrent, prefixLifted⟩ :=
    (cohort proofs pre).prefix_from_current pre.valid (current proofs pre) actual
  have covered : (cohort proofs pre).toCohort.Covers before := (cohort proofs pre).covers rfl
  obtain ⟨cutEmpty, _cutCovered, _otherCurrent, _prefixRetiring⟩ :=
    (cohort proofs pre).toCohort.schedule_from_current covered
      ((cohort proofs pre).current_toCohort (current proofs pre)) pre.empty actual
  have cutValid : WellFormed cut .ownedOnly := schedule_wellFormed pre.valid actual
  have cutCount : cut.workers.length = before.workers.length :=
    ScheduleTrace.workers_length actual
  obtain ⟨suffix⟩ := (cohort proofs pre).complete_from_current cutValid cutCount cutCurrent
    cutEmpty choices (fun tid => offset tid + Mixed.ChoiceTrace.issues tid actions)
  exact ⟨atCut, cutCurrent, prefixLifted, suffix, append_actual actual suffix.actual,
    prefixLifted.append suffix.lifted⟩

/-- Every slot's complete original prefix RMWs have the independently admitted
actor, target, address and unit delta, and its Nat count cannot exceed its
independent low32 request. One constructed extension proves both facts for
all slots; it neither filters observations nor substitutes another prefix. -/
theorem prefix_events_counts
    (proofs : CounterCommon.ProofProvider compiler)
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : TSO64.schedule before actions .ownedOnly .arithmetic =
      .ok (cut, observations)) :
    ∀ slot : Fin before.workers.length,
      (∀ event, Observation.rmw slot.val event ∈ observations →
        CounterCommon.EventOK (subjects proofs pre slot).site
          (subjects proofs pre slot).call event) ∧
      Mixed.Counts.countRMW slot.val observations ≤ (requests slot).toNat := by
  obtain ⟨_atCut, _cutCurrent, _prefixLifted, suffix, whole, _wholeLifted⟩ :=
    completion_after_prefix proofs pre actual (fun _ _ => false) (fun _ => 0)
  intro slot
  let subject := subjects proofs pre slot
  have bound : slot.val < suffix.final.workers.length := by
    rw [suffix.finalWorkers]
    exact slot.isLt
  have live : suffix.final.workers[slot.val]? =
      some (suffix.final.workers[slot.val]'bound) := List.getElem?_eq_getElem bound
  have ownLive : suffix.final.workers[subject.site.tid]? =
      some (suffix.final.workers[slot.val]'bound) := by
    change suffix.final.workers[slot.val]? = _
    exact live
  have returned : (suffix.final.workers[slot.val]'bound).phase = .returned :=
    suffix.returned _ (List.mem_of_getElem? live)
  have ownRun : TSO64.schedule before (actions ++ suffix.actions)
      subject.site.profile .arithmetic =
        .ok (suffix.final, observations ++ suffix.observations) := by
    rw [subject.ownedOnly]
    exact whole
  have authenticated := subject.proof.completed_events ownRun ownLive returned
  have total := subject.proof.completed_count ownRun ownLive returned
  change Mixed.Counts.countRMW slot.val (observations ++ suffix.observations) =
    (requests slot).toNat at total
  rw [Mixed.Counts.countRMW_append] at total
  refine ⟨?_, ?_⟩
  · intro event member
    apply authenticated event
    change Observation.rmw slot.val event ∈ observations ++ suffix.observations
    exact List.mem_append.mpr (Or.inl member)
  · exact Nat.le_trans (Nat.le_add_right (Mixed.Counts.countRMW slot.val observations)
      (Mixed.Counts.countRMW slot.val suffix.observations)) (Nat.le_of_eq total)

/-- Exhaustive authentication uses the actual original Fin slot for every RMW
in the original log, independently of its actor and event payload. -/
theorem prefix_event
    (proofs : CounterCommon.ProofProvider compiler)
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : TSO64.schedule before actions .ownedOnly .arithmetic =
      .ok (cut, observations))
    {tid : Nat} {event : Atomics64.FetchAddEvent}
    (member : Observation.rmw tid event ∈ observations) :
    ∃ slot : Fin before.workers.length, slot.val = tid ∧
      CounterCommon.EventOK (subjects proofs pre slot).site (subjects proofs pre slot).call event := by
  let slot : Fin before.workers.length := ⟨tid, ScheduleTrace.rmw_tid_lt actual member⟩
  exact ⟨slot, rfl, (prefix_events_counts proofs pre actual slot).1 event member⟩

/-- Indexed observations retain their original scheduler position; no expected
value or target filter is used to obtain the actual subject. -/
theorem prefix_event_at
    (proofs : CounterCommon.ProofProvider compiler)
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : TSO64.schedule before actions .ownedOnly .arithmetic =
      .ok (cut, observations))
    {index tid : Nat} {event : Atomics64.FetchAddEvent}
    (observed : observations[index]? = some (Observation.rmw tid event)) :
    ∃ slot : Fin before.workers.length, slot.val = tid ∧
      CounterCommon.EventOK (subjects proofs pre slot).site (subjects proofs pre slot).call event :=
  prefix_event proofs pre actual (List.mem_of_getElem? observed)

/-- A slot that has actually returned already has its exact requested count
in this same original run. No future completion or final memory premise is
needed for this equality. -/
theorem completed_count
    (proofs : CounterCommon.ProofProvider compiler)
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : TSO64.schedule before actions .ownedOnly .arithmetic =
      .ok (cut, observations))
    (slot : Fin before.workers.length) {worker : Worker}
    (live : cut.workers[slot.val]? = some worker) (returned : worker.phase = .returned) :
    Mixed.Counts.countRMW slot.val observations = (requests slot).toNat := by
  have ownRun : TSO64.schedule before actions (subjects proofs pre slot).site.profile .arithmetic =
      .ok (cut, observations) := by
    rw [(subjects proofs pre slot).ownedOnly]
    exact actual
  have ownLive : cut.workers[(subjects proofs pre slot).site.tid]? = some worker := by
    change cut.workers[slot.val]? = some worker
    exact live
  exact (subjects proofs pre slot).proof.completed_count ownRun ownLive returned

#print axioms append_actual
#print axioms completion_after_prefix
#print axioms prefix_events_counts
#print axioms prefix_event
#print axioms prefix_event_at
#print axioms completed_count

end EDSL.Corpus.V1.CounterCounted

#audit_edsl
