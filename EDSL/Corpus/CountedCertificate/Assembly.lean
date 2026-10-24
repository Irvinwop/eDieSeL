/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.CountedCertificate
import EDSL.OS.TSO64.ScheduleComposition

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Assemble independent counted-call admission from the actual finite worker
population, and useful overlap evidence from actual prefix/suffix executions.
The complete named image and loaded batch retain their original indices and
resource obligations. The overlap has no instruction layout, rank, requested
constant or cleanup requirement. Its RMW positions are original log indices.

The unrestricted independent Claim remains a separate input: one completed
overlap establishes none of its universal safety or progress obligations.
The imported coherent scalar RAM, protected-resource, stable-translation/
no-alias, represented-CPU and long-mode/CET-off assumptions remain in force.
-/

namespace EDSL.Corpus.Counted
open X86 OS OS.TSO64 Grading.ConcurrentTask.Counted64

/-- Assemble all seven independent admission fields for any actual finite
population, including zero. Casts preserve the original physical slot values. -/
theorem pre_of_population {n : Nat} (image : ScalarCall64.Image)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell) (before : TSO64.State)
    (population : before.workers.length = n) (amounts : Fin n → BitVec 32)
    (workers : Fin n → Worker)
    (valid : WellFormed before .ownedOnly) (empty : Quiescent before)
    (liveTarget : before.world.cells target = some cell)
    (validCell : Atomics64.ValidCell before.world.legacy.shared cell)
    (live : ∀ slot : Fin n, before.workers[slot.val]? = some (workers slot))
    (entries : ∀ slot : Fin n,
      Entry image target cell (amounts slot) before (workers slot))
    (privateCallers : ∀ (i j : Fin n), i ≠ j →
      Ownership.Disjoint (workers i).resources.caller.loan.region
        (workers j).resources.caller.loan.region)
    (codeCallerSeparation : ∀ slot : Fin n,
      Ownership.Disjoint ⟨image.base, image.bytes.length⟩
        (workers slot).resources.caller.loan.region) :
    Pre image target cell before (fun slot => amounts (Fin.cast population slot)) := by
  constructor
  · exact valid
  · exact empty
  · exact liveTarget
  · exact validCell
  · intro slot
    let selected : Fin n := Fin.cast population slot
    exact ⟨workers selected, live selected, entries selected⟩
  · intro i j first second different firstLive secondLive
    let left : Fin n := Fin.cast population i
    let right : Fin n := Fin.cast population j
    have leftLive : before.workers[left.val]? = some (workers left) := live left
    have rightLive : before.workers[right.val]? = some (workers right) := live right
    have firstEq : first = workers left :=
      Option.some.inj (firstLive.symm.trans leftLive)
    have secondEq : second = workers right :=
      Option.some.inj (secondLive.symm.trans rightLive)
    have slotDifferent : left ≠ right := by
      intro same
      apply different
      exact Fin.ext (congrArg (fun slot : Fin n => slot.val) same)
    rw [firstEq, secondEq]
    exact privateCallers left right slotDifferent
  · intro slot worker found
    let selected : Fin n := Fin.cast population slot
    have known : before.workers[selected.val]? = some (workers selected) := live selected
    have same : worker = workers selected := Option.some.inj (found.symm.trans known)
    rw [same]
    exact codeCallerSeparation selected

variable {file name : List Byte} {cap : Nat} {named : NamedImage file name cap}

/-- Actual completed execution evidence for this exact loaded batch. The
ordered own/peer/own RMW pattern permits other observations and RMWs, retaining
the original full-prefix positions and the actual event payloads. -/
structure OverlapWitness (batch : LoadedBatch named) where
  population : batch.before.workers.length = 2
  own : Fin batch.before.workers.length
  peer : Fin batch.before.workers.length
  distinct : own ≠ peer
  prefixActions : List Action
  suffixActions : List Action
  prefixObservations : List Observation
  suffixObservations : List Observation
  cut : TSO64.State
  final : TSO64.State
  prefixRun : schedule batch.before prefixActions .ownedOnly .arithmetic =
    .ok (cut, prefixObservations)
  suffixRun : schedule cut suffixActions .ownedOnly .arithmetic =
    .ok (final, suffixObservations)
  returned : Returned final
  cutRunning : ∀ slot : Fin batch.before.workers.length,
    ∃ worker, cut.workers[slot.val]? = some worker ∧ worker.phase = .running
  unfinished : ∀ slot : Fin batch.before.workers.length,
    EffectSimulation.Mixed.Counts.countRMW slot.val prefixObservations <
      (batch.requests slot).toNat
  pattern : ∃ i j k : Nat, i < j ∧ j < k ∧
    ∃ e0 e1 e2 : Atomics64.FetchAddEvent,
      prefixObservations[i]? = some (.rmw own.val e0) ∧
      prefixObservations[j]? = some (.rmw peer.val e1) ∧
      prefixObservations[k]? = some (.rmw own.val e2)

/-- Apply the independent universal claim to the witness's composed actual
execution. Existential elimination retains all eight execution projections
without extracting data by classical choice or changing the batch admission. -/
theorem useful_of_witness (batch : LoadedBatch named)
    (claim : Claim named.image) (w : OverlapWitness batch) :
    ∃ run : UsefulRun batch,
      run.own = w.own ∧
      run.peer = w.peer ∧
      run.prefixActions = w.prefixActions ∧
      run.prefixObservations = w.prefixObservations ∧
      run.cut = w.cut ∧
      run.suffixActions = w.suffixActions ∧
      run.suffixObservations = w.suffixObservations ∧
      run.final = w.final := by
  have actual :
      schedule batch.before (w.prefixActions ++ w.suffixActions) .ownedOnly .arithmetic =
        .ok (w.final, w.prefixObservations ++ w.suffixObservations) :=
    schedule_append_of_success w.prefixRun w.suffixRun
  obtain ⟨post⟩ := claim.completed batch.before batch.target batch.cell batch.requests
    batch.pre (w.prefixActions ++ w.suffixActions)
    (w.final, w.prefixObservations ++ w.suffixObservations) actual w.returned
  obtain ⟨first, middle, last, firstLess, middleLess,
    firstEvent, peerEvent, lastEvent, firstObserved, peerObserved, lastObserved⟩ := w.pattern
  obtain ⟨lastBound, _lastValue⟩ := List.getElem?_eq_some_iff.mp lastObserved
  let run : UsefulRun batch := {
    population := w.population
    own := w.own
    peer := w.peer
    distinct := w.distinct
    prefixActions := w.prefixActions
    prefixObservations := w.prefixObservations
    cut := w.cut
    prefixRun := w.prefixRun
    cutRunning := w.cutRunning
    unfinished := w.unfinished
    suffixActions := w.suffixActions
    suffixObservations := w.suffixObservations
    final := w.final
    suffixRun := w.suffixRun
    post := post
    first := first
    middle := middle
    last := last
    firstBeforeMiddle := firstLess
    middleBeforeLast := middleLess
    beforeCut := lastBound
    firstEvent := firstEvent
    peerEvent := peerEvent
    lastEvent := lastEvent
    firstObserved := firstObserved
    peerObserved := peerObserved
    lastObserved := lastObserved }
  exact ⟨run, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end EDSL.Corpus.Counted
