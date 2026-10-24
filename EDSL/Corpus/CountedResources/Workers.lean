/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.CountedResources.Image
import EDSL.OS.TSO64.Setup

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Actual production attachments for two callers of one checked named image.
The manager supplies the current resource identities. The first attachment's
actual result supplies the second operation's input, and the initial worker
list is projected from that successful composition.

All uint32 requests, upper RSI halves, old64 words and modeled flags remain
arbitrary. StartTotal is present preparation evidence for those actual gates;
it is not an added premise of the independent counted Pre or Claim. Current
validity and worker fields below follow by inversion of the real operations.
No assigned loan descriptors, future execution, requested result, progress,
native authority or compiler/physical-OS correspondence is supplied here.
The imported represented-CPU/CET-off, coherent scalar RAM, protected-resource
and stable-translation/no-alias assumptions remain in force.
-/

namespace EDSL.Corpus.CountedResources.Workers
open X86 OS OS.TSO64

variable {file name : List Byte} {cap : Nat}
variable (named : Counted.NamedImage file name cap) (total : Image.Total named)

def actor (slot : Fin 2) : Nat := if slot.val = 0 then 11 else 12

def stack (slot : Fin 2) : Word :=
  if slot.val = 0 then PlainResources.standard.stackA else PlainResources.standard.stackB

def continuation (slot : Fin 2) : Word :=
  if slot.val = 0 then PlainResources.standard.returnA else PlainResources.standard.returnB

/-- Select identities from the actual successful manager output. -/
def codeId (old : Word) (slot : Fin 2) : Nat :=
  if slot.val = 0 then (Image.resources named total old).codeA
  else (Image.resources named total old).codeB

def callerId (old : Word) (slot : Fin 2) : Nat :=
  if slot.val = 0 then (Image.resources named total old).callerA
  else (Image.resources named total old).callerB

def atomicId (old : Word) (slot : Fin 2) : Atomics64.HandleId64 :=
  if slot.val = 0 then (Image.resources named total old).atomicA
  else (Image.resources named total old).atomicB

/-- Preserve all supplied upper bits while admitting only low32 as count. -/
def argument (count upper : BitVec 32) : Word := upper ++ count

theorem argument_low32 (count upper : BitVec 32) :
    (argument count upper).setWidth 32 = count :=
  BitVec.setWidth_append_eq_right

theorem argument_upper32 (count upper : BitVec 32) :
    (argument count upper).extractLsb' 32 32 = upper :=
  BitVec.extractLsb'_append_eq_left

def context (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) : Context where
  registers register := match register with
    | .rsp => stack slot
    | .rdi => (Image.resources named total old).cell.address
    | .rsi => argument (count slot) (upper slot)
    | _ => 0x8877665544332211
  rip := named.image.base
  flags := flags slot

private def emptyState (old : Word) : TSO64.State :=
  ⟨(Image.resources named total old).managed.world, []⟩

/-- The actual second attach consumes precisely the first attach's output. -/
def start (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) : Except TSO64.Fault TSO64.State := do
  let first ← TSO64.attach (emptyState named total old) (actor 0)
    (context named total old count upper flags 0)
    (codeId named total old 0) (callerId named total old 0) [] [atomicId named total old 0]
  TSO64.attach first (actor 1) (context named total old count upper flags 1)
    (codeId named total old 1) (callerId named total old 1) [] [atomicId named total old 1]

/-- Proved success of current attachment gates for every original input. -/
abbrev StartTotal : Prop :=
  ∀ (old : Word) (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word),
    (start named total old count upper flags).toOption.isSome = true

variable (started : StartTotal named total)

/-- The actual successful composition, rather than an assigned worker fixture. -/
def initial (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) : TSO64.State :=
  (start named total old count upper flags).toOption.get (started old count upper flags)

theorem started_eq (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :
    start named total old count upper flags =
      .ok (initial named total started old count upper flags) :=
  PlainResources.checked_get _ (started old count upper flags)

/-- Operation-derived normalization facts, with no reconstructed loans. -/
private structure Made (principal : Nat) (entry : Context) (code caller : Nat)
    (identifier : Atomics64.HandleId64) (worker : Worker) : Prop where
  context : worker.context = entry
  running : worker.phase = .running
  pending : worker.pending = []
  nextStore : worker.nextStore = 0
  actor : worker.resources.actor = principal
  codeId : worker.resources.code.identifier = code
  callerId : worker.resources.caller.identifier = caller
  callerAddress : worker.resources.callerAddress = entry.registers .rsp
  grants : worker.resources.grants = []
  atomics : worker.resources.atomics = [identifier]

private theorem made_of_success {world : TSO64.World} {principal code caller : Nat}
    {entry : Context} {identifier : Atomics64.HandleId64} {worker : Worker}
    (success : TSO64.makeWorker world principal entry code caller [] [identifier] = .ok worker) :
    Made principal entry code caller identifier worker := by
  cases codeResult : Borrowing.authorize world.legacy.shared principal code with
  | error fault => simp [TSO64.makeWorker, codeResult, Except.mapError] at success
  | ok codeLoan =>
    cases callerResult : Borrowing.authorize world.legacy.shared principal caller with
    | error fault => simp [TSO64.makeWorker, codeResult, callerResult, Except.mapError] at success
    | ok callerLoan =>
      dsimp only [TSO64.makeWorker] at success
      simp only [codeResult, callerResult, Except.mapError, ok_bind] at success
      split at success
      next valid =>
        simp only [pure_ok, Except.ok.injEq] at success
        cases success
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      next => cases success

private theorem attach_output {before after : TSO64.State} {principal code caller : Nat}
    {entry : Context} {identifier : Atomics64.HandleId64}
    (success : TSO64.attach before principal entry code caller [] [identifier] = .ok after) :
    ∃ worker,
      TSO64.makeWorker before.world principal entry code caller [] [identifier] = .ok worker ∧
      after.world = before.world ∧ after.workers = before.workers ++ [worker] := by
  cases made : TSO64.makeWorker before.world principal entry code caller [] [identifier] with
  | error fault => simp [TSO64.attach, made] at success
  | ok worker =>
    simp only [TSO64.attach, made, ok_bind, pure_ok, Except.ok.injEq] at success
    cases success
    exact ⟨worker, rfl, rfl, rfl⟩

/-- Both real attachment equations and their actual output projections. -/
private theorem initial_outputs (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :
    ∃ first left right,
      TSO64.attach (emptyState named total old) (actor 0)
        (context named total old count upper flags 0)
        (codeId named total old 0) (callerId named total old 0) [] [atomicId named total old 0] =
        .ok first ∧
      TSO64.attach first (actor 1) (context named total old count upper flags 1)
        (codeId named total old 1) (callerId named total old 1) [] [atomicId named total old 1] =
        .ok (initial named total started old count upper flags) ∧
      (initial named total started old count upper flags).world =
        (Image.resources named total old).managed.world ∧
      (initial named total started old count upper flags).workers = [left, right] ∧
      Made (actor 0) (context named total old count upper flags 0)
        (codeId named total old 0) (callerId named total old 0) (atomicId named total old 0) left ∧
      Made (actor 1) (context named total old count upper flags 1)
        (codeId named total old 1) (callerId named total old 1) (atomicId named total old 1) right := by
  have success := started_eq named total started old count upper flags
  cases firstResult : TSO64.attach (emptyState named total old) (actor 0)
      (context named total old count upper flags 0)
      (codeId named total old 0) (callerId named total old 0) [] [atomicId named total old 0] with
  | error fault => simp [start, firstResult] at success
  | ok first =>
    have secondResult :
        TSO64.attach first (actor 1) (context named total old count upper flags 1)
          (codeId named total old 1) (callerId named total old 1) [] [atomicId named total old 1] =
          .ok (initial named total started old count upper flags) := by
      simpa only [start, firstResult, ok_bind] using success
    obtain ⟨left, leftMade, firstWorld, firstWorkers⟩ := attach_output firstResult
    obtain ⟨right, rightMade, finalWorld, finalWorkers⟩ := attach_output secondResult
    have world : (initial named total started old count upper flags).world =
        (Image.resources named total old).managed.world := finalWorld.trans firstWorld
    have workers : (initial named total started old count upper flags).workers = [left, right] := by
      rw [finalWorkers, firstWorkers]
      rfl
    exact ⟨first, left, right, rfl, secondResult, world, workers,
      made_of_success leftMade, made_of_success rightMade⟩

theorem initial_world (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :
    (initial named total started old count upper flags).world =
      (Image.resources named total old).managed.world := by
  obtain ⟨_first, _left, _right, _firstResult, _secondResult, world, _rest⟩ :=
    initial_outputs named total started old count upper flags
  exact world

theorem workerUniverse2 (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :
    (initial named total started old count upper flags).workers.length = 2 := by
  obtain ⟨_first, _left, _right, _firstResult, _secondResult, _world, workers, _rest⟩ :=
    initial_outputs named total started old count upper flags
  rw [workers]
  rfl

/-- The explicit ownedOnly profile follows from production attachment. -/
theorem wellFormed (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :
    WellFormed (initial named total started old count upper flags) .ownedOnly := by
  obtain ⟨_first, _left, _right, firstResult, secondResult, _rest⟩ :=
    initial_outputs named total started old count upper flags
  have emptyValid : WellFormed (emptyState named total old) .ownedOnly :=
    ⟨(Image.resources named total old).managed.valid, by simp [emptyState]⟩
  exact TSO64.attach_valid_for .ownedOnly
    (TSO64.attach_valid_for .ownedOnly emptyValid firstResult) secondResult

theorem quiescent (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :
    Quiescent (initial named total started old count upper flags) := by
  obtain ⟨_first, left, right, _firstResult, _secondResult, _world, workers, leftMade, rightMade⟩ :=
    initial_outputs named total started old count upper flags
  intro current member
  rw [workers] at member
  rcases List.mem_cons.mp member with same | member
  · cases same
    exact leftMade.pending
  · rcases List.mem_cons.mp member with same | member
    · cases same
      exact rightMade.pending
    · cases member

/-- Always project the actual initial list, using its proved population. -/
def worker (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) : Worker :=
  (initial named total started old count upper flags).workers[slot.val]'(by
    rw [workerUniverse2 named total started old count upper flags]
    exact slot.isLt)

theorem worker_live (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (initial named total started old count upper flags).workers[slot.val]? =
      some (worker named total started old count upper flags slot) :=
  List.getElem?_eq_getElem (by
    rw [workerUniverse2 named total started old count upper flags]
    exact slot.isLt)

private theorem worker_made (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    Made (actor slot) (context named total old count upper flags slot)
      (codeId named total old slot) (callerId named total old slot) (atomicId named total old slot)
      (worker named total started old count upper flags slot) := by
  obtain ⟨_first, left, right, _firstResult, _secondResult, _world, workers, leftMade, rightMade⟩ :=
    initial_outputs named total started old count upper flags
  rcases slot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl
  · have selected : worker named total started old count upper flags 0 = left := by
      apply Option.some.inj
      exact (worker_live named total started old count upper flags 0).symm.trans (by
        rw [workers]
        rfl)
    exact selected.symm ▸ leftMade
  · have selected : worker named total started old count upper flags 1 = right := by
      apply Option.some.inj
      exact (worker_live named total started old count upper flags 1).symm.trans (by
        rw [workers]
        rfl)
    exact selected.symm ▸ rightMade

theorem worker_context (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker named total started old count upper flags slot).context =
      context named total old count upper flags slot :=
  (worker_made named total started old count upper flags slot).context

theorem worker_running (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker named total started old count upper flags slot).phase = .running :=
  (worker_made named total started old count upper flags slot).running

theorem worker_pending (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker named total started old count upper flags slot).pending = [] :=
  (worker_made named total started old count upper flags slot).pending

theorem worker_nextStore (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker named total started old count upper flags slot).nextStore = 0 :=
  (worker_made named total started old count upper flags slot).nextStore

/-- Authority comes from actual successful operations and current validity. -/
theorem worker_resources (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    ResourcesValid (initial named total started old count upper flags).world
      (worker named total started old count upper flags slot).resources :=
  ((wellFormed named total started old count upper flags).2 _
    (List.mem_of_getElem? (worker_live named total started old count upper flags slot))).1

theorem worker_actor (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker named total started old count upper flags slot).resources.actor = actor slot :=
  (worker_made named total started old count upper flags slot).actor

theorem worker_callerId (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker named total started old count upper flags slot).resources.caller.identifier =
      callerId named total old slot :=
  (worker_made named total started old count upper flags slot).callerId

theorem worker_codeId (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker named total started old count upper flags slot).resources.code.identifier =
      codeId named total old slot :=
  (worker_made named total started old count upper flags slot).codeId

theorem worker_callerAddress (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker named total started old count upper flags slot).resources.callerAddress = stack slot :=
  (worker_made named total started old count upper flags slot).callerAddress

theorem worker_atomics (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker named total started old count upper flags slot).resources.atomics =
      [atomicId named total old slot] :=
  (worker_made named total started old count upper flags slot).atomics

theorem worker_grants (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker named total started old count upper flags slot).resources.grants = [] :=
  (worker_made named total started old count upper flags slot).grants

theorem worker_count (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    ((worker named total started old count upper flags slot).context.registers .rsi).setWidth 32 =
      count slot := by
  rw [worker_context]
  exact argument_low32 _ _

theorem worker_upper (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    ((worker named total started old count upper flags slot).context.registers .rsi).extractLsb' 32 32 =
      upper slot := by
  rw [worker_context]
  exact argument_upper32 _ _

theorem worker_flags (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (worker named total started old count upper flags slot).context.flags = flags slot := by
  rw [worker_context]
  rfl

#print axioms actor
#print axioms stack
#print axioms continuation
#print axioms codeId
#print axioms callerId
#print axioms atomicId
#print axioms argument
#print axioms argument_low32
#print axioms argument_upper32
#print axioms context
#print axioms emptyState
#print axioms start
#print axioms StartTotal
#print axioms initial
#print axioms started_eq
#print axioms Made
#print axioms made_of_success
#print axioms attach_output
#print axioms initial_outputs
#print axioms initial_world
#print axioms workerUniverse2
#print axioms wellFormed
#print axioms quiescent
#print axioms worker
#print axioms worker_live
#print axioms worker_made
#print axioms worker_context
#print axioms worker_running
#print axioms worker_pending
#print axioms worker_nextStore
#print axioms worker_resources
#print axioms worker_actor
#print axioms worker_callerId
#print axioms worker_codeId
#print axioms worker_callerAddress
#print axioms worker_atomics
#print axioms worker_grants
#print axioms worker_count
#print axioms worker_upper
#print axioms worker_flags

end EDSL.Corpus.CountedResources.Workers
#audit_edsl
