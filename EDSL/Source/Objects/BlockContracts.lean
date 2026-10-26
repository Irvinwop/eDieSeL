/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.BlockEval
import Init.Data.List.Range

set_option autoImplicit false
namespace EDSL.Source.Objects.BlockContracts
open StateSyntax LifecycleContracts

/-! Contracts for the existing block driver's complete reservation prefix.
The deterministic records below describe exact allocation effects; they are not
an alternate source evaluator or an admission condition. Admissions use only
registry metadata and abstract remaining object slots. -/

variable {target : Target} {parameters : List IntType} {Environment : Type}

/-- Source-order identities, determined by the initial fresh counter. -/
def reservationEnv (base : Nat) : (kinds : List ArithmeticType) → Env kinds
  | [] => .nil
  | _ :: kinds => .cons ⟨base⟩ (reservationEnv (base + 1) kinds)

/-- Exact reservation-only registry/resource specification. -/
def reservedAllState (dialect : Dialect) : List ArithmeticType →
    State target parameters Environment → State target parameters Environment
  | [], state => state
  | kind :: kinds, state => reservedAllState dialect kinds (reservedState dialect kind state)

/-- Each prefix reservation's actual primitive observations, in source order. -/
def reservationEvents (dialect : Dialect) (actor base : Nat) : List ArithmeticType → List Event
  | [] => []
  | kind :: kinds => reserveEvents dialect base kind actor ++
      reservationEvents dialect actor (base + 1) kinds

theorem reservedAllState_next (dialect : Dialect) (kinds : List ArithmeticType)
    (state : State target parameters Environment) :
    (reservedAllState dialect kinds state).next = state.next + kinds.length := by
  induction kinds generalizing state with
  | nil => simp [reservedAllState]
  | cons kind kinds ih =>
      simpa [reservedAllState, reservedState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih (reservedState dialect kind state)

theorem reservedAllState_frozen (dialect : Dialect) (kinds : List ArithmeticType)
    (state : State target parameters Environment) : Frozen state (reservedAllState dialect kinds state) := by
  induction kinds generalizing state with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons kind kinds ih =>
      simpa [reservedAllState, Frozen, reservedState, State.putObject]
        using ih (reservedState dialect kind state)

theorem reservedAllState_slots (dialect : Dialect) (kinds : List ArithmeticType)
    (state : State target parameters Environment) (capacity : kinds.length ≤ state.automaticSlots) :
    (reservedAllState dialect kinds state).automaticSlots + kinds.length = state.automaticSlots := by
  induction kinds generalizing state with
  | nil => simp [reservedAllState]
  | cons kind kinds ih =>
      have remaining : kinds.length ≤ (reservedState dialect kind state).automaticSlots := by
        simp only [reservedState]
        simp only [List.length_cons] at capacity
        omega
      have tail := ih (reservedState dialect kind state) remaining
      change (reservedAllState dialect kinds (reservedState dialect kind state)).automaticSlots +
        (kinds.length + 1) = state.automaticSlots
      have step : (reservedState dialect kind state).automaticSlots = state.automaticSlots - 1 := rfl
      rw [step] at tail
      simp only [List.length_cons] at capacity
      omega

theorem reservedAllState_wellFormed (dialect : Dialect) (kinds : List ArithmeticType)
    (state : State target parameters Environment) (metadata : state.WellFormed) :
    (reservedAllState dialect kinds state).WellFormed := by
  induction kinds generalizing state with
  | nil => exact metadata
  | cons kind kinds ih =>
      exact ih _ (reservedState_wellFormed dialect kind state metadata)

/-- Every identity outside the newly allocated interval is preserved exactly. -/
theorem reservedAllState_outside (dialect : Dialect) (kinds : List ArithmeticType)
    (state : State target parameters Environment) (query : Nat)
    (outside : query < state.next ∨ state.next + kinds.length ≤ query) :
    (reservedAllState dialect kinds state).objects query = state.objects query := by
  induction kinds generalizing state with
  | nil => rfl
  | cons kind kinds ih =>
      have different : query ≠ state.next := by
        simp only [List.length_cons] at outside
        omega
      have tailOutside : query < (reservedState dialect kind state).next ∨
          (reservedState dialect kind state).next + kinds.length ≤ query := by
        simp only [reservedState, List.length_cons] at *
        omega
      exact (ih _ tailOutside).trans (by
        exact State.putObject_other state state.next query _ different)

/-- Existing registered records, including tombstones, remain exactly registered. -/
theorem reservedAllState_registered (dialect : Dialect) (kinds : List ArithmeticType)
    (state : State target parameters Environment) (metadata : state.WellFormed)
    (id : Nat) (object : Object target) (registered : state.objects id = some object) :
    (reservedAllState dialect kinds state).objects id = some object := by
  rw [reservedAllState_outside dialect kinds state id (Or.inl (metadata id object registered).1)]
  exact registered

/-- Successful reservation of the entire prefix follows from metadata and capacity.
No operation result, source success, NoUB or program postcondition is admitted. -/
theorem reserveAll_eq (dialect : Dialect) (kinds : List ArithmeticType)
    (state : State target parameters Environment) (metadata : state.WellFormed)
    (capacity : kinds.length ≤ state.automaticSlots) :
    BlockEval.reserveAll dialect kinds state =
      (.ok (reservationEnv state.next kinds), reservedAllState dialect kinds state,
        reservationEvents dialect state.actor state.next kinds) := by
  induction kinds generalizing state with
  | nil => rfl
  | cons kind kinds ih =>
      have available : 0 < state.automaticSlots := by
        simp only [List.length_cons] at capacity
        omega
      have ready : CanReserve state := ⟨fresh_of_wellFormed state metadata, available⟩
      have remaining : kinds.length ≤ (reservedState dialect kind state).automaticSlots := by
        simp only [reservedState, List.length_cons] at *
        omega
      have tail := ih (reservedState dialect kind state)
        (reservedState_wellFormed dialect kind state metadata) remaining
      simp only [BlockEval.reserveAll, Op.bind, Effects.Op.bind, reserve_eq dialect kind state ready]
      rw [tail]
      simp only [Op.pure, List.append_nil, reservationEnv, reservedAllState, reservationEvents,
        reservedState, State.putObject]

/-- Every actual returned identity belongs to the fresh contiguous interval. -/
theorem reservationEnv_bounds (base : Nat) (kinds : List ArithmeticType) :
    ∀ id ∈ (reservationEnv base kinds).ids, base ≤ id ∧ id < base + kinds.length := by
  induction kinds generalizing base with
  | nil => simp [reservationEnv, Env.ids]
  | cons kind kinds ih =>
      intro id member
      simp only [reservationEnv, Env.ids, List.mem_cons] at member
      rcases member with same | member
      · subst id; simp only [List.length_cons]; omega
      · have bound := ih (base + 1) id member
        simp only [List.length_cons]
        omega

theorem reservationEnv_unique (base : Nat) (kinds : List ArithmeticType) :
    (reservationEnv base kinds).Unique := by
  induction kinds generalizing base with
  | nil => exact Env.unique_nil
  | cons kind kinds ih =>
      apply (Env.unique_extend_iff (reservationEnv (base + 1) kinds) (⟨base⟩ : LValue kind)).mpr
      refine ⟨?_, ih _⟩
      intro member
      have bound := reservationEnv_bounds (base + 1) kinds base member
      omega

/-- Typed source-order bindings name matching pending records in the final registry. -/
def PendingBindings (dialect : Dialect) (owner : Nat)
    (state : State target parameters Environment) : {kinds : List ArithmeticType} → Env kinds → Prop
  | [], .nil => True
  | kind :: _, .cons reference rest =>
      state.objects reference.id = some (pendingObject dialect kind owner ⟨true, true⟩) ∧
      PendingBindings dialect owner state rest

theorem reservedAllState_pending (dialect : Dialect) (kinds : List ArithmeticType)
    (state : State target parameters Environment) :
    PendingBindings dialect state.actor (reservedAllState dialect kinds state)
      (reservationEnv state.next kinds) := by
  induction kinds generalizing state with
  | nil => trivial
  | cons kind kinds ih =>
      refine ⟨?_, ?_⟩
      · change (reservedAllState dialect kinds (reservedState dialect kind state)).objects state.next = _
        rw [reservedAllState_outside dialect kinds (reservedState dialect kind state) state.next
          (Or.inl (by simp only [reservedState]; omega))]
        exact State.putObject_same state state.next _
      · exact ih (reservedState dialect kind state)

/-- The returned binding list is ordered, not merely a set of fresh identities. -/
theorem reservationEnv_ids (base : Nat) (kinds : List ArithmeticType) :
    (reservationEnv base kinds).ids = List.range' base kinds.length := by
  induction kinds generalizing base with
  | nil => simp [reservationEnv, Env.ids]
  | cons kind kinds ih => simp [reservationEnv, Env.ids, List.range'_succ, ih]

/-- No returned binding aliases any preexisting registry entry. -/
theorem reservationEnv_fresh (kinds : List ArithmeticType)
    (state : State target parameters Environment) (metadata : state.WellFormed) :
    ∀ id ∈ (reservationEnv state.next kinds).ids, state.objects id = none := by
  intro id member
  have bound := (reservationEnv_bounds state.next kinds id member).1
  cases registered : state.objects id with
  | none => rfl
  | some object =>
      have old := (metadata id object registered).1
      omega

/-- Complete prefix contract derived only from metadata and remaining capacity.
Exact bindings/effects and resource/frame facts are consequences, not admissions. -/
theorem reserveAll_contract (dialect : Dialect) (kinds : List ArithmeticType)
    (state : State target parameters Environment) (metadata : state.WellFormed)
    (capacity : kinds.length ≤ state.automaticSlots) :
    ∃ (environment : Env kinds) (finalState : State target parameters Environment) (events : List Event),
      BlockEval.reserveAll dialect kinds state = (.ok environment, finalState, events) ∧
      environment.ids = List.range' state.next kinds.length ∧ environment.Unique ∧
      (∀ id ∈ environment.ids, state.objects id = none) ∧
      PendingBindings dialect state.actor finalState environment ∧ finalState.WellFormed ∧
      Frozen state finalState ∧ finalState.next = state.next + kinds.length ∧
      finalState.automaticSlots + kinds.length = state.automaticSlots ∧
      (∀ query, query < state.next ∨ state.next + kinds.length ≤ query →
        finalState.objects query = state.objects query) ∧
      events = reservationEvents dialect state.actor state.next kinds := by
  refine ⟨reservationEnv state.next kinds, reservedAllState dialect kinds state,
    reservationEvents dialect state.actor state.next kinds,
    reserveAll_eq dialect kinds state metadata capacity,
    reservationEnv_ids state.next kinds, reservationEnv_unique state.next kinds,
    reservationEnv_fresh kinds state metadata, reservedAllState_pending dialect kinds state,
    reservedAllState_wellFormed dialect kinds state metadata,
    reservedAllState_frozen dialect kinds state, reservedAllState_next dialect kinds state,
    reservedAllState_slots dialect kinds state capacity, ?_, rfl⟩
  exact reservedAllState_outside dialect kinds state

/-- Independent cleanup admission: each binding currently denotes a reached live
object of its matching kind, owned by the current actor. No result is assumed. -/
def LiveBindings (state : State target parameters Environment) :
    {kinds : List ArithmeticType} → Env kinds → Prop
  | [], .nil => True
  | _ :: _, .cons reference rest => CanEnd reference state ∧ LiveBindings state rest

/-- Every successfully closed binding has an ended record of its matching kind
and owner, with a typed optional value and permissions; its identity is retained. -/
def EndedBindings (owner : Nat) (state : State target parameters Environment) :
    {kinds : List ArithmeticType} → Env kinds → Prop
  | [], .nil => True
  | kind :: _, .cons reference rest =>
      (∃ (value : Option (Value target kind.asIntType)) (permissions : Permissions),
        state.objects reference.id =
          some { liveObject kind owner permissions value with life := .ended }) ∧
      EndedBindings owner state rest

theorem endedBindings_transport {kinds : List ArithmeticType} (environment : Env kinds)
    (owner : Nat) (before after : State target parameters Environment)
    (same : ∀ id ∈ environment.ids, after.objects id = before.objects id)
    (ended : EndedBindings owner before environment) : EndedBindings owner after environment := by
  induction environment with
  | nil => trivial
  | @cons kind kinds reference environment ih =>
      refine ⟨?_, ih ?_ ended.2⟩
      · obtain ⟨value, permissions, registered⟩ := ended.1
        refine ⟨value, permissions, ?_⟩
        rw [same reference.id (by simp [Env.ids])]
        exact registered
      · intro id member
        exact same id (by simp only [Env.ids, List.mem_cons]; exact Or.inr member)

/-- Successful cleanup observations are reverse declaration order. -/
def closingEvents : {kinds : List ArithmeticType} → Env kinds → List Event
  | [], .nil => []
  | kind :: _, .cons reference rest => closingEvents rest ++ [.endLifetime reference.id kind]

/-- Cleanup follows from independent live bindings and identity uniqueness;
complete state framing and slot restoration are conclusions. Stored values and
permissions are unrestricted. This covers successful normal cleanup only. -/
theorem closeAll_contract {kinds : List ArithmeticType} (environment : Env kinds)
    (state : State target parameters Environment) (metadata : state.WellFormed)
    (unique : environment.Unique) (live : LiveBindings state environment) :
    ∃ finalState : State target parameters Environment,
      BlockEval.closeAll environment state = (.ok (), finalState, closingEvents environment) ∧
      Frozen state finalState ∧ finalState.next = state.next ∧
      finalState.automaticSlots = state.automaticSlots + kinds.length ∧ finalState.WellFormed ∧
      EndedBindings state.actor finalState environment ∧
      (∀ query, query ∉ environment.ids → finalState.objects query = state.objects query) := by
  induction environment generalizing state with
  | nil =>
      refine ⟨state, rfl, ⟨rfl, rfl, rfl⟩, rfl, ?_, metadata, trivial, ?_⟩
      · simp
      · intros; rfl
  | @cons kind kinds reference environment ih =>
      obtain ⟨fresh, tailUnique⟩ := (Env.unique_extend_iff environment reference).mp unique
      obtain ⟨middle, tailRun, frozen, counter, slots, tailMetadata, tailEnded, frame⟩ :=
        ih state metadata tailUnique live.2
      have ready : CanEnd reference middle := by
        obtain ⟨object, registered, matching, lifetime, reached, owner⟩ := live.1
        refine ⟨object, ?_, matching, lifetime, reached, owner.trans frozen.2.2.symm⟩
        rw [frame reference.id fresh]
        exact registered
      obtain ⟨value, permissions, registered⟩ := (canEnd_iff_snapshot reference middle).mp ready
      have headRun := endLifetime_eq reference middle permissions value registered
      refine ⟨endedState reference permissions value middle, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [BlockEval.closeAll, Op.bind, Effects.Op.bind, tailRun, headRun, closingEvents]
      · simpa only [Frozen, endedState, State.putObject] using frozen
      · change middle.next = state.next
        exact counter
      · change middle.automaticSlots + 1 = state.automaticSlots + (kinds.length + 1)
        omega
      · exact endedState_wellFormed reference middle permissions value tailMetadata registered
      · refine ⟨⟨value, permissions, ?_⟩, ?_⟩
        · change (middle.putObject reference.id
              { liveObject kind middle.actor permissions value with life := .ended }).objects reference.id = _
          rw [State.putObject_same, frozen.2.2]
        · apply endedBindings_transport environment state.actor middle
            (endedState reference permissions value middle) _ tailEnded
          intro query member
          apply State.putObject_other middle reference.id query _
          intro same
          exact fresh (same ▸ member)
      · intro query outside
        have different : query ≠ reference.id := by
          intro same
          apply outside
          simp only [Env.ids, List.mem_cons]
          exact Or.inl same
        have tailOutside : query ∉ environment.ids := by
          intro member
          exact outside (by simp only [Env.ids, List.mem_cons]; exact Or.inr member)
        exact (State.putObject_other middle reference.id query _ different).trans
          (frame query tailOutside)

end EDSL.Source.Objects.BlockContracts
