/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.BlockContracts
import EDSL.Source.Objects.BlockEquations
import EDSL.Source.Objects.AccessContracts

set_option autoImplicit false
namespace EDSL.Source.Objects.ParameterContracts
open StateSyntax LifecycleContracts BlockContracts

/-! Contracts for the actual formal-parameter entry operation. Admissions are
only registry metadata and remaining abstract object slots. Call values, target,
dialect, old registry, immutable state inputs and external environment are arbitrary.
The record/event folds specify allocation and initialization effects; they do not
execute source expressions. No interference, byte layout, ABI, native execution,
or whole-program definedness claim is made here. -/

variable {target : Target} {stateParameters : List IntType} {Environment : Type}

/-- One fresh formal object, with the exact externally supplied typed value. -/
def parameterState (dialect : Dialect) {kind : ArithmeticType}
    (value : Value target kind.asIntType) (state : State target stateParameters Environment) :
    State target stateParameters Environment :=
  initializedState (⟨state.next⟩ : LValue kind) ⟨true, true⟩ (some value)
    (reservedState dialect kind state)

/-- Source-order fold of exact reservation and initialization records. -/
def parametersState (dialect : Dialect) : {kinds : List ArithmeticType} →
    CallInputs target kinds → State target stateParameters Environment →
    State target stateParameters Environment
  | [], .nil, state => state
  | _ :: _, .cons value rest, state =>
      parametersState dialect rest (parameterState dialect value state)

/-- Internal primitive events, including dialect-specific lifetime placement. -/
def parameterEvents (dialect : Dialect) (actor base : Nat) :
    {kinds : List ArithmeticType} → CallInputs target kinds → List Event
  | [], .nil => []
  | kind :: _, .cons value rest =>
      reserveEvents dialect base kind actor ++
      (initializeEvents dialect base kind (some value.toInt) ++
        parameterEvents dialect actor (base + 1) rest)

/-- Each source-order binding names a reached, live, fully authorized record
containing its corresponding external value. This is a registry predicate. -/
def InitializedBindings (owner : Nat) (state : State target stateParameters Environment) :
    {kinds : List ArithmeticType} → Env kinds → CallInputs target kinds → Prop
  | [], .nil, .nil => True
  | kind :: _, .cons reference tail, .cons value rest =>
      state.objects reference.id = some (liveObject kind owner ⟨true, true⟩ (some value)) ∧
      InitializedBindings owner state tail rest

theorem parameterState_registered (dialect : Dialect) {kind : ArithmeticType}
    (value : Value target kind.asIntType) (state : State target stateParameters Environment) :
    (parameterState dialect value state).objects state.next =
      some (liveObject kind state.actor ⟨true, true⟩ (some value)) := by
  exact State.putObject_same (reservedState dialect kind state) state.next _

theorem parameterState_other (dialect : Dialect) {kind : ArithmeticType}
    (value : Value target kind.asIntType) (state : State target stateParameters Environment)
    (query : Nat) (different : query ≠ state.next) :
    (parameterState dialect value state).objects query = state.objects query := by
  exact (State.putObject_other (reservedState dialect kind state) state.next query _ different).trans
    (State.putObject_other state state.next query _ different)

theorem parameterState_wellFormed (dialect : Dialect) {kind : ArithmeticType}
    (value : Value target kind.asIntType) (state : State target stateParameters Environment)
    (metadata : state.WellFormed) : (parameterState dialect value state).WellFormed := by
  exact initializedState_wellFormed dialect ⟨state.next⟩ (reservedState dialect kind state)
    ⟨true, true⟩ (some value) (reservedState_wellFormed dialect kind state metadata)
    (State.putObject_same state state.next _)

theorem parametersState_next (dialect : Dialect) {kinds : List ArithmeticType}
    (values : CallInputs target kinds) (state : State target stateParameters Environment) :
    (parametersState dialect values state).next = state.next + kinds.length := by
  induction kinds generalizing state with
  | nil => cases values; simp [parametersState]
  | cons kind kinds ih =>
      cases values with
      | cons value rest =>
          have tail := ih rest (parameterState dialect value state)
          change (parametersState dialect rest (parameterState dialect value state)).next =
            state.next + (kinds.length + 1)
          change (parametersState dialect rest (parameterState dialect value state)).next =
            state.next + 1 + kinds.length at tail
          omega

theorem parametersState_frozen (dialect : Dialect) {kinds : List ArithmeticType}
    (values : CallInputs target kinds) (state : State target stateParameters Environment) :
    Frozen state (parametersState dialect values state) := by
  induction kinds generalizing state with
  | nil => cases values; exact ⟨rfl, rfl, rfl⟩
  | cons kind kinds ih =>
      cases values with
      | cons value rest =>
          exact ih rest (parameterState dialect value state)

theorem parametersState_slots (dialect : Dialect) {kinds : List ArithmeticType}
    (values : CallInputs target kinds) (state : State target stateParameters Environment)
    (capacity : kinds.length ≤ state.automaticSlots) :
    (parametersState dialect values state).automaticSlots + kinds.length = state.automaticSlots := by
  induction kinds generalizing state with
  | nil => cases values; simp [parametersState]
  | cons kind kinds ih =>
      cases values with
      | cons value rest =>
          have step : (parameterState dialect value state).automaticSlots =
              state.automaticSlots - 1 := rfl
          have remaining : kinds.length ≤ (parameterState dialect value state).automaticSlots := by
            simp only [List.length_cons] at capacity
            rw [step]
            omega
          have tail := ih rest (parameterState dialect value state) remaining
          change (parametersState dialect rest (parameterState dialect value state)).automaticSlots +
            (kinds.length + 1) = state.automaticSlots
          rw [step] at tail
          simp only [List.length_cons] at capacity
          omega

theorem parametersState_wellFormed (dialect : Dialect) {kinds : List ArithmeticType}
    (values : CallInputs target kinds) (state : State target stateParameters Environment)
    (metadata : state.WellFormed) : (parametersState dialect values state).WellFormed := by
  induction kinds generalizing state with
  | nil => cases values; exact metadata
  | cons kind kinds ih =>
      cases values with
      | cons value rest =>
          exact ih rest _ (parameterState_wellFormed dialect value state metadata)

/-- Every entry outside the newly allocated half-open interval is unchanged. -/
theorem parametersState_outside (dialect : Dialect) {kinds : List ArithmeticType}
    (values : CallInputs target kinds) (state : State target stateParameters Environment)
    (query : Nat) (outside : query < state.next ∨ state.next + kinds.length ≤ query) :
    (parametersState dialect values state).objects query = state.objects query := by
  induction kinds generalizing state with
  | nil => cases values; rfl
  | cons kind kinds ih =>
      cases values with
      | cons value rest =>
          have different : query ≠ state.next := by
            simp only [List.length_cons] at outside
            omega
          have tailOutside : query < (parameterState dialect value state).next ∨
              (parameterState dialect value state).next + kinds.length ≤ query := by
            change query < state.next + 1 ∨ state.next + 1 + kinds.length ≤ query
            simp only [List.length_cons] at outside
            omega
          exact (ih rest _ tailOutside).trans (parameterState_other dialect value state query different)

/-- This includes arbitrary preexisting live, pending and ended records. -/
theorem parametersState_registered (dialect : Dialect) {kinds : List ArithmeticType}
    (values : CallInputs target kinds) (state : State target stateParameters Environment)
    (metadata : state.WellFormed) (id : Nat) (object : Object target)
    (registered : state.objects id = some object) :
    (parametersState dialect values state).objects id = some object := by
  rw [parametersState_outside dialect values state id (Or.inl (metadata id object registered).1)]
  exact registered

theorem parametersState_initialized (dialect : Dialect) {kinds : List ArithmeticType}
    (values : CallInputs target kinds) (state : State target stateParameters Environment) :
    InitializedBindings state.actor (parametersState dialect values state)
      (reservationEnv state.next kinds) values := by
  induction kinds generalizing state with
  | nil => cases values; trivial
  | cons kind kinds ih =>
      cases values with
      | cons value rest =>
          refine ⟨?_, ih rest (parameterState dialect value state)⟩
          change (parametersState dialect rest (parameterState dialect value state)).objects state.next = _
          rw [parametersState_outside dialect rest (parameterState dialect value state) state.next
            (Or.inl (by change state.next < state.next + 1; omega))]
          exact parameterState_registered dialect value state

/-- Actual successful parameter entry, proved by the public constructor equations
and lifecycle primitive contracts. No execution result is an admission. -/
theorem enterParameters_eq (dialect : Dialect) {kinds : List ArithmeticType}
    (values : CallInputs target kinds) (state : State target stateParameters Environment)
    (metadata : state.WellFormed) (capacity : kinds.length ≤ state.automaticSlots) :
    BlockEval.enterParameters dialect values state =
      (.ok (reservationEnv state.next kinds), parametersState dialect values state,
        parameterEvents dialect state.actor state.next values) := by
  induction kinds generalizing state with
  | nil => cases values; rfl
  | cons kind kinds ih =>
      cases values with
      | cons value rest =>
          have available : 0 < state.automaticSlots := by
            simp only [List.length_cons] at capacity
            omega
          have ready : CanReserve state := ⟨fresh_of_wellFormed state metadata, available⟩
          have remaining : kinds.length ≤ (parameterState dialect value state).automaticSlots := by
            change kinds.length ≤ state.automaticSlots - 1
            simp only [List.length_cons] at capacity
            omega
          have tail := ih rest (parameterState dialect value state)
            (parameterState_wellFormed dialect value state metadata) remaining
          have completion := initialize_eq dialect (⟨state.next⟩ : LValue kind)
            (reservedState dialect kind state) ⟨true, true⟩ (some value)
            (State.putObject_same state state.next _) rfl
          rw [BlockEval.enterParameters_cons]
          simp only [Op.bind, Effects.Op.bind, reserve_eq dialect kind state ready, completion]
          dsimp only [parameterState] at tail
          rw [tail]
          simp only [Op.pure, List.append_nil]
          rfl

/-- The recursive registry specification resolves every typed source variable
to its corresponding externally supplied value, including mixed-kind lists. -/
theorem initializedBindings_get {kinds : List ArithmeticType} (environment : Env kinds)
    (values : CallInputs target kinds) (owner : Nat)
    (state : State target stateParameters Environment)
    (initialized : InitializedBindings owner state environment values)
    {kind : ArithmeticType} (index : Vars kinds kind) :
    state.objects (environment.get index).id =
      some (liveObject kind owner ⟨true, true⟩ (some (values.get index))) := by
  induction environment with
  | nil => cases index
  | @cons head kinds reference environment ih =>
      cases values with
      | cons value rest =>
          cases head <;> cases kind <;> cases index
          all_goals first | exact initialized.1 | exact ih rest initialized.2 _

/-- Both independent access admissions follow from the exact typed records.
No load/store execution equation is assumed. -/
theorem initializedBindings_access {kinds : List ArithmeticType} (environment : Env kinds)
    (values : CallInputs target kinds) (state : State target stateParameters Environment)
    (initialized : InitializedBindings state.actor state environment values)
    {kind : ArithmeticType} (index : Vars kinds kind) :
    CanLoad state (environment.get index) (values.get index) ∧
      CanStore state (environment.get index) := by
  have registered := initializedBindings_get environment values state.actor state initialized index
  exact ⟨⟨⟨true, true⟩, registered, rfl⟩,
    ⟨some (values.get index), ⟨true, true⟩, registered, rfl⟩⟩

/-- Exact initialized records also provide the existing normal-cleanup admission. -/
theorem initializedBindings_live {kinds : List ArithmeticType} (environment : Env kinds)
    (values : CallInputs target kinds) (state : State target stateParameters Environment)
    (initialized : InitializedBindings state.actor state environment values) :
    LiveBindings state environment := by
  induction environment with
  | nil => trivial
  | @cons kind kinds reference environment ih =>
      cases values with
      | cons value rest =>
          exact ⟨⟨_, initialized.1, rfl, rfl, rfl, rfl⟩, ih rest initialized.2⟩

/-- A preexisting record cannot alias any of the returned parameter identities. -/
theorem reservationEnv_noAlias (kinds : List ArithmeticType)
    (state : State target stateParameters Environment) (metadata : state.WellFormed)
    (oldId : Nat) (object : Object target) (registered : state.objects oldId = some object) :
    ∀ id ∈ (reservationEnv state.next kinds).ids, id ≠ oldId := by
  intro id member
  have fresh := (reservationEnv_bounds state.next kinds id member).1
  have old := (metadata oldId object registered).1
  omega

/-- Complete parameter-entry contract for arbitrary initial registries and typed
external call values. Metadata and capacity are the only admissions. Every
returned binding and all resource, access and frame facts are consequences. -/
theorem enterParameters_contract (dialect : Dialect) {kinds : List ArithmeticType}
    (values : CallInputs target kinds) (state : State target stateParameters Environment)
    (metadata : state.WellFormed) (capacity : kinds.length ≤ state.automaticSlots) :
    ∃ (environment : Env kinds) (finalState : State target stateParameters Environment)
        (events : List Event),
      BlockEval.enterParameters dialect values state = (.ok environment, finalState, events) ∧
      environment = reservationEnv state.next kinds ∧
      environment.ids = List.range' state.next kinds.length ∧ environment.Unique ∧
      (∀ id ∈ environment.ids, state.objects id = none) ∧
      (∀ oldId object, state.objects oldId = some object →
        (∀ id ∈ environment.ids, id ≠ oldId) ∧ finalState.objects oldId = some object) ∧
      InitializedBindings state.actor finalState environment values ∧
      (∀ (kind : ArithmeticType) (index : Vars kinds kind),
        CanLoad finalState (environment.get index) (values.get index) ∧
          CanStore finalState (environment.get index)) ∧
      LiveBindings finalState environment ∧ finalState.WellFormed ∧ Frozen state finalState ∧
      finalState.next = state.next + kinds.length ∧
      finalState.automaticSlots + kinds.length = state.automaticSlots ∧
      (∀ query, query < state.next ∨ state.next + kinds.length ≤ query →
        finalState.objects query = state.objects query) ∧
      finalState = parametersState dialect values state ∧
      events = parameterEvents dialect state.actor state.next values := by
  have initialized := parametersState_initialized dialect values state
  have frozen := parametersState_frozen dialect values state
  have owned : InitializedBindings (parametersState dialect values state).actor
      (parametersState dialect values state) (reservationEnv state.next kinds) values := by
    rw [frozen.2.2]
    exact initialized
  refine ⟨reservationEnv state.next kinds, parametersState dialect values state,
    parameterEvents dialect state.actor state.next values,
    enterParameters_eq dialect values state metadata capacity, rfl,
    reservationEnv_ids state.next kinds, reservationEnv_unique state.next kinds,
    reservationEnv_fresh kinds state metadata, ?_, initialized, ?_,
    initializedBindings_live _ values _ owned,
    parametersState_wellFormed dialect values state metadata, frozen,
    parametersState_next dialect values state, parametersState_slots dialect values state capacity,
    parametersState_outside dialect values state, rfl, rfl⟩
  · intro oldId object registered
    exact ⟨reservationEnv_noAlias kinds state metadata oldId object registered,
      parametersState_registered dialect values state metadata oldId object registered⟩
  · intro kind index
    exact initializedBindings_access _ values _ owned index

end EDSL.Source.Objects.ParameterContracts
