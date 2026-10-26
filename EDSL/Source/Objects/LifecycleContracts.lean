/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Access

set_option autoImplicit false

namespace EDSL.Source.Objects.LifecycleContracts

/-! Checked contracts for the finite automatic-object declaration prefix.

All admissions below describe the current registry, metadata, authority and slot
capacity, independently of an operation's result. The actor and external world
are frozen: no interference, scheduler or OS correspondence is assumed or proved.
Slots count abstract automatic objects, not bytes. Initializers are already typed
values, not source expressions. Source completion, exceptions, unwinding and
pending-declaration recovery are outside this model. Raw traces are internal;
there is no source-program, object-byte, ABI or native-execution claim here.
-/

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {kind : ArithmeticType}

/-- Whole external world, including the current actor, is unchanged. -/
def Frozen (before after : State target parameters Environment) : Prop :=
  after.inputs = before.inputs ∧ after.environment = before.environment ∧
    after.actor = before.actor

/-- Every registry entry except the designated identity is unchanged. -/
def OtherObjects (before after : State target parameters Environment) (id : Nat) : Prop :=
  ∀ query, query ≠ id → after.objects query = before.objects query

/-- A declaration's independent pending metadata: C is already live; C++ is reserved.
Neither has reached its declaration or acquired an initialized value. -/
def pendingObject (dialect : Dialect) (kind : ArithmeticType) (owner : Nat)
    (permissions : Permissions) : Object target where
  kind := kind
  life := match dialect with | .gnuC23 => .live | .gnuCpp26 => .reserved
  reached := false
  value := none
  owner := owner
  permissions := permissions

/-- A reached live record with the exact supplied typed option, including `none`. -/
def liveObject (kind : ArithmeticType) (owner : Nat) (permissions : Permissions)
    (value : Option (Value target kind.asIntType)) : Object target where
  kind := kind
  life := .live
  reached := true
  value := value
  owner := owner
  permissions := permissions

/-- Current freshness and remaining capacity; no success or definedness premise. -/
def CanReserve (state : State target parameters Environment) : Prop :=
  state.objects state.next = none ∧ 0 < state.automaticSlots

/-- Registry equality specifies kind, pending lifetime, unreached declaration,
no old value, and current ownership. Write authority is required independently;
read authority and remaining capacity are irrelevant to declaration completion. -/
def CanInitialize (dialect : Dialect) (ref : LValue kind)
    (state : State target parameters Environment) : Prop :=
  ∃ object : Object target, state.objects ref.id = some object ∧ object.kind = kind ∧
    object.reached = false ∧
    object.life = (match dialect with | .gnuC23 => .live | .gnuCpp26 => .reserved) ∧
    object.value = none ∧ object.owner = state.actor ∧ object.permissions.writable = true

/-- End requires this kind, reached/live metadata and current ownership.
Permissions and the stored typed option are unrestricted; ending needs no write
permission and does not read the value. -/
def CanEnd (ref : LValue kind) (state : State target parameters Environment) : Prop :=
  ∃ object : Object target, state.objects ref.id = some object ∧ object.kind = kind ∧
    object.life = .live ∧ object.reached = true ∧ object.owner = state.actor

theorem canInitialize_iff_snapshot (dialect : Dialect) (ref : LValue kind)
    (state : State target parameters Environment) :
    CanInitialize dialect ref state ↔
      ∃ permissions : Permissions, permissions.writable = true ∧
        state.objects ref.id = some (pendingObject dialect kind state.actor permissions) := by
  constructor
  · rintro ⟨object, registered, same, unreached, life, uninitialized, owner, writable⟩
    cases object with
    | mk objectKind objectLife objectReached objectValue objectOwner permissions =>
        dsimp only at same unreached life uninitialized owner writable
        subst objectKind objectLife objectReached objectOwner
        subst objectValue
        exact ⟨permissions, writable, registered⟩
  · rintro ⟨permissions, writable, registered⟩
    exact ⟨_, registered, rfl, rfl, rfl, rfl, rfl, writable⟩

theorem canEnd_iff_snapshot (ref : LValue kind) (state : State target parameters Environment) :
    CanEnd ref state ↔
      ∃ (value : Option (Value target kind.asIntType)) (permissions : Permissions),
        state.objects ref.id = some (liveObject kind state.actor permissions value) := by
  constructor
  · rintro ⟨object, registered, same, life, reached, owner⟩
    cases object with
    | mk objectKind objectLife objectReached objectValue objectOwner permissions =>
        dsimp only at same life reached owner
        subst objectKind objectLife objectReached objectOwner
        exact ⟨objectValue, permissions, registered⟩
  · rintro ⟨value, permissions, registered⟩
    exact ⟨_, registered, rfl, rfl, rfl, rfl⟩

/-- Specification states name exact effects; they are not admission predicates. -/
def reservedState (dialect : Dialect) (kind : ArithmeticType)
    (state : State target parameters Environment) : State target parameters Environment :=
  { state.putObject state.next (pendingObject dialect kind state.actor ⟨true, true⟩) with
    next := state.next + 1
    automaticSlots := state.automaticSlots - 1 }

def initializedState (ref : LValue kind) (permissions : Permissions)
    (value : Option (Value target kind.asIntType))
    (state : State target parameters Environment) : State target parameters Environment :=
  state.putObject ref.id (liveObject kind state.actor permissions value)

def endedState (ref : LValue kind) (permissions : Permissions)
    (value : Option (Value target kind.asIntType))
    (state : State target parameters Environment) : State target parameters Environment :=
  { state.putObject ref.id { liveObject kind state.actor permissions value with life := .ended }
    with automaticSlots := state.automaticSlots + 1 }

def reserveEvents (dialect : Dialect) (id : Nat) (kind : ArithmeticType) (actor : Nat) :
    List Event :=
  match dialect with
  | .gnuC23 => [.reserve id kind actor, .beginLifetime id kind]
  | .gnuCpp26 => [.reserve id kind actor]

/-- C++ completion is observed before lifetime begin. -/
def initializeEvents (dialect : Dialect) (id : Nat) (kind : ArithmeticType)
    (value : Option Int) : List Event :=
  match dialect with
  | .gnuC23 => [.initialize id kind value]
  | .gnuCpp26 => [.initialize id kind value, .beginLifetime id kind]

theorem reserve_eq (dialect : Dialect) (kind : ArithmeticType)
    (state : State target parameters Environment) (ready : CanReserve state) :
    reserve dialect kind state =
      (.ok ⟨state.next⟩, reservedState dialect kind state,
        reserveEvents dialect state.next kind state.actor) := by
  have available : state.automaticSlots ≠ 0 := by have positive := ready.2; omega
  cases dialect <;>
    simp [reserve, ready.1, available, reservedState, pendingObject,
      reservationLife, reserveEvents]

theorem initialize_eq (dialect : Dialect) (ref : LValue kind)
    (state : State target parameters Environment) (permissions : Permissions)
    (value : Option (Value target kind.asIntType))
    (registered : state.objects ref.id =
      some (pendingObject dialect kind state.actor permissions))
    (writable : permissions.writable = true) :
    Objects.initialize dialect ref value state =
      (.ok (), initializedState ref permissions value state,
        initializeEvents dialect ref.id kind (value.map Value.toInt)) := by
  cases dialect <;>
    simp [Objects.initialize, registered, pendingObject, reservationLife,
      writable, initializedState, liveObject, initializeEvents]

theorem endLifetime_eq (ref : LValue kind) (state : State target parameters Environment)
    (permissions : Permissions) (value : Option (Value target kind.asIntType))
    (registered : state.objects ref.id = some (liveObject kind state.actor permissions value)) :
    endLifetime ref state =
      (.ok (), endedState ref permissions value state, [.endLifetime ref.id kind]) := by
  simp [endLifetime, registered, liveObject, endedState]

/-- Admissions establish actual success, rather than presupposing it. -/
theorem initialize_contract (dialect : Dialect) (ref : LValue kind)
    (state : State target parameters Environment) (value : Option (Value target kind.asIntType))
    (ready : CanInitialize dialect ref state) :
    ∃ permissions, permissions.writable = true ∧
      Objects.initialize dialect ref value state =
        (.ok (), initializedState ref permissions value state,
          initializeEvents dialect ref.id kind (value.map Value.toInt)) := by
  obtain ⟨permissions, writable, registered⟩ := (canInitialize_iff_snapshot dialect ref state).mp ready
  exact ⟨permissions, writable, initialize_eq dialect ref state permissions value registered writable⟩

theorem endLifetime_contract (ref : LValue kind) (state : State target parameters Environment)
    (ready : CanEnd ref state) :
    ∃ value permissions, endLifetime ref state =
      (.ok (), endedState ref permissions value state, [.endLifetime ref.id kind]) := by
  obtain ⟨value, permissions, registered⟩ := (canEnd_iff_snapshot ref state).mp ready
  exact ⟨value, permissions, endLifetime_eq ref state permissions value registered⟩

/-- The new registry entry is bounded, and every old entry keeps its bound. -/
theorem putObject_wellFormed (state : State target parameters Environment)
    (id : Nat) (object : Object target) (wellFormed : state.WellFormed)
    (bound : id < state.next) (metadata : object.WellFormed) :
    (state.putObject id object).WellFormed := by
  intro query found registered
  by_cases same : query = id
  · subst query
    rw [State.putObject_same] at registered
    cases registered
    exact ⟨bound, metadata⟩
  · rw [State.putObject_other state id query object same] at registered
    exact wellFormed query found registered

theorem fresh_of_wellFormed (state : State target parameters Environment)
    (wellFormed : state.WellFormed) : state.objects state.next = none := by
  cases registered : state.objects state.next with
  | none => rfl
  | some object =>
      have bound := (wellFormed state.next object registered).1
      omega

theorem pendingObject_wellFormed (dialect : Dialect) (kind : ArithmeticType)
    (owner : Nat) (permissions : Permissions) :
    (pendingObject (target := target) dialect kind owner permissions).WellFormed := by
  cases dialect <;> simp [Object.WellFormed, pendingObject]

theorem liveObject_wellFormed (kind : ArithmeticType) (owner : Nat)
    (permissions : Permissions) (value : Option (Value target kind.asIntType)) :
    (liveObject kind owner permissions value).WellFormed := by
  simp [Object.WellFormed, liveObject]

theorem reservedState_wellFormed (dialect : Dialect) (kind : ArithmeticType)
    (state : State target parameters Environment) (wellFormed : state.WellFormed) :
    (reservedState dialect kind state).WellFormed := by
  intro id object registered
  by_cases same : id = state.next
  · subst id
    have equal : pendingObject dialect kind state.actor ⟨true, true⟩ = object := by
      simpa [reservedState, State.putObject] using registered
    subst object
    exact ⟨by simp [reservedState], pendingObject_wellFormed dialect kind state.actor _⟩
  · have previous : state.objects id = some object := by
      simpa [reservedState, State.putObject, same] using registered
    have old := wellFormed id object previous
    exact ⟨by have bound := old.1; simp only [reservedState]; omega, old.2⟩

theorem initializedState_wellFormed (dialect : Dialect) (ref : LValue kind)
    (state : State target parameters Environment) (permissions : Permissions)
    (value : Option (Value target kind.asIntType))
    (wellFormed : state.WellFormed)
    (registered : state.objects ref.id =
      some (pendingObject dialect kind state.actor permissions)) :
    (initializedState ref permissions value state).WellFormed := by
  exact putObject_wellFormed state ref.id _ wellFormed
    (wellFormed ref.id _ registered).1 (liveObject_wellFormed kind state.actor permissions value)

theorem endedState_wellFormed (ref : LValue kind) (state : State target parameters Environment)
    (permissions : Permissions) (value : Option (Value target kind.asIntType))
    (wellFormed : state.WellFormed)
    (registered : state.objects ref.id = some (liveObject kind state.actor permissions value)) :
    (endedState ref permissions value state).WellFormed := by
  have updated := putObject_wellFormed state ref.id
    { liveObject kind state.actor permissions value with life := .ended } wellFormed
    (wellFormed ref.id _ registered).1 (by simp [Object.WellFormed, liveObject])
  exact updated

/-- A primitive's own failure preserves the entire state and emits nothing. These
laws include malformed inputs, and say nothing about rolling back earlier binds. -/
theorem reserve_rejects_unchanged (dialect : Dialect) (kind : ArithmeticType)
    (state : State target parameters Environment) (reason : Stop)
    (rejected : (reserve dialect kind state).1 = .error reason) :
    reserve dialect kind state = (.error reason, state, []) := by
  unfold reserve at rejected ⊢
  repeat' first | split at rejected | simp_all [Op.reject]

theorem initialize_rejects_unchanged (dialect : Dialect) (ref : LValue kind)
    (value : Option (Value target kind.asIntType))
    (state : State target parameters Environment) (reason : Stop)
    (rejected : (Objects.initialize dialect ref value state).1 = .error reason) :
    Objects.initialize dialect ref value state = (.error reason, state, []) := by
  unfold Objects.initialize at rejected ⊢
  repeat' first | split at rejected | simp_all [Op.reject]

theorem endLifetime_rejects_unchanged (ref : LValue kind)
    (state : State target parameters Environment) (reason : Stop)
    (rejected : (endLifetime ref state).1 = .error reason) :
    endLifetime ref state = (.error reason, state, []) := by
  unfold endLifetime at rejected ⊢
  repeat' first | split at rejected | simp_all [Op.reject]

/-- All outcomes, including rejection, frame the external world. -/
theorem reserve_frozen (dialect : Dialect) (kind : ArithmeticType)
    (state : State target parameters Environment) :
    Frozen state (reserve dialect kind state).2.1 := by
  unfold reserve
  repeat' first | split | exact ⟨rfl, rfl, rfl⟩

theorem initialize_frozen (dialect : Dialect) (ref : LValue kind)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment) :
    Frozen state (Objects.initialize dialect ref value state).2.1 := by
  unfold Objects.initialize
  repeat' first | split | exact ⟨rfl, rfl, rfl⟩

theorem endLifetime_frozen (ref : LValue kind) (state : State target parameters Environment) :
    Frozen state (endLifetime ref state).2.1 := by
  unfold endLifetime
  repeat' first | split | exact ⟨rfl, rfl, rfl⟩

/-- Declaration completion consumes no additional resource or identity. -/
theorem initialize_counters (dialect : Dialect) (ref : LValue kind)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment) :
    (Objects.initialize dialect ref value state).2.1.next = state.next ∧
    (Objects.initialize dialect ref value state).2.1.automaticSlots = state.automaticSlots := by
  unfold Objects.initialize
  repeat' first | split | exact ⟨rfl, rfl⟩

theorem endLifetime_next (ref : LValue kind) (state : State target parameters Environment) :
    (endLifetime ref state).2.1.next = state.next := by
  unfold endLifetime
  repeat' first | split | rfl

theorem reserve_next_monotone (dialect : Dialect) (kind : ArithmeticType)
    (state : State target parameters Environment) :
    state.next ≤ (reserve dialect kind state).2.1.next := by
  unfold reserve
  repeat' first | split | exact Nat.le_refl _ | exact Nat.le_succ _

theorem reserve_otherObjects (dialect : Dialect) (kind : ArithmeticType)
    (state : State target parameters Environment) :
    OtherObjects state (reserve dialect kind state).2.1 state.next := by
  intro query different
  unfold reserve
  repeat' first | split | rfl | exact State.putObject_other state state.next query _ different

theorem initialize_otherObjects (dialect : Dialect) (ref : LValue kind)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment) :
    OtherObjects state (Objects.initialize dialect ref value state).2.1 ref.id := by
  intro query different
  unfold Objects.initialize
  repeat' first | split | rfl | exact State.putObject_other state ref.id query _ different

theorem endLifetime_otherObjects (ref : LValue kind) (state : State target parameters Environment) :
    OtherObjects state (endLifetime ref state).2.1 ref.id := by
  intro query different
  unfold endLifetime
  repeat' first | split | rfl | exact State.putObject_other state ref.id query _ different

/-- Exact successful resource deltas avoid assuming a global capacity invariant. -/
theorem reserve_effects (dialect : Dialect) (kind : ArithmeticType)
    (state : State target parameters Environment) (ready : CanReserve state) :
    (reserve dialect kind state).1 = .ok ⟨state.next⟩ ∧
    (reserve dialect kind state).2.1.objects state.next =
      some (pendingObject dialect kind state.actor ⟨true, true⟩) ∧
    (reserve dialect kind state).2.1.next = state.next + 1 ∧
    (reserve dialect kind state).2.1.automaticSlots + 1 = state.automaticSlots ∧
    (reserve dialect kind state).2.2 = reserveEvents dialect state.next kind state.actor := by
  rw [reserve_eq dialect kind state ready]
  have positive := ready.2
  refine ⟨rfl, ?_, rfl, ?_, rfl⟩
  · exact State.putObject_same state state.next _
  · change state.automaticSlots - 1 + 1 = state.automaticSlots
    omega

/-- The exact typed option is stored: `none` stays absent and `some value` keeps
that value with its original type/range proof. Owner and both permissions frame. -/
theorem initialize_effects (dialect : Dialect) (ref : LValue kind)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment)
    (ready : CanInitialize dialect ref state) :
    ∃ permissions,
      state.objects ref.id = some (pendingObject dialect kind state.actor permissions) ∧
      (Objects.initialize dialect ref value state).1 = .ok () ∧
      (Objects.initialize dialect ref value state).2.1.objects ref.id =
        some (liveObject kind state.actor permissions value) ∧
      (Objects.initialize dialect ref value state).2.1.next = state.next ∧
      (Objects.initialize dialect ref value state).2.1.automaticSlots = state.automaticSlots ∧
      (Objects.initialize dialect ref value state).2.2 =
        initializeEvents dialect ref.id kind (value.map Value.toInt) := by
  obtain ⟨permissions, writable, registered⟩ := (canInitialize_iff_snapshot dialect ref state).mp ready
  refine ⟨permissions, registered, ?_⟩
  rw [initialize_eq dialect ref state permissions value registered writable]
  exact ⟨rfl, State.putObject_same state ref.id _, rfl, rfl, rfl⟩

/-- Tombstones retain kind, reached flag, owner, permissions and typed value.
Ending releases exactly one slot and keeps the fresh identity counter. -/
theorem endLifetime_effects (ref : LValue kind) (state : State target parameters Environment)
    (ready : CanEnd ref state) :
    ∃ value permissions,
      state.objects ref.id = some (liveObject kind state.actor permissions value) ∧
      (endLifetime ref state).1 = .ok () ∧
      (endLifetime ref state).2.1.objects ref.id =
        some { liveObject kind state.actor permissions value with life := .ended } ∧
      (endLifetime ref state).2.1.next = state.next ∧
      (endLifetime ref state).2.1.automaticSlots = state.automaticSlots + 1 ∧
      (endLifetime ref state).2.2 = [.endLifetime ref.id kind] := by
  obtain ⟨value, permissions, registered⟩ := (canEnd_iff_snapshot ref state).mp ready
  refine ⟨value, permissions, registered, ?_⟩
  rw [endLifetime_eq ref state permissions value registered]
  exact ⟨rfl, State.putObject_same state ref.id _, rfl, rfl, rfl⟩

/-- Fresh allocation preserves every registered object, including ended records.
Its returned identity is strictly above every previously registered identity. -/
theorem reserve_preserves_registered (dialect : Dialect) (kind : ArithmeticType)
    (state : State target parameters Environment) (wellFormed : state.WellFormed)
    (id : Nat) (object : Object target) (registered : state.objects id = some object) :
    id < state.next ∧ (reserve dialect kind state).2.1.objects id = some object := by
  have bound := (wellFormed id object registered).1
  refine ⟨bound, ?_⟩
  rw [reserve_otherObjects dialect kind state id (by omega)]
  exact registered

theorem reserve_preserves_wellFormed (dialect : Dialect) (kind : ArithmeticType)
    (state : State target parameters Environment) (wellFormed : state.WellFormed) :
    (reserve dialect kind state).2.1.WellFormed := by
  by_cases available : 0 < state.automaticSlots
  · rw [reserve_eq dialect kind state ⟨fresh_of_wellFormed state wellFormed, available⟩]
    exact reservedState_wellFormed dialect kind state wellFormed
  · have exhausted : state.automaticSlots = 0 := by omega
    simp [reserve, fresh_of_wellFormed state wellFormed, exhausted, Op.reject, wellFormed]

/-- Preservation holds for every outcome, not just calls satisfying admission. -/
theorem initialize_preserves_wellFormed (dialect : Dialect) (ref : LValue kind)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment)
    (wellFormed : state.WellFormed) :
    (Objects.initialize dialect ref value state).2.1.WellFormed := by
  unfold Objects.initialize
  repeat' first | split | exact wellFormed
  all_goals
    apply putObject_wellFormed state ref.id _ wellFormed
    · exact (wellFormed ref.id _ (by assumption)).1
    · simp [Object.WellFormed]

theorem endLifetime_preserves_wellFormed (ref : LValue kind)
    (state : State target parameters Environment) (wellFormed : state.WellFormed) :
    (endLifetime ref state).2.1.WellFormed := by
  unfold endLifetime
  repeat' first | split | exact wellFormed
  rename_i object registered _ _ _ _ _
  have old := wellFormed ref.id object registered
  apply putObject_wellFormed state ref.id _ wellFormed
  · exact old.1
  · constructor
    · intro impossible
      cases impossible
    · exact old.2.2

/-- Resource denial is separate from invalid registry binding. Collision wins
over exhaustion if both gates are violated. Neither is classified as ISO UB. -/
theorem reserve_exhausted (dialect : Dialect) (kind : ArithmeticType)
    (state : State target parameters Environment) (fresh : state.objects state.next = none)
    (exhausted : state.automaticSlots = 0) :
    reserve dialect kind state = (.error (.denied .automaticStorageExhausted), state, []) := by
  simp [reserve, fresh, exhausted, Op.reject]

theorem reserve_collision (dialect : Dialect) (kind : ArithmeticType)
    (state : State target parameters Environment) (object : Object target)
    (collision : state.objects state.next = some object) :
    reserve dialect kind state = (.error (.invalidBinding .invalidDeclarationState), state, []) := by
  simp [reserve, collision, Op.reject]

theorem initialize_wrongOwner (dialect : Dialect) (ref : LValue kind)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment)
    (owner : Nat) (permissions : Permissions)
    (registered : state.objects ref.id = some (pendingObject dialect kind owner permissions))
    (wrongOwner : owner ≠ state.actor) :
    Objects.initialize dialect ref value state = (.error (.denied .wrongOwner), state, []) := by
  cases dialect <;>
    simp [Objects.initialize, registered, pendingObject, reservationLife, wrongOwner, Op.reject]

theorem initialize_writeDenied (dialect : Dialect) (ref : LValue kind)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment)
    (permissions : Permissions)
    (registered : state.objects ref.id = some (pendingObject dialect kind state.actor permissions))
    (denied : permissions.writable = false) :
    Objects.initialize dialect ref value state = (.error (.denied .writePermission), state, []) := by
  cases dialect <;>
    simp [Objects.initialize, registered, pendingObject, reservationLife, denied, Op.reject]

theorem endLifetime_wrongOwner (ref : LValue kind) (state : State target parameters Environment)
    (owner : Nat) (permissions : Permissions) (value : Option (Value target kind.asIntType))
    (registered : state.objects ref.id = some (liveObject kind owner permissions value))
    (wrongOwner : owner ≠ state.actor) :
    endLifetime ref state = (.error (.denied .wrongOwner), state, []) := by
  simp [endLifetime, registered, liveObject, wrongOwner, Op.reject]

/-- Unstarted C++ lifetimes cannot end or release capacity. -/
theorem endLifetime_unstartedCpp (ref : LValue kind) (state : State target parameters Environment)
    (owner : Nat) (permissions : Permissions)
    (registered : state.objects ref.id = some (pendingObject .gnuCpp26 kind owner permissions)) :
    endLifetime ref state = (.error (.undefined .outsideLifetime), state, []) := by
  simp [endLifetime, registered, pendingObject, Op.reject]

/-- C reservation is live but does not bypass declaration reachability. -/
theorem endLifetime_unreachedC (ref : LValue kind) (state : State target parameters Environment)
    (owner : Nat) (permissions : Permissions)
    (registered : state.objects ref.id = some (pendingObject .gnuC23 kind owner permissions)) :
    endLifetime ref state = (.error (.invalidBinding .declarationNotReached), state, []) := by
  simp [endLifetime, registered, pendingObject, Op.reject]

theorem initialize_alreadyReached (dialect : Dialect) (ref : LValue kind)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment)
    (object : Object target) (registered : state.objects ref.id = some object)
    (same : object.kind = kind) (reached : object.reached = true) :
    Objects.initialize dialect ref value state =
      (.error (.invalidBinding .declarationAlreadyInitialized), state, []) := by
  simp [Objects.initialize, registered, same, reached, Op.reject]

theorem endLifetime_alreadyEnded (ref : LValue kind) (state : State target parameters Environment)
    (object : Object target) (registered : state.objects ref.id = some object)
    (same : object.kind = kind) (ended : object.life = .ended) :
    endLifetime ref state = (.error (.invalidBinding .alreadyEnded), state, []) := by
  simp [endLifetime, registered, same, ended, Op.reject]

/-- Once completed, even `none` counts as initialization. A second attempt
retains the first completion's entire state and emits no second completion. -/
theorem initialize_once (dialect laterDialect : Dialect) (ref : LValue kind)
    (first later : Option (Value target kind.asIntType)) (state : State target parameters Environment)
    (ready : CanInitialize dialect ref state) :
    Objects.initialize laterDialect ref later (Objects.initialize dialect ref first state).2.1 =
      (.error (.invalidBinding .declarationAlreadyInitialized),
        (Objects.initialize dialect ref first state).2.1, []) := by
  obtain ⟨permissions, writable, registered⟩ := (canInitialize_iff_snapshot dialect ref state).mp ready
  rw [initialize_eq dialect ref state permissions first registered writable]
  exact initialize_alreadyReached laterDialect ref later _ _ (State.putObject_same state ref.id _) rfl rfl

/-- The second end cannot return another slot.
The first call's tombstone, counter and released slot are all retained. -/
theorem endLifetime_once (ref : LValue kind) (state : State target parameters Environment)
    (ready : CanEnd ref state) :
    endLifetime ref (endLifetime ref state).2.1 =
      (.error (.invalidBinding .alreadyEnded), (endLifetime ref state).2.1, []) := by
  obtain ⟨value, permissions, registered⟩ := (canEnd_iff_snapshot ref state).mp ready
  rw [endLifetime_eq ref state permissions value registered]
  exact endLifetime_alreadyEnded ref _ _ (State.putObject_same state ref.id _) rfl rfl

/-- Classification only; read access contracts belong to the separate module.
Ordinary full-int C++ uninitialized production is erroneous, not C's UB stop. -/
theorem uninitialized_classification :
    uninitializedRead .gnuC23 = .undefined .uninitializedAutomaticRead ∧
    uninitializedRead .gnuCpp26 = .erroneous .uninitializedAutomaticRead := ⟨rfl, rfl⟩

theorem denial_not_undefined (denial : Denial) (reason : ObjectUB) :
    Stop.denied denial ≠ Stop.undefined reason := by
  intro impossible
  cases impossible

theorem bindingFault_not_undefined (fault : BindingFault) (reason : ObjectUB) :
    Stop.invalidBinding fault ≠ Stop.undefined reason := by
  intro impossible
  cases impossible

/-- Admission is also necessary, including on arbitrary malformed states. -/
theorem reserve_admission_iff (dialect : Dialect) (kind : ArithmeticType)
    (state : State target parameters Environment) :
    (∃ ref, (reserve dialect kind state).1 = .ok ref) ↔ CanReserve state := by
  constructor
  · rintro ⟨ref, accepted⟩
    unfold reserve at accepted
    split at accepted
    · contradiction
    · rename_i fresh
      split at accepted
      · contradiction
      · rename_i available
        exact ⟨fresh, by omega⟩
  · intro ready
    exact ⟨_, congrArg Prod.fst (reserve_eq dialect kind state ready)⟩

theorem initialize_admission_iff (dialect : Dialect) (ref : LValue kind)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment) :
    (Objects.initialize dialect ref value state).1 = .ok () ↔ CanInitialize dialect ref state := by
  constructor
  · intro accepted
    unfold Objects.initialize at accepted
    repeat' first | split at accepted | contradiction
    all_goals
      refine ⟨_, by assumption, by assumption, ?_, ?_, by assumption, ?_, ?_⟩ <;>
        simp_all [reservationLife]
  · intro ready
    obtain ⟨permissions, writable, registered⟩ := (canInitialize_iff_snapshot dialect ref state).mp ready
    exact congrArg Prod.fst (initialize_eq dialect ref state permissions value registered writable)

theorem endLifetime_admission_iff (ref : LValue kind) (state : State target parameters Environment) :
    (endLifetime ref state).1 = .ok () ↔ CanEnd ref state := by
  constructor
  · intro accepted
    unfold endLifetime at accepted
    repeat' first | split at accepted | contradiction
    refine ⟨_, by assumption, by assumption, ?_, ?_, ?_⟩ <;> simp_all
  · intro ready
    obtain ⟨value, permissions, registered⟩ := (canEnd_iff_snapshot ref state).mp ready
    exact congrArg Prod.fst (endLifetime_eq ref state permissions value registered)

/-- In particular, C++ completion's internal event comes before lifetime begin. -/
theorem initialize_cpp_completion_before_begin (ref : LValue kind)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment)
    (ready : CanInitialize .gnuCpp26 ref state) :
    (Objects.initialize .gnuCpp26 ref value state).2.2 =
      [.initialize ref.id kind (value.map Value.toInt), .beginLifetime ref.id kind] := by
  obtain ⟨permissions, writable, registered⟩ := (canInitialize_iff_snapshot .gnuCpp26 ref state).mp ready
  rw [initialize_eq .gnuCpp26 ref state permissions value registered writable]
  rfl

/-- Bind retains the first successful end and its event when the next end fails;
only that first end releases a slot. This is not exception unwinding. -/
theorem double_end_bind (ref : LValue kind) (state : State target parameters Environment)
    (ready : CanEnd ref state) :
    Op.bind (endLifetime ref) (fun _ => endLifetime ref) state =
      (.error (.invalidBinding .alreadyEnded), (endLifetime ref state).2.1,
        [.endLifetime ref.id kind]) := by
  obtain ⟨value, permissions, registered⟩ := (canEnd_iff_snapshot ref state).mp ready
  have first := endLifetime_eq ref state permissions value registered
  have second := endLifetime_once ref state ready
  rw [first] at second ⊢
  simp only [Op.bind, Effects.Op.bind, first, second, List.append_nil]

/-- Only the three primitives compose here; no source statement semantics or
recovery after a failed initializer is supplied by this definition. -/
def declarationCycle (dialect : Dialect) (kind : ArithmeticType)
    (value : Option (Value target kind.asIntType)) :
    Op target parameters Environment (LValue kind) :=
  Op.bind (reserve dialect kind) fun ref =>
    Op.bind (Objects.initialize dialect ref value) fun _ =>
      Op.bind (endLifetime ref) fun _ => Op.pure ref

/-- Final-state specification has the old capacity and exactly one new tombstone.
The dialect affects the internal trace, but not this final state. -/
def completedState (kind : ArithmeticType) (value : Option (Value target kind.asIntType))
    (state : State target parameters Environment) : State target parameters Environment :=
  { state.putObject state.next
      { liveObject kind state.actor ⟨true, true⟩ value with life := .ended } with
    next := state.next + 1 }

theorem cycle_state_eq (dialect : Dialect) (kind : ArithmeticType)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment)
    (capacity : 0 < state.automaticSlots) :
    endedState ⟨state.next⟩ ⟨true, true⟩ value
      (initializedState ⟨state.next⟩ ⟨true, true⟩ value (reservedState dialect kind state)) =
        completedState kind value state := by
  have conserved : state.automaticSlots - 1 + 1 = state.automaticSlots := by omega
  simp [endedState, initializedState, reservedState, completedState, State.putObject, conserved]
  funext query
  by_cases same : query = state.next <;> simp [same]

theorem declarationCycle_eq (dialect : Dialect) (kind : ArithmeticType)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment)
    (ready : CanReserve state) :
    declarationCycle dialect kind value state =
      (.ok ⟨state.next⟩, completedState kind value state,
        reserveEvents dialect state.next kind state.actor ++
        initializeEvents dialect state.next kind (value.map Value.toInt) ++
        [.endLifetime state.next kind]) := by
  let ref : LValue kind := ⟨state.next⟩
  let reserved := reservedState dialect kind state
  let initialized := initializedState ref ⟨true, true⟩ value reserved
  have reservation := reserve_eq dialect kind state ready
  have initialization := initialize_eq dialect ref reserved ⟨true, true⟩ value
    (State.putObject_same state state.next _) rfl
  have ending := endLifetime_eq ref initialized ⟨true, true⟩ value
    (State.putObject_same reserved ref.id _)
  have final := cycle_state_eq dialect kind value state ready.2
  change endedState ref ⟨true, true⟩ value initialized = completedState kind value state at final
  dsimp only [ref, reserved, initialized] at initialization ending final
  simp only [declarationCycle, Op.bind, Effects.Op.bind, reservation, initialization, ending, Op.pure,
    List.append_nil, final, List.append_assoc]

/-- Completed cycle conserves slots, advances freshness once and leaves the exact
typed value in a tombstone. All other objects and the external world frame. -/
theorem declarationCycle_effects (dialect : Dialect) (kind : ArithmeticType)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment)
    (ready : CanReserve state) :
    (declarationCycle dialect kind value state).2.1.automaticSlots = state.automaticSlots ∧
    (declarationCycle dialect kind value state).2.1.next = state.next + 1 ∧
    (declarationCycle dialect kind value state).2.1.objects state.next =
      some { liveObject kind state.actor ⟨true, true⟩ value with life := .ended } ∧
    Frozen state (declarationCycle dialect kind value state).2.1 ∧
    OtherObjects state (declarationCycle dialect kind value state).2.1 state.next := by
  rw [declarationCycle_eq dialect kind value state ready]
  refine ⟨rfl, rfl, State.putObject_same state state.next _, ⟨rfl, rfl, rfl⟩, ?_⟩
  intro query different
  exact State.putObject_other state state.next query _ different

theorem declarationCycle_preserves_wellFormed (dialect : Dialect) (kind : ArithmeticType)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment)
    (wellFormed : state.WellFormed) :
    (declarationCycle dialect kind value state).2.1.WellFormed := by
  by_cases capacity : 0 < state.automaticSlots
  · have ready : CanReserve state := ⟨fresh_of_wellFormed state wellFormed, capacity⟩
    rw [declarationCycle_eq dialect kind value state ready]
    intro id object registered
    by_cases same : id = state.next
    · subst id
      have equal : { liveObject kind state.actor ⟨true, true⟩ value with life := .ended } = object := by
        simpa [completedState, State.putObject] using registered
      subst object
      exact ⟨by simp [completedState], by simp [Object.WellFormed, liveObject]⟩
    · have previous : state.objects id = some object := by
        simpa [completedState, State.putObject, same] using registered
      have old := wellFormed id object previous
      exact ⟨by have bound := old.1; simp only [completedState]; omega, old.2⟩
  · have exhausted : state.automaticSlots = 0 := by omega
    have failure := reserve_exhausted dialect kind state (fresh_of_wellFormed state wellFormed) exhausted
    simpa only [declarationCycle, Op.bind, Effects.Op.bind, failure] using wellFormed

/-- A completed cycle's tombstone remains registered on the next reserve, whose
fresh identity is its successor. Freed slots never recycle object identities. -/
theorem reserve_after_cycle_no_reuse (dialect nextDialect : Dialect) (kind nextKind : ArithmeticType)
    (value : Option (Value target kind.asIntType)) (state : State target parameters Environment)
    (ready : CanReserve state) (wellFormed : state.WellFormed) :
    let final := (declarationCycle dialect kind value state).2.1
    (reserve nextDialect nextKind final).1 = .ok ⟨state.next + 1⟩ ∧
    (reserve nextDialect nextKind final).2.1.objects state.next =
      some { liveObject kind state.actor ⟨true, true⟩ value with life := .ended } := by
  rw [declarationCycle_eq dialect kind value state ready]
  dsimp only
  have finalWellFormed := declarationCycle_preserves_wellFormed dialect kind value state wellFormed
  rw [declarationCycle_eq dialect kind value state ready] at finalWellFormed
  have fresh := fresh_of_wellFormed (completedState kind value state) finalWellFormed
  have capacity : 0 < (completedState kind value state).automaticSlots := ready.2
  rw [reserve_eq nextDialect nextKind _ ⟨fresh, capacity⟩]
  refine ⟨rfl, ?_⟩
  simp [reservedState, completedState, State.putObject]

end EDSL.Source.Objects.LifecycleContracts
