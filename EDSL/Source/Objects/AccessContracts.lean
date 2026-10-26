/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Access

set_option autoImplicit false
namespace EDSL.Source.Objects

/- These are independent conditions on the registry before execution. They do
not assume a source input domain is defined, nor establish program/OS/native
safety. Only the full integral objects of Model/Access are covered: no bytes,
source pointers, object layout, interference or source read-order claims. -/

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {kind : ArithmeticType}

/-- Exactly the prestate data needed to read this typed value. Write permission
is deliberately unrestricted. All inputs and environment values are arbitrary. -/
def CanLoad (state : State target parameters Environment) (ref : LValue kind)
    (value : Value target kind.asIntType) : Prop :=
  ∃ permissions : Permissions,
    state.objects ref.id = some {
      kind := kind, life := .live, reached := true, value := some value,
      owner := state.actor, permissions := permissions } ∧
    permissions.readable = true

/-- A store needs current write authority, but neither read authority nor an
initialized old value. The previous contents range over the entire Option. -/
def CanStore (state : State target parameters Environment) (ref : LValue kind) : Prop :=
  ∃ previous : Option (Value target kind.asIntType), ∃ permissions : Permissions,
    state.objects ref.id = some {
      kind := kind, life := .live, reached := true, value := previous,
      owner := state.actor, permissions := permissions } ∧
    permissions.writable = true

/-- A primitive write preserves all state outside its designated object's value.
This includes inputs, environment, actor, fresh identity and storage budget. -/
def AccessFrame (before after : State target parameters Environment)
    (ref : LValue kind) : Prop :=
  after.inputs = before.inputs ∧ after.environment = before.environment ∧
  after.actor = before.actor ∧ after.next = before.next ∧
  after.automaticSlots = before.automaticSlots ∧
  ∀ query, query ≠ ref.id → after.objects query = before.objects query

/-- Object metadata excludes only the optional integral contents. -/
def SameAccessMetadata (before after : Object target) : Prop :=
  after.kind = before.kind ∧ after.life = before.life ∧
  after.reached = before.reached ∧ after.owner = before.owner ∧
  after.permissions = before.permissions

theorem load_contract (dialect : Dialect) (state : State target parameters Environment)
    (ref : LValue kind) (value : Value target kind.asIntType)
    (authorized : CanLoad state ref value) :
    load dialect ref state = (.ok value, state, [.read ref.id kind value.toInt]) := by
  rcases authorized with ⟨permissions, registered, readable⟩
  simp [load, registered, readable]

/-- The exact update is accompanied below by integer, event, metadata and frame
laws. No execution equation occurs among the public preconditions. -/
theorem store_contract (state : State target parameters Environment)
    (ref : LValue kind) (value : Value target kind.asIntType)
    (authorized : CanStore state ref) :
    ∃ previous : Option (Value target kind.asIntType), ∃ permissions : Permissions,
      state.objects ref.id = some {
        kind := kind, life := .live, reached := true, value := previous,
        owner := state.actor, permissions := permissions } ∧
      permissions.writable = true ∧
      store ref value state = (.ok (), state.putObject ref.id {
        kind := kind, life := .live, reached := true, value := some value,
        owner := state.actor, permissions := permissions }, [.write ref.id kind value.toInt]) := by
  rcases authorized with ⟨previous, permissions, registered, writable⟩
  exact ⟨previous, permissions, registered, writable, by simp [store, registered, writable]⟩

/-- The independent read condition characterizes success, rather than merely
being a sufficient subset of an operation-defined safety predicate. -/
theorem load_success_iff (dialect : Dialect) (state : State target parameters Environment)
    (ref : LValue kind) (value : Value target kind.asIntType) :
    (load dialect ref state).1 = .ok value ↔ CanLoad state ref value := by
  constructor
  · intro accepted
    unfold load at accepted
    split at accepted
    · cases accepted
    · rename_i object registered
      rcases object with ⟨objectKind, life, reached, previous, owner, permissions⟩
      split at accepted
      · rename_i same
        cases same
        split at accepted
        · cases accepted
        · rename_i live
          split at accepted
          · cases accepted
          · rename_i reachedTrue
            split at accepted
            · cases accepted
            · rename_i owned
              split at accepted
              · cases accepted
              · rename_i readable
                split at accepted
                · cases dialect <;> cases accepted
                · rename_i stored contents
                  have values : stored = value := by simpa using accepted
                  subst value
                  have isLive : life = .live := Decidable.of_not_not live
                  have isReached : reached = true := Bool.eq_true_of_ne_false reachedTrue
                  have isOwner : owner = state.actor := Decidable.of_not_not owned
                  have isValue : previous = some stored := contents
                  refine ⟨permissions, ?_, ?_⟩
                  · simpa [isLive, isReached, isOwner, isValue] using registered
                  · exact Bool.eq_true_of_ne_false readable
      · cases accepted
  · intro authorized
    rw [load_contract dialect state ref value authorized]

/-- Store success does not depend on the new value or old initialization. -/
theorem store_success_iff (state : State target parameters Environment)
    (ref : LValue kind) (value : Value target kind.asIntType) :
    (store ref value state).1 = .ok () ↔ CanStore state ref := by
  constructor
  · intro accepted
    unfold store at accepted
    split at accepted
    · cases accepted
    · rename_i object registered
      rcases object with ⟨objectKind, life, reached, previous, owner, permissions⟩
      split at accepted
      · rename_i same
        cases same
        split at accepted
        · cases accepted
        · rename_i live
          split at accepted
          · cases accepted
          · rename_i reachedTrue
            split at accepted
            · cases accepted
            · rename_i owned
              split at accepted
              · cases accepted
              · rename_i writable
                have isLive : life = .live := Decidable.of_not_not live
                have isReached : reached = true := Bool.eq_true_of_ne_false reachedTrue
                have isOwner : owner = state.actor := Decidable.of_not_not owned
                refine ⟨previous, permissions, ?_, ?_⟩
                · simpa [isLive, isReached, isOwner] using registered
                · exact Bool.eq_true_of_ne_false writable
      · cases accepted
  · intro authorized
    obtain ⟨previous, permissions, registered, writable, accepted⟩ :=
      store_contract state ref value authorized
    rw [accepted]

private theorem accessFrame_refl (state : State target parameters Environment)
    (ref : LValue kind) : AccessFrame state state ref :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

private theorem accessFrame_putObject (state : State target parameters Environment)
    (ref : LValue kind) (object : Object target) :
    AccessFrame state (state.putObject ref.id object) ref :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun query different =>
    State.putObject_other state ref.id query object different⟩

/-- This frame holds for every execution, including rejection. -/
theorem store_preserves_frame (state : State target parameters Environment)
    (ref : LValue kind) (value : Value target kind.asIntType) :
    AccessFrame state (store ref value state).2.1 ref := by
  unfold store
  repeat' first | split | exact accessFrame_refl state ref | apply accessFrame_putObject

private theorem putValue_preserves_metadata (state : State target parameters Environment)
    (id : Nat) (object : Object target)
    (value : Option (Value target object.kind.asIntType))
    (registered : state.objects id = some object) (query : Nat) (before : Object target)
    (present : state.objects query = some before) :
    ∃ after, (state.putObject id { object with value := value }).objects query = some after ∧
      SameAccessMetadata before after := by
  by_cases same : query = id
  · subst query
    have equal : object = before := Option.some.inj (registered.symm.trans present)
    subst before
    exact ⟨{ object with value := value }, State.putObject_same _ _ _,
      rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨before, (State.putObject_other _ _ _ _ same).trans present,
      rfl, rfl, rfl, rfl, rfl⟩

/-- Every existing record retains its kind, lifetime, declaration status,
owner and both permissions, whether or not the write is accepted. -/
theorem store_preserves_metadata (state : State target parameters Environment)
    (ref : LValue kind) (value : Value target kind.asIntType)
    (query : Nat) (before : Object target) (registered : state.objects query = some before) :
    ∃ after, (store ref value state).2.1.objects query = some after ∧
      SameAccessMetadata before after := by
  unfold store
  repeat' first
    | split
    | exact ⟨before, registered, rfl, rfl, rfl, rfl, rfl⟩
    | exact putValue_preserves_metadata state ref.id _ _ (by assumption) query before registered

private theorem putValue_wellFormed (state : State target parameters Environment)
    (id : Nat) (object : Object target)
    (value : Option (Value target object.kind.asIntType))
    (registered : state.objects id = some object) (reached : object.reached = true)
    (wellFormed : state.WellFormed) :
    (state.putObject id { object with value := value }).WellFormed := by
  intro query after present
  by_cases same : query = id
  · subst query
    have equal : { object with value := value } = after := by
      simpa only [State.putObject_same, Option.some.injEq] using present
    subst after
    obtain ⟨bounded, reserved, _⟩ := wellFormed id object registered
    exact ⟨bounded, reserved, by simp [reached]⟩
  · rw [State.putObject_other _ _ _ _ same] at present
    exact wellFormed query after present

/-- Stores preserve the registry invariant; they allocate or retire no objects. -/
theorem store_preserves_wellFormed (state : State target parameters Environment)
    (ref : LValue kind) (value : Value target kind.asIntType)
    (wellFormed : state.WellFormed) : (store ref value state).2.1.WellFormed := by
  unfold store
  repeat' first
    | split
    | exact wellFormed
    | apply putValue_wellFormed state ref.id _ _ (by assumption)
        (Bool.eq_true_of_ne_false (by assumption)) wellFormed

/-- Primitive rejection is atomic: it preserves the entire state and emits
no events, including for an attempted write of the current value. -/
theorem store_rejection (state : State target parameters Environment)
    (ref : LValue kind) (value : Value target kind.asIntType) (reason : Stop)
    (rejected : (store ref value state).1 = .error reason) :
    store ref value state = (.error reason, state, []) := by
  unfold store at rejected ⊢
  repeat' first | split at rejected | simp_all [Op.reject]

/-- Read rejection also preserves the entire state and emits no events. -/
theorem load_rejection (dialect : Dialect) (state : State target parameters Environment)
    (ref : LValue kind) (reason : Stop)
    (rejected : (load dialect ref state).1 = .error reason) :
    load dialect ref state = (.error reason, state, []) := by
  unfold load at rejected ⊢
  repeat' first | split at rejected | simp_all [Op.reject]

/-- Integer and event observations are independent of the representation of the
registry update. The frame includes all non-object state and every other object. -/
theorem store_value_event_frame (state : State target parameters Environment)
    (ref : LValue kind) (value : Value target kind.asIntType)
    (authorized : CanStore state ref) :
    ∃ updated object,
      store ref value state = (.ok (), updated, [.write ref.id kind value.toInt]) ∧
      updated.objects ref.id = some object ∧
      object.value.map Value.toInt = some value.toInt ∧ AccessFrame state updated ref := by
  obtain ⟨previous, permissions, registered, writable, accepted⟩ :=
    store_contract state ref value authorized
  refine ⟨_, _, accepted, State.putObject_same _ _ _, rfl, ?_⟩
  exact accessFrame_putObject state ref _

/-- A store changes no other object's load outcome or event trace. The returned
state still carries the accepted store; this is no source read-order claim. -/
theorem load_other_after_store {otherKind : ArithmeticType} (dialect : Dialect)
    (state : State target parameters Environment) (ref : LValue kind)
    (value : Value target kind.asIntType) (other : LValue otherKind)
    (different : other.id ≠ ref.id) :
    (load dialect other (store ref value state).2.1).1 = (load dialect other state).1 ∧
    (load dialect other (store ref value state).2.1).2.2 = (load dialect other state).2.2 := by
  obtain ⟨_, _, sameActor, _, _, otherObjects⟩ := store_preserves_frame state ref value
  constructor
  all_goals
    unfold load
    rw [otherObjects other.id different, sameActor]
    repeat' first | split | rfl

/-- Read-after-write for any prior contents, including none. Read authority is
separate from CanStore and is needed only for the subsequent load. -/
theorem load_after_store (dialect : Dialect) (state : State target parameters Environment)
    (ref : LValue kind) (value : Value target kind.asIntType)
    (authorized : CanStore state ref)
    (readable : ∀ object, state.objects ref.id = some object →
      object.permissions.readable = true) :
    ∃ updated,
      store ref value state = (.ok (), updated, [.write ref.id kind value.toInt]) ∧
      CanLoad updated ref value ∧
      load dialect ref updated = (.ok value, updated, [.read ref.id kind value.toInt]) ∧
      Op.bind (store ref value) (fun _ => load dialect ref) state =
        (.ok value, updated, [.write ref.id kind value.toInt, .read ref.id kind value.toInt]) := by
  obtain ⟨previous, permissions, registered, writable, accepted⟩ :=
    store_contract state ref value authorized
  have readPermission : permissions.readable = true := readable _ registered
  let updated := state.putObject ref.id {
    kind := kind, life := .live, reached := true, value := some value,
    owner := state.actor, permissions := permissions }
  have canLoad : CanLoad updated ref value :=
    ⟨permissions, State.putObject_same _ _ _, readPermission⟩
  have stored : store ref value state =
      (.ok (), updated, [.write ref.id kind value.toInt]) := accepted
  have loaded := load_contract dialect updated ref value canLoad
  refine ⟨updated, stored, canLoad, loaded, ?_⟩
  simp [Op.bind, stored, loaded]

/-- In particular, writing a reached live uninitialized object establishes the
read condition. No premise assumes that reading its old contents was defined. -/
theorem store_load_uninitialized (dialect : Dialect)
    (state : State target parameters Environment) (ref : LValue kind)
    (value : Value target kind.asIntType) (permissions : Permissions)
    (registered : state.objects ref.id = some {
      kind := kind, life := .live, reached := true, value := none,
      owner := state.actor, permissions := permissions })
    (writable : permissions.writable = true) (readable : permissions.readable = true) :
    ∃ updated, CanLoad updated ref value ∧ AccessFrame state updated ref ∧
      Op.bind (store ref value) (fun _ => load dialect ref) state =
        (.ok value, updated, [.write ref.id kind value.toInt, .read ref.id kind value.toInt]) := by
  have authorized : CanStore state ref := ⟨none, permissions, registered, writable⟩
  have readPermission : ∀ object, state.objects ref.id = some object →
      object.permissions.readable = true := by
    intro object present
    have equal := Option.some.inj (registered.symm.trans present)
    cases equal
    exact readable
  obtain ⟨updated, accepted, canLoad, loaded, composed⟩ :=
    load_after_store dialect state ref value authorized readPermission
  refine ⟨updated, canLoad, ?_, composed⟩
  have frame := store_preserves_frame state ref value
  simpa only [accepted] using frame

/-- Ordinary full-integral uninitialized automatic reads retain the dialect's
classification. Both cases reject atomically, after checking read authority. -/
theorem load_uninitialized (dialect : Dialect) (state : State target parameters Environment)
    (ref : LValue kind) (permissions : Permissions)
    (registered : state.objects ref.id = some {
      kind := kind, life := .live, reached := true, value := none,
      owner := state.actor, permissions := permissions })
    (readable : permissions.readable = true) :
    load dialect ref state = (.error (uninitializedRead dialect), state, []) := by
  simp [load, registered, readable, Op.reject]

theorem load_uninitialized_c23 (state : State target parameters Environment)
    (ref : LValue kind) (permissions : Permissions)
    (registered : state.objects ref.id = some {
      kind := kind, life := .live, reached := true, value := none,
      owner := state.actor, permissions := permissions })
    (readable : permissions.readable = true) :
    load .gnuC23 ref state = (.error (.undefined .uninitializedAutomaticRead), state, []) :=
  load_uninitialized .gnuC23 state ref permissions registered readable

theorem load_uninitialized_cpp26 (state : State target parameters Environment)
    (ref : LValue kind) (permissions : Permissions)
    (registered : state.objects ref.id = some {
      kind := kind, life := .live, reached := true, value := none,
      owner := state.actor, permissions := permissions })
    (readable : permissions.readable = true) :
    load .gnuCpp26 ref state = (.error (.erroneous .uninitializedAutomaticRead), state, []) :=
  load_uninitialized .gnuCpp26 state ref permissions registered readable

/-- Even retained initialized contents cannot make an ended typed record load. -/
theorem load_ended (dialect : Dialect) (state : State target parameters Environment)
    (ref : LValue kind) (object : Object target)
    (registered : state.objects ref.id = some object) (typed : object.kind = kind)
    (ended : object.life = .ended) :
    load dialect ref state = (.error (.undefined .outsideLifetime), state, []) := by
  simp [load, registered, typed, ended, Op.reject]

theorem load_wrong_owner (dialect : Dialect) (state : State target parameters Environment)
    (ref : LValue kind) (object : Object target)
    (registered : state.objects ref.id = some object) (typed : object.kind = kind)
    (live : object.life = .live) (reached : object.reached = true)
    (unauthorized : object.owner ≠ state.actor) :
    load dialect ref state = (.error (.denied .wrongOwner), state, []) := by
  simp [load, registered, typed, live, reached, unauthorized, Op.reject]

theorem load_without_read_permission (dialect : Dialect)
    (state : State target parameters Environment) (ref : LValue kind) (object : Object target)
    (registered : state.objects ref.id = some object) (typed : object.kind = kind)
    (live : object.life = .live) (reached : object.reached = true)
    (owned : object.owner = state.actor) (unreadable : object.permissions.readable = false) :
    load dialect ref state = (.error (.denied .readPermission), state, []) := by
  simp [load, registered, typed, live, reached, owned, unreadable, Op.reject]

theorem store_wrong_owner (state : State target parameters Environment)
    (ref : LValue kind) (value : Value target kind.asIntType) (object : Object target)
    (registered : state.objects ref.id = some object) (typed : object.kind = kind)
    (live : object.life = .live) (reached : object.reached = true)
    (unauthorized : object.owner ≠ state.actor) :
    store ref value state = (.error (.denied .wrongOwner), state, []) := by
  simp [store, registered, typed, live, reached, unauthorized, Op.reject]

theorem store_without_write_permission (state : State target parameters Environment)
    (ref : LValue kind) (value : Value target kind.asIntType) (object : Object target)
    (registered : state.objects ref.id = some object) (typed : object.kind = kind)
    (live : object.life = .live) (reached : object.reached = true)
    (owned : object.owner = state.actor) (unwritable : object.permissions.writable = false) :
    store ref value state = (.error (.denied .writePermission), state, []) := by
  simp [store, registered, typed, live, reached, owned, unwritable, Op.reject]

/-- Equality with the current contents never substitutes for authority. Wrong
ownership has priority over missing write permission; neither emits an event. -/
theorem store_same_value_unauthorized (state : State target parameters Environment)
    (ref : LValue kind) (value : Value target kind.asIntType)
    (owner : Nat) (permissions : Permissions)
    (registered : state.objects ref.id = some {
      kind := kind, life := .live, reached := true, value := some value,
      owner := owner, permissions := permissions })
    (unauthorized : owner ≠ state.actor ∨ permissions.writable = false) :
    store ref value state =
      (.error (if owner ≠ state.actor then .denied .wrongOwner else .denied .writePermission),
        state, []) := by
  by_cases wrongOwner : owner ≠ state.actor
  · simp [store, registered, wrongOwner, Op.reject]
  · have unwritable : permissions.writable = false := unauthorized.resolve_left wrongOwner
    simp [store, registered, wrongOwner, unwritable, Op.reject]

/-- Write-only authority accepts any new value, even over none. A following
read still fails; composition retains precisely the accepted write and event. -/
theorem store_without_read_permission (dialect : Dialect)
    (state : State target parameters Environment) (ref : LValue kind)
    (value : Value target kind.asIntType) (previous : Option (Value target kind.asIntType))
    (permissions : Permissions)
    (registered : state.objects ref.id = some {
      kind := kind, life := .live, reached := true, value := previous,
      owner := state.actor, permissions := permissions })
    (writable : permissions.writable = true) (unreadable : permissions.readable = false) :
    ∃ updated,
      store ref value state = (.ok (), updated, [.write ref.id kind value.toInt]) ∧
      load dialect ref updated = (.error (.denied .readPermission), updated, []) ∧
      Op.bind (store ref value) (fun _ => load dialect ref) state =
        (.error (.denied .readPermission), updated, [.write ref.id kind value.toInt]) := by
  let updated := state.putObject ref.id {
    kind := kind, life := .live, reached := true, value := some value,
    owner := state.actor, permissions := permissions }
  have accepted : store ref value state =
      (.ok (), updated, [.write ref.id kind value.toInt]) := by
    simp [store, registered, writable, updated]
  have rejected : load dialect ref updated =
      (.error (.denied .readPermission), updated, []) :=
    load_without_read_permission dialect updated ref _
      (State.putObject_same _ _ _) rfl rfl rfl rfl unreadable
  exact ⟨updated, accepted, rejected, by simp [Op.bind, accepted, rejected]⟩

/- Audit all public laws, including the frozen whole-state read frame. These
commands report dependencies only; they introduce no proof assumptions. -/

end EDSL.Source.Objects
