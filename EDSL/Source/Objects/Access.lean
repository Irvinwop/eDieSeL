/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Model

set_option autoImplicit false
namespace EDSL.Source.Objects

/-- C storage reservation begins this slice's lifetime; C++ waits for initialization. -/
def reservationLife (dialect : Dialect) : Life :=
  match dialect with
  | .gnuC23 => .live
  | .gnuCpp26 => .reserved

/-- Reserve one abstract automatic-object slot with a fresh, never recycled identity.
A collision is an invalid model state, not a claim of source-language UB. -/
def reserve {target : Target} {parameters : List IntType} {Environment : Type}
    (dialect : Dialect) (kind : ArithmeticType) :
    Op target parameters Environment (LValue kind) := fun state =>
  match state.objects state.next with
  | some _ => Op.reject (.invalidBinding .invalidDeclarationState) state
  | none =>
      if state.automaticSlots = 0 then
        Op.reject (.denied .automaticStorageExhausted) state
      else
        let object : Object target := {
          kind := kind
          life := reservationLife dialect
          reached := false
          value := none
          owner := state.actor
          permissions := { readable := true, writable := true }
        }
        let registered := state.putObject state.next object
        let updated := { registered with
          next := state.next + 1
          automaticSlots := state.automaticSlots - 1
        }
        let events := match dialect with
          | .gnuC23 => [.reserve state.next kind state.actor, .beginLifetime state.next kind]
          | .gnuCpp26 => [.reserve state.next kind state.actor]
        (.ok ⟨state.next⟩, updated, events)

/-- Reach a declaration exactly once. `none` leaves its value uninitialized.
The caller supplies an already typed value; expression evaluation is separate. -/
def «initialize» {target : Target} {parameters : List IntType} {Environment : Type}
    {kind : ArithmeticType} (dialect : Dialect) (ref : LValue kind)
    (initial : Option (Value target kind.asIntType)) : Op target parameters Environment Unit :=
  fun state =>
    match state.objects ref.id with
    | none => Op.reject (.invalidBinding .unknownObject) state
    | some object =>
        if same : object.kind = kind then
          if object.reached = true then
            Op.reject (.invalidBinding .declarationAlreadyInitialized) state
          else if object.life ≠ reservationLife dialect then
            Op.reject (.invalidBinding .invalidDeclarationState) state
          else
            match object.value with
            | some _ => Op.reject (.invalidBinding .invalidDeclarationState) state
            | none =>
                if object.owner ≠ state.actor then
                  Op.reject (.denied .wrongOwner) state
                else if object.permissions.writable = false then
                  Op.reject (.denied .writePermission) state
                else
                  let stored := cast
                    (congrArg (fun k => Option (Value target k.asIntType)) same.symm) initial
                  let updated : Object target := {
                    object with life := .live, reached := true, value := stored
                  }
                  let event := Event.initialize ref.id kind (initial.map Value.toInt)
                  let events := match dialect with
                    | .gnuC23 => [event]
                    | .gnuCpp26 => [event, .beginLifetime ref.id kind]
                  (.ok (), state.putObject ref.id updated, events)
        else
          Op.reject (.invalidBinding .wrongKind) state

/-- Read a reached live full-int object with current ownership and read authority.
Ordinary uninitialized automatic reads have distinct C and C++ stops. -/
def load {target : Target} {parameters : List IntType} {Environment : Type}
    {kind : ArithmeticType} (dialect : Dialect) (ref : LValue kind) :
    Op target parameters Environment (Value target kind.asIntType) := fun state =>
  match state.objects ref.id with
  | none => Op.reject (.invalidBinding .unknownObject) state
  | some object =>
      if same : object.kind = kind then
        if object.life ≠ .live then
          Op.reject (.undefined .outsideLifetime) state
        else if object.reached = false then
          Op.reject (.invalidBinding .declarationNotReached) state
        else if object.owner ≠ state.actor then
          Op.reject (.denied .wrongOwner) state
        else if object.permissions.readable = false then
          Op.reject (.denied .readPermission) state
        else
          match object.value with
          | none => Op.reject (uninitializedRead dialect) state
          | some stored =>
              let value := cast (congrArg (fun k => Value target k.asIntType) same) stored
              (.ok value, state, [.read ref.id kind value.toInt])
      else
        Op.reject (.invalidBinding .wrongKind) state

/-- A write can initialize a reached live object. Every write checks current
ownership and write authority and emits an event, including same-value writes. -/
def store {target : Target} {parameters : List IntType} {Environment : Type}
    {kind : ArithmeticType} (ref : LValue kind) (value : Value target kind.asIntType) :
    Op target parameters Environment Unit := fun state =>
  match state.objects ref.id with
  | none => Op.reject (.invalidBinding .unknownObject) state
  | some object =>
      if same : object.kind = kind then
        if object.life ≠ .live then
          Op.reject (.undefined .outsideLifetime) state
        else if object.reached = false then
          Op.reject (.invalidBinding .declarationNotReached) state
        else if object.owner ≠ state.actor then
          Op.reject (.denied .wrongOwner) state
        else if object.permissions.writable = false then
          Op.reject (.denied .writePermission) state
        else
          let stored := cast (congrArg (fun k => Value target k.asIntType) same.symm) value
          let updated : Object target := { object with value := some stored }
          (.ok (), state.putObject ref.id updated, [.write ref.id kind value.toInt])
      else
        Op.reject (.invalidBinding .wrongKind) state

/-- End a reached live object's lifetime and return its slot exactly once.
The tombstone retains identity and metadata. Pending-declaration cleanup is outside
this finite declaration-prefix slice; an unstarted C++ lifetime cannot be ended. -/
def endLifetime {target : Target} {parameters : List IntType} {Environment : Type}
    {kind : ArithmeticType} (ref : LValue kind) : Op target parameters Environment Unit :=
  fun state =>
    match state.objects ref.id with
    | none => Op.reject (.invalidBinding .unknownObject) state
    | some object =>
        if object.kind = kind then
          if object.life = .ended then
            Op.reject (.invalidBinding .alreadyEnded) state
          else if object.life ≠ .live then
            Op.reject (.undefined .outsideLifetime) state
          else if object.reached = false then
            Op.reject (.invalidBinding .declarationNotReached) state
          else if object.owner ≠ state.actor then
            Op.reject (.denied .wrongOwner) state
          else
            let ended : Object target := { object with life := .ended }
            let registered := state.putObject ref.id ended
            (.ok (), { registered with automaticSlots := state.automaticSlots + 1 },
              [.endLifetime ref.id kind])
        else
          Op.reject (.invalidBinding .wrongKind) state

/-- Successful and rejected reads both preserve the entire object state. -/
theorem load_preserves_state {target : Target} {parameters : List IntType}
    {Environment : Type} {kind : ArithmeticType} (dialect : Dialect) (ref : LValue kind)
    (state : State target parameters Environment) :
    (load dialect ref state).2.1 = state := by
  unfold load
  repeat' first | split | rfl

/-- A rejected later primitive does not roll back an earlier successful operation. -/
theorem Op.bind_reject_after_success {target : Target} {parameters : List IntType}
    {Environment α β : Type} (first : Op target parameters Environment α)
    (state updated : State target parameters Environment) (value : α)
    (events : List Event) (reason : Stop)
    (accepted : first state = (.ok value, updated, events)) :
    Op.bind first (fun _ => Op.reject (α := β) reason) state =
      (.error reason, updated, events) := by
  unfold Op.bind Effects.Op.bind
  rw [accepted]
  exact congrArg (fun trace => ((.error reason : Except Stop β), updated, trace))
    (List.append_nil events)

end EDSL.Source.Objects
