/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Eval
import EDSL.Source.Objects.Registry

set_option autoImplicit false
namespace EDSL.Source.Objects

/-- An internal typed object designator, not a source pointer or address. -/
structure LValue (kind : ArithmeticType) where
  id : Nat
  deriving DecidableEq, Repr

/-- Full-integer specialization of the shared root-record representation. -/
abbrev Object (target : Target) :=
  Registry.Record ArithmeticType (fun kind => Option (Value target kind.asIntType))

/-- Pending records contain no initialized value; C++ reservation is pending. -/
def Object.WellFormed {target : Target} (object : Object target) : Prop :=
  (object.life = .reserved → object.reached = false) ∧
  (object.reached = false → object.value = none)

/-- Existing integer inputs and records specialize the single registry state. -/
abbrev State (target : Target) (parameters : List IntType) (Environment : Type) :=
  Registry.State (Inputs target parameters) Environment (Object target)

/-- The registry is finite below the fresh identity and metadata is consistent.
Identity is never reused, even when a record's lifetime has ended. -/
def State.WellFormed {target : Target} {parameters : List IntType} {Environment : Type}
    (state : State target parameters Environment) : Prop :=
  ∀ id object, state.objects id = some object → id < state.next ∧ object.WellFormed

/-- The legacy invariant is exactly the generic root invariant, including
arbitrary malformed records. This is an equality of predicates, not admission. -/
theorem Object.wellFormed_eq_registry {target : Target} (object : Object target) :
    object.WellFormed = Registry.Record.WellFormed (fun _ value => value = none) object := rfl

theorem State.wellFormed_eq_registry {target : Target} {parameters : List IntType}
    {Environment : Type} (state : State target parameters Environment) :
    state.WellFormed = Registry.State.WellFormed Object.WellFormed state := rfl

def State.empty {target : Target} {parameters : List IntType} {Environment : Type}
    (inputs : Inputs target parameters) (environment : Environment)
    (actor capacity : Nat) : State target parameters Environment :=
  Registry.State.empty inputs environment actor capacity

theorem State.empty_wellFormed {target : Target} {parameters : List IntType}
    {Environment : Type} (inputs : Inputs target parameters) (environment : Environment)
    (actor capacity : Nat) : (State.empty inputs environment actor capacity).WellFormed := by
  intro id object registered
  cases registered

def State.putObject {target : Target} {parameters : List IntType} {Environment : Type}
    (state : State target parameters Environment) (id : Nat) (object : Object target) :
    State target parameters Environment :=
  Registry.State.putObject state id object

@[simp] theorem State.putObject_same {target : Target} {parameters : List IntType}
    {Environment : Type} (state : State target parameters Environment)
    (id : Nat) (object : Object target) :
    (state.putObject id object).objects id = some object := by
  simp only [State.putObject, ↓reduceIte]

theorem State.putObject_other {target : Target} {parameters : List IntType}
    {Environment : Type} (state : State target parameters Environment)
    (id query : Nat) (object : Object target) (different : query ≠ id) :
    (state.putObject id object).objects query = state.objects query := by
  simp only [State.putObject, different, ↓reduceIte]

inductive ObjectUB where
  | outsideLifetime
  | uninitializedAutomaticRead
  deriving DecidableEq, Repr

inductive Erroneous where
  | uninitializedAutomaticRead
  deriving DecidableEq, Repr

inductive Denial where
  | automaticStorageExhausted | wrongOwner | readPermission | writePermission
  deriving DecidableEq, Repr

inductive BindingFault where
  | unknownObject | wrongKind | declarationNotReached
  | declarationAlreadyInitialized | invalidDeclarationState | alreadyEnded
  deriving DecidableEq, Repr

/-- Language failures, coverage and model authority/binding failures are separate.
Ordinary C++ automatic int reads may produce erroneous behavior rather than C UB. -/
inductive Stop where
  | scalar (reason : UBReason)
  | undefined (reason : ObjectUB)
  | erroneous (reason : Erroneous)
  | denied (reason : Denial)
  | invalidBinding (reason : BindingFault)
  | unsupported (feature : UnsupportedFeature)
  deriving DecidableEq, Repr

def uninitializedRead (dialect : Dialect) : Stop :=
  match dialect with
  | .gnuC23 => .undefined .uninitializedAutomaticRead
  | .gnuCpp26 => .erroneous .uninitializedAutomaticRead

/-- Internal value/authority observations; no native byte or read-order claim. -/
inductive Event where
  | reserve (id : Nat) (kind : ArithmeticType) (owner : Nat)
  | beginLifetime (id : Nat) (kind : ArithmeticType)
  | initialize (id : Nat) (kind : ArithmeticType) (value : Option Int)
  | read (id : Nat) (kind : ArithmeticType) (value : Int)
  | write (id : Nat) (kind : ArithmeticType) (value : Int)
  | endLifetime (id : Nat) (kind : ArithmeticType)
  deriving DecidableEq, Repr

abbrev Result (target : Target) (parameters : List IntType) (Environment : Type)
    (α : Type) := Except Stop α × State target parameters Environment × List Event
abbrev Op (target : Target) (parameters : List IntType) (Environment : Type)
    (α : Type) := State target parameters Environment → Result target parameters Environment α

def Op.pure {target : Target} {parameters : List IntType} {Environment α : Type}
    (value : α) : Op target parameters Environment α :=
  fun state => (.ok value, state, [])

def Op.reject {target : Target} {parameters : List IntType} {Environment α : Type}
    (reason : Stop) : Op target parameters Environment α :=
  fun state => (.error reason, state, [])

/-- Composition retains all earlier accepted state changes/events if a later
operation fails. Primitive rejection itself remains state preserving. -/
def Op.bind {target : Target} {parameters : List IntType} {Environment α β : Type}
    (first : Op target parameters Environment α) (next : α → Op target parameters Environment β) :
    Op target parameters Environment β := fun state =>
  let (outcome, updated, events) := first state
  match outcome with
  | .error reason => (.error reason, updated, events)
  | .ok value =>
      let (result, finalState, moreEvents) := next value updated
      (result, finalState, events ++ moreEvents)

end EDSL.Source.Objects
