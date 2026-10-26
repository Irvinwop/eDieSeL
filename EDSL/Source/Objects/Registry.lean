/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Types

set_option autoImplicit false
namespace EDSL.Source.Objects

inductive Life where
  | reserved | live | ended
  deriving DecidableEq, Repr

structure Permissions where
  readable : Bool
  writable : Bool
  deriving DecidableEq, Repr

namespace Registry

/-- Common root metadata and typed contents. This representation alone supplies
no access, allocation, lifetime or source-language rule. -/
structure Record (Kind : Type) (Contents : Kind → Type) where
  kind : Kind
  life : Life
  reached : Bool
  value : Contents kind
  owner : Nat
  permissions : Permissions

/-- One registry shape shared by its contents representations. Array leaves
belong to their root's contents; this state does not allocate subobject roots. -/
structure State (Input Environment Object : Type) where
  inputs : Input
  environment : Environment
  actor : Nat
  next : Nat
  /-- Remaining abstract automatic-object slots, not a byte capacity. -/
  automaticSlots : Nat
  objects : Nat → Option Object

abbrev Record.WellFormed {Kind : Type} {Contents : Kind → Type}
    (empty : (kind : Kind) → Contents kind → Prop) (object : Record Kind Contents) : Prop :=
  (object.life = .reserved → object.reached = false) ∧
  (object.reached = false → empty object.kind object.value)

abbrev State.WellFormed {Input Environment Object : Type}
    (good : Object → Prop) (state : State Input Environment Object) : Prop :=
  ∀ id object, state.objects id = some object → id < state.next ∧ good object

abbrev State.empty {Input Environment Object : Type}
    (inputs : Input) (environment : Environment) (actor capacity : Nat) :
    State Input Environment Object where
  inputs := inputs
  environment := environment
  actor := actor
  next := 0
  automaticSlots := capacity
  objects := fun _ => none

abbrev State.putObject {Input Environment Object : Type}
    (state : State Input Environment Object) (id : Nat) (object : Object) :
    State Input Environment Object :=
  { state with objects := fun query => if query = id then some object else state.objects query }

end Registry
end EDSL.Source.Objects
