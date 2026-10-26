/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Model

set_option autoImplicit false
namespace EDSL.Source.Objects

/-- A state/error/event carrier for the shared expression traversal.
The carrier imposes no source sequencing, environment or scheduler assumptions. -/
abbrev EffectM (target : Target) (parameters : List IntType) (Environment : Type)
    (α : Type) := Effects.EffectM (State target parameters Environment) Stop Event α

namespace EffectM

/-- Preserve the old qualified constructor and projection on the specialization. -/
@[match_pattern] abbrev mk {target : Target} {parameters : List IntType} {Environment α : Type}
    (run : Op target parameters Environment α) : EffectM target parameters Environment α :=
  Effects.EffectM.mk run

abbrev run {target : Target} {parameters : List IntType} {Environment α : Type}
    (self : EffectM target parameters Environment α) : Op target parameters Environment α :=
  Effects.EffectM.run self

theorem ext {target : Target} {parameters : List IntType} {Environment α : Type}
    {first second : EffectM target parameters Environment α}
    (same : first.run = second.run) : first = second := Effects.EffectM.ext same

/-- The old instance name forwards to the generic instance; no second instance
or implementation of composition is installed. -/
abbrev instMonad {target : Target} {parameters : List IntType} {Environment : Type} :
    Monad (EffectM target parameters Environment) := Effects.EffectM.instMonad

def ofOp {target : Target} {parameters : List IntType} {Environment α : Type}
    (operation : Op target parameters Environment α) : EffectM target parameters Environment α :=
  Effects.EffectM.ofOp operation

theorem bind_pure_left {target : Target} {parameters : List IntType} {Environment α β : Type}
    (value : α) (next : α → EffectM target parameters Environment β) :
    (pure value >>= next) = next value := Effects.EffectM.bind_pure_left value next

theorem bind_pure_right {target : Target} {parameters : List IntType} {Environment α : Type}
    (first : EffectM target parameters Environment α) :
    (first >>= pure) = first := Effects.EffectM.bind_pure_right first

theorem bind_assoc {target : Target} {parameters : List IntType} {Environment α β γ : Type}
    (first : EffectM target parameters Environment α)
    (next : α → EffectM target parameters Environment β)
    (last : β → EffectM target parameters Environment γ) :
    ((first >>= next) >>= last) = (first >>= fun value => next value >>= last) :=
  Effects.EffectM.bind_assoc first next last

/-- Scalar failures retain their identity while gaining the explicit object-state
carrier. No object failure is reclassified as a scalar UB here. -/
def scalarOutcome {α : Type} : Outcome α → Except Stop α
  | .defined value => .ok value
  | .undefined reason => .error (.scalar reason)
  | .unsupported feature => .error (.unsupported feature)

/-- Pure scalar computation preserves the complete state and emits no events. -/
def liftScalar {target : Target} {parameters : List IntType} {Environment α : Type}
    (outcome : Outcome α) : EffectM target parameters Environment α :=
  ⟨fun state => (scalarOutcome outcome, state, [])⟩

theorem run_liftScalar {target : Target} {parameters : List IntType} {Environment α : Type}
    (outcome : Outcome α) (state : State target parameters Environment) :
    (liftScalar outcome).run state = (scalarOutcome outcome, state, []) := rfl

theorem liftScalar_pure {target : Target} {parameters : List IntType} {Environment α : Type}
    (value : α) :
    (liftScalar (.defined value) : EffectM target parameters Environment α) = pure value := rfl

theorem liftScalar_bind {target : Target} {parameters : List IntType} {Environment α β : Type}
    (outcome : Outcome α) (next : α → Outcome β) :
    (liftScalar (outcome.andThen next) : EffectM target parameters Environment β) =
      (liftScalar outcome >>= fun value => liftScalar (next value)) := by
  cases outcome <;> rfl

end EffectM
end EDSL.Source.Objects
