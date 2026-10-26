/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Model

set_option autoImplicit false
namespace EDSL.Source.Objects

/-- A state/error/event carrier for the shared expression traversal.
The carrier imposes no source sequencing, environment or scheduler assumptions. -/
structure EffectM (target : Target) (parameters : List IntType) (Environment : Type)
    (α : Type) where
  run : Op target parameters Environment α

namespace EffectM

theorem ext {target : Target} {parameters : List IntType} {Environment α : Type}
    {first second : EffectM target parameters Environment α}
    (same : first.run = second.run) : first = second := by
  cases first
  cases second
  cases same
  rfl

instance {target : Target} {parameters : List IntType} {Environment : Type} :
    Monad (EffectM target parameters Environment) where
  pure value := ⟨Op.pure value⟩
  bind first next := ⟨Op.bind first.run (fun value => (next value).run)⟩

def ofOp {target : Target} {parameters : List IntType} {Environment α : Type}
    (operation : Op target parameters Environment α) : EffectM target parameters Environment α :=
  ⟨operation⟩

theorem bind_pure_left {target : Target} {parameters : List IntType} {Environment α β : Type}
    (value : α) (next : α → EffectM target parameters Environment β) :
    (pure value >>= next) = next value := by
  apply ext
  funext state
  change Op.bind (Op.pure value) (fun value => (next value).run) state = (next value).run state
  unfold Op.bind Op.pure
  cases execution : (next value).run state with
  | mk outcome rest =>
      rcases rest with ⟨updated, events⟩
      simp only [execution, List.nil_append]

theorem bind_pure_right {target : Target} {parameters : List IntType} {Environment α : Type}
    (first : EffectM target parameters Environment α) :
    (first >>= pure) = first := by
  apply ext
  funext state
  change Op.bind first.run (fun value => Op.pure value) state = first.run state
  cases execution : first.run state with
  | mk outcome rest =>
      rcases rest with ⟨updated, events⟩
      cases outcome <;> simp [Op.bind, Op.pure, execution]

theorem bind_assoc {target : Target} {parameters : List IntType} {Environment α β γ : Type}
    (first : EffectM target parameters Environment α)
    (next : α → EffectM target parameters Environment β)
    (last : β → EffectM target parameters Environment γ) :
    ((first >>= next) >>= last) = (first >>= fun value => next value >>= last) := by
  apply ext
  funext state
  change Op.bind (Op.bind first.run (fun value => (next value).run))
      (fun value => (last value).run) state =
    Op.bind first.run (fun value => Op.bind (next value).run (fun result => (last result).run)) state
  cases execution : first.run state with
  | mk outcome rest =>
      rcases rest with ⟨updated, events⟩
      cases outcome with
      | error reason => simp [Op.bind, execution]
      | ok value =>
          cases following : (next value).run updated with
          | mk outcome rest =>
              rcases rest with ⟨followingState, followingEvents⟩
              cases outcome with
              | error reason => simp [Op.bind, execution, following]
              | ok result =>
                  cases final : (last result).run followingState with
                  | mk outcome rest =>
                      rcases rest with ⟨finalState, finalEvents⟩
                      simp [Op.bind, execution, following, final, List.append_assoc]

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
