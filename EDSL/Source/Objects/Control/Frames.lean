/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.Machine
import EDSL.Source.Objects.AccessContracts

set_option autoImplicit false
namespace EDSL.Source.Objects.Control
open StateSyntax
variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {context : List ArithmeticType} {result : IntType} {α β : Type}

/-- This ordinary-object control fragment changes only object values. It has no
allocation, cleanup or environmental/interference transition. These fields remain
first-class state, rather than being erased from the execution observation. -/
structure WorldFrame (before after : State target parameters Environment) : Prop where
  inputs : after.inputs = before.inputs
  environment : after.environment = before.environment
  actor : after.actor = before.actor
  next : after.next = before.next
  automaticSlots : after.automaticSlots = before.automaticSlots

theorem WorldFrame.refl (state : State target parameters Environment) : WorldFrame state state :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem WorldFrame.trans {first middle final : State target parameters Environment}
    (before : WorldFrame first middle) (after : WorldFrame middle final) : WorldFrame first final :=
  ⟨after.inputs.trans before.inputs, after.environment.trans before.environment,
    after.actor.trans before.actor, after.next.trans before.next,
    after.automaticSlots.trans before.automaticSlots⟩

def PreservesWorld (operation : Op target parameters Environment α) : Prop :=
  ∀ state, WorldFrame state (operation state).2.1

private theorem preservesWorld_bind (first : Op target parameters Environment α)
    (next : α → Op target parameters Environment β)
    (firstFrame : PreservesWorld first) (nextFrame : ∀ value, PreservesWorld (next value)) :
    PreservesWorld (Op.bind first next) := by
  intro state
  cases execution : first state with
  | mk outcome rest =>
      rcases rest with ⟨middle, events⟩
      have earlier : WorldFrame state middle := by
        simpa only [execution] using firstFrame state
      cases outcome with
      | error reason => simpa only [Op.bind, execution] using earlier
      | ok value =>
          simp only [Op.bind, execution]
          exact earlier.trans (nextFrame value middle)

theorem evalExpr_worldFrame (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) {type : IntType} (expression : RHS target context type) :
    PreservesWorld (StateEval.evalExpr (stateParameters := parameters) (Environment := Environment)
      dialect policy bindings expression) := by
  intro state
  rw [StateEval.evalExpr_preserves_state]
  exact WorldFrame.refl state

theorem store_worldFrame {kind : ArithmeticType} (reference : LValue kind)
    (value : Value target kind.asIntType) :
    PreservesWorld (store (parameters := parameters) (Environment := Environment) reference value) := by
  intro state
  have frame := store_preserves_frame state reference value
  exact ⟨frame.1, frame.2.1, frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2.1⟩

theorem assign_worldFrame {kind : ArithmeticType} (dialect : Dialect)
    (policy : IntegerConversionPolicy) (bindings : Env context)
    (index : Vars context kind) (value : RHS target context kind.asIntType) :
    PreservesWorld (assign (parameters := parameters) (Environment := Environment)
      dialect policy bindings index value) :=
  preservesWorld_bind _ _ (evalExpr_worldFrame dialect policy bindings value)
    (fun evaluated => store_worldFrame (bindings.get index) evaluated)

private theorem perform_worldFrame (operation : Op target parameters Environment α)
    (next : α → Config target parameters Environment context result →
      Config target parameters Environment context result)
    (operationFrame : PreservesWorld operation)
    (nextFrame : ∀ value config, WorldFrame config.state (next value config).state)
    (initial : Config target parameters Environment context result) :
    WorldFrame initial.state (perform operation next initial).state := by
  cases execution : operation initial.state with
  | mk outcome rest =>
      rcases rest with ⟨updated, events⟩
      have earlier : WorldFrame initial.state updated := by
        simpa only [execution] using operationFrame initial.state
      cases outcome with
      | error reason => simpa only [perform, execution] using earlier
      | ok value =>
          simp only [perform, execution]
          exact earlier.trans (nextFrame value { initial with
            state := updated, events := initial.events ++ events })

/-- Every actual transition preserves the complete caller world and capacity,
on success and refusal alike. This is not a scheduler/noninterference assumption
for a richer language: the current Code has only ordinary local object effects. -/
theorem tick_worldFrame (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) (initial : Config target parameters Environment context result) :
    WorldFrame initial.state (tick dialect policy bindings initial).state := by
  cases initial with
  | mk control state events status =>
      cases status with
      | returned value => exact WorldFrame.refl state
      | fellThrough => exact WorldFrame.refl state
      | stopped reason => exact WorldFrame.refl state
      | running =>
          cases control with
          | nil => exact WorldFrame.refl state
          | cons code rest =>
              cases code with
              | skip => exact WorldFrame.refl state
              | seq first next => exact WorldFrame.refl state
              | unsupported feature => exact WorldFrame.refl state
              | assign index value =>
                  apply perform_worldFrame _ _ (assign_worldFrame dialect policy bindings index value)
                  intro ignored current
                  exact WorldFrame.refl current.state
              | branch condition yes no =>
                  apply perform_worldFrame _ _ (evalExpr_worldFrame dialect policy bindings condition)
                  intro evaluated current
                  exact WorldFrame.refl current.state
              | loop condition body =>
                  apply perform_worldFrame _ _ (evalExpr_worldFrame dialect policy bindings condition)
                  intro evaluated current
                  exact WorldFrame.refl current.state
              | ret value =>
                  apply perform_worldFrame _ _ (evalExpr_worldFrame dialect policy bindings value)
                  intro evaluated current
                  exact WorldFrame.refl current.state

/-- The frame holds over every finite prefix, including prefixes of a genuinely
diverging run. No completion, source NoUB or promised future state is assumed. -/
theorem run_worldFrame (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) (steps : Nat)
    (initial : Config target parameters Environment context result) :
    WorldFrame initial.state (run dialect policy bindings steps initial).state := by
  induction steps with
  | zero => exact WorldFrame.refl initial.state
  | succ steps ih => exact ih.trans (tick_worldFrame dialect policy bindings _)

end EDSL.Source.Objects.Control
