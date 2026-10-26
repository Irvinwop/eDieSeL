/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0

Pure compatibility with the scalar specialization of the shared traversal.
These results do not implement mutable-source programs, loaded input objects,
operand sequencing/read-order invariance, OS/scheduler or native correspondence.
-/
import EDSL.Source.ExpressionCore
import EDSL.Source.Certificate
import EDSL.Source.Objects.Effects

set_option autoImplicit false

namespace EDSL.Source.Objects.PureEmbedding

@[instance_reducible] private def outcomeMonad : Monad Outcome where
  pure := Outcome.defined
  bind := Outcome.andThen

attribute [local instance] outcomeMonad

/-- Pure supplied inputs, specialized through the same generic traversal.
Lookup neither loads an object nor consults or modifies the carrier state. -/
def evalExpr {target : Target} {parameters : List IntType} {Environment : Type} {ty : IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (expression : Expr target parameters ty) : EffectM target parameters Environment (Value target ty) :=
  ExpressionCore.evalCore policy EffectM.liftScalar (fun index => pure (inputs.get index)) expression

/-- Equality of complete computations for every raw outcome, with no coverage,
definedness, well-formed-state or inhabited-environment premise. -/
theorem evalExpr_eq_liftScalar
    {target : Target} {parameters : List IntType} {Environment : Type} {ty : IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (expression : Expr target parameters ty) :
    (evalExpr policy inputs expression : EffectM target parameters Environment (Value target ty)) =
      EffectM.liftScalar (Source.evalExpr policy inputs expression) := by
  have transported := ExpressionCore.evalCore_map
    (M := Outcome) (N := EffectM target parameters Environment) policy
    (fun outcome => EffectM.liftScalar outcome)
    (fun value => EffectM.liftScalar_pure value)
    (fun outcome next => EffectM.liftScalar_bind outcome next)
    (fun outcome => outcome) (fun outcome => EffectM.liftScalar outcome)
    (fun index => .defined (inputs.get index)) (fun index => pure (inputs.get index))
    (fun _ => rfl) (fun index => EffectM.liftScalar_pure (inputs.get index)) expression
  change EffectM.liftScalar (ExpressionCore.evalOutcome policy inputs expression) =
    evalExpr policy inputs expression at transported
  exact transported.symm

/-- Exact raw result: the whole state, including environment and all object
metadata, is retained; the event list is empty on success, UB and unsupported. -/
theorem run_evalExpr
    {target : Target} {parameters : List IntType} {Environment : Type} {ty : IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (expression : Expr target parameters ty) (state : State target parameters Environment) :
    (evalExpr policy inputs expression).run state =
      (EffectM.scalarOutcome (Source.evalExpr policy inputs expression), state, []) := by
  rw [evalExpr_eq_liftScalar, EffectM.run_liftScalar]

/-- Embed the original scalar Program using its exact public coverage gate and
explicit entry-state inputs. No object load, allocation or mutation is inserted. -/
def evalProgram {target : Target} {parameters : List IntType} {Environment : Type} {ty : IntType}
    (program : Program target parameters ty) : EffectM target parameters Environment (Value target ty) :=
  ⟨fun state => match program.body.firstUnsupported with
    | none => (evalExpr program.conversions state.inputs program.body).run state
    | some feature => (EffectM.liftScalar (.unsupported feature)).run state⟩

theorem run_evalProgram {target : Target} {parameters : List IntType} {Environment : Type}
    {ty : IntType} (program : Program target parameters ty)
    (state : State target parameters Environment) :
    (evalProgram program).run state =
      (EffectM.scalarOutcome (Source.eval program state.inputs), state, []) := by
  unfold evalProgram Source.eval
  cases program.body.firstUnsupported <;>
    simp only [run_evalExpr, EffectM.run_liftScalar]

/-- An existing source proof supplies actual execution and complete state frame.
This is proof reuse, without a target-NoUB premise in any input admission. -/
theorem verifies_embeds {target : Target} {parameters : List IntType} {Environment : Type}
    {ty : IntType} (program : Program target parameters ty)
    (admitted : Inputs target parameters → Prop)
    (post : Inputs target parameters → Value target ty → Prop)
    (verified : Source.Verifies program admitted post)
    (state : State target parameters Environment) (permitted : admitted state.inputs) :
    ∃ value, (evalProgram program).run state = (.ok value, state, []) ∧
      post state.inputs value := by
  obtain ⟨value, execution, resultPost⟩ := verified state.inputs permitted
  refine ⟨value, ?_, resultPost⟩
  rw [run_evalProgram, execution]
  rfl

/-- Nonvacuous state evidence needs an actual environment value. An empty
Environment type cannot be used to manufacture a useful source certificate. -/
theorem certificate_has_state {target : Target} {parameters : List IntType} {Environment : Type}
    {ty : IntType} (program : Program target parameters ty)
    (admitted : Inputs target parameters → Prop)
    (post : Inputs target parameters → Value target ty → Prop)
    (certificate : Source.Certificate program admitted post) (environment : Environment) :
    ∃ (state : State target parameters Environment) (value : Value target ty), admitted state.inputs ∧
      (evalProgram program).run state = (.ok value, state, []) ∧ post state.inputs value := by
  obtain ⟨inputs, permitted⟩ := certificate.useful
  let state := State.empty inputs environment 0 0
  obtain ⟨value, execution, resultPost⟩ :=
    verifies_embeds program admitted post certificate.verified state permitted
  exact ⟨state, value, permitted, execution, resultPost⟩


end EDSL.Source.Objects.PureEmbedding
