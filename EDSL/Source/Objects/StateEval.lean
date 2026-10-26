/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.StateSyntax
import EDSL.Source.Objects.Effects
import EDSL.Source.Objects.Access
import EDSL.Source.ExpressionCore.PureInvariant

set_option autoImplicit false

namespace EDSL.Source.Objects.StateEval

open StateSyntax

/-! Finite statement execution over an already bound object environment.
The state input type is independent of the growing source context. The only
expression traversal is ExpressionCore.evalCore. Every variable read uses load,
including a mutable formal parameter; State.inputs is never queried here.
Allocation, initialization, cleanup, OS refinement and a source certificate are
outside this module. Internal RHS read order is not a native sequencing claim.
-/

/-- Resolve a typed source variable through its current object, with all actual
lifetime, ownership, authority, initialization and dialect-specific checks. -/
def resolve {target : Target} {stateParameters : List IntType} {Environment : Type}
    {context : List ArithmeticType} (dialect : Dialect) (environment : Env context) :
    {type : IntType} → Param (VariableTypes context) type →
      EffectM target stateParameters Environment (Value target type) :=
  match environment with
  | .nil => fun index => nomatch index
  | .cons reference tail => fun index =>
      match index with
      | .here => EffectM.ofOp (load dialect reference)
      | .there index => resolve dialect tail index

/-- The shared expression engine specialized to actual object reads. -/
def evalExpr {target : Target} {stateParameters : List IntType} {Environment : Type}
    {context : List ArithmeticType} {type : IntType} (dialect : Dialect)
    (policy : IntegerConversionPolicy) (environment : Env context)
    (expression : RHS target context type) :
    Op target stateParameters Environment (Value target type) :=
  (ExpressionCore.evalCore (M := EffectM target stateParameters Environment) policy
    (fun outcome => EffectM.liftScalar outcome) (resolve dialect environment) expression).run

/-- Internal sequenced full expressions and lazy statement selection. The caller
must use whole-program coverage before allocation; runStmt also supplies a
standalone whole-statement preflight. Return is evaluated before caller cleanup. -/
def evalStmt {target : Target} {stateParameters : List IntType} {Environment : Type}
    {context : List ArithmeticType} {result : IntType} (dialect : Dialect)
    (policy : IntegerConversionPolicy) (environment : Env context) :
    Stmt target context result → Op target stateParameters Environment (Value target result)
  | .set index value next =>
      Op.bind (evalExpr dialect policy environment value) fun evaluated =>
        Op.bind (store (environment.get index) evaluated) fun _ =>
          evalStmt dialect policy environment next
  | .branch condition yes no =>
      Op.bind (evalExpr dialect policy environment condition) fun evaluated =>
        if evaluated.toInt = 0 then evalStmt dialect policy environment no
        else evalStmt dialect policy environment yes
  | .ret value => evalExpr dialect policy environment value
  | .unsupported feature => Op.reject (.unsupported feature)

/-- Public statement runner rejects unsupported syntax anywhere before effects,
including RHSs and syntax in branches which dynamic execution would skip. -/
def runStmt {target : Target} {stateParameters : List IntType} {Environment : Type}
    {context : List ArithmeticType} {result : IntType} (dialect : Dialect)
    (policy : IntegerConversionPolicy) (environment : Env context)
    (statement : Stmt target context result) :
    Op target stateParameters Environment (Value target result) :=
  match statement.firstUnsupported with
  | some feature => Op.reject (.unsupported feature)
  | none => evalStmt dialect policy environment statement

@[simp] theorem evalExpr_literal {target : Target} {stateParameters : List IntType}
    {Environment : Type} {context : List ArithmeticType} {type : IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (environment : Env context)
    (value : Value target type) :
    (evalExpr dialect policy environment (.literal value) :
      Op target stateParameters Environment _) = Op.pure value := rfl

@[simp] theorem resolve_here {target : Target} {stateParameters : List IntType}
    {Environment : Type} {context : List ArithmeticType} {kind : ArithmeticType}
    (dialect : Dialect) (environment : Env context) (reference : LValue kind) :
    (resolve dialect (environment.extend reference) (.here : Vars (kind :: context) kind) :
      EffectM target stateParameters Environment _) = EffectM.ofOp (load dialect reference) := rfl

@[simp] theorem resolve_there {target : Target} {stateParameters : List IntType}
    {Environment : Type} {context : List ArithmeticType} {kind : ArithmeticType} {type : IntType}
    (dialect : Dialect) (environment : Env context) (reference : LValue kind)
    (index : Param (VariableTypes context) type) :
    (resolve dialect (environment.extend reference) (.there index) :
      EffectM target stateParameters Environment _) = resolve dialect environment index := rfl

/-- Source object lookup agrees with the typed environment lookup, rather than
any immutable external input. -/
theorem resolve_var {target : Target} {stateParameters : List IntType}
    {Environment : Type} {context : List ArithmeticType} {kind : ArithmeticType}
    (dialect : Dialect) (environment : Env context) (index : Vars context kind) :
    (resolve dialect environment index : EffectM target stateParameters Environment _) =
      EffectM.ofOp (load dialect (environment.get index)) := by
  induction environment with
  | nil => cases index
  | @cons head context reference tail ih =>
      cases head <;> cases kind <;> cases index <;> first
      | rfl
      | exact ih _

@[simp] theorem evalExpr_var {target : Target} {stateParameters : List IntType}
    {Environment : Type} {context : List ArithmeticType} {kind : ArithmeticType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (environment : Env context)
    (index : Vars context kind) :
    (evalExpr dialect policy environment (.param index) : Op target stateParameters Environment _) =
      load dialect (environment.get index) := by
  simp only [evalExpr, ExpressionCore.evalCore, ExpressionCore.evalEngine,
    ExpressionCore.integerResolver_index, Param.ofIndex_toIndex, resolve_var, EffectM.ofOp,
    Effects.EffectM.ofOp]

@[simp] theorem evalStmt_ret {target : Target} {stateParameters : List IntType}
    {Environment : Type} {context : List ArithmeticType} {result : IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (environment : Env context)
    (value : RHS target context result) :
    (evalStmt dialect policy environment (.ret value) : Op target stateParameters Environment _) =
      evalExpr dialect policy environment value := rfl

/-- Supported public execution is exactly the internal statement operation. -/
theorem runStmt_supported {target : Target} {stateParameters : List IntType}
    {Environment : Type} {context : List ArithmeticType} {result : IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (environment : Env context)
    (statement : Stmt target context result) (supported : statement.Supported) :
    (runStmt dialect policy environment statement : Op target stateParameters Environment _) =
      evalStmt dialect policy environment statement := by
  unfold runStmt
  rw [statement.firstUnsupported_eq_none_iff.mpr supported]

/-- Unsupported syntax rejects with the exact initial state and empty trace,
independently of whether dynamic evaluation would have demanded that syntax. -/
theorem runStmt_unsupported {target : Target} {stateParameters : List IntType}
    {Environment : Type} {context : List ArithmeticType} {result : IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (environment : Env context)
    (statement : Stmt target context result) (feature : UnsupportedFeature)
    (uncovered : statement.firstUnsupported = some feature)
    (state : State target stateParameters Environment) :
    runStmt dialect policy environment statement state = (.error (.unsupported feature), state, []) := by
  simp only [runStmt, uncovered, Op.reject]

/-- Complete object/input/environment/resource state preservation, including a
computation which rejects. Event observations are retained independently. -/
def PreservesState {target : Target} {stateParameters : List IntType}
    {Environment α : Type} (operation : EffectM target stateParameters Environment α) : Prop :=
  ∀ state, (operation.run state).2.1 = state

private theorem preserves_pure {target : Target} {stateParameters : List IntType}
    {Environment α : Type} (value : α) :
    PreservesState (pure value : EffectM target stateParameters Environment α) := by
  intro state
  rfl

private theorem preserves_bind {target : Target} {stateParameters : List IntType}
    {Environment α β : Type} (first : EffectM target stateParameters Environment α)
    (next : α → EffectM target stateParameters Environment β)
    (firstStable : PreservesState first) (nextStable : ∀ value, PreservesState (next value)) :
    PreservesState (first >>= next) := by
  intro state
  change (Op.bind first.run (fun value => (next value).run) state).2.1 = state
  cases firstResult : first.run state with
  | mk outcome rest =>
      rcases rest with ⟨updated, events⟩
      have firstSame : updated = state := by
        simpa only [firstResult] using firstStable state
      cases outcome with
      | error reason => simpa only [Op.bind, Effects.Op.bind, firstResult] using firstSame
      | ok value =>
          simp only [Op.bind, Effects.Op.bind, firstResult]
          exact (nextStable value updated).trans firstSame

private theorem preserves_liftScalar {target : Target} {stateParameters : List IntType}
    {Environment α : Type} (outcome : Outcome α) :
    PreservesState (EffectM.liftScalar outcome : EffectM target stateParameters Environment α) := by
  intro state
  rfl

/-- Rejected lookup cannot mutate state either; actual load is used on every
source slot. This statement needs no initialized/readable premise. -/
theorem resolve_preserves_state {target : Target} {stateParameters : List IntType}
    {Environment : Type} {context : List ArithmeticType} {type : IntType}
    (dialect : Dialect) (environment : Env context)
    (index : Param (VariableTypes context) type) :
    PreservesState (resolve dialect environment index :
      EffectM target stateParameters Environment (Value target type)) := by
  induction environment with
  | nil => cases index
  | @cons head context reference tail ih =>
      cases index with
      | here => exact load_preserves_state dialect reference
      | there index => exact ih index

/-- The object specialization of the shared expression engine never changes
state, for success and every stop. It still emits demanded read observations.
This is not an interference, volatile/atomic or native operand-order theorem. -/
theorem evalExpr_preserves_state {target : Target} {stateParameters : List IntType}
    {Environment : Type} {context : List ArithmeticType} {type : IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (environment : Env context)
    (expression : RHS target context type) (state : State target stateParameters Environment) :
    (evalExpr dialect policy environment expression state).2.1 = state := by
  have allStable : PreservesState
      (ExpressionCore.evalCore (M := EffectM target stateParameters Environment) policy
        (fun outcome => EffectM.liftScalar outcome) (resolve dialect environment) expression) := by
    exact ExpressionCore.evalCore_property (fun operation => PreservesState operation)
      preserves_pure preserves_bind policy (fun outcome => EffectM.liftScalar outcome)
      (resolve dialect environment) preserves_liftScalar
      (fun index => resolve_preserves_state dialect environment index) expression
  exact allStable state

/-- Once an RHS succeeds, assignment performs its actual authority-checked store
before the next full expression. Earlier accepted events/state survive failure
of either store or continuation. -/
theorem evalStmt_set_after_expression {target : Target} {stateParameters : List IntType}
    {Environment : Type} {context : List ArithmeticType} {kind : ArithmeticType}
    {result : IntType} (dialect : Dialect) (policy : IntegerConversionPolicy)
    (environment : Env context) (index : Vars context kind)
    (value : RHS target context kind.asIntType) (next : Stmt target context result)
    (state evaluatedState : State target stateParameters Environment)
    (evaluated : Value target kind.asIntType) (readEvents : List Event)
    (computed : evalExpr dialect policy environment value state =
      (.ok evaluated, evaluatedState, readEvents)) :
    evalStmt dialect policy environment (.set index value next) state =
      let continuation := Op.bind (store (environment.get index) evaluated)
        (fun _ => evalStmt dialect policy environment next) evaluatedState
      (continuation.1, continuation.2.1, readEvents ++ continuation.2.2) := by
  simp only [evalStmt, Op.bind, Effects.Op.bind, computed]

/-- Statement branch demands exactly the selected subtree once the condition
has been computed. No claim is made that skipped syntax passed coverage. -/
theorem evalStmt_branch_after_expression {target : Target} {stateParameters : List IntType}
    {Environment : Type} {context : List ArithmeticType} {result : IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (environment : Env context)
    (condition : RHS target context (.small .boolean)) (yes no : Stmt target context result)
    (state evaluatedState : State target stateParameters Environment)
    (evaluated : Value target (.small .boolean)) (readEvents : List Event)
    (computed : evalExpr dialect policy environment condition state =
      (.ok evaluated, evaluatedState, readEvents)) :
    evalStmt dialect policy environment (.branch condition yes no) state =
      let continuation := evalStmt dialect policy environment
        (if evaluated.toInt = 0 then no else yes) evaluatedState
      (continuation.1, continuation.2.1, readEvents ++ continuation.2.2) := by
  simp only [evalStmt, Op.bind, Effects.Op.bind, computed]
  split <;> rfl

end EDSL.Source.Objects.StateEval
