/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.StateEval
import EDSL.Source.Objects.ReadOrder
import EDSL.Source.Objects.Protocol

set_option autoImplicit false
namespace EDSL.Source.Objects.ExpressionReadOrder
open StateSyntax Protocol
variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {α β : Type}

/-- Only the internal ordinary read observations belong to this class. -/
def IsRead : Event → Prop
  | .read _ _ _ => True
  | _ => False

def Reads (events : List Event) : Prop := ∀ event ∈ events, IsRead event

def ReadsOnly (operation : EffectM target parameters Environment α) : Prop :=
  ∀ state, Reads (operation.run state).2.2

private theorem reads_append {left right : List Event}
    (first : Reads left) (second : Reads right) : Reads (left ++ right) := by
  intro event member
  rcases List.mem_append.mp member with before | after
  · exact first event before
  · exact second event after

private theorem reads_pure (value : α) :
    ReadsOnly (pure value : EffectM target parameters Environment α) := by
  intro state event member
  cases member

private theorem reads_scalar (outcome : Outcome α) :
    ReadsOnly (EffectM.liftScalar outcome : EffectM target parameters Environment α) := by
  intro state event member
  cases member

private theorem reads_bind (first : EffectM target parameters Environment α)
    (next : α → EffectM target parameters Environment β)
    (firstReads : ReadsOnly first) (nextReads : ∀ value, ReadsOnly (next value)) :
    ReadsOnly (first >>= next) := by
  intro state
  change Reads (Op.bind first.run (fun value => (next value).run) state).2.2
  cases execution : first.run state with
  | mk outcome rest =>
      rcases rest with ⟨middle, events⟩
      have earlier : Reads events := by simpa only [execution] using firstReads state
      cases outcome with
      | error reason => simpa only [Op.bind, Effects.Op.bind, execution] using earlier
      | ok value =>
          simp only [Op.bind, Effects.Op.bind, execution]
          exact reads_append earlier (nextReads value middle)

/-- Actual load emits either its ordinary read event or no event on refusal.
This theorem assumes no success, metadata or authority condition. -/
theorem load_reads {kind : ArithmeticType} (dialect : Dialect) (reference : LValue kind) :
    ReadsOnly (EffectM.ofOp (load dialect reference) :
      EffectM target parameters Environment (Value target kind.asIntType)) := by
  intro state
  change Reads (load dialect reference state).2.2
  unfold load
  repeat' first | split | simp [Op.reject, Reads, IsRead]

theorem resolve_reads {context : List ArithmeticType} {type : IntType}
    (dialect : Dialect) (environment : Env context)
    (index : Param (VariableTypes context) type) :
    ReadsOnly (StateEval.resolve dialect environment index :
      EffectM target parameters Environment (Value target type)) := by
  induction environment with
  | nil => cases index
  | @cons kind context reference tail ih =>
      cases index with
      | here => exact load_reads dialect reference
      | there index => exact ih index

/-- Every demanded observation of the shared expression traversal is a read,
including a prefix retained before failure. Skipped arms emit no observations;
this proof follows the existing evaluator, with no second expression semantics. -/
theorem evalExpr_reads {context : List ArithmeticType} {type : IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (environment : Env context)
    (expression : RHS target context type) (state : State target parameters Environment) :
    Reads (StateEval.evalExpr dialect policy environment expression state).2.2 := by
  have allReads : ReadsOnly
      (ExpressionCore.evalCore (M := EffectM target parameters Environment) policy
        (fun outcome => EffectM.liftScalar outcome) (StateEval.resolve dialect environment) expression) := by
    exact ExpressionCore.evalCore_property (fun operation => ReadsOnly operation)
      reads_pure reads_bind policy (fun outcome => EffectM.liftScalar outcome)
      (StateEval.resolve dialect environment) reads_scalar
      (fun index => resolve_reads dialect environment index) expression
  exact allReads state

/-- INTERNAL composition of two arbitrary source RHS computations from their
proved obligations at one frozen state. These conditions are VCs to discharge,
not source admission premises or a native C/C++ operand-order theorem. Each VC
requires only its own dynamically demanded reads. Errors are not reordered. -/
theorem expression_pair_commutes {context : List ArithmeticType} {leftType rightType : IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (environment : Env context)
    (left : RHS target context leftType) (right : RHS target context rightType)
    (state : State target parameters Environment)
    (leftPost : Value target leftType → Prop) (rightPost : Value target rightType → Prop)
    (leftCondition : WP (StateEval.evalExpr dialect policy environment left)
      (fun _ value _ _ => leftPost value) state)
    (rightCondition : WP (StateEval.evalExpr dialect policy environment right)
      (fun _ value _ _ => rightPost value) state) :
    ∃ leftValue rightValue leftEvents rightEvents,
      StateEval.evalExpr dialect policy environment left state = (.ok leftValue, state, leftEvents) ∧
      StateEval.evalExpr dialect policy environment right state = (.ok rightValue, state, rightEvents) ∧
      leftPost leftValue ∧ rightPost rightValue ∧ Reads leftEvents ∧ Reads rightEvents ∧
      ReadOrder.Related Prod.swap
        ((ReadOrder.pair (EffectM.ofOp (StateEval.evalExpr dialect policy environment left))
          (EffectM.ofOp (StateEval.evalExpr dialect policy environment right))).run state)
        ((ReadOrder.pair (EffectM.ofOp (StateEval.evalExpr dialect policy environment right))
          (EffectM.ofOp (StateEval.evalExpr dialect policy environment left))).run state) := by
  obtain ⟨leftValue, leftState, leftEvents, leftRun, leftResult⟩ := (wp_iff _ _ _).mp leftCondition
  obtain ⟨rightValue, rightState, rightEvents, rightRun, rightResult⟩ := (wp_iff _ _ _).mp rightCondition
  have leftSame : leftState = state := by
    simpa only [leftRun] using StateEval.evalExpr_preserves_state dialect policy environment left state
  have rightSame : rightState = state := by
    simpa only [rightRun] using StateEval.evalExpr_preserves_state dialect policy environment right state
  subst leftState
  subst rightState
  have leftReads : Reads leftEvents := by
    simpa only [leftRun] using evalExpr_reads dialect policy environment left state
  have rightReads : Reads rightEvents := by
    simpa only [rightRun] using evalExpr_reads dialect policy environment right state
  have diamond := ReadOrder.commute_success
    (EffectM.ofOp (StateEval.evalExpr dialect policy environment left))
    (EffectM.ofOp (StateEval.evalExpr dialect policy environment right))
    state leftValue rightValue leftEvents rightEvents leftRun rightRun
  exact ⟨leftValue, rightValue, leftEvents, rightEvents, leftRun, rightRun,
    leftResult, rightResult, leftReads, rightReads, diamond.2.2⟩

end EDSL.Source.Objects.ExpressionReadOrder
