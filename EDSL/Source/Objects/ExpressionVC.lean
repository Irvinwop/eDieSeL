/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.ObjectWP
import EDSL.Source.Objects.StateEval

set_option autoImplicit false

namespace EDSL.Source.Objects.ExpressionVC

open StateSyntax Protocol

/-! Expression verification through the same ExpressionCore.evalCore traversal
as StateEval.evalExpr. Only scalar outcomes and typed object lookup are reflected
here; there is no second expression interpreter. The success conditions for a
read are independent of dialect, but exactness holds for each actual dialect.

The carrier keeps complete intermediate states and actual event concatenation.
The public postcondition also retains the original prestate. Dynamic selection
is lazy; whole-syntax unsupported coverage remains a separate caller obligation.
These are internal full-integral-object rules, not native operand sequencing,
interference, volatile/atomic, allocation, cleanup, OS or compiler claims. -/

/-- A continuation observes the returned value, complete final state and trace.
The fixed state indices are explicit so this is a Type → Type carrier. -/
abbrev M (target : Target) (stateParameters : List IntType) (Environment α : Type) :=
  (α → State target stateParameters Environment → List Event → Prop) →
    State target stateParameters Environment → Prop

variable {target : Target} {stateParameters : List IntType} {Environment α β : Type}

namespace M

def pure (value : α) : M target stateParameters Environment α :=
  fun post state => post value state []

/-- The suffix runs in the actual intermediate state, and its observations
follow the prefix. No state-preservation premise is built into this carrier. -/
def bind (first : M target stateParameters Environment α)
    (next : α → M target stateParameters Environment β) : M target stateParameters Environment β :=
  fun post initial => first (fun value middle earlierEvents =>
    next value (fun result final suffix => post result final (earlierEvents ++ suffix)) middle) initial

instance : Monad (M target stateParameters Environment) where
  pure := M.pure
  bind := M.bind

end M

/-- Map a complete actual operation to its exact success condition. Its original
prestate is deliberately ignored here; vcExpr captures it outside the carrier. -/
def ofEffect (operation : EffectM target stateParameters Environment α) :
    M target stateParameters Environment α :=
  fun post => WP operation.run (fun _ value final events => post value final events)

theorem ofEffect_pure (value : α) :
    ofEffect (pure value : EffectM target stateParameters Environment α) = pure value := by
  funext post initial
  exact propext (wp_pure value (fun _ result final events => post result final events) initial)

/-- wp_bind supplies the original-prestate and actual-trace composition law;
function/proposition extensionality turns it into a carrier equation. -/
theorem ofEffect_bind (first : EffectM target stateParameters Environment α)
    (next : α → EffectM target stateParameters Environment β) :
    ofEffect (first >>= next) = (ofEffect first >>= fun value => ofEffect (next value)) := by
  funext post initial
  exact propext (wp_bind first.run (fun value => (next value).run)
    (fun _ result final events => post result final events) initial)

/-- Reflect only a scalar leaf. Scalar UB and unsupported coverage cannot
establish any postcondition, including True. Their actual Stop identities are
retained by EffectM.liftScalar, to which this condition is proved exact. -/
def liftScalar : Outcome α → M target stateParameters Environment α
  | .defined value => pure value
  | .undefined _ => fun _ _ => False
  | .unsupported _ => fun _ _ => False

@[simp] theorem liftScalar_defined (value : α)
    (post : α → State target stateParameters Environment → List Event → Prop)
    (state : State target stateParameters Environment) :
    liftScalar (.defined value) post state ↔ post value state [] := Iff.rfl

@[simp] theorem liftScalar_undefined (reason : UBReason)
    (post : α → State target stateParameters Environment → List Event → Prop)
    (state : State target stateParameters Environment) :
    liftScalar (.undefined reason) post state ↔ False := Iff.rfl

@[simp] theorem liftScalar_unsupported (feature : UnsupportedFeature)
    (post : α → State target stateParameters Environment → List Event → Prop)
    (state : State target stateParameters Environment) :
    liftScalar (.unsupported feature) post state ↔ False := Iff.rfl

theorem ofEffect_liftScalar (outcome : Outcome α) :
    ofEffect (EffectM.liftScalar outcome : EffectM target stateParameters Environment α) =
      liftScalar outcome := by
  funext post state
  cases outcome <;> rfl

/-- Independent registry, lifetime, ownership, authority and stored-value data,
with the exact unchanged state and single demanded read observation. -/
def read {kind : ArithmeticType} (reference : LValue kind) :
    M target stateParameters Environment (Value target kind.asIntType) :=
  fun post state => ∃ value,
    CanLoad state reference value ∧ post value state [.read reference.id kind value.toInt]

theorem ofEffect_load {kind : ArithmeticType} (dialect : Dialect) (reference : LValue kind) :
    ofEffect (EffectM.ofOp (load dialect reference) : EffectM target stateParameters Environment _) =
      read reference := by
  funext post state
  exact propext (ObjectWP.wp_load dialect reference
    (fun _ value final events => post value final events) state)

/-- Typed source variables resolve to current objects, never State.inputs.
This traverses only the binding environment, not expression syntax. -/
def resolve {context : List ArithmeticType} (environment : Env context) :
    {type : IntType} → Param (VariableTypes context) type →
      M target stateParameters Environment (Value target type) :=
  match environment with
  | .nil => fun index => nomatch index
  | .cons reference tail => fun index =>
      match index with
      | .here => read reference
      | .there index => resolve tail index

theorem ofEffect_resolve {context : List ArithmeticType} {type : IntType}
    (dialect : Dialect) (environment : Env context) (index : Param (VariableTypes context) type) :
    ofEffect (StateEval.resolve dialect environment index :
      EffectM target stateParameters Environment _) = resolve environment index := by
  induction environment with
  | nil => cases index
  | cons reference tail ih =>
      cases index with
      | here => exact ofEffect_load dialect reference
      | there index => exact ih index

theorem resolve_var {context : List ArithmeticType} {kind : ArithmeticType}
    (environment : Env context) (index : Vars context kind) :
    (resolve environment index : M target stateParameters Environment _) =
      read (environment.get index) := by
  rw [← ofEffect_resolve .gnuC23, StateEval.resolve_var, ofEffect_load]

/-- Specialize the shared traversal to reflected scalar/read leaves. Dialect
does not affect successful-read obligations; the theorem below quantifies over
each dialect's actual operation, with every distinct Stop still excluded. -/
def evalExpr {context : List ArithmeticType} {type : IntType}
    (policy : IntegerConversionPolicy) (environment : Env context)
    (expression : RHS target context type) :
    M target stateParameters Environment (Value target type) :=
  ExpressionCore.evalCore (M := M target stateParameters Environment) policy
    (fun outcome => liftScalar outcome) (resolve environment) expression

/-- Equality of entire predicate transformers, obtained by transporting the
shared traversal through the proved carrier/scalar/resolver equations. -/
theorem evalExpr_eq_wp {context : List ArithmeticType} {type : IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (environment : Env context)
    (expression : RHS target context type) :
    (evalExpr policy environment expression : M target stateParameters Environment _) =
      fun post initial => WP (StateEval.evalExpr dialect policy environment expression)
        (fun _ value final events => post value final events) initial := by
  exact (ExpressionCore.evalCore_map
    (M := EffectM target stateParameters Environment) (N := M target stateParameters Environment)
    policy ofEffect (fun value => ofEffect_pure value)
    (fun first next => ofEffect_bind first next)
    (fun outcome => EffectM.liftScalar outcome) (fun outcome => liftScalar outcome)
    (StateEval.resolve dialect environment) (resolve environment)
    (fun outcome => ofEffect_liftScalar outcome)
    (fun index => ofEffect_resolve dialect environment index) expression).symm

/-- Capture the original initial state once, before any intermediate binds. -/
def vcExpr {context : List ArithmeticType} {type : IntType}
    (policy : IntegerConversionPolicy) (environment : Env context)
    (expression : RHS target context type)
    (post : Post target stateParameters Environment (Value target type))
    (initial : State target stateParameters Environment) : Prop :=
  evalExpr policy environment expression (post initial) initial

theorem vcExpr_iff_wp {context : List ArithmeticType} {type : IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (environment : Env context)
    (expression : RHS target context type)
    (post : Post target stateParameters Environment (Value target type))
    (initial : State target stateParameters Environment) :
    vcExpr policy environment expression post initial ↔
      WP (StateEval.evalExpr dialect policy environment expression) post initial := by
  unfold vcExpr
  rw [evalExpr_eq_wp dialect]
  rfl

/-- Exact actual success, complete final state and observations. No success or
definedness of the target computation is assumed as an entry condition. -/
theorem vcExpr_iff {context : List ArithmeticType} {type : IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (environment : Env context)
    (expression : RHS target context type)
    (post : Post target stateParameters Environment (Value target type))
    (initial : State target stateParameters Environment) :
    vcExpr policy environment expression post initial ↔ ∃ value final events,
      StateEval.evalExpr dialect policy environment expression initial = (.ok value, final, events) ∧
        post initial value final events := by
  rw [vcExpr_iff_wp dialect, wp_iff]

@[simp] theorem vcExpr_literal {context : List ArithmeticType} {type : IntType}
    (policy : IntegerConversionPolicy) (environment : Env context) (value : Value target type)
    (post : Post target stateParameters Environment (Value target type))
    (initial : State target stateParameters Environment) :
    vcExpr policy environment (.literal value) post initial ↔ post initial value initial [] := Iff.rfl

theorem vcExpr_var {context : List ArithmeticType} {kind : ArithmeticType}
    (policy : IntegerConversionPolicy) (environment : Env context) (index : Vars context kind)
    (post : Post target stateParameters Environment (Value target kind.asIntType))
    (initial : State target stateParameters Environment) :
    vcExpr policy environment (.param index) post initial ↔ ∃ value,
      CanLoad initial (environment.get index) value ∧
        post initial value initial [.read (environment.get index).id kind value.toInt] := by
  simp only [vcExpr, evalExpr, ExpressionCore.evalCore, ExpressionCore.evalEngine,
    ExpressionCore.integerResolver_index, Param.ofIndex_toIndex]
  change resolve environment index (post initial) initial ↔ _
  rw [resolve_var]
  rfl

/-- The branch operations stay inside the condition's continuation, so an
undemanded arm contributes neither read conditions nor events. -/
theorem evalExpr_select {context : List ArithmeticType} {type : IntType}
    (policy : IntegerConversionPolicy) (environment : Env context)
    (condition : RHS target context (.small .boolean)) (yes no : RHS target context type) :
    (evalExpr policy environment (.select condition yes no) : M target stateParameters Environment _) =
      (evalExpr policy environment condition >>= fun value =>
        if value.toInt = 0 then evalExpr policy environment no
        else evalExpr policy environment yes) := rfl

theorem verifies_iff_vcExpr {context : List ArithmeticType} {type : IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (environment : Env context)
    (expression : RHS target context type)
    (admitted : State target stateParameters Environment → Prop)
    (post : Post target stateParameters Environment (Value target type)) :
    Protocol.Verifies (StateEval.evalExpr dialect policy environment expression) admitted post ↔
      ∀ initial, admitted initial → vcExpr policy environment expression post initial := by
  rw [verifies_iff_wp]
  simp only [vcExpr_iff_wp dialect]

/-- Failure exclusion is quantified over Stop itself: scalar/object UB, C++
erroneous behavior, denials, binding faults and unsupported syntax stay distinct.
Any already accepted observations on an actual failure remain in its result. -/
theorem no_failure_of_vcExpr {context : List ArithmeticType} {type : IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (environment : Env context)
    (expression : RHS target context type)
    (post : Post target stateParameters Environment (Value target type))
    (initial : State target stateParameters Environment)
    (condition : vcExpr policy environment expression post initial)
    (reason : Stop) (final : State target stateParameters Environment) (events : List Event) :
    StateEval.evalExpr dialect policy environment expression initial ≠ (.error reason, final, events) := by
  obtain ⟨value, actualFinal, actualEvents, execution, _⟩ :=
    (vcExpr_iff dialect policy environment expression post initial).mp condition
  rw [execution]
  intro impossible
  cases impossible

end EDSL.Source.Objects.ExpressionVC
