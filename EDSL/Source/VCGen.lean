/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Certificate

set_option autoImplicit false

namespace EDSL.Source

/-- The local obligation for a primitive's actual outcome. UB and unsupported
coverage cannot establish a postcondition, even when the postcondition is True. -/
def Outcome.requires {α : Type} (outcome : Outcome α) (post : α → Prop) : Prop :=
  match outcome with
  | .defined value => post value
  | .undefined _ => False
  | .unsupported _ => False

theorem Outcome.requires_defined {α : Type} (value : α) (post : α → Prop) :
    (Outcome.defined value).requires post ↔ post value := Iff.rfl

theorem Outcome.requires_undefined {α : Type} (reason : UBReason) (post : α → Prop) :
    (Outcome.undefined reason : Outcome α).requires post ↔ False := Iff.rfl

theorem Outcome.requires_unsupported {α : Type} (feature : UnsupportedFeature) (post : α → Prop) :
    (Outcome.unsupported feature : Outcome α).requires post ↔ False := Iff.rfl

theorem Outcome.requires_ite {α : Type} (condition : Prop) [Decidable condition]
    (yes no : Outcome α) (post : α → Prop) :
    (if condition then yes else no).requires post ↔
      if condition then yes.requires post else no.requires post := by
  split <;> rfl

theorem Outcome.requires_iff {α : Type} (outcome : Outcome α) (post : α → Prop) :
    outcome.requires post ↔ ∃ value, outcome = .defined value ∧ post value := by
  cases outcome <;> simp [requires]

theorem Outcome.requires_andThen {α β : Type} (outcome : Outcome α)
    (next : α → Outcome β) (post : β → Prop) :
    (outcome.andThen next).requires post ↔
      outcome.requires (fun value => (next value).requires post) := by
  cases outcome <;> rfl

namespace VerificationCarrier

/-- Predicates on results are computed through the same traversal as execution. -/
abbrev Predicate (α : Type) : Type := (α → Prop) → Prop

instance : Monad Predicate where
  pure value post := post value
  bind first next post := first (fun value => next value post)

@[instance_reducible] def outcomeMonad : Monad Outcome where
  pure := Outcome.defined
  bind := Outcome.andThen

attribute [local instance] outcomeMonad

theorem requires_pure {α : Type} (value : α) :
    (pure value : Outcome α).requires = (pure value : Predicate α) := rfl

theorem requires_bind {α β : Type} (first : Outcome α) (next : α → Outcome β) :
    (first >>= next).requires =
      (first.requires >>= fun value => (next value).requires : Predicate β) := by
  funext post
  exact propext (Outcome.requires_andThen first next post)

end VerificationCarrier

attribute [local instance] VerificationCarrier.outcomeMonad

/-- The logical carrier specializes the one shared expression traversal.
Primitive UB and unsupported outcomes require False; branch demand is exactly
that of execution. Whole-tree source coverage remains the separate public VC
preflight. No second arithmetic syntax traversal or solver premise is used. -/
def vcExpr {target : Target} {parameters : List IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters) :
    {ty : IntType} → Expr target parameters ty → (Value target ty → Prop) → Prop :=
  fun {_} expression post =>
    ExpressionCore.evalCore (M := VerificationCarrier.Predicate) policy
      (fun outcome => outcome.requires) (fun index post => post (inputs.get index))
      expression post

/-- Exactness follows by mapping complete computations of the shared core,
including lazy selection and failures, into the logical carrier. -/
theorem vcExpr_iff {target : Target} {parameters : List IntType} {ty : IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (expression : Expr target parameters ty)
    (post : Value target ty → Prop) :
    vcExpr policy inputs expression post ↔ (evalExpr policy inputs expression).requires post := by
  have mapped := ExpressionCore.evalCore_map
    (M := Outcome) (N := VerificationCarrier.Predicate) policy
    (fun outcome => outcome.requires)
    (fun value => VerificationCarrier.requires_pure value)
    (fun first next => VerificationCarrier.requires_bind first next)
    (fun outcome => outcome) (fun outcome => outcome.requires)
    (fun index => Outcome.defined (inputs.get index))
    (fun index post => post (inputs.get index))
    (fun _ => rfl) (fun _ => rfl) expression
  exact Iff.of_eq (congrFun mapped post).symm

/-- Each admitted input requires full static model coverage followed by the raw
expression VC. An empty admission remains vacuous, as for `Verifies`; inhabited
admission is required separately by `Certificate`. -/
def VC {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result)
    (admitted : Inputs target parameters → Prop)
    (post : Inputs target parameters → Value target result → Prop) : Prop :=
  ∀ inputs, admitted inputs →
    match program.body.firstUnsupported with
    | none => vcExpr program.conversions inputs program.body (post inputs)
    | some _ => False

theorem vc_iff_verifies {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result)
    (admitted : Inputs target parameters → Prop)
    (post : Inputs target parameters → Value target result → Prop) :
    VC program admitted post ↔ Verifies program admitted post := by
  cases coverage : program.body.firstUnsupported <;>
    simp [VC, Verifies, eval, coverage, vcExpr_iff, Outcome.requires_iff]

theorem certificate_of_vc {target : Target} {parameters : List IntType} {result : IntType}
    {program : Program target parameters result}
    {admitted : Inputs target parameters → Prop}
    {post : Inputs target parameters → Value target result → Prop}
    (useful : ∃ inputs, admitted inputs) (condition : VC program admitted post) :
    Certificate program admitted post :=
  ⟨useful, (vc_iff_verifies program admitted post).mp condition⟩

end EDSL.Source
