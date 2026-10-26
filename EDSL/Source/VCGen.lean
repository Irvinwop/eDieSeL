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

/-- Structural verification-condition generation for the finite pure fragment.
Arithmetic leaves use the shared evaluator's primitive operations, rather than
an alternate language semantics. Kernel reduction exposes their range and
nonzero-divisor obligations. Select requires its condition and chosen arm only;
the program VC separately checks static coverage of all syntax. There is no
execution-fuel or solver premise. -/
def vcExpr {target : Target} {parameters : List IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters) :
    {ty : IntType} → Expr target parameters ty → (Value target ty → Prop) → Prop
  | _, .literal value, post => post value
  | _, .param index, post => post (inputs.get index)
  | _, .promote operand, post =>
      vcExpr policy inputs operand fun value =>
        post (IntegerPromotions.promoteValue value)
  | _, .convert destination operand, post =>
      vcExpr policy inputs operand fun value =>
        (convertValue policy target _ destination value).requires post
  | _, .uadd left right, post =>
      vcExpr policy inputs left fun x => vcExpr policy inputs right fun y =>
        (unsignedAdd target x y).requires post
  | _, .sadd left right, post =>
      vcExpr policy inputs left fun x => vcExpr policy inputs right fun y =>
        (signedAdd target x y).requires post
  | _, .usub left right, post =>
      vcExpr policy inputs left fun x => vcExpr policy inputs right fun y =>
        (unsignedSub target x y).requires post
  | _, .ssub left right, post =>
      vcExpr policy inputs left fun x => vcExpr policy inputs right fun y =>
        (signedSub target x y).requires post
  | _, .umul left right, post =>
      vcExpr policy inputs left fun x => vcExpr policy inputs right fun y =>
        (unsignedMul target x y).requires post
  | _, .smul left right, post =>
      vcExpr policy inputs left fun x => vcExpr policy inputs right fun y =>
        (signedMul target x y).requires post
  | _, .udiv left right, post =>
      vcExpr policy inputs left fun x => vcExpr policy inputs right fun y =>
        (unsignedDiv target x y).requires post
  | _, .sdiv left right, post =>
      vcExpr policy inputs left fun x => vcExpr policy inputs right fun y =>
        (signedDiv target x y).requires post
  | _, .urem left right, post =>
      vcExpr policy inputs left fun x => vcExpr policy inputs right fun y =>
        (unsignedRem target x y).requires post
  | _, .srem left right, post =>
      vcExpr policy inputs left fun x => vcExpr policy inputs right fun y =>
        (signedRem target x y).requires post
  | _, .compare operation _ left right, post =>
      vcExpr policy inputs left fun x => vcExpr policy inputs right fun y =>
        post (compareValues operation x y)
  | _, .select condition onTrue onFalse, post =>
      vcExpr policy inputs condition fun value =>
        if value.toInt = 0 then vcExpr policy inputs onFalse post
        else vcExpr policy inputs onTrue post
  | _, .unsupported _, _ => False

/-- The generated condition is exact for this finite grammar. Its soundness
includes actual defined execution; it cannot merely exclude an error by
omitting the corresponding behavior. -/
theorem vcExpr_iff {target : Target} {parameters : List IntType} {ty : IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (expression : Expr target parameters ty)
    (post : Value target ty → Prop) :
    vcExpr policy inputs expression post ↔ (evalExpr policy inputs expression).requires post := by
  unfold evalExpr ExpressionCore.evalOutcome
  induction expression <;>
    simp_all only [vcExpr, ExpressionCore.evalCore, bind, pure,
      Outcome.requires_andThen, Outcome.requires_defined,
      Outcome.requires_unsupported, Outcome.requires_ite]

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
