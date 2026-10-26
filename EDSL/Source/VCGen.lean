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
nonzero-divisor obligations. There is no execution-fuel or solver premise. -/
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
  | _, .udiv left right, post =>
      vcExpr policy inputs left fun x => vcExpr policy inputs right fun y =>
        (unsignedDiv target x y).requires post
  | _, .sdiv left right, post =>
      vcExpr policy inputs left fun x => vcExpr policy inputs right fun y =>
        (signedDiv target x y).requires post
  | _, .unsupported _, _ => False

/-- The generated condition is exact for this finite grammar. Its soundness
includes actual defined execution; it cannot merely exclude an error by
omitting the corresponding behavior. -/
theorem vcExpr_iff {target : Target} {parameters : List IntType} {ty : IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (expression : Expr target parameters ty)
    (post : Value target ty → Prop) :
    vcExpr policy inputs expression post ↔ (evalExpr policy inputs expression).requires post := by
  induction expression with
  | literal value => rfl
  | param index => rfl
  | promote operand operandIH =>
      simp only [vcExpr, evalExpr]
      rw [Outcome.requires_andThen]
      exact operandIH _
  | convert destination operand operandIH =>
      simp only [vcExpr, evalExpr, Outcome.requires_andThen]
      exact operandIH _
  | uadd left right leftIH rightIH =>
      simp only [vcExpr, evalExpr, Outcome.requires_andThen]
      rw [leftIH]
      simp only [rightIH]
  | sadd left right leftIH rightIH =>
      simp only [vcExpr, evalExpr, Outcome.requires_andThen]
      rw [leftIH]
      simp only [rightIH]
  | udiv left right leftIH rightIH =>
      simp only [vcExpr, evalExpr, Outcome.requires_andThen]
      rw [leftIH]
      simp only [rightIH]
  | sdiv left right leftIH rightIH =>
      simp only [vcExpr, evalExpr, Outcome.requires_andThen]
      rw [leftIH]
      simp only [rightIH]
  | unsupported feature => rfl

def VC {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result)
    (admitted : Inputs target parameters → Prop)
    (post : Inputs target parameters → Value target result → Prop) : Prop :=
  ∀ inputs, admitted inputs → vcExpr program.conversions inputs program.body (post inputs)

theorem vc_iff_verifies {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result)
    (admitted : Inputs target parameters → Prop)
    (post : Inputs target parameters → Value target result → Prop) :
    VC program admitted post ↔ Verifies program admitted post := by
  simp only [VC, Verifies, vcExpr_iff, Outcome.requires_iff, eval]

theorem certificate_of_vc {target : Target} {parameters : List IntType} {result : IntType}
    {program : Program target parameters result}
    {admitted : Inputs target parameters → Prop}
    {post : Inputs target parameters → Value target result → Prop}
    (useful : ∃ inputs, admitted inputs) (condition : VC program admitted post) :
    Certificate program admitted post :=
  ⟨useful, (vc_iff_verifies program admitted post).mp condition⟩

end EDSL.Source
