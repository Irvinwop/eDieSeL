/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.VCGen

set_option autoImplicit false

namespace EDSL.Source

/-! Named structural equations for the actual pure `vcExpr` specialization of
the shared expression/place engine. These are proof rules, not another syntax
traversal. No rule is registered in the default simp set. Primitive outcomes
retain their UB and unsupported obligations; selection demands only one arm.
-/

variable {target : Target} {parameters : List IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)

theorem vcExpr_literal {ty : IntType} (value : Value target ty)
    (post : Value target ty → Prop) :
    vcExpr policy inputs (.literal value) post = post value := rfl

/-- Works for any typed parameter, without exposing its scalar-index map. -/
theorem vcExpr_param {ty : IntType} (index : Param parameters ty)
    (post : Value target ty → Prop) :
    vcExpr policy inputs (.param index) post = post (inputs.get index) := by
  change (ExpressionCore.integerResolver (M := VerificationCarrier.Predicate) (target := target)
    (fun index post => post (inputs.get index)) index.toIndex) post = _
  rw [ExpressionCore.integerResolver_index, Param.ofIndex_toIndex]

theorem vcExpr_promote {source : IntType} (operand : Expr target parameters source)
    (post : Value target (promotedType target source).asIntType → Prop) :
    vcExpr policy inputs (.promote operand) post =
      vcExpr policy inputs operand (fun value =>
        post (IntegerPromotions.promoteValue value)) := rfl

theorem vcExpr_convert (destination : IntType) {source : IntType}
    (operand : Expr target parameters source) (post : Value target destination → Prop) :
    vcExpr policy inputs (.convert destination operand) post =
      vcExpr policy inputs operand (fun value =>
        (convertValue policy target source destination value).requires post) := rfl

theorem vcExpr_uadd (left right : Expr target parameters .uint)
    (post : Value target .uint → Prop) :
    vcExpr policy inputs (.uadd left right) post =
      vcExpr policy inputs left (fun x => vcExpr policy inputs right (fun y =>
        (unsignedAdd target x y).requires post)) := rfl

theorem vcExpr_sadd (left right : Expr target parameters .sint)
    (post : Value target .sint → Prop) :
    vcExpr policy inputs (.sadd left right) post =
      vcExpr policy inputs left (fun x => vcExpr policy inputs right (fun y =>
        (signedAdd target x y).requires post)) := rfl

theorem vcExpr_usub (left right : Expr target parameters .uint)
    (post : Value target .uint → Prop) :
    vcExpr policy inputs (.usub left right) post =
      vcExpr policy inputs left (fun x => vcExpr policy inputs right (fun y =>
        (unsignedSub target x y).requires post)) := rfl

theorem vcExpr_ssub (left right : Expr target parameters .sint)
    (post : Value target .sint → Prop) :
    vcExpr policy inputs (.ssub left right) post =
      vcExpr policy inputs left (fun x => vcExpr policy inputs right (fun y =>
        (signedSub target x y).requires post)) := rfl

theorem vcExpr_umul (left right : Expr target parameters .uint)
    (post : Value target .uint → Prop) :
    vcExpr policy inputs (.umul left right) post =
      vcExpr policy inputs left (fun x => vcExpr policy inputs right (fun y =>
        (unsignedMul target x y).requires post)) := rfl

theorem vcExpr_smul (left right : Expr target parameters .sint)
    (post : Value target .sint → Prop) :
    vcExpr policy inputs (.smul left right) post =
      vcExpr policy inputs left (fun x => vcExpr policy inputs right (fun y =>
        (signedMul target x y).requires post)) := rfl

theorem vcExpr_udiv (left right : Expr target parameters .uint)
    (post : Value target .uint → Prop) :
    vcExpr policy inputs (.udiv left right) post =
      vcExpr policy inputs left (fun x => vcExpr policy inputs right (fun y =>
        (unsignedDiv target x y).requires post)) := rfl

theorem vcExpr_sdiv (left right : Expr target parameters .sint)
    (post : Value target .sint → Prop) :
    vcExpr policy inputs (.sdiv left right) post =
      vcExpr policy inputs left (fun x => vcExpr policy inputs right (fun y =>
        (signedDiv target x y).requires post)) := rfl

theorem vcExpr_urem (left right : Expr target parameters .uint)
    (post : Value target .uint → Prop) :
    vcExpr policy inputs (.urem left right) post =
      vcExpr policy inputs left (fun x => vcExpr policy inputs right (fun y =>
        (unsignedRem target x y).requires post)) := rfl

theorem vcExpr_srem (left right : Expr target parameters .sint)
    (post : Value target .sint → Prop) :
    vcExpr policy inputs (.srem left right) post =
      vcExpr policy inputs left (fun x => vcExpr policy inputs right (fun y =>
        (signedRem target x y).requires post)) := rfl

theorem vcExpr_compare (operation : ComparisonOp) (kind : ArithmeticType)
    (left right : Expr target parameters kind.asIntType)
    (post : Value target (.small .boolean) → Prop) :
    vcExpr policy inputs (.compare operation kind left right) post =
      vcExpr policy inputs left (fun x => vcExpr policy inputs right (fun y =>
        post (compareValues operation x y))) := rfl

theorem vcExpr_select {ty : IntType}
    (condition : Expr target parameters (.small .boolean))
    (onTrue onFalse : Expr target parameters ty) (post : Value target ty → Prop) :
    vcExpr policy inputs (.select condition onTrue onFalse) post =
      vcExpr policy inputs condition (fun flag =>
        if flag.toInt = 0 then vcExpr policy inputs onFalse post
        else vcExpr policy inputs onTrue post) := by
  change vcExpr policy inputs condition (fun flag =>
    (if flag.toInt = 0 then vcExpr policy inputs onFalse
      else vcExpr policy inputs onTrue) post) = _
  apply congrArg (vcExpr policy inputs condition)
  funext flag
  split <;> rfl

theorem vcExpr_unsupported {ty : IntType} (feature : UnsupportedFeature)
    (post : Value target ty → Prop) :
    vcExpr policy inputs (.unsupported feature) post = False := rfl

end EDSL.Source
