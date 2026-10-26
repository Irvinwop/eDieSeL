/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Eval

set_option autoImplicit false

namespace EDSL.Source

/-- Common type after integer promotion. Only the full int/unsigned-int pair
is present at this stage; larger integer ranks remain unsupported. -/
def ArithmeticType.common : ArithmeticType → ArithmeticType → ArithmeticType
  | .sint, .sint => .sint
  | _, _ => .uint

def commonType (target : Target) (left right : IntType) : IntType :=
  ((promotedType target left).common (promotedType target right)).asIntType

/-- Addition of already promoted operands, normalized to shared conversions
and arithmetic primitives. -/
def Expr.promotedAdd {target : Target} {parameters : List IntType}
    {leftKind rightKind : ArithmeticType}
    (left : Expr target parameters leftKind.asIntType)
    (right : Expr target parameters rightKind.asIntType) :
    Expr target parameters (leftKind.common rightKind).asIntType :=
  match leftKind, rightKind with
  | .sint, .sint => .sadd (.convert .sint left) (.convert .sint right)
  | .sint, .uint => .uadd (.convert .uint left) (.convert .uint right)
  | .uint, .sint => .uadd (.convert .uint left) (.convert .uint right)
  | .uint, .uint => .uadd (.convert .uint left) (.convert .uint right)

def Expr.promotedDiv {target : Target} {parameters : List IntType}
    {leftKind rightKind : ArithmeticType}
    (left : Expr target parameters leftKind.asIntType)
    (right : Expr target parameters rightKind.asIntType) :
    Expr target parameters (leftKind.common rightKind).asIntType :=
  match leftKind, rightKind with
  | .sint, .sint => .sdiv (.convert .sint left) (.convert .sint right)
  | .sint, .uint => .udiv (.convert .uint left) (.convert .uint right)
  | .uint, .sint => .udiv (.convert .uint left) (.convert .uint right)
  | .uint, .uint => .udiv (.convert .uint left) (.convert .uint right)

/-- Promote both operands before selecting the common arithmetic type. -/
def Expr.usualAdd {target : Target} {parameters : List IntType}
    {leftType rightType : IntType}
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    Expr target parameters (commonType target leftType rightType) :=
  Expr.promotedAdd (leftKind := promotedType target leftType)
    (rightKind := promotedType target rightType) (.promote left) (.promote right)

def Expr.usualDiv {target : Target} {parameters : List IntType}
    {leftType rightType : IntType}
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    Expr target parameters (commonType target leftType rightType) :=
  Expr.promotedDiv (leftKind := promotedType target leftType)
    (rightKind := promotedType target rightType) (.promote left) (.promote right)

def commonAdd (target : Target) (kind : ArithmeticType) :
    Value target kind.asIntType → Value target kind.asIntType →
      Outcome (Value target kind.asIntType) :=
  match kind with
  | .uint => unsignedAdd target
  | .sint => signedAdd target

def commonDiv (target : Target) (kind : ArithmeticType) :
    Value target kind.asIntType → Value target kind.asIntType →
      Outcome (Value target kind.asIntType) :=
  match kind with
  | .uint => unsignedDiv target
  | .sint => signedDiv target

theorem eval_promotedAdd {target : Target} {parameters : List IntType}
    {leftKind rightKind : ArithmeticType} (policy : IntegerConversionPolicy)
    (inputs : Inputs target parameters)
    (left : Expr target parameters leftKind.asIntType)
    (right : Expr target parameters rightKind.asIntType) :
    evalExpr policy inputs (left.promotedAdd right) =
      ((evalExpr policy inputs left).andThen fun value =>
        convertValue policy target leftKind.asIntType
          (leftKind.common rightKind).asIntType value).andThen
      fun x => ((evalExpr policy inputs right).andThen fun value =>
        convertValue policy target rightKind.asIntType
          (leftKind.common rightKind).asIntType value).andThen
      fun y => commonAdd target (leftKind.common rightKind) x y := by
  cases leftKind <;> cases rightKind <;> rfl

theorem eval_promotedDiv {target : Target} {parameters : List IntType}
    {leftKind rightKind : ArithmeticType} (policy : IntegerConversionPolicy)
    (inputs : Inputs target parameters)
    (left : Expr target parameters leftKind.asIntType)
    (right : Expr target parameters rightKind.asIntType) :
    evalExpr policy inputs (left.promotedDiv right) =
      ((evalExpr policy inputs left).andThen fun value =>
        convertValue policy target leftKind.asIntType
          (leftKind.common rightKind).asIntType value).andThen
      fun x => ((evalExpr policy inputs right).andThen fun value =>
        convertValue policy target rightKind.asIntType
          (leftKind.common rightKind).asIntType value).andThen
      fun y => commonDiv target (leftKind.common rightKind) x y := by
  cases leftKind <;> cases rightKind <;> rfl

/-- Normalization uses the same primitive semantics after explicit promotion
and common-type conversion; operand failures are retained. -/
theorem eval_usualAdd {target : Target} {parameters : List IntType}
    {leftType rightType : IntType} (policy : IntegerConversionPolicy)
    (inputs : Inputs target parameters)
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    evalExpr policy inputs (left.usualAdd right) =
      ((evalExpr policy inputs (.promote left)).andThen fun value =>
        convertValue policy target (promotedType target leftType).asIntType
          (commonType target leftType rightType) value).andThen
      fun x => ((evalExpr policy inputs (.promote right)).andThen fun value =>
        convertValue policy target (promotedType target rightType).asIntType
          (commonType target leftType rightType) value).andThen
      fun y => commonAdd target
        ((promotedType target leftType).common (promotedType target rightType)) x y := by
  exact eval_promotedAdd (leftKind := promotedType target leftType)
    (rightKind := promotedType target rightType) policy inputs (.promote left) (.promote right)

theorem eval_usualDiv {target : Target} {parameters : List IntType}
    {leftType rightType : IntType} (policy : IntegerConversionPolicy)
    (inputs : Inputs target parameters)
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    evalExpr policy inputs (left.usualDiv right) =
      ((evalExpr policy inputs (.promote left)).andThen fun value =>
        convertValue policy target (promotedType target leftType).asIntType
          (commonType target leftType rightType) value).andThen
      fun x => ((evalExpr policy inputs (.promote right)).andThen fun value =>
        convertValue policy target (promotedType target rightType).asIntType
          (commonType target leftType rightType) value).andThen
      fun y => commonDiv target
        ((promotedType target leftType).common (promotedType target rightType)) x y := by
  exact eval_promotedDiv (leftKind := promotedType target leftType)
    (rightKind := promotedType target rightType) policy inputs (.promote left) (.promote right)

end EDSL.Source
