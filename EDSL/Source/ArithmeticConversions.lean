/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Eval

set_option autoImplicit false

namespace EDSL.Source

/-- Common type after integer promotion within the admitted int hierarchy. -/
def ArithmeticType.common : ArithmeticType → ArithmeticType → ArithmeticType
  | .sint, .sint => .sint
  | _, _ => .uint

def commonType (target : Target) (left right : IntType) : IntType :=
  ((promotedType target left).common (promotedType target right)).asIntType

/-- Operations normalized by one shared promotion/common-type construction. -/
inductive ArithmeticOp where
  | add
  | sub
  | mul
  | div
  | rem
  deriving DecidableEq, Repr

/-- Build a same-type arithmetic node; no operand is evaluated by this helper. -/
def Expr.primitiveBinary {target : Target} {parameters : List IntType}
    (operation : ArithmeticOp) (kind : ArithmeticType)
    (left right : Expr target parameters kind.asIntType) :
    Expr target parameters kind.asIntType :=
  match kind, operation with
  | .uint, .add => .uadd left right
  | .uint, .sub => .usub left right
  | .uint, .mul => .umul left right
  | .uint, .div => .udiv left right
  | .uint, .rem => .urem left right
  | .sint, .add => .sadd left right
  | .sint, .sub => .ssub left right
  | .sint, .mul => .smul left right
  | .sint, .div => .sdiv left right
  | .sint, .rem => .srem left right

/-- Normalize already promoted operands through the same explicit conversions. -/
def Expr.promotedBinary {target : Target} {parameters : List IntType}
    {leftKind rightKind : ArithmeticType} (operation : ArithmeticOp)
    (left : Expr target parameters leftKind.asIntType)
    (right : Expr target parameters rightKind.asIntType) :
    Expr target parameters (leftKind.common rightKind).asIntType :=
  Expr.primitiveBinary operation (leftKind.common rightKind)
    (.convert (leftKind.common rightKind).asIntType left)
    (.convert (leftKind.common rightKind).asIntType right)

/-- Integer promotion precedes common-type conversion for every operation. -/
def Expr.usualBinary {target : Target} {parameters : List IntType}
    {leftType rightType : IntType} (operation : ArithmeticOp)
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    Expr target parameters (commonType target leftType rightType) :=
  Expr.promotedBinary (leftKind := promotedType target leftType)
    (rightKind := promotedType target rightType) operation (.promote left) (.promote right)

def Expr.promotedAdd {target : Target} {parameters : List IntType}
    {leftKind rightKind : ArithmeticType}
    (left : Expr target parameters leftKind.asIntType)
    (right : Expr target parameters rightKind.asIntType) :
    Expr target parameters (leftKind.common rightKind).asIntType :=
  Expr.promotedBinary (leftKind := leftKind) (rightKind := rightKind) .add left right

def Expr.usualAdd {target : Target} {parameters : List IntType}
    {leftType rightType : IntType}
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    Expr target parameters (commonType target leftType rightType) :=
  Expr.usualBinary .add left right

def Expr.promotedSub {target : Target} {parameters : List IntType}
    {leftKind rightKind : ArithmeticType}
    (left : Expr target parameters leftKind.asIntType)
    (right : Expr target parameters rightKind.asIntType) :
    Expr target parameters (leftKind.common rightKind).asIntType :=
  Expr.promotedBinary (leftKind := leftKind) (rightKind := rightKind) .sub left right

def Expr.usualSub {target : Target} {parameters : List IntType}
    {leftType rightType : IntType}
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    Expr target parameters (commonType target leftType rightType) :=
  Expr.usualBinary .sub left right

def Expr.promotedMul {target : Target} {parameters : List IntType}
    {leftKind rightKind : ArithmeticType}
    (left : Expr target parameters leftKind.asIntType)
    (right : Expr target parameters rightKind.asIntType) :
    Expr target parameters (leftKind.common rightKind).asIntType :=
  Expr.promotedBinary (leftKind := leftKind) (rightKind := rightKind) .mul left right

def Expr.usualMul {target : Target} {parameters : List IntType}
    {leftType rightType : IntType}
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    Expr target parameters (commonType target leftType rightType) :=
  Expr.usualBinary .mul left right

def Expr.promotedDiv {target : Target} {parameters : List IntType}
    {leftKind rightKind : ArithmeticType}
    (left : Expr target parameters leftKind.asIntType)
    (right : Expr target parameters rightKind.asIntType) :
    Expr target parameters (leftKind.common rightKind).asIntType :=
  Expr.promotedBinary (leftKind := leftKind) (rightKind := rightKind) .div left right

def Expr.usualDiv {target : Target} {parameters : List IntType}
    {leftType rightType : IntType}
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    Expr target parameters (commonType target leftType rightType) :=
  Expr.usualBinary .div left right

def Expr.promotedRem {target : Target} {parameters : List IntType}
    {leftKind rightKind : ArithmeticType}
    (left : Expr target parameters leftKind.asIntType)
    (right : Expr target parameters rightKind.asIntType) :
    Expr target parameters (leftKind.common rightKind).asIntType :=
  Expr.promotedBinary (leftKind := leftKind) (rightKind := rightKind) .rem left right

def Expr.usualRem {target : Target} {parameters : List IntType}
    {leftType rightType : IntType}
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    Expr target parameters (commonType target leftType rightType) :=
  Expr.usualBinary .rem left right

/-- The same numeric primitives used by evalExpr, selected after normalization. -/
def commonBinary (target : Target) (operation : ArithmeticOp) (kind : ArithmeticType) :
    Value target kind.asIntType → Value target kind.asIntType →
      Outcome (Value target kind.asIntType) :=
  match kind, operation with
  | .uint, .add => unsignedAdd target
  | .uint, .sub => unsignedSub target
  | .uint, .mul => unsignedMul target
  | .uint, .div => unsignedDiv target
  | .uint, .rem => unsignedRem target
  | .sint, .add => signedAdd target
  | .sint, .sub => signedSub target
  | .sint, .mul => signedMul target
  | .sint, .div => signedDiv target
  | .sint, .rem => signedRem target

def commonAdd (target : Target) (kind : ArithmeticType) :
    Value target kind.asIntType → Value target kind.asIntType →
      Outcome (Value target kind.asIntType) :=
  commonBinary target .add kind

def commonDiv (target : Target) (kind : ArithmeticType) :
    Value target kind.asIntType → Value target kind.asIntType →
      Outcome (Value target kind.asIntType) :=
  commonBinary target .div kind

/-- Compose operand evaluations with the selected primitive's checked result.
This works for every admitted arithmetic operation and full integer type. -/
theorem eval_primitiveBinary_defined {target : Target} {parameters : List IntType}
    (operation : ArithmeticOp) (kind : ArithmeticType)
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (left right : Expr target parameters kind.asIntType)
    (x y result : Value target kind.asIntType)
    (left_eval : evalExpr policy inputs left = .defined x)
    (right_eval : evalExpr policy inputs right = .defined y)
    (primitive_eval : commonBinary target operation kind x y = .defined result) :
    evalExpr policy inputs (Expr.primitiveBinary operation kind left right) =
      .defined result := by
  cases operation <;> cases kind <;>
    change ((evalExpr policy inputs left).andThen (fun x =>
      (evalExpr policy inputs right).andThen (fun y => _))) = _ <;>
    rw [left_eval, right_eval] <;> exact primitive_eval

/-- Normalization preserves actual operand execution, conversions, primitive
semantics and failures for every operation and promoted type pair. -/
theorem eval_promotedBinary {target : Target} {parameters : List IntType}
    {leftKind rightKind : ArithmeticType} (operation : ArithmeticOp)
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (left : Expr target parameters leftKind.asIntType)
    (right : Expr target parameters rightKind.asIntType) :
    evalExpr policy inputs (Expr.promotedBinary operation left right) =
      ((evalExpr policy inputs left).andThen fun value =>
        convertValue policy target leftKind.asIntType
          (leftKind.common rightKind).asIntType value).andThen
      fun x => ((evalExpr policy inputs right).andThen fun value =>
        convertValue policy target rightKind.asIntType
          (leftKind.common rightKind).asIntType value).andThen
      fun y => commonBinary target operation (leftKind.common rightKind) x y := by
  cases operation <;> cases leftKind <;> cases rightKind <;> rfl

theorem eval_usualBinary {target : Target} {parameters : List IntType}
    {leftType rightType : IntType} (operation : ArithmeticOp)
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    evalExpr policy inputs (Expr.usualBinary operation left right) =
      ((evalExpr policy inputs (.promote left)).andThen fun value =>
        convertValue policy target (promotedType target leftType).asIntType
          (commonType target leftType rightType) value).andThen
      fun x => ((evalExpr policy inputs (.promote right)).andThen fun value =>
        convertValue policy target (promotedType target rightType).asIntType
          (commonType target leftType rightType) value).andThen
      fun y => commonBinary target operation
        ((promotedType target leftType).common (promotedType target rightType)) x y := by
  exact eval_promotedBinary (leftKind := promotedType target leftType)
    (rightKind := promotedType target rightType) operation policy inputs (.promote left) (.promote right)

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
      fun y => commonAdd target (leftKind.common rightKind) x y :=
  eval_promotedBinary .add policy inputs left right

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
        ((promotedType target leftType).common (promotedType target rightType)) x y :=
  eval_usualBinary .add policy inputs left right

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
      fun y => commonDiv target (leftKind.common rightKind) x y :=
  eval_promotedBinary .div policy inputs left right

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
        ((promotedType target leftType).common (promotedType target rightType)) x y :=
  eval_usualBinary .div policy inputs left right

end EDSL.Source
