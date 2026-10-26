/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Eval

set_option autoImplicit false

namespace EDSL.Source

/-- The usual arithmetic common type for this pair of full-rank integer types.
This is not a rank hierarchy or an implementation of smaller-type promotions. -/
def commonType : IntType → IntType → IntType
  | .sint, .sint => .sint
  | _, _ => .uint

/-- Normalize usual addition into the shared conversion and arithmetic syntax.
Both operands are converted to the common type before the operation. -/
def Expr.usualAdd {target : Target} {parameters : List IntType}
    {leftType rightType : IntType}
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    Expr target parameters (commonType leftType rightType) :=
  match leftType, rightType with
  | .sint, .sint => .sadd (.convert .sint left) (.convert .sint right)
  | .sint, .uint => .uadd (.convert .uint left) (.convert .uint right)
  | .uint, .sint => .uadd (.convert .uint left) (.convert .uint right)
  | .uint, .uint => .uadd (.convert .uint left) (.convert .uint right)

/-- Normalize usual division, retaining zero-divisor and signed-overflow checks
of the existing primitives after the common-type conversions. -/
def Expr.usualDiv {target : Target} {parameters : List IntType}
    {leftType rightType : IntType}
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    Expr target parameters (commonType leftType rightType) :=
  match leftType, rightType with
  | .sint, .sint => .sdiv (.convert .sint left) (.convert .sint right)
  | .sint, .uint => .udiv (.convert .uint left) (.convert .uint right)
  | .uint, .sint => .udiv (.convert .uint left) (.convert .uint right)
  | .uint, .uint => .udiv (.convert .uint left) (.convert .uint right)

def commonAdd (target : Target) (ty : IntType) :
    Value target ty → Value target ty → Outcome (Value target ty) :=
  match ty with
  | .uint => unsignedAdd target
  | .sint => signedAdd target

def commonDiv (target : Target) (ty : IntType) :
    Value target ty → Value target ty → Outcome (Value target ty) :=
  match ty with
  | .uint => unsignedDiv target
  | .sint => signedDiv target

/-- The smart constructor uses exactly the shared primitive semantics. -/
theorem eval_usualAdd {target : Target} {parameters : List IntType}
    {leftType rightType : IntType} (policy : IntegerConversionPolicy)
    (inputs : Inputs target parameters)
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    evalExpr policy inputs (left.usualAdd right) =
      ((evalExpr policy inputs left).andThen fun value =>
        convertValue policy target leftType (commonType leftType rightType) value).andThen
      fun x => ((evalExpr policy inputs right).andThen fun value =>
        convertValue policy target rightType (commonType leftType rightType) value).andThen
      fun y => commonAdd target (commonType leftType rightType) x y := by
  cases leftType <;> cases rightType <;> rfl

theorem eval_usualDiv {target : Target} {parameters : List IntType}
    {leftType rightType : IntType} (policy : IntegerConversionPolicy)
    (inputs : Inputs target parameters)
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    evalExpr policy inputs (left.usualDiv right) =
      ((evalExpr policy inputs left).andThen fun value =>
        convertValue policy target leftType (commonType leftType rightType) value).andThen
      fun x => ((evalExpr policy inputs right).andThen fun value =>
        convertValue policy target rightType (commonType leftType rightType) value).andThen
      fun y => commonDiv target (commonType leftType rightType) x y := by
  cases leftType <;> cases rightType <;> rfl

end EDSL.Source
