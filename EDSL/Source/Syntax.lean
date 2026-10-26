/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Source.Types

set_option autoImplicit false

namespace EDSL.Source

/-- A typed parameter reference into a finite source signature. -/
inductive Param : List IntType → IntType → Type where
  | here {ty : IntType} {rest : List IntType} : Param (ty :: rest) ty
  | there {ty other : IntType} {rest : List IntType} :
      Param rest ty → Param (other :: rest) ty

/-- Externally supplied typed parameter values. There is no hidden input generator. -/
inductive Inputs (target : Target) : List IntType → Type where
  | nil : Inputs target []
  | cons {ty : IntType} {rest : List IntType} :
      Value target ty → Inputs target rest → Inputs target (ty :: rest)

def Inputs.get {target : Target} {parameters : List IntType} {ty : IntType} :
    Inputs target parameters → Param parameters ty → Value target ty
  | .cons head _, .here => head
  | .cons _ tail, .there index => tail.get index

/-- A diagnostic marker, not an implementation of the named source feature. -/
inductive UnsupportedFeature where
  | conversion
  | memoryAccess
  | functionCall
  | dialectExtension
  deriving DecidableEq, Repr

/-- Finite typed source expressions. Arithmetic and comparison primitives take
operands of the same full-rank type; explicit conversion changes type. Select
requires a bool condition and arms of one type, without implicit conversions.
Literals are already typed values, not parsed literal tokens. An unsupported
marker explicitly records a hole in coverage and cannot execute successfully. -/
inductive Expr (target : Target) (parameters : List IntType) : IntType → Type where
  | literal {ty : IntType} : Value target ty → Expr target parameters ty
  | param {ty : IntType} : Param parameters ty → Expr target parameters ty
  | convert (destination : IntType) {source : IntType} :
      Expr target parameters source → Expr target parameters destination
  | promote {source : IntType} : Expr target parameters source →
      Expr target parameters (promotedType target source).asIntType
  | uadd : Expr target parameters .uint → Expr target parameters .uint →
      Expr target parameters .uint
  | sadd : Expr target parameters .sint → Expr target parameters .sint →
      Expr target parameters .sint
  | usub : Expr target parameters .uint → Expr target parameters .uint →
      Expr target parameters .uint
  | ssub : Expr target parameters .sint → Expr target parameters .sint →
      Expr target parameters .sint
  | umul : Expr target parameters .uint → Expr target parameters .uint →
      Expr target parameters .uint
  | smul : Expr target parameters .sint → Expr target parameters .sint →
      Expr target parameters .sint
  | udiv : Expr target parameters .uint → Expr target parameters .uint →
      Expr target parameters .uint
  | sdiv : Expr target parameters .sint → Expr target parameters .sint →
      Expr target parameters .sint
  | urem : Expr target parameters .uint → Expr target parameters .uint →
      Expr target parameters .uint
  | srem : Expr target parameters .sint → Expr target parameters .sint →
      Expr target parameters .sint
  | compare (operation : ComparisonOp) (kind : ArithmeticType)
      (left right : Expr target parameters kind.asIntType) :
      Expr target parameters (.small .boolean)
  | select {ty : IntType} (condition : Expr target parameters (.small .boolean))
      (onTrue onFalse : Expr target parameters ty) : Expr target parameters ty
  | unsupported {ty : IntType} : UnsupportedFeature → Expr target parameters ty

namespace Expr

@[simp] private def firstSome (first second : Option UnsupportedFeature) : Option UnsupportedFeature :=
  match first with
  | some feature => some feature
  | none => second

/-- Static model coverage in left-first syntax order, including the condition
and both select arms. This scan does not execute expressions or diagnose UB;
even a marker in an unchosen arm means the program exceeds model coverage. -/
@[simp] def firstUnsupported {target : Target} {parameters : List IntType} :
    {ty : IntType} → Expr target parameters ty → Option UnsupportedFeature
  | _, .literal _ => none
  | _, .param _ => none
  | _, .convert _ operand => operand.firstUnsupported
  | _, .promote operand => operand.firstUnsupported
  | _, .uadd left right => firstSome left.firstUnsupported right.firstUnsupported
  | _, .sadd left right => firstSome left.firstUnsupported right.firstUnsupported
  | _, .usub left right => firstSome left.firstUnsupported right.firstUnsupported
  | _, .ssub left right => firstSome left.firstUnsupported right.firstUnsupported
  | _, .umul left right => firstSome left.firstUnsupported right.firstUnsupported
  | _, .smul left right => firstSome left.firstUnsupported right.firstUnsupported
  | _, .udiv left right => firstSome left.firstUnsupported right.firstUnsupported
  | _, .sdiv left right => firstSome left.firstUnsupported right.firstUnsupported
  | _, .urem left right => firstSome left.firstUnsupported right.firstUnsupported
  | _, .srem left right => firstSome left.firstUnsupported right.firstUnsupported
  | _, .compare _ _ left right => firstSome left.firstUnsupported right.firstUnsupported
  | _, .select condition onTrue onFalse =>
      firstSome condition.firstUnsupported
        (firstSome onTrue.firstUnsupported onFalse.firstUnsupported)
  | _, .unsupported feature => some feature

/-- Coverage of all syntax, separately from source typing and defined execution. -/
def Supported {target : Target} {parameters : List IntType} {ty : IntType}
    (expression : Expr target parameters ty) : Prop :=
  expression.firstUnsupported = none

end Expr

/-- The entire program form is `return expression;`, with exactly the expression's
type as its result type. This is neither a parser nor a general function body. The conversion policy
is fixed once for the whole program and must be provided explicitly. -/
structure Program (target : Target) (parameters : List IntType) (result : IntType) where
  dialect : Dialect
  conversions : IntegerConversionPolicy
  body : Expr target parameters result

end EDSL.Source
