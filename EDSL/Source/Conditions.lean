/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.ArithmeticConversions
import EDSL.Source.Coverage

set_option autoImplicit false

namespace EDSL.Source

/-- Integer truth uses the existing zero/nonzero conversion rule. -/
def Expr.truth {target : Target} {parameters : List IntType} {ty : IntType}
    (operand : Expr target parameters ty) : Expr target parameters (.small .boolean) :=
  .convert (.small .boolean) operand

/-- C's predicate result is int; C++ keeps the canonical bool. -/
def Expr.logicalResult {target : Target} {parameters : List IntType} (dialect : Dialect)
    (operand : Expr target parameters (.small .boolean)) :
    Expr target parameters dialect.logicalType :=
  match dialect with
  | .gnuC23 => .promote operand
  | .gnuCpp26 => operand

def Expr.promotedCompare {target : Target} {parameters : List IntType}
    {leftKind rightKind : ArithmeticType} (operation : ComparisonOp)
    (left : Expr target parameters leftKind.asIntType)
    (right : Expr target parameters rightKind.asIntType) :
    Expr target parameters (.small .boolean) :=
  .compare operation (leftKind.common rightKind)
    (.convert (leftKind.common rightKind).asIntType left)
    (.convert (leftKind.common rightKind).asIntType right)

/-- Compare after promotion and common-type conversion. The internal result is
bool; sourceCompare supplies the language-specific result type. -/
def Expr.usualCompare {target : Target} {parameters : List IntType}
    {leftType rightType : IntType} (operation : ComparisonOp)
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    Expr target parameters (.small .boolean) :=
  Expr.promotedCompare (leftKind := promotedType target leftType)
    (rightKind := promotedType target rightType) operation (.promote left) (.promote right)

def Expr.sourceCompare {target : Target} {parameters : List IntType}
    {leftType rightType : IntType} (dialect : Dialect) (operation : ComparisonOp)
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    Expr target parameters dialect.logicalType :=
  Expr.logicalResult dialect (Expr.usualCompare operation left right)

/-- Built-in integral AND; right is evaluated only when left is nonzero. -/
def Expr.logicalAnd {target : Target} {parameters : List IntType}
    {leftType rightType : IntType} (dialect : Dialect)
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    Expr target parameters dialect.logicalType :=
  Expr.logicalResult dialect
    (.select left.truth right.truth (.literal (booleanValue false)))

/-- Built-in integral OR; right is evaluated only when left is zero. -/
def Expr.logicalOr {target : Target} {parameters : List IntType}
    {leftType rightType : IntType} (dialect : Dialect)
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    Expr target parameters dialect.logicalType :=
  Expr.logicalResult dialect
    (.select left.truth (.literal (booleanValue true)) right.truth)

/-- Result type for unqualified integral value arms. C applies arithmetic
conversions; C++ preserves matching prvalue types before that common-type case.
This does not model conditional glvalues, cv/reference rules or class operands. -/
def conditionalType (target : Target) (dialect : Dialect) (left right : IntType) : IntType :=
  match dialect with
  | .gnuC23 => commonType target left right
  | .gnuCpp26 => if left = right then left else commonType target left right

/-- Integral value conditional. Each conversion remains inside its own arm,
so a skipped arm is not evaluated merely to select the result type. -/
def Expr.conditional {target : Target} {parameters : List IntType}
    {conditionType leftType rightType : IntType} (dialect : Dialect)
    (condition : Expr target parameters conditionType)
    (onTrue : Expr target parameters leftType) (onFalse : Expr target parameters rightType) :
    Expr target parameters (conditionalType target dialect leftType rightType) := by
  cases dialect with
  | gnuC23 =>
      exact .select condition.truth
        (.convert (commonType target leftType rightType) (.promote onTrue))
        (.convert (commonType target leftType rightType) (.promote onFalse))
  | gnuCpp26 =>
      by_cases same : leftType = rightType
      · subst rightType
        simpa only [conditionalType, ↓reduceIte] using
          (Expr.select condition.truth onTrue onFalse)
      · change Expr target parameters
          (if leftType = rightType then leftType else commonType target leftType rightType)
        rw [ite_eq_right same]
        exact .select condition.truth
          (.convert (commonType target leftType rightType) (.promote onTrue))
          (.convert (commonType target leftType rightType) (.promote onFalse))

theorem eval_truth_defined {target : Target} {parameters : List IntType} {ty : IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (operand : Expr target parameters ty) (value : Value target ty)
    (execution : evalExpr policy inputs operand = .defined value) :
    evalExpr policy inputs operand.truth =
      .defined (IntegerCasts.castValue (.small .boolean) value) := by
  cases policy
  change (evalExpr .gnuModulo inputs operand).andThen
    (fun current => convertValue .gnuModulo target ty (.small .boolean) current) = _
  rw [execution]
  rfl

theorem eval_logicalResult {target : Target} {parameters : List IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (operand : Expr target parameters (.small .boolean)) :
    evalExpr policy inputs (Expr.logicalResult dialect operand) =
      (evalExpr policy inputs operand).andThen fun flag => .defined (dialect.logicalValue flag) := by
  cases dialect with
  | gnuC23 => rfl
  | gnuCpp26 =>
      change evalExpr policy inputs operand =
        (evalExpr policy inputs operand).andThen (fun flag => .defined flag)
      cases evalExpr policy inputs operand <;> rfl

theorem eval_compare_defined {target : Target} {parameters : List IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (operation : ComparisonOp) (kind : ArithmeticType)
    (left right : Expr target parameters kind.asIntType)
    (x y : Value target kind.asIntType)
    (left_eval : evalExpr policy inputs left = .defined x)
    (right_eval : evalExpr policy inputs right = .defined y) :
    evalExpr policy inputs (.compare operation kind left right) =
      .defined (compareValues operation x y) := by
  change (evalExpr policy inputs left).andThen (fun first =>
    (evalExpr policy inputs right).andThen (fun second => .defined (compareValues operation first second))) = _
  rw [left_eval, right_eval]
  rfl

theorem eval_select_zero {target : Target} {parameters : List IntType} {ty : IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (condition : Expr target parameters (.small .boolean))
    (onTrue onFalse : Expr target parameters ty) (flag : Value target (.small .boolean))
    (condition_eval : evalExpr policy inputs condition = .defined flag) (zero : flag.toInt = 0) :
    evalExpr policy inputs (.select condition onTrue onFalse) =
      evalExpr policy inputs onFalse := by
  change (evalExpr policy inputs condition).andThen (fun current =>
    if current.toInt = 0 then evalExpr policy inputs onFalse else evalExpr policy inputs onTrue) = _
  rw [condition_eval]
  exact ite_eq_left zero

theorem eval_select_nonzero {target : Target} {parameters : List IntType} {ty : IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (condition : Expr target parameters (.small .boolean))
    (onTrue onFalse : Expr target parameters ty) (flag : Value target (.small .boolean))
    (condition_eval : evalExpr policy inputs condition = .defined flag) (nonzero : flag.toInt ≠ 0) :
    evalExpr policy inputs (.select condition onTrue onFalse) =
      evalExpr policy inputs onTrue := by
  change (evalExpr policy inputs condition).andThen (fun current =>
    if current.toInt = 0 then evalExpr policy inputs onFalse else evalExpr policy inputs onTrue) = _
  rw [condition_eval]
  exact ite_eq_right nonzero

theorem eval_promotedCompare {target : Target} {parameters : List IntType}
    {leftKind rightKind : ArithmeticType} (operation : ComparisonOp)
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (left : Expr target parameters leftKind.asIntType)
    (right : Expr target parameters rightKind.asIntType) :
    evalExpr policy inputs (Expr.promotedCompare operation left right) =
      ((evalExpr policy inputs left).andThen fun value =>
        convertValue policy target leftKind.asIntType (leftKind.common rightKind).asIntType value).andThen
      fun x => ((evalExpr policy inputs right).andThen fun value =>
        convertValue policy target rightKind.asIntType (leftKind.common rightKind).asIntType value).andThen
      fun y => .defined (compareValues operation x y) := by
  cases leftKind <;> cases rightKind <;> rfl

theorem eval_usualCompare {target : Target} {parameters : List IntType}
    {leftType rightType : IntType} (operation : ComparisonOp)
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    evalExpr policy inputs (Expr.usualCompare operation left right) =
      ((evalExpr policy inputs (.promote left)).andThen fun value =>
        convertValue policy target (promotedType target leftType).asIntType
          (commonType target leftType rightType) value).andThen
      fun x => ((evalExpr policy inputs (.promote right)).andThen fun value =>
        convertValue policy target (promotedType target rightType).asIntType
          (commonType target leftType rightType) value).andThen
      fun y => .defined (compareValues operation x y) :=
  eval_promotedCompare (leftKind := promotedType target leftType)
    (rightKind := promotedType target rightType) operation policy inputs (.promote left) (.promote right)

theorem conditionalType_c (target : Target) (left right : IntType) :
    conditionalType target .gnuC23 left right = commonType target left right := rfl

theorem conditionalType_cpp_same (target : Target) (ty : IntType) :
    conditionalType target .gnuCpp26 ty ty = ty := by
  simp only [conditionalType, ↓reduceIte]

theorem conditionalType_cpp_distinct (target : Target) (left right : IntType)
    (different : left ≠ right) :
    conditionalType target .gnuCpp26 left right = commonType target left right := by
  exact ite_eq_right different

/-- Logical construction preserves the chosen-only raw execution of select. -/
theorem eval_logicalAnd {target : Target} {parameters : List IntType}
    {leftType rightType : IntType} (dialect : Dialect)
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    evalExpr policy inputs (Expr.logicalAnd dialect left right) =
      ((evalExpr policy inputs left.truth).andThen fun flag =>
        if flag.toInt = 0 then .defined (booleanValue false)
        else evalExpr policy inputs right.truth).andThen
      fun flag => .defined (dialect.logicalValue flag) := by
  rw [Expr.logicalAnd, eval_logicalResult]
  rfl

theorem eval_logicalOr {target : Target} {parameters : List IntType}
    {leftType rightType : IntType} (dialect : Dialect)
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (left : Expr target parameters leftType) (right : Expr target parameters rightType) :
    evalExpr policy inputs (Expr.logicalOr dialect left right) =
      ((evalExpr policy inputs left.truth).andThen fun flag =>
        if flag.toInt = 0 then evalExpr policy inputs right.truth
        else .defined (booleanValue true)).andThen
      fun flag => .defined (dialect.logicalValue flag) := by
  rw [Expr.logicalOr, eval_logicalResult]
  rfl

end EDSL.Source
