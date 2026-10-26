/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Conditions
import EDSL.Source.IntegerUnary
set_option autoImplicit false
namespace EDSL.Source

/-- Integral unary operators with promotion. Logical not has a dialect result. -/
inductive UnaryOp where
  | plus | minus | complement | logicalNot
  deriving DecidableEq, Repr

/-- The logical result follows C/C++ rules; other unary results are promoted. -/
def unaryType (target : Target) (dialect : Dialect) (operation : UnaryOp)
    (source : IntType) : IntType :=
  match operation with
  | .logicalNot => dialect.logicalType
  | _ => (promotedType target source).asIntType

/-- Zero at the admitted full arithmetic type. -/
def unaryZero (target : Target) (kind : ArithmeticType) : Value target kind.asIntType :=
  match kind with
  | .uint => IntegerUnary.unsignedZero target
  | .sint => IntegerUnary.signedZero target

/-- Full-width all-ones integer; numeric ranges do not specify object storage. -/
def unaryOnes (target : Target) (kind : ArithmeticType) : Value target kind.asIntType :=
  match kind with
  | .uint => IntegerUnary.unsignedMaximum target
  | .sint => IntegerUnary.signedMinusOne target

/-- Unary + is exactly integer promotion. -/
def Expr.unaryPlus {target : Target} {parameters : List IntType} {source : IntType}
    (operand : Expr target parameters source) :
    Expr target parameters (promotedType target source).asIntType := .promote operand

/-- Negate an already promoted operand using the shared subtraction node. -/
def Expr.primitiveMinus {target : Target} {parameters : List IntType}
    (kind : ArithmeticType) (operand : Expr target parameters kind.asIntType) :
    Expr target parameters kind.asIntType :=
  Expr.primitiveBinary .sub kind (.literal (unaryZero target kind)) operand

/-- Complement an already promoted operand in its full integer range. -/
def Expr.primitiveComplement {target : Target} {parameters : List IntType}
    (kind : ArithmeticType) (operand : Expr target parameters kind.asIntType) :
    Expr target parameters kind.asIntType :=
  Expr.primitiveBinary .sub kind (.literal (unaryOnes target kind)) operand

/-- Pure unary minus is represented by zero minus the promoted operand.
Its diagnostic is the shared subtraction-overflow reason. Operand occurs once. -/
def Expr.unaryMinus {target : Target} {parameters : List IntType} {source : IntType}
    (operand : Expr target parameters source) :
    Expr target parameters (promotedType target source).asIntType :=
  Expr.primitiveMinus (promotedType target source) (.promote operand)

/-- Complement on admitted two's-complement value ranges is all-ones minus
its promoted operand. The numeric law is proved separately for both kinds. -/
def Expr.unaryComplement {target : Target} {parameters : List IntType} {source : IntType}
    (operand : Expr target parameters source) :
    Expr target parameters (promotedType target source).asIntType :=
  Expr.primitiveComplement (promotedType target source) (.promote operand)

/-- Built-in integral logical not, using the shared zero/nonzero conversion.
This is not a C++ overloaded operator. Operand occurs exactly once. -/
def Expr.logicalNot {target : Target} {parameters : List IntType} {source : IntType}
    (dialect : Dialect) (operand : Expr target parameters source) :
    Expr target parameters dialect.logicalType :=
  Expr.logicalResult dialect
    (.select operand.truth (.literal (booleanValue false)) (.literal (booleanValue true)))

/-- Construct unary syntax without adding another evaluator or soundness proof. -/
def Expr.unary {target : Target} {parameters : List IntType} {source : IntType}
    (dialect : Dialect) (operation : UnaryOp) (operand : Expr target parameters source) :
    Expr target parameters (unaryType target dialect operation source) :=
  match operation with
  | .plus => operand.unaryPlus
  | .minus => operand.unaryMinus
  | .complement => operand.unaryComplement
  | .logicalNot => operand.logicalNot dialect

/-- The numeric operation for an already promoted value. -/
def promotedNegate (target : Target) : (kind : ArithmeticType) →
    Value target kind.asIntType → Outcome (Value target kind.asIntType)
  | .uint, value => unsignedSub target (unaryZero target .uint) value
  | .sint, value => signedSub target (unaryZero target .sint) value

def promotedComplement (target : Target) : (kind : ArithmeticType) →
    Value target kind.asIntType → Outcome (Value target kind.asIntType)
  | .uint, value => unsignedSub target (unaryOnes target .uint) value
  | .sint, value => signedSub target (unaryOnes target .sint) value

/-- Raw execution laws expose the original, single operand evaluation. -/
theorem eval_primitiveMinus {target : Target} {parameters : List IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (kind : ArithmeticType) (operand : Expr target parameters kind.asIntType) :
    evalExpr policy inputs (Expr.primitiveMinus kind operand) =
      (evalExpr policy inputs operand).andThen (promotedNegate target kind) := by
  cases kind <;> rfl

theorem eval_primitiveComplement {target : Target} {parameters : List IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (kind : ArithmeticType) (operand : Expr target parameters kind.asIntType) :
    evalExpr policy inputs (Expr.primitiveComplement kind operand) =
      (evalExpr policy inputs operand).andThen (promotedComplement target kind) := by
  cases kind <;> rfl

theorem Expr.firstUnsupported_primitiveMinus {target : Target} {parameters : List IntType}
    (kind : ArithmeticType) (operand : Expr target parameters kind.asIntType) :
    (Expr.primitiveMinus kind operand).firstUnsupported = operand.firstUnsupported := by
  cases kind <;> rfl

theorem Expr.firstUnsupported_primitiveComplement {target : Target} {parameters : List IntType}
    (kind : ArithmeticType) (operand : Expr target parameters kind.asIntType) :
    (Expr.primitiveComplement kind operand).firstUnsupported = operand.firstUnsupported := by
  cases kind <;> rfl

theorem Expr.firstUnsupported_unaryPlus {target : Target} {parameters : List IntType}
    {source : IntType} (operand : Expr target parameters source) :
    operand.unaryPlus.firstUnsupported = operand.firstUnsupported := rfl

theorem Expr.firstUnsupported_unaryMinus {target : Target} {parameters : List IntType}
    {source : IntType} (operand : Expr target parameters source) :
    operand.unaryMinus.firstUnsupported = operand.firstUnsupported := by
  exact Expr.firstUnsupported_primitiveMinus _ _

theorem Expr.firstUnsupported_unaryComplement {target : Target} {parameters : List IntType}
    {source : IntType} (operand : Expr target parameters source) :
    operand.unaryComplement.firstUnsupported = operand.firstUnsupported := by
  exact Expr.firstUnsupported_primitiveComplement _ _

theorem Expr.firstUnsupported_logicalNot {target : Target} {parameters : List IntType}
    {source : IntType} (dialect : Dialect) (operand : Expr target parameters source) :
    (operand.logicalNot dialect).firstUnsupported = operand.firstUnsupported := by
  cases dialect <;> cases coverage : operand.firstUnsupported <;>
    simp [Expr.logicalNot, Expr.logicalResult, Expr.truth, coverage]

theorem eval_unaryPlus {target : Target} {parameters : List IntType} {source : IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (operand : Expr target parameters source) :
    evalExpr policy inputs operand.unaryPlus = (evalExpr policy inputs operand).andThen
      (fun value => .defined (IntegerPromotions.promoteValue value)) := rfl

theorem eval_unaryMinus {target : Target} {parameters : List IntType} {source : IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (operand : Expr target parameters source) :
    evalExpr policy inputs operand.unaryMinus = (evalExpr policy inputs operand).andThen
      (fun value => promotedNegate target (promotedType target source)
        (IntegerPromotions.promoteValue value)) := by
  rw [Expr.unaryMinus, eval_primitiveMinus]
  change ((evalExpr policy inputs operand).andThen
    (fun value => .defined (IntegerPromotions.promoteValue value))).andThen _ = _
  cases evalExpr policy inputs operand <;> rfl

theorem eval_unaryComplement {target : Target} {parameters : List IntType} {source : IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (operand : Expr target parameters source) :
    evalExpr policy inputs operand.unaryComplement = (evalExpr policy inputs operand).andThen
      (fun value => promotedComplement target (promotedType target source)
        (IntegerPromotions.promoteValue value)) := by
  rw [Expr.unaryComplement, eval_primitiveComplement]
  change ((evalExpr policy inputs operand).andThen
    (fun value => .defined (IntegerPromotions.promoteValue value))).andThen _ = _
  cases evalExpr policy inputs operand <;> rfl

theorem Expr.firstUnsupported_unary {target : Target} {parameters : List IntType}
    {source : IntType} (dialect : Dialect) (operation : UnaryOp)
    (operand : Expr target parameters source) :
    (Expr.unary dialect operation operand).firstUnsupported = operand.firstUnsupported := by
  cases operation
  · exact Expr.firstUnsupported_unaryPlus operand
  · exact Expr.firstUnsupported_unaryMinus operand
  · exact Expr.firstUnsupported_unaryComplement operand
  · exact Expr.firstUnsupported_logicalNot dialect operand

/-- Raw logical-not execution follows the original operand and inverts its truth. -/
theorem eval_logicalNot_defined {target : Target} {parameters : List IntType} {source : IntType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (operand : Expr target parameters source) (value : Value target source)
    (execution : evalExpr policy inputs operand = .defined value) :
    ∃ result, evalExpr policy inputs (operand.logicalNot dialect) = .defined result ∧
      result.toInt = (if value.toInt = 0 then 1 else 0) := by
  by_cases zero : value.toInt = 0
  · refine ⟨dialect.logicalValue (booleanValue true), ?_, ?_⟩
    · rw [Expr.logicalNot, eval_logicalResult,
        eval_select_zero policy inputs _ _ _ _
          (eval_truth_defined policy inputs operand value execution)
          ((IntegerCasts.castValue_boolean_eq_zero_iff value).mpr zero)]
      rfl
    · rw [Dialect.logicalValue_toInt, booleanValue_toInt]
      simp only [↓reduceIte, zero]
  · refine ⟨dialect.logicalValue (booleanValue false), ?_, ?_⟩
    · have nonzero : (IntegerCasts.castValue (.small .boolean) value).toInt ≠ 0 := by
        exact fun equation => zero ((IntegerCasts.castValue_boolean_eq_zero_iff value).mp equation)
      rw [Expr.logicalNot, eval_logicalResult,
        eval_select_nonzero policy inputs _ _ _ _
          (eval_truth_defined policy inputs operand value execution) nonzero]
      rfl
    · rw [Dialect.logicalValue_toInt, booleanValue_toInt]
      simp only [Bool.false_eq_true, ↓reduceIte, zero]

end EDSL.Source
