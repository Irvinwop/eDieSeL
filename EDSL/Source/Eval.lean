/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.ExpressionCore

set_option autoImplicit false
namespace EDSL.Source

/-- Scalar specialization of the shared expression traversal. Public program
coverage remains separate; raw selection evaluates only the chosen branch. -/
def evalExpr {target : Target} {parameters : List IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    {ty : IntType} (expression : Expr target parameters ty) : Outcome (Value target ty) :=
  ExpressionCore.evalOutcome policy inputs expression

/-- Compose defined operand executions and a proved signed-sum range through
the shared evaluator. No source-safety premise replaces either operand proof. -/
theorem eval_sadd_defined {target : Target} {parameters : List IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (left right : Expr target parameters .sint)
    (x y : Value target .sint)
    (left_eval : evalExpr policy inputs left = .defined x)
    (right_eval : evalExpr policy inputs right = .defined y)
    (fits : -target.signedBound ≤ x.val + y.val ∧ x.val + y.val < target.signedBound) :
    evalExpr policy inputs (.sadd left right) = .defined ⟨x.val + y.val, fits⟩ := by
  change ((evalExpr policy inputs left).andThen (fun x =>
    (evalExpr policy inputs right).andThen (fun y => signedAdd target x y))) = _
  rw [left_eval, right_eval]
  exact dite_eq_left fits

/-- Public program evaluation checks static model coverage once, before any
execution. The first unsupported marker takes precedence over execution UB,
including markers in unchosen arms. This is a tool coverage gate, not native
diagnosis or execution of dead syntax: modeled UB in an unchosen arm is inert. -/
def eval {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result) (inputs : Inputs target parameters) :
    Outcome (Value target result) :=
  match program.body.firstUnsupported with
  | none => evalExpr program.conversions inputs program.body
  | some feature => .unsupported feature

theorem eval_dialect_independent {target : Target} {parameters : List IntType}
    {result : IntType} (body : Expr target parameters result)
    (first second : Dialect) (policy : IntegerConversionPolicy)
    (inputs : Inputs target parameters) :
    eval ⟨first, policy, body⟩ inputs = eval ⟨second, policy, body⟩ inputs := rfl

end EDSL.Source
