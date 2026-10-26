/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Source.IntegerCasts
import EDSL.Source.IntegerPromotions
import EDSL.Source.IntegerComparisons

set_option autoImplicit false

namespace EDSL.Source

inductive UBReason where
  | signedAdditionOverflow
  | signedSubtractionOverflow
  | signedMultiplicationOverflow
  | divisionByZero
  | signedDivisionOverflow
  | signedRemainderOverflow
  deriving DecidableEq, Repr

/-- Unsupported coverage is separate from both a defined value and source UB. -/
inductive Outcome (α : Type) where
  | defined : α → Outcome α
  | undefined : UBReason → Outcome α
  | unsupported : UnsupportedFeature → Outcome α
  deriving DecidableEq, Repr

def Outcome.andThen {α β : Type} (outcome : Outcome α)
    (next : α → Outcome β) : Outcome β :=
  match outcome with
  | .defined value => next value
  | .undefined reason => .undefined reason
  | .unsupported feature => .unsupported feature

def unsignedAdd (target : Target) (x y : Value target .uint) :
    Outcome (Value target .uint) :=
  .defined ⟨(x.val + y.val) % target.modulus, Nat.mod_lt _ target.modulus_pos⟩

/-- Signed results are checked as mathematical integers before constructing a value. -/
def checkedSigned (target : Target) (reason : UBReason) (z : Int) :
    Outcome (Value target .sint) :=
  if h : -target.signedBound ≤ z ∧ z < target.signedBound then
    .defined ⟨z, h⟩
  else
    .undefined reason

def signedAdd (target : Target) (x y : Value target .sint) :
    Outcome (Value target .sint) :=
  checkedSigned target .signedAdditionOverflow (x.val + y.val)

/-- Adding a modulus before subtracting prevents Nat saturation because
both operands are already strictly below that modulus. -/
def unsignedSub (target : Target) (x y : Value target .uint) :
    Outcome (Value target .uint) :=
  .defined ⟨(x.val + target.modulus - y.val) % target.modulus,
    Nat.mod_lt _ target.modulus_pos⟩

def signedSub (target : Target) (x y : Value target .sint) :
    Outcome (Value target .sint) :=
  checkedSigned target .signedSubtractionOverflow (x.val - y.val)

def unsignedMul (target : Target) (x y : Value target .uint) :
    Outcome (Value target .uint) :=
  .defined ⟨(x.val * y.val) % target.modulus, Nat.mod_lt _ target.modulus_pos⟩

def signedMul (target : Target) (x y : Value target .sint) :
    Outcome (Value target .sint) :=
  checkedSigned target .signedMultiplicationOverflow (x.val * y.val)

def unsignedDiv (target : Target) (x y : Value target .uint) :
    Outcome (Value target .uint) :=
  if y.val = 0 then .undefined .divisionByZero
  else .defined ⟨x.val / y.val, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt⟩

/-- Division truncates toward zero. Zero is rejected before calling Lean's total
division; an unrepresentable quotient is signed-division UB, never wrapping. -/
def signedDiv (target : Target) (x y : Value target .sint) :
    Outcome (Value target .sint) :=
  if y.val = 0 then .undefined .divisionByZero
  else checkedSigned target .signedDivisionOverflow (x.val.tdiv y.val)

def unsignedRem (target : Target) (x y : Value target .uint) :
    Outcome (Value target .uint) :=
  if h : y.val = 0 then .undefined .divisionByZero
  else .defined ⟨x.val % y.val,
    Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero h)) y.isLt⟩

/-- Remainder uses truncating division. Reject zero first, then require the
quotient to fit even when the remainder is zero (INT_MIN % -1 is UB).
The remainder itself is checked before constructing its signed value. -/
def signedRem (target : Target) (x y : Value target .sint) :
    Outcome (Value target .sint) :=
  if y.val = 0 then .undefined .divisionByZero
  else if -target.signedBound ≤ x.val.tdiv y.val ∧
      x.val.tdiv y.val < target.signedBound then
    checkedSigned target .signedRemainderOverflow (x.val.tmod y.val)
  else .undefined .signedRemainderOverflow

/-- One total integral conversion rule under the program's explicit GNU policy.
Boolean destinations test zero/nonzero; other destinations select the congruent
representative in their range. Arithmetic overflow is checked separately. -/
def convertValue (policy : IntegerConversionPolicy) (target : Target)
    (source destination : IntType) (value : Value target source) :
    Outcome (Value target destination) :=
  match policy with
  | .gnuModulo => .defined (IntegerCasts.castValue destination value)

/-- One structurally recursive evaluator for the common fragment. Left-first
diagnostics do not claim a source-language operand sequencing guarantee: all
supported expressions are pure. Select executes only its chosen arm. This raw
evaluator follows execution; public program evaluation first checks coverage
of all syntax. There is no fuel, scheduler, or hidden state. -/
def evalExpr {target : Target} {parameters : List IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters) :
    {ty : IntType} → Expr target parameters ty → Outcome (Value target ty)
  | _, .literal value => .defined value
  | _, .param index => .defined (inputs.get index)
  | _, .promote operand =>
      (evalExpr policy inputs operand).andThen fun value =>
        .defined (IntegerPromotions.promoteValue value)
  | _, .convert destination operand =>
      (evalExpr policy inputs operand).andThen fun value =>
        convertValue policy target _ destination value
  | _, .uadd left right =>
      (evalExpr policy inputs left).andThen fun x =>
        (evalExpr policy inputs right).andThen fun y => unsignedAdd target x y
  | _, .sadd left right =>
      (evalExpr policy inputs left).andThen fun x =>
        (evalExpr policy inputs right).andThen fun y => signedAdd target x y
  | _, .usub left right =>
      (evalExpr policy inputs left).andThen fun x =>
        (evalExpr policy inputs right).andThen fun y => unsignedSub target x y
  | _, .ssub left right =>
      (evalExpr policy inputs left).andThen fun x =>
        (evalExpr policy inputs right).andThen fun y => signedSub target x y
  | _, .umul left right =>
      (evalExpr policy inputs left).andThen fun x =>
        (evalExpr policy inputs right).andThen fun y => unsignedMul target x y
  | _, .smul left right =>
      (evalExpr policy inputs left).andThen fun x =>
        (evalExpr policy inputs right).andThen fun y => signedMul target x y
  | _, .udiv left right =>
      (evalExpr policy inputs left).andThen fun x =>
        (evalExpr policy inputs right).andThen fun y => unsignedDiv target x y
  | _, .sdiv left right =>
      (evalExpr policy inputs left).andThen fun x =>
        (evalExpr policy inputs right).andThen fun y => signedDiv target x y
  | _, .urem left right =>
      (evalExpr policy inputs left).andThen fun x =>
        (evalExpr policy inputs right).andThen fun y => unsignedRem target x y
  | _, .srem left right =>
      (evalExpr policy inputs left).andThen fun x =>
        (evalExpr policy inputs right).andThen fun y => signedRem target x y
  | _, .compare operation _ left right =>
      (evalExpr policy inputs left).andThen fun x =>
        (evalExpr policy inputs right).andThen fun y => .defined (compareValues operation x y)
  | _, .select condition onTrue onFalse =>
      (evalExpr policy inputs condition).andThen fun value =>
        if value.toInt = 0 then evalExpr policy inputs onFalse
        else evalExpr policy inputs onTrue
  | _, .unsupported feature => .unsupported feature

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
