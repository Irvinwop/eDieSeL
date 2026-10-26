/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Source.Syntax

set_option autoImplicit false

namespace EDSL.Source

inductive UBReason where
  | signedAdditionOverflow
  | divisionByZero
  | signedDivisionOverflow
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

/-- One structurally recursive evaluator for the common fragment. Left-first
diagnostics do not claim a source-language operand sequencing guarantee: all
supported expressions are pure. There is no fuel, scheduler, or hidden state. -/
def evalExpr {target : Target} {parameters : List IntType}
    (inputs : Inputs target parameters) :
    {ty : IntType} → Expr target parameters ty → Outcome (Value target ty)
  | _, .literal value => .defined value
  | _, .param index => .defined (inputs.get index)
  | _, .uadd left right =>
      (evalExpr inputs left).andThen fun x =>
        (evalExpr inputs right).andThen fun y => unsignedAdd target x y
  | _, .sadd left right =>
      (evalExpr inputs left).andThen fun x =>
        (evalExpr inputs right).andThen fun y => signedAdd target x y
  | _, .udiv left right =>
      (evalExpr inputs left).andThen fun x =>
        (evalExpr inputs right).andThen fun y => unsignedDiv target x y
  | _, .sdiv left right =>
      (evalExpr inputs left).andThen fun x =>
        (evalExpr inputs right).andThen fun y => signedDiv target x y
  | _, .unsupported feature => .unsupported feature

def eval {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result) (inputs : Inputs target parameters) :
    Outcome (Value target result) :=
  evalExpr inputs program.body

theorem eval_dialect_independent {target : Target} {parameters : List IntType}
    {result : IntType} (body : Expr target parameters result)
    (first second : Dialect) (inputs : Inputs target parameters) :
    eval ⟨first, body⟩ inputs = eval ⟨second, body⟩ inputs := rfl

end EDSL.Source
