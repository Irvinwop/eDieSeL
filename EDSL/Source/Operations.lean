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


end EDSL.Source
