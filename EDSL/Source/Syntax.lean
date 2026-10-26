/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Std

set_option autoImplicit false

namespace EDSL.Source

/-- Language selection, recorded even though this common fragment has one evaluator. -/
inductive Dialect where
  | gnuC23
  | gnuCpp26
  deriving DecidableEq, Repr

/-- An admitted *value-range* profile for `int` and `unsigned int` only.
`intBits` includes the sign bit of two's-complement `int`; it is not an ABI,
object-layout, host-machine, compiler-option, or complete GNU target description. -/
structure Target where
  intBits : Nat
  atLeast16 : 16 ≤ intBits

namespace Target

def modulus (target : Target) : Nat := 2 ^ target.intBits

theorem modulus_pos (target : Target) : 0 < target.modulus :=
  Nat.two_pow_pos _

def signedBound (target : Target) : Int := (2 ^ (target.intBits - 1) : Nat)

def int32 : Target := ⟨32, by decide +kernel⟩

end Target

/-- The two full-rank source types. Smaller types, promotions, extended integers
and a general rank hierarchy remain unsupported. -/
inductive IntType where
  | uint
  | sint
  deriving DecidableEq, Repr

/-- Mathematical values with their representability proof, not machine storage.
In particular, constructing a literal cannot silently truncate its value. -/
def Value (target : Target) : IntType → Type
  | .uint => Fin target.modulus
  | .sint => { z : Int // -target.signedBound ≤ z ∧ z < target.signedBound }

instance valueDecidableEq (target : Target) (ty : IntType) : DecidableEq (Value target ty) := by
  cases ty <;> unfold Value <;> infer_instance

instance valueRepr (target : Target) (ty : IntType) : Repr (Value target ty) := by
  cases ty <;> unfold Value <;> infer_instance

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

/-- Finite typed source expressions. Arithmetic primitives take operands of the
same full-rank type; explicit conversion changes type. Literals are already
typed values, not parsed literal tokens. An unsupported
marker explicitly records a hole in coverage and cannot execute successfully. -/
inductive Expr (target : Target) (parameters : List IntType) : IntType → Type where
  | literal {ty : IntType} : Value target ty → Expr target parameters ty
  | param {ty : IntType} : Param parameters ty → Expr target parameters ty
  | convert (destination : IntType) {source : IntType} :
      Expr target parameters source → Expr target parameters destination
  | uadd : Expr target parameters .uint → Expr target parameters .uint →
      Expr target parameters .uint
  | sadd : Expr target parameters .sint → Expr target parameters .sint →
      Expr target parameters .sint
  | udiv : Expr target parameters .uint → Expr target parameters .uint →
      Expr target parameters .uint
  | sdiv : Expr target parameters .sint → Expr target parameters .sint →
      Expr target parameters .sint
  | unsupported {ty : IntType} : UnsupportedFeature → Expr target parameters ty

/-- The fixed GNU integer-conversion policy. Out-of-range conversion to signed
uses the destination-range modulo representative, with no conversion signal.
This records a GNU implementation choice for C23, not a universal ISO C23 rule.
Conversion policy does not change signed arithmetic overflow into wrapping. -/
inductive IntegerConversionPolicy where
  | gnuModulo
  deriving DecidableEq, Repr

/-- The entire program form is `return expression;`, with exactly the expression's
type as its result type. This is neither a parser nor a general function body. The conversion policy
is fixed once for the whole program and must be provided explicitly. -/
structure Program (target : Target) (parameters : List IntType) (result : IntType) where
  dialect : Dialect
  conversions : IntegerConversionPolicy
  body : Expr target parameters result

end EDSL.Source
