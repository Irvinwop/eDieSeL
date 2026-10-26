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

/-- An admitted *value-range* profile for the modeled integer types.
Signed widths include the sign bit of the two's-complement numeric range.
These are not ABI, storage, host-machine, compiler-option, or complete GNU
target descriptions. In particular, no storage width is specified for bool. -/
structure Target where
  intBits : Nat
  atLeast16 : 16 ≤ intBits
  charBits : Nat
  charAtLeast8 : 8 ≤ charBits
  shortBits : Nat
  shortAtLeast16 : 16 ≤ shortBits
  charLeShort : charBits ≤ shortBits
  shortLeInt : shortBits ≤ intBits
  plainCharSigned : Bool

namespace Target

def modulus (target : Target) : Nat := 2 ^ target.intBits

theorem modulus_pos (target : Target) : 0 < target.modulus :=
  Nat.two_pow_pos _

def signedBound (target : Target) : Int := (2 ^ (target.intBits - 1) : Nat)

def int32 : Target where
  intBits := 32
  atLeast16 := by decide +kernel
  charBits := 8
  charAtLeast8 := by decide +kernel
  shortBits := 16
  shortAtLeast16 := by decide +kernel
  charLeShort := by decide +kernel
  shortLeInt := by decide +kernel
  plainCharSigned := true

/-- Equal short/int numeric widths exercise unsigned-short promotion to uint. -/
def int16 : Target where
  intBits := 16
  atLeast16 := by decide +kernel
  charBits := 8
  charAtLeast8 := by decide +kernel
  shortBits := 16
  shortAtLeast16 := by decide +kernel
  charLeShort := by decide +kernel
  shortLeInt := by decide +kernel
  plainCharSigned := true

end Target

/-- Only the small integer types supported by this fragment. Enum, BitInt,
bit-field and extended integer types are outside its coverage. -/
inductive SmallType where
  | boolean
  | plainChar
  | schar
  | uchar
  | sshort
  | ushort
  deriving DecidableEq, Repr

namespace SmallType

/-- Exponent describing the mathematical range, not a storage width.
For bool, exponent 1 describes exactly the values 0 and 1. -/
def rangeBits (target : Target) : SmallType → Nat
  | .boolean => 1
  | .plainChar | .schar | .uchar => target.charBits
  | .sshort | .ushort => target.shortBits

def isSigned (target : Target) : SmallType → Bool
  | .boolean | .uchar | .ushort => false
  | .plainChar => target.plainCharSigned
  | .schar | .sshort => true

def lowerBound (target : Target) (ty : SmallType) : Int :=
  if ty.isSigned target then -((2 ^ (ty.rangeBits target - 1) : Nat) : Int) else 0

/-- Exclusive upper bound. Bool has the exact range `[0,2)`. -/
def upperBound (target : Target) (ty : SmallType) : Int :=
  if ty.isSigned target then (2 ^ (ty.rangeBits target - 1) : Nat)
  else (2 ^ ty.rangeBits target : Nat)

/-- Rank metadata for this finite fragment, independent of numeric widths:
bool < every char type < every short type < either full int type (rank 3).
This does not specify a complete source-language rank hierarchy. -/
def rank : SmallType → Nat
  | .boolean => 0
  | .plainChar | .schar | .uchar => 1
  | .sshort | .ushort => 2

end SmallType

/-- The admitted integer types. Long and a complete integer hierarchy remain
unsupported. Signed and unsigned variants at each level have the same rank. -/
inductive IntType where
  | uint
  | sint
  | small (ty : SmallType)
  deriving DecidableEq, Repr

namespace IntType

def rank : IntType → Nat
  | .uint | .sint => 3
  | .small ty => ty.rank

def lowerBound (target : Target) : IntType → Int
  | .uint => 0
  | .sint => -target.signedBound
  | .small ty => ty.lowerBound target

def upperBound (target : Target) : IntType → Int
  | .uint => target.modulus
  | .sint => target.signedBound
  | .small ty => ty.upperBound target

theorem small_rank_lt_full (ty : SmallType) :
    (IntType.small ty).rank < IntType.sint.rank ∧
      (IntType.small ty).rank < IntType.uint.rank := by
  cases ty <;> decide +kernel

end IntType

/-- Mathematical values with their representability proof, not machine storage.
In particular, constructing a literal cannot silently truncate its value. -/
def Value (target : Target) : IntType → Type
  | .uint => Fin target.modulus
  | .sint => { z : Int // -target.signedBound ≤ z ∧ z < target.signedBound }
  | .small ty => { z : Int // ty.lowerBound target ≤ z ∧ z < ty.upperBound target }

instance valueDecidableEq (target : Target) (ty : IntType) : DecidableEq (Value target ty) := by
  cases ty <;> unfold Value <;> infer_instance

instance valueRepr (target : Target) (ty : IntType) : Repr (Value target ty) := by
  cases ty <;> unfold Value <;> infer_instance

namespace Value

/-- The mathematical integer represented by any admitted typed value. -/
def toInt {target : Target} {ty : IntType} : Value target ty → Int :=
  match ty with
  | .uint => fun value => (value.val : Int)
  | .sint => fun value => value.val
  | .small _ => fun value => value.val

theorem range {target : Target} {ty : IntType} (value : Value target ty) :
    ty.lowerBound target ≤ value.toInt ∧ value.toInt < ty.upperBound target := by
  cases ty with
  | uint => exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr value.isLt⟩
  | sint => exact value.property
  | small _ => exact value.property

theorem toInt_injective {target : Target} {ty : IntType} :
    Function.Injective (@toInt target ty) := by
  intro left right same
  cases ty with
  | uint => exact Fin.ext (Int.natCast_inj.mp same)
  | sint => exact Subtype.ext same
  | small _ => exact Subtype.ext same

theorem boolean_values {target : Target} (value : Value target (.small .boolean)) :
    value.toInt = 0 ∨ value.toInt = 1 := by
  have bounds := value.property
  change 0 ≤ value.toInt ∧ value.toInt < 2 at bounds
  omega

end Value

/-- Full int types accepted by the arithmetic primitives after promotion. -/
inductive ArithmeticType where
  | sint
  | uint
  deriving DecidableEq, Repr

def ArithmeticType.asIntType : ArithmeticType → IntType
  | .sint => .sint
  | .uint => .uint

/-- Integer promotion within the admitted fragment. Unsigned small ranges fit
signed int exactly when their width is strictly smaller than `intBits`.
Plain char signedness is explicit in the value-range profile. -/
def promotedType (target : Target) : IntType → ArithmeticType
  | .uint => .uint
  | .sint => .sint
  | .small .boolean => .sint
  | .small ty =>
      if ty.isSigned target then .sint
      else if ty.rangeBits target < target.intBits then .sint else .uint

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
  | promote {source : IntType} : Expr target parameters source →
      Expr target parameters (promotedType target source).asIntType
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
