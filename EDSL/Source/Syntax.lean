/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Memory.Types

set_option autoImplicit false

namespace EDSL.Source
open Memory

/-- Generic typed membership, with no binding or object-validity assertion. -/
inductive Index {α : Type} : List α → α → Type where
  | here {a : α} {tail : List α} : Index (a :: tail) a
  | there {a b : α} {tail : List α} : Index tail a → Index (b :: tail) a

/-- The original integer parameter API is intentionally retained. -/
inductive Param : List IntType → IntType → Type where
  | here {ty : IntType} {rest : List IntType} : Param (ty :: rest) ty
  | there {ty other : IntType} {rest : List IntType} :
      Param rest ty → Param (other :: rest) ty

/-- Externally supplied integer inputs; unchanged, including named binders. -/
inductive Inputs (target : Target) : List IntType → Type where
  | nil : Inputs target []
  | cons {ty : IntType} {rest : List IntType} :
      Value target ty → Inputs target rest → Inputs target (ty :: rest)

def Inputs.get {target : Target} {parameters : List IntType} {ty : IntType} :
    Inputs target parameters → Param parameters ty → Value target ty
  | .cons head _, .here => head
  | .cons _ tail, .there index => tail.get index

/-- Scalar call inputs, distinct from mutable object bindings. -/
inductive ScalarInputs (target : Target) : List ScalarType → Type where
  | nil : ScalarInputs target []
  | cons {ty : ScalarType} {rest : List ScalarType} :
      ScalarValue target ty → ScalarInputs target rest → ScalarInputs target (ty :: rest)

def ScalarInputs.get {target : Target} {parameters : List ScalarType} {ty : ScalarType} :
    ScalarInputs target parameters → Index parameters ty → ScalarValue target ty
  | .cons head _, .here => head
  | .cons _ tail, .there index => tail.get index

def Param.toIndex {parameters : List IntType} {ty : IntType} :
    Param parameters ty → Index (parameters.map ScalarType.integer) (.integer ty)
  | .here => .here
  | .there index => .there index.toIndex

def Param.ofIndex : {parameters : List IntType} → {ty : IntType} →
    Index (parameters.map ScalarType.integer) (.integer ty) → Param parameters ty
  | _ :: _, _, .here => .here
  | _ :: _, _, .there index => .there (ofIndex index)

@[simp] theorem Param.ofIndex_toIndex {parameters : List IntType} {ty : IntType}
    (index : Param parameters ty) : ofIndex index.toIndex = index := by
  induction index <;> simp_all only [toIndex, ofIndex]

@[simp] theorem Param.toIndex_ofIndex {parameters : List IntType} {ty : IntType}
    (index : Index (parameters.map ScalarType.integer) (.integer ty)) :
    (ofIndex index).toIndex = index := by
  match parameters, ty, index with
  | _ :: _, _, .here => rfl
  | _ :: _, _, .there index =>
      exact congrArg Index.there (toIndex_ofIndex index)

def Inputs.toScalar {target : Target} {parameters : List IntType} :
    Inputs target parameters → ScalarInputs target (parameters.map ScalarType.integer)
  | .nil => .nil
  | .cons head tail => .cons head tail.toScalar

def Inputs.ofScalar {target : Target} : {parameters : List IntType} →
    ScalarInputs target (parameters.map ScalarType.integer) → Inputs target parameters
  | [], .nil => .nil
  | _ :: _, .cons head tail => .cons head (ofScalar tail)

@[simp] theorem Inputs.ofScalar_toScalar {target : Target} {parameters : List IntType}
    (inputs : Inputs target parameters) : ofScalar inputs.toScalar = inputs := by
  match parameters, inputs with
  | [], .nil => rfl
  | _ :: _, .cons head tail =>
      exact congrArg (Inputs.cons head) (ofScalar_toScalar tail)

@[simp] theorem Inputs.toScalar_ofScalar {target : Target} {parameters : List IntType}
    (inputs : ScalarInputs target (parameters.map ScalarType.integer)) :
    (ofScalar inputs).toScalar = inputs := by
  match parameters, inputs with
  | [], .nil => rfl
  | _ :: _, .cons head tail =>
      exact congrArg (ScalarInputs.cons head) (toScalar_ofScalar tail)

@[simp] theorem Inputs.get_toScalar {target : Target} {parameters : List IntType}
    (inputs : Inputs target parameters) {ty : IntType} (index : Param parameters ty) :
    inputs.toScalar.get index.toIndex = inputs.get index := by
  induction index with
  | here => cases inputs; rfl
  | there index ih => cases inputs with | cons head tail => exact ih tail

@[simp] theorem Inputs.get_ofScalar {target : Target} {parameters : List IntType}
    (inputs : ScalarInputs target (parameters.map ScalarType.integer)) {ty : IntType}
    (index : Index (parameters.map ScalarType.integer) (.integer ty)) :
    (Inputs.ofScalar inputs).get (Param.ofIndex index) = inputs.get index := by
  rw [← Inputs.get_toScalar, Inputs.toScalar_ofScalar, Param.toIndex_ofIndex]

/-- A diagnostic marker; supporting a syntax form never executes this marker. -/
inductive UnsupportedFeature where
  | conversion
  | memoryAccess
  | functionCall
  | dialectExtension
  deriving DecidableEq, Repr

/-- A grammar index, not an evaluation strategy. Memory constructors are object-only. -/
inductive Fragment where
  | pureInteger
  | object
  deriving DecidableEq, Repr

/-- Pointer-first syntax; subtraction is not unsigned integer negation. -/
inductive OffsetOp where
  | add
  | sub
  deriving DecidableEq, Repr

namespace Engine

/- One scalar expression grammar mutually containing object places.
Integer positions use exactly the existing Value/IntType/ArithmeticType indices.
No source literal accepts pointer descriptors. This is syntax, not execution. -/
mutual
  inductive Expr (target : Target) (inputs : List ScalarType) (objects : List ObjectType) :
      Fragment → ScalarType → Type where
    | literal {f : Fragment} {ty : IntType} :
        Value target ty → Expr target inputs objects f (.integer ty)
    | param {f : Fragment} {ty : ScalarType} :
        Index inputs ty → Expr target inputs objects f ty
    | convert {f : Fragment} (destination : IntType) {source : IntType} :
        Expr target inputs objects f (.integer source) →
        Expr target inputs objects f (.integer destination)
    | promote {f : Fragment} {source : IntType} :
        Expr target inputs objects f (.integer source) →
        Expr target inputs objects f (.integer (promotedType target source).asIntType)
    | uadd {f : Fragment} : Expr target inputs objects f (.integer .uint) →
        Expr target inputs objects f (.integer .uint) →
        Expr target inputs objects f (.integer .uint)
    | sadd {f : Fragment} : Expr target inputs objects f (.integer .sint) →
        Expr target inputs objects f (.integer .sint) →
        Expr target inputs objects f (.integer .sint)
    | usub {f : Fragment} : Expr target inputs objects f (.integer .uint) →
        Expr target inputs objects f (.integer .uint) →
        Expr target inputs objects f (.integer .uint)
    | ssub {f : Fragment} : Expr target inputs objects f (.integer .sint) →
        Expr target inputs objects f (.integer .sint) →
        Expr target inputs objects f (.integer .sint)
    | umul {f : Fragment} : Expr target inputs objects f (.integer .uint) →
        Expr target inputs objects f (.integer .uint) →
        Expr target inputs objects f (.integer .uint)
    | smul {f : Fragment} : Expr target inputs objects f (.integer .sint) →
        Expr target inputs objects f (.integer .sint) →
        Expr target inputs objects f (.integer .sint)
    | udiv {f : Fragment} : Expr target inputs objects f (.integer .uint) →
        Expr target inputs objects f (.integer .uint) →
        Expr target inputs objects f (.integer .uint)
    | sdiv {f : Fragment} : Expr target inputs objects f (.integer .sint) →
        Expr target inputs objects f (.integer .sint) →
        Expr target inputs objects f (.integer .sint)
    | urem {f : Fragment} : Expr target inputs objects f (.integer .uint) →
        Expr target inputs objects f (.integer .uint) →
        Expr target inputs objects f (.integer .uint)
    | srem {f : Fragment} : Expr target inputs objects f (.integer .sint) →
        Expr target inputs objects f (.integer .sint) →
        Expr target inputs objects f (.integer .sint)
    | compare {f : Fragment} (operation : ComparisonOp) (kind : ArithmeticType)
        (left right : Expr target inputs objects f (.integer kind.asIntType)) :
        Expr target inputs objects f (.integer (.small .boolean))
    | select {f : Fragment} {ty : ScalarType}
        (condition : Expr target inputs objects f (.integer (.small .boolean)))
        (onTrue onFalse : Expr target inputs objects f ty) : Expr target inputs objects f ty
    | unsupported {f : Fragment} {ty : ScalarType} :
        UnsupportedFeature → Expr target inputs objects f ty
    | null {object : ObjectType} : Expr target inputs objects .object (.pointer object)
    | load {ty : ScalarType} :
        Place target inputs objects (.scalar ty) → Expr target inputs objects .object ty
    | address {object : ObjectType} :
        Place target inputs objects object → Expr target inputs objects .object (.pointer object)
    | decay {element : ObjectType} {length : Nat} :
        Place target inputs objects (.array element length) →
        Expr target inputs objects .object (.pointer element)
    | offset {object : ObjectType} {index : IntType} (operation : OffsetOp)
        (base : Expr target inputs objects .object (.pointer object))
        (displacement : Expr target inputs objects .object (.integer index)) :
        Expr target inputs objects .object (.pointer object)

  /-- A designator is not a load. Indirection stays explicit under address-of,
  so the later core can choose address interpretation before designation. -/
  inductive Place (target : Target) (inputs : List ScalarType) (objects : List ObjectType) :
      ObjectType → Type where
    | variable {object : ObjectType} :
        Index objects object → Place target inputs objects object
    | indirect {object : ObjectType} :
        Expr target inputs objects .object (.pointer object) → Place target inputs objects object
    | unsupported {object : ObjectType} :
        UnsupportedFeature → Place target inputs objects object
end

def Place.subscript {target : Target} {inputs : List ScalarType} {objects : List ObjectType}
    {object : ObjectType} {index : IntType}
    (base : Expr target inputs objects .object (.pointer object))
    (displacement : Expr target inputs objects .object (.integer index)) :
    Place target inputs objects object :=
  .indirect (.offset .add base displacement)

/-- Object RHSs have no immutable-input leaves. Mutable formals are objects. -/
abbrev RHS (target : Target) (objects : List ObjectType) (result : ScalarType) :=
  Expr target [] objects .object result

abbrev FormalObjects (parameters : List ScalarType) := parameters.map ObjectType.scalar

end Engine

/-- The exact guarded pure domain. An integer outer result alone is insufficient. -/
abbrev Expr (target : Target) (parameters : List IntType) (result : IntType) :=
  Engine.Expr target (parameters.map ScalarType.integer) [] .pureInteger (.integer result)

namespace Expr

@[match_pattern] abbrev literal {target : Target} {parameters : List IntType} {ty : IntType}
    (value : Value target ty) : Expr target parameters ty := Engine.Expr.literal value

/-- Construction adapter. Eliminate a raw param with Param.ofIndex; this adapter's
nontrivial index map is not a constructor pattern. -/
abbrev param {target : Target} {parameters : List IntType} {ty : IntType}
    (index : Param parameters ty) : Expr target parameters ty := Engine.Expr.param index.toIndex

@[match_pattern] abbrev convert {target : Target} {parameters : List IntType}
    (destination : IntType) {source : IntType} (operand : Expr target parameters source) :
    Expr target parameters destination := Engine.Expr.convert destination operand

@[match_pattern] abbrev promote {target : Target} {parameters : List IntType}
    {source : IntType} (operand : Expr target parameters source) :
    Expr target parameters (promotedType target source).asIntType := Engine.Expr.promote operand
@[match_pattern] abbrev uadd {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .uint) : Expr target parameters .uint := Engine.Expr.uadd left right

@[match_pattern] abbrev sadd {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .sint) : Expr target parameters .sint := Engine.Expr.sadd left right

@[match_pattern] abbrev usub {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .uint) : Expr target parameters .uint := Engine.Expr.usub left right

@[match_pattern] abbrev ssub {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .sint) : Expr target parameters .sint := Engine.Expr.ssub left right

@[match_pattern] abbrev umul {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .uint) : Expr target parameters .uint := Engine.Expr.umul left right

@[match_pattern] abbrev smul {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .sint) : Expr target parameters .sint := Engine.Expr.smul left right

@[match_pattern] abbrev udiv {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .uint) : Expr target parameters .uint := Engine.Expr.udiv left right

@[match_pattern] abbrev sdiv {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .sint) : Expr target parameters .sint := Engine.Expr.sdiv left right

@[match_pattern] abbrev urem {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .uint) : Expr target parameters .uint := Engine.Expr.urem left right

@[match_pattern] abbrev srem {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .sint) : Expr target parameters .sint := Engine.Expr.srem left right

@[match_pattern] abbrev compare {target : Target} {parameters : List IntType}
    (operation : ComparisonOp) (kind : ArithmeticType)
    (left right : Expr target parameters kind.asIntType) :
    Expr target parameters (.small .boolean) := Engine.Expr.compare operation kind left right

@[match_pattern] abbrev select {target : Target} {parameters : List IntType} {ty : IntType}
    (condition : Expr target parameters (.small .boolean))
    (onTrue onFalse : Expr target parameters ty) : Expr target parameters ty :=
  Engine.Expr.select condition onTrue onFalse

@[match_pattern] abbrev unsupported {target : Target} {parameters : List IntType} {ty : IntType}
    (feature : UnsupportedFeature) : Expr target parameters ty := Engine.Expr.unsupported feature

end Expr

/-- Keep function returns and the old pure program interface integer-indexed. -/
structure Program (target : Target) (parameters : List IntType) (result : IntType) where
  dialect : Dialect
  conversions : IntegerConversionPolicy
  body : Expr target parameters result

end EDSL.Source

namespace EDSL.Source
open Memory

namespace Engine

/-- Syntax/data admission only, not runtime support or a source-standard map.
The common profile keeps old full-int object forms in both dialects. The new
data/layout profile is constructible only at C23. No execution uses it here. -/
inductive SyntaxProfile (target : Target) : Dialect → Type where
  | common {dialect : Dialect} : SyntaxProfile target dialect
  | c23Data (layout : StorageLayout target) : SyntaxProfile target .gnuC23

def SyntaxProfile.scalarCovered {target : Target} {dialect : Dialect}
    (profile : SyntaxProfile target dialect) (ty : ScalarType) : Bool :=
  match profile, ty with
  | .common, .integer _ => true
  | .common, .pointer _ => false
  | .c23Data layout, ty => Memory.typeCovered .gnuC23 layout (.scalar ty)

def SyntaxProfile.objectCovered {target : Target} {dialect : Dialect}
    (profile : SyntaxProfile target dialect) (object : ObjectType) : Bool :=
  match profile, object with
  | .common, .scalar (.integer .sint) => true
  | .common, .scalar (.integer .uint) => true
  | .common, _ => false
  | .c23Data layout, object => Memory.typeCovered .gnuC23 layout object

/-- Left-first diagnostics; the second argument's syntax is still scanned by
the logical coverage specification even if the first diagnostic wins. -/
@[simp] def firstSome (first second : Option UnsupportedFeature) : Option UnsupportedFeature :=
  match first with
  | some feature => some feature
  | none => second

@[simp] theorem firstSome_eq_none_iff (first second : Option UnsupportedFeature) :
    firstSome first second = none ↔ first = none ∧ second = none := by
  cases first <;> simp only [firstSome, reduceCtorEq, false_and, true_and]

def typeDiagnostic (covered : Bool) : Option UnsupportedFeature :=
  if covered then none else some .memoryAccess

def SyntaxProfile.pointerDiagnostic {target : Target} {dialect : Dialect}
    (profile : SyntaxProfile target dialect) (object : ObjectType) : Option UnsupportedFeature :=
  typeDiagnostic (profile.scalarCovered (.pointer object))

/-- The old common load shape is exactly a variable designator of full int.
Admitting the new syntax under c23Data does not implement the operation. -/
def Expr.loadDiagnostic {target : Target} {dialect : Dialect}
    {inputs : List ScalarType} {objects : List ObjectType} {ty : ScalarType}
    (profile : SyntaxProfile target dialect)
    (place : Place target inputs objects (.scalar ty)) : Option UnsupportedFeature :=
  match profile, place with
  | .common, .variable _ => typeDiagnostic (profile.objectCovered (.scalar ty))
  | .common, _ => some .memoryAccess
  | .c23Data _, _ => typeDiagnostic (profile.objectCovered (.scalar ty))

/-- Whole-array offset is outside this initial operation syntax profile. -/
def SyntaxProfile.offsetDiagnostic {target : Target} {dialect : Dialect}
    (profile : SyntaxProfile target dialect) (object : ObjectType) : Option UnsupportedFeature :=
  match object with
  | .scalar (.integer _) => profile.pointerDiagnostic object
  | _ => some .memoryAccess

mutual
  /-- Whole-tree scan, independent of dynamic demand. Own profile/type checks
  precede children; children use documented pointer-first/left-first syntax order. -/
  @[simp] def Expr.firstUnsupported {target : Target} {dialect : Dialect}
      {inputs : List ScalarType} {objects : List ObjectType}
      (profile : SyntaxProfile target dialect) :
      {f : Fragment} → {ty : ScalarType} → Expr target inputs objects f ty →
        Option UnsupportedFeature
    | _, _, .literal _ => none
    | _, _, .param (ty := ty) _ => typeDiagnostic (profile.scalarCovered ty)
    | _, _, .convert _ operand => operand.firstUnsupported profile
    | _, _, .promote operand => operand.firstUnsupported profile
    | _, _, .uadd left right => firstSome (left.firstUnsupported profile) (right.firstUnsupported profile)
    | _, _, .sadd left right => firstSome (left.firstUnsupported profile) (right.firstUnsupported profile)
    | _, _, .usub left right => firstSome (left.firstUnsupported profile) (right.firstUnsupported profile)
    | _, _, .ssub left right => firstSome (left.firstUnsupported profile) (right.firstUnsupported profile)
    | _, _, .umul left right => firstSome (left.firstUnsupported profile) (right.firstUnsupported profile)
    | _, _, .smul left right => firstSome (left.firstUnsupported profile) (right.firstUnsupported profile)
    | _, _, .udiv left right => firstSome (left.firstUnsupported profile) (right.firstUnsupported profile)
    | _, _, .sdiv left right => firstSome (left.firstUnsupported profile) (right.firstUnsupported profile)
    | _, _, .urem left right => firstSome (left.firstUnsupported profile) (right.firstUnsupported profile)
    | _, _, .srem left right => firstSome (left.firstUnsupported profile) (right.firstUnsupported profile)
    | _, _, .compare _ _ left right =>
        firstSome (left.firstUnsupported profile) (right.firstUnsupported profile)
    | _, _, .select (ty := ty) condition onTrue onFalse =>
        firstSome (typeDiagnostic (profile.scalarCovered ty))
          (firstSome (condition.firstUnsupported profile)
            (firstSome (onTrue.firstUnsupported profile) (onFalse.firstUnsupported profile)))
    | _, _, .unsupported feature => some feature
    | _, _, .null (object := object) => profile.pointerDiagnostic object
    | _, _, .load place =>
        firstSome (Expr.loadDiagnostic profile place) (place.firstUnsupported profile)
    | _, _, .address (object := object) place =>
        firstSome (profile.pointerDiagnostic object) (place.firstUnsupported profile)
    | _, _, .decay (element := element) (length := length) place =>
        firstSome (typeDiagnostic (profile.objectCovered (.array element length)))
          (firstSome (profile.pointerDiagnostic element) (place.firstUnsupported profile))
    | _, _, .offset (object := object) _ base displacement =>
        firstSome (profile.offsetDiagnostic object)
          (firstSome (base.firstUnsupported profile) (displacement.firstUnsupported profile))

  /-- Designation is not performed by preflight, including below address-of.
  Canceled indirection's syntax and operand constraints are still scanned. -/
  @[simp] def Place.firstUnsupported {target : Target} {dialect : Dialect}
      {inputs : List ScalarType} {objects : List ObjectType}
      (profile : SyntaxProfile target dialect) :
      {object : ObjectType} → Place target inputs objects object → Option UnsupportedFeature
    | object, .variable _ => typeDiagnostic (profile.objectCovered object)
    | object, .indirect pointer =>
        firstSome (profile.pointerDiagnostic object) (pointer.firstUnsupported profile)
    | _, .unsupported feature => some feature
end

/-- Header lists are checked in their declared order, even if unused. -/
def firstUnsupportedTypes {α : Type} (covered : α → Bool) : List α → Option UnsupportedFeature
  | [] => none
  | head :: tail => firstSome (typeDiagnostic (covered head)) (firstUnsupportedTypes covered tail)

/-- Standalone expression preflight: immutable inputs, result, object context,
then the entire expression. No entry/allocation/evaluation effect occurs here. -/
def Expr.preflight {target : Target} {dialect : Dialect}
    {inputs : List ScalarType} {objects : List ObjectType} {f : Fragment} {ty : ScalarType}
    (profile : SyntaxProfile target dialect) (expression : Expr target inputs objects f ty) :
    Option UnsupportedFeature :=
  firstSome (firstUnsupportedTypes profile.scalarCovered inputs)
    (firstSome (typeDiagnostic (profile.scalarCovered ty))
      (firstSome (firstUnsupportedTypes profile.objectCovered objects)
        (expression.firstUnsupported profile)))

/-- A standalone place checks immutable inputs, its result object type, the
complete object context and then its tree. No validity of designation is claimed. -/
def Place.preflight {target : Target} {dialect : Dialect}
    {inputs : List ScalarType} {objects : List ObjectType} {object : ObjectType}
    (profile : SyntaxProfile target dialect) (place : Place target inputs objects object) :
    Option UnsupportedFeature :=
  firstSome (firstUnsupportedTypes profile.scalarCovered inputs)
    (firstSome (typeDiagnostic (profile.objectCovered object))
      (firstSome (firstUnsupportedTypes profile.objectCovered objects)
        (place.firstUnsupported profile)))

/-- Intended interpretation context for the later one mutual core.
Address mode may cancel an indirect place before ordinary designation. -/
inductive PlaceIntent where
  | designate
  | address
  deriving DecidableEq, Repr

def PlaceResult (Handle : ObjectType → Type) (intent : PlaceIntent) (object : ObjectType) : Type :=
  match intent with
  | .designate => Handle object
  | .address => PointerValue object

end Engine

namespace Expr

/-- Legacy coverage keeps exactly its old signature and scans all pure arms. -/
def firstUnsupported {target : Target} {parameters : List IntType} {ty : IntType}
    (expression : Expr target parameters ty) : Option UnsupportedFeature :=
  Engine.Expr.firstUnsupported (Engine.SyntaxProfile.common (dialect := .gnuC23)) expression

def Supported {target : Target} {parameters : List IntType} {ty : IntType}
    (expression : Expr target parameters ty) : Prop :=
  expression.firstUnsupported = none

/-- Preserve the old simplifier boundary: an unknown pure expression remains
opaque, while constructor equations expose its child scans. -/
@[simp] theorem firstUnsupported_literal {target : Target} {parameters : List IntType} {ty : IntType}
    (value : Value target ty) : Expr.firstUnsupported (parameters := parameters) (Engine.Expr.literal value) = none := rfl

@[simp] theorem firstUnsupported_param {target : Target} {parameters : List IntType} {ty : IntType}
    (index : Param parameters ty) : Expr.firstUnsupported (target := target) (Engine.Expr.param index.toIndex) = none := rfl

@[simp] theorem firstUnsupported_convert {target : Target} {parameters : List IntType}
    (destination : IntType) {source : IntType} (operand : Expr target parameters source) :
    Expr.firstUnsupported (parameters := parameters) (Engine.Expr.convert destination operand) = operand.firstUnsupported := rfl

@[simp] theorem firstUnsupported_promote {target : Target} {parameters : List IntType}
    {source : IntType} (operand : Expr target parameters source) :
    Expr.firstUnsupported (parameters := parameters) (Engine.Expr.promote operand) = operand.firstUnsupported := rfl

@[simp] theorem firstUnsupported_uadd {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .uint) :
    Expr.firstUnsupported (parameters := parameters) (Engine.Expr.uadd left right) =
      Engine.firstSome left.firstUnsupported right.firstUnsupported := rfl

@[simp] theorem firstUnsupported_sadd {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .sint) :
    Expr.firstUnsupported (parameters := parameters) (Engine.Expr.sadd left right) =
      Engine.firstSome left.firstUnsupported right.firstUnsupported := rfl

@[simp] theorem firstUnsupported_usub {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .uint) :
    Expr.firstUnsupported (parameters := parameters) (Engine.Expr.usub left right) =
      Engine.firstSome left.firstUnsupported right.firstUnsupported := rfl

@[simp] theorem firstUnsupported_ssub {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .sint) :
    Expr.firstUnsupported (parameters := parameters) (Engine.Expr.ssub left right) =
      Engine.firstSome left.firstUnsupported right.firstUnsupported := rfl

@[simp] theorem firstUnsupported_umul {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .uint) :
    Expr.firstUnsupported (parameters := parameters) (Engine.Expr.umul left right) =
      Engine.firstSome left.firstUnsupported right.firstUnsupported := rfl

@[simp] theorem firstUnsupported_smul {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .sint) :
    Expr.firstUnsupported (parameters := parameters) (Engine.Expr.smul left right) =
      Engine.firstSome left.firstUnsupported right.firstUnsupported := rfl

@[simp] theorem firstUnsupported_udiv {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .uint) :
    Expr.firstUnsupported (parameters := parameters) (Engine.Expr.udiv left right) =
      Engine.firstSome left.firstUnsupported right.firstUnsupported := rfl

@[simp] theorem firstUnsupported_sdiv {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .sint) :
    Expr.firstUnsupported (parameters := parameters) (Engine.Expr.sdiv left right) =
      Engine.firstSome left.firstUnsupported right.firstUnsupported := rfl

@[simp] theorem firstUnsupported_urem {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .uint) :
    Expr.firstUnsupported (parameters := parameters) (Engine.Expr.urem left right) =
      Engine.firstSome left.firstUnsupported right.firstUnsupported := rfl

@[simp] theorem firstUnsupported_srem {target : Target} {parameters : List IntType}
    (left right : Expr target parameters .sint) :
    Expr.firstUnsupported (parameters := parameters) (Engine.Expr.srem left right) =
      Engine.firstSome left.firstUnsupported right.firstUnsupported := rfl

@[simp] theorem firstUnsupported_compare {target : Target} {parameters : List IntType}
    (operation : ComparisonOp) (kind : ArithmeticType)
    (left right : Expr target parameters kind.asIntType) :
    Expr.firstUnsupported (parameters := parameters) (Engine.Expr.compare operation kind left right) =
      Engine.firstSome left.firstUnsupported right.firstUnsupported := rfl

@[simp] theorem firstUnsupported_select {target : Target} {parameters : List IntType} {ty : IntType}
    (condition : Expr target parameters (.small .boolean)) (onTrue onFalse : Expr target parameters ty) :
    Expr.firstUnsupported (parameters := parameters) (Engine.Expr.select condition onTrue onFalse) =
      Engine.firstSome condition.firstUnsupported
        (Engine.firstSome onTrue.firstUnsupported onFalse.firstUnsupported) := rfl

@[simp] theorem firstUnsupported_unsupported {target : Target} {parameters : List IntType} {ty : IntType}
    (feature : UnsupportedFeature) :
    Expr.firstUnsupported (target := target) (parameters := parameters) (ty := ty)
      (Engine.Expr.unsupported feature) =
      some feature := rfl

end Expr
end EDSL.Source
