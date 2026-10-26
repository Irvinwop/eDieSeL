/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Types

set_option autoImplicit false

namespace EDSL.Source.Memory

/-! Raw type/value vocabulary for future integration into the existing source
object registry and expression core. Type construction is not source coverage,
pointer validity, object existence, or an implementation of a memory operation.
The grammar contains only unqualified types. -/

mutual
  inductive ScalarType where
    | integer (kind : IntType)
    | pointer (pointee : ObjectType)
    deriving DecidableEq, Repr

  inductive ObjectType where
    | scalar (kind : ScalarType)
    | array (element : ObjectType) (length : Nat)
    deriving DecidableEq, Repr
end

/-- Integer objects admitted as pointer targets by the initial shape profile.
Recursive type syntax does not admit recursive array or pointer shapes here. -/
def ObjectType.isIntegerObject : ObjectType → Bool
  | .scalar (.integer _) => true
  | .array (.scalar (.integer _)) length => decide (0 < length)
  | _ => false

def ScalarType.inC23Profile : ScalarType → Bool
  | .integer _ => true
  | .pointer pointee => pointee.isIntegerObject

/-- Shape coverage only: unqualified integer/pointer scalars and positive fixed
integer arrays. No qualifiers, nested arrays, pointer arrays or pointer chains.
This does not certify execution of any source construct. -/
def ObjectType.inC23Profile : ObjectType → Bool
  | .scalar kind => kind.inC23Profile
  | .array (.scalar (.integer _)) length => decide (0 < length)
  | .array _ _ => false

@[simp] theorem ObjectType.zeroArray_not_inC23Profile (element : ObjectType) :
    (ObjectType.array element 0).inC23Profile = false := by
  cases element with
  | scalar kind => cases kind <;> rfl
  | array _ _ => rfl

/-- Canonical root-relative array indices. A raw path can be malformed; typed
storage paths and future registry validation establish that its steps exist. -/
abbrev SubobjectPath := List Nat

/-- An array domain is distinct from a standalone object's singleton domain.
The path names the governing object, not a bound copied into a pointer value.
For an array element pointer this retains the containing array association. -/
inductive PointerDomain where
  | singleton (path : SubobjectPath)
  | arrayElements (path : SubobjectPath)
  deriving DecidableEq, Repr

/-- Internal descriptor, not a machine address or a source expression.
`root` uses the existing registry's never-reused identity, including tombstones.
`displacement` is signed C bytes from the start of the governing domain.
Unknown roots, stale lifetimes and invalid offsets remain representable.
Domain shape, element type, extent, stride and lifetime must be checked against
the authoritative registry before any future source use. -/
structure PointerDescriptor where
  root : Nat
  domain : PointerDomain
  displacement : Int
  deriving DecidableEq, Repr

/-- Raw typed pointer data. The phantom pointee index is not a validity proof.
There is no source nonnull literal, integer-to-pointer map or address-forming
operation here. Registry/address contracts must justify future origins. -/
inductive PointerValue (pointee : ObjectType) where
  | null
  | object (descriptor : PointerDescriptor)
  deriving DecidableEq, Repr

/-- Integer values are definitionally the old Value family, with no wrapper,
arithmetic, truncation, alternate range or pointer-to-integer encoding. -/
def ScalarValue (target : Target) : ScalarType → Type
  | .integer kind => Value target kind
  | .pointer pointee => PointerValue pointee

instance scalarValueDecidableEq (target : Target) (kind : ScalarType) :
    DecidableEq (ScalarValue target kind) := by
  cases kind <;> unfold ScalarValue <;> infer_instance

instance scalarValueRepr (target : Target) (kind : ScalarType) :
    Repr (ScalarValue target kind) := by
  cases kind <;> unfold ScalarValue <;> infer_instance

namespace ScalarValue

def integer {target : Target} {kind : IntType} (value : Value target kind) :
    ScalarValue target (.integer kind) := value

def toInteger {target : Target} {kind : IntType}
    (value : ScalarValue target (.integer kind)) : Value target kind := value

@[simp] theorem toInteger_integer {target : Target} {kind : IntType}
    (value : Value target kind) : (integer value).toInteger = value := rfl

@[simp] theorem integer_toInteger {target : Target} {kind : IntType}
    (value : ScalarValue target (.integer kind)) : integer value.toInteger = value := rfl

theorem integer_injective {target : Target} {kind : IntType} :
    Function.Injective (@integer target kind) := fun _ _ same => same

/-- Reuse the existing range theorem at the new integer scalar index. -/
theorem integer_range {target : Target} {kind : IntType}
    (value : ScalarValue target (.integer kind)) :
    kind.lowerBound target ≤ value.toInteger.toInt ∧
      value.toInteger.toInt < kind.upperBound target := Value.range value

end ScalarValue

/-- A supplied scalar storage contract in C bytes. Power-of-two alignment is
explicit; complete scalar size is positive and a multiple of its alignment.
This is not a physical address, numeric value width or executable ABI. -/
structure ScalarLayout where
  sizeBytes : Nat
  sizePositive : 0 < sizeBytes
  alignmentExponent : Nat
  alignmentDividesSize : 2 ^ alignmentExponent ∣ sizeBytes

def ScalarLayout.alignmentBytes (layout : ScalarLayout) : Nat :=
  2 ^ layout.alignmentExponent

theorem ScalarLayout.alignmentPositive (layout : ScalarLayout) :
    0 < layout.alignmentBytes := Nat.two_pow_pos _

/-- Every mathematical array element displacement respects its scalar stride's
alignment. This is a layout law, not a source address-validity operation. -/
theorem ScalarLayout.elementOffsetAligned (layout : ScalarLayout) (index : Nat) :
    layout.alignmentBytes ∣ index * layout.sizeBytes := by
  obtain ⟨factor, same⟩ := layout.alignmentDividesSize
  refine ⟨index * factor, ?_⟩
  change index * layout.sizeBytes = 2 ^ layout.alignmentExponent * (index * factor)
  rw [same]
  exact Nat.mul_left_comm _ _ _

/-- Numeric exponent used only for a lower bound on storage capacity. In
particular bool has exponent 1 but occupies a positive number of C bytes. -/
def integerRangeBits (target : Target) : IntType → Nat
  | .uint | .sint => target.intBits
  | .small kind => kind.rangeBits target

/-- Explicit layout assumptions, separate from Target's numeric ranges.
Character size is one C byte; no equation sets a C byte to eight bits.
Signed/unsigned counterparts share size and alignment. Pointer layouts are
supplied separately and need not equal any integer layout. `sizeMax` is an
independent SIZE_MAX bound, not an alias for uint or a resource budget.
Representations, padding, byte order and source sizeof/alignof remain absent. -/
structure StorageLayout (target : Target) where
  integer : IntType → ScalarLayout
  pointer : ObjectType → ScalarLayout
  sizeMax : Nat
  integerBounded : ∀ kind, (integer kind).sizeBytes ≤ sizeMax
  pointerBounded : ∀ pointee, (pointer pointee).sizeBytes ≤ sizeMax
  integerFits : ∀ kind,
    integerRangeBits target kind ≤ (integer kind).sizeBytes * target.charBits
  plainCharBytes : (integer (.small .plainChar)).sizeBytes = 1
  signedCharBytes : (integer (.small .schar)).sizeBytes = 1
  unsignedCharBytes : (integer (.small .uchar)).sizeBytes = 1
  intPairSize : (integer .sint).sizeBytes = (integer .uint).sizeBytes
  intPairAlignment : (integer .sint).alignmentBytes = (integer .uint).alignmentBytes
  shortPairSize : (integer (.small .sshort)).sizeBytes = (integer (.small .ushort)).sizeBytes
  shortPairAlignment :
    (integer (.small .sshort)).alignmentBytes = (integer (.small .ushort)).alignmentBytes

def StorageLayout.bitsPerByte {target : Target} (_ : StorageLayout target) : Nat :=
  target.charBits

theorem StorageLayout.bitsPerByte_atLeast8 {target : Target}
    (layout : StorageLayout target) : 8 ≤ layout.bitsPerByte := target.charAtLeast8

theorem StorageLayout.sizeMaxPositive {target : Target} (layout : StorageLayout target) :
    0 < layout.sizeMax := by
  have bound := layout.integerBounded (.small .uchar)
  rw [layout.unsignedCharBytes] at bound
  omega

def ScalarType.layout {target : Target} (profile : StorageLayout target) :
    ScalarType → ScalarLayout
  | .integer kind => profile.integer kind
  | .pointer pointee => profile.pointer pointee

/-- Mathematical extent for raw grammar. Zero-size arrays and sizes beyond
SIZE_MAX can be described here; coverage separately rejects them. -/
def ObjectType.sizeBytes {target : Target} (profile : StorageLayout target) : ObjectType → Nat
  | .scalar kind => (kind.layout profile).sizeBytes
  | .array element length => length * element.sizeBytes profile

def ObjectType.alignmentBytes {target : Target} (profile : StorageLayout target) :
    ObjectType → Nat
  | .scalar kind => (kind.layout profile).alignmentBytes
  | .array element _ => element.alignmentBytes profile

/-- The initial shape profile allows only integer scalar/array pointees, so a
single extra extent check covers all complete pointee shapes it can admit.
This predicate alone does not admit broader recursive pointer types. -/
def ObjectType.directPointeeFits {target : Target} (profile : StorageLayout target) :
    ObjectType → Bool
  | .scalar (.pointer pointee) => decide (pointee.sizeBytes profile ≤ profile.sizeMax)
  | _ => true

theorem ObjectType.profile_sizePositive {target : Target} (layout : StorageLayout target)
    (kind : ObjectType) (covered : kind.inC23Profile = true) :
    0 < kind.sizeBytes layout := by
  cases kind with
  | scalar scalar => exact (scalar.layout layout).sizePositive
  | array element length =>
      cases element with
      | scalar scalar =>
          cases scalar with
          | integer kind =>
              have positive : 0 < length := of_decide_eq_true covered
              exact Nat.mul_pos positive (layout.integer kind).sizePositive
          | pointer _ => cases covered
      | array _ _ => cases covered

/-- Data-type/layout coverage, not an execution coverage gate. C++ memory rules
are unimplemented. Old scalar APIs do not consult or change under this gate. -/
def typeCovered {target : Target} (dialect : Dialect) (layout : StorageLayout target)
    (kind : ObjectType) : Bool :=
  dialect == .gnuC23 && kind.inC23Profile && decide (kind.sizeBytes layout ≤ layout.sizeMax)
    && kind.directPointeeFits layout

@[simp] theorem cpp_typeCovered {target : Target} (layout : StorageLayout target)
    (kind : ObjectType) : typeCovered .gnuCpp26 layout kind = false := rfl

theorem covered_size {target : Target} (layout : StorageLayout target) (kind : ObjectType)
    (covered : typeCovered .gnuC23 layout kind = true) :
    0 < kind.sizeBytes layout ∧ kind.sizeBytes layout ≤ layout.sizeMax := by
  simp only [typeCovered, beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
    decide_eq_true_eq] at covered
  exact ⟨kind.profile_sizePositive layout covered.1.1, covered.1.2⟩

end EDSL.Source.Memory
