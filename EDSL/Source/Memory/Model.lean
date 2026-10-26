/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Memory.Types

set_option autoImplicit false

namespace EDSL.Source.Memory

/-! Pure typed contents for one declared root. These operations are structural
tree lookup/replacement, not source loads/stores. There is deliberately no
State, registry, allocation, lifetime, ownership or expression evaluator here.
Integration must replace the contents of existing Objects.Object records and
retain the single existing State.objects registry. -/

/-- Each scalar leaf has its own optional typed value. `none` supplies no zero
value and does not classify any particular source indeterminate read. Arrays
have bounded children in the same contents tree, not separately owned roots. -/
def Payload (target : Target) : ObjectType → Type
  | .scalar kind => Option (ScalarValue target kind)
  | .array element length => Fin length → Payload target element

/-- A canonical scalar path; its indices are in bounds by construction. The
empty path selects a scalar root, and each array contributes exactly one step.
This makes neither a root exist nor its lifetime or permissions valid. -/
inductive ScalarPath : ObjectType → ScalarType → Type where
  | scalar {kind : ScalarType} : ScalarPath (.scalar kind) kind
  | element {object : ObjectType} {length : Nat} {kind : ScalarType}
      (index : Fin length) (tail : ScalarPath object kind) :
      ScalarPath (.array object length) kind

def ScalarPath.indices {object : ObjectType} {kind : ScalarType} :
    ScalarPath object kind → SubobjectPath
  | .scalar => []
  | .element index tail => index.val :: tail.indices

/-- Raw shape resolution checks bounds and requires a full scalar path.
An array root/subarray is not itself a scalar cell. -/
def ObjectType.scalarAt : ObjectType → SubobjectPath → Option ScalarType
  | .scalar kind, [] => some kind
  | .array element length, index :: rest =>
      if index < length then element.scalarAt rest else none
  | _, _ => none

@[simp] theorem ObjectType.scalarAt_array_outOfBounds
    (element : ObjectType) (length index : Nat) (rest : SubobjectPath)
    (outside : length ≤ index) :
    (ObjectType.array element length).scalarAt (index :: rest) = none := by
  simp only [scalarAt, Nat.not_lt.mpr outside, ↓reduceIte]

theorem ScalarPath.scalarAt_indices {object : ObjectType} {kind : ScalarType}
    (path : ScalarPath object kind) : object.scalarAt path.indices = some kind := by
  induction path with
  | scalar => rfl
  | element index tail ih =>
      simpa only [indices, ObjectType.scalarAt, index.isLt, ↓reduceIte] using ih

/-- Raw successful resolution has a bounded typed witness. This is a shape
fact only, independent of stored contents and source access checks. -/
theorem ObjectType.scalarAt_complete (object : ObjectType) (indices : SubobjectPath)
    (kind : ScalarType) (found : object.scalarAt indices = some kind) :
    ∃ path : ScalarPath object kind, path.indices = indices := by
  match object, indices with
  | .scalar leafKind, [] =>
      cases found
      exact ⟨.scalar, rfl⟩
  | .scalar _, _ :: _ => cases found
  | .array _ _, [] => cases found
  | .array element length, index :: rest =>
      by_cases inside : index < length
      · simp only [scalarAt, inside, ↓reduceIte] at found
        obtain ⟨tail, same⟩ := element.scalarAt_complete rest kind found
        exact ⟨.element ⟨index, inside⟩ tail, congrArg (List.cons index) same⟩
      · simp only [scalarAt, inside, ↓reduceIte] at found
        cases found

theorem ScalarPath.indices_injective {object : ObjectType} {kind : ScalarType} :
    Function.Injective (@ScalarPath.indices object kind) := by
  intro first
  induction first with
  | scalar =>
      intro second _
      cases second
      rfl
  | element index tail ih =>
      intro second same
      cases second with
      | element other otherTail =>
          have heads := (List.cons.inj same).1
          have tails := (List.cons.inj same).2
          have equalIndex : index = other := Fin.ext heads
          cases equalIndex
          have equalTail := ih tails
          cases equalTail
          rfl

theorem ScalarPath.kind_eq_of_indices_eq {object : ObjectType} {firstKind secondKind : ScalarType}
    (first : ScalarPath object firstKind) (second : ScalarPath object secondKind)
    (same : first.indices = second.indices) : firstKind = secondKind := by
  apply Option.some.inj
  calc
    some firstKind = object.scalarAt first.indices := first.scalarAt_indices.symm
    _ = object.scalarAt second.indices := congrArg object.scalarAt same
    _ = some secondKind := second.scalarAt_indices

/-- Canonical paths have no alternate typed identity for the same indices. -/
theorem ScalarPath.heq_of_indices_eq {object : ObjectType} {firstKind secondKind : ScalarType}
    (first : ScalarPath object firstKind) (second : ScalarPath object secondKind)
    (same : first.indices = second.indices) : HEq first second := by
  have kinds := first.kind_eq_of_indices_eq second same
  cases kinds
  exact heq_of_eq (indices_injective same)

namespace Payload

def lookup {target : Target} {object : ObjectType} {kind : ScalarType}
    (contents : Payload target object) (path : ScalarPath object kind) :
    Option (ScalarValue target kind) :=
  match path with
  | .scalar => contents
  | .element index tail => lookup (contents index) tail

def update {target : Target} {object : ObjectType} {kind : ScalarType}
    (contents : Payload target object) (path : ScalarPath object kind)
    (value : Option (ScalarValue target kind)) : Payload target object :=
  match path with
  | .scalar => value
  | .element index tail => fun query =>
      if query = index then update (contents index) tail value else contents query

/-- Scalar observations completely determine this one contents tree. No second
mutable representation is hidden behind the structural interface. -/
theorem ext {target : Target} {object : ObjectType}
    (first second : Payload target object)
    (same : ∀ (kind : ScalarType) (path : ScalarPath object kind),
      lookup first path = lookup second path) : first = second := by
  match object with
  | .scalar kind => exact same kind .scalar
  | .array element length =>
      funext index
      apply ext (first index) (second index)
      intro kind path
      exact same kind (.element index path)

@[simp] theorem lookup_update_same {target : Target} {object : ObjectType} {kind : ScalarType}
    (contents : Payload target object) (path : ScalarPath object kind)
    (value : Option (ScalarValue target kind)) :
    lookup (update contents path value) path = value := by
  induction path with
  | scalar => rfl
  | element index tail ih =>
      simpa only [lookup, update, ↓reduceIte] using ih (contents := contents index) value

/-- A same-root frame law for arbitrary scalar types and recursive raw shapes.
The paths, not just root identities, determine whether leaves overlap. -/
theorem lookup_update_other {target : Target} {object : ObjectType}
    {writtenKind readKind : ScalarType} (contents : Payload target object)
    (written : ScalarPath object writtenKind) (read : ScalarPath object readKind)
    (value : Option (ScalarValue target writtenKind))
    (different : read.indices ≠ written.indices) :
    lookup (update contents written value) read = lookup contents read := by
  induction written generalizing readKind with
  | scalar =>
      cases read
      exact (different rfl).elim
  | element index tail ih =>
      cases read with
      | element other otherTail =>
          by_cases same : other = index
          · cases same
            have tailDifferent : otherTail.indices ≠ tail.indices := by
              intro sameTail
              exact different (congrArg (List.cons index.val) sameTail)
            simpa only [lookup, update, ↓reduceIte] using
              ih (contents := contents index) otherTail value tailDifferent
          · simp only [lookup, update, same, ↓reduceIte]

theorem update_lookup {target : Target} {object : ObjectType} {kind : ScalarType}
    (contents : Payload target object) (path : ScalarPath object kind) :
    update contents path (lookup contents path) = contents := by
  induction path with
  | scalar => rfl
  | element index tail ih =>
      funext query
      by_cases same : query = index
      · cases same
        simpa only [lookup, update, ↓reduceIte] using ih (contents := contents index)
      · simp only [update, same, ↓reduceIte]

theorem update_overwrite {target : Target} {object : ObjectType} {kind : ScalarType}
    (contents : Payload target object) (path : ScalarPath object kind)
    (first second : Option (ScalarValue target kind)) :
    update (update contents path first) path second = update contents path second := by
  induction path with
  | scalar => rfl
  | element index tail ih =>
      funext query
      by_cases same : query = index
      · cases same
        simpa only [update, ↓reduceIte] using ih (contents := contents index) first second
      · simp only [update, same, ↓reduceIte]

/-- Exact embedding of the old optional full-int cell. No arithmetic map,
integer re-encoding or default initialization is involved. -/
def fullIntCell {target : Target} (kind : ArithmeticType)
    (value : Option (Value target kind.asIntType)) :
    Payload target (.scalar (.integer kind.asIntType)) := value

@[simp] theorem lookup_fullIntCell {target : Target} (kind : ArithmeticType)
    (value : Option (Value target kind.asIntType)) :
    lookup (fullIntCell kind value) .scalar = value := rfl

theorem fullIntCell_injective {target : Target} (kind : ArithmeticType) :
    Function.Injective (@fullIntCell target kind) := fun _ _ same => same

@[simp] theorem update_fullIntCell {target : Target} (kind : ArithmeticType)
    (before after : Option (Value target kind.asIntType)) :
    update (fullIntCell kind before) .scalar after = fullIntCell kind after := rfl

end Payload

/-- Shape plus one typed contents tree, for the contents field of a future
generalized existing object record. No lifecycle/authority state is duplicated. -/
structure RootPayload (target : Target) where
  type : ObjectType
  contents : Payload target type

def RootPayload.fullInt {target : Target} (kind : ArithmeticType)
    (value : Option (Value target kind.asIntType)) : RootPayload target where
  type := .scalar (.integer kind.asIntType)
  contents := Payload.fullIntCell kind value

end EDSL.Source.Memory
