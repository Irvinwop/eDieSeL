/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Memory.Model

set_option autoImplicit false

namespace EDSL.Source.Memory

/-! Structural subobject queries for the existing type and payload tree. A path
may stop at a scalar, array, or root. These are mathematical shape witnesses;
they supply no object existence, coverage, access, or pointer validity claim. -/

/-- Unlike `ScalarPath`, a bounded path can stop at any node, including an array.
Raw zero/nested array types remain representable without expanding coverage. -/
inductive ObjectPath : ObjectType → ObjectType → Type where
  | here {object : ObjectType} : ObjectPath object object
  | element {element object : ObjectType} {length : Nat}
      (index : Fin length) (tail : ObjectPath element object) :
      ObjectPath (.array element length) object

def ObjectPath.indices {root object : ObjectType} :
    ObjectPath root object → SubobjectPath
  | .here => []
  | .element index tail => index.val :: tail.indices

/-- Resolve an actual subobject shape. Empty indices select the whole root;
every consumed index must be strictly below the corresponding array length.
In particular the exact one-past index does not designate a subobject. -/
def ObjectType.objectAt : ObjectType → SubobjectPath → Option ObjectType
  | object, [] => some object
  | .scalar _, _ :: _ => none
  | .array element length, index :: rest =>
      if index < length then element.objectAt rest else none

@[simp] theorem ObjectType.objectAt_nil (object : ObjectType) :
    object.objectAt [] = some object := by
  cases object <;> rfl

@[simp] theorem ObjectType.objectAt_scalar_cons (kind : ScalarType)
    (index : Nat) (rest : SubobjectPath) :
    (ObjectType.scalar kind).objectAt (index :: rest) = none := rfl

theorem ObjectType.objectAt_array_outOfBounds
    (element : ObjectType) (length index : Nat) (rest : SubobjectPath)
    (outside : length ≤ index) :
    (ObjectType.array element length).objectAt (index :: rest) = none := by
  simp only [objectAt, Nat.not_lt.mpr outside, ↓reduceIte]

@[simp] theorem ObjectType.objectAt_array_onePast
    (element : ObjectType) (length : Nat) (rest : SubobjectPath) :
    (ObjectType.array element length).objectAt (length :: rest) = none :=
  objectAt_array_outOfBounds element length length rest (Nat.le_refl _)

theorem ObjectPath.objectAt_indices {root object : ObjectType}
    (path : ObjectPath root object) : root.objectAt path.indices = some object := by
  induction path with
  | here => exact ObjectType.objectAt_nil _
  | element index tail ih =>
      simpa only [indices, ObjectType.objectAt, index.isLt, ↓reduceIte] using ih

theorem ObjectType.objectAt_complete (root : ObjectType) (indices : SubobjectPath)
    (object : ObjectType) (found : root.objectAt indices = some object) :
    ∃ path : ObjectPath root object, path.indices = indices := by
  match root, indices with
  | .scalar _, [] | .array _ _, [] =>
      cases found
      exact ⟨.here, rfl⟩
  | .scalar _, _ :: _ => cases found
  | .array element length, index :: rest =>
      by_cases inside : index < length
      · simp only [objectAt, inside, ↓reduceIte] at found
        obtain ⟨tail, same⟩ := element.objectAt_complete rest object found
        exact ⟨.element ⟨index, inside⟩ tail, congrArg (List.cons index) same⟩
      · simp only [objectAt, inside, ↓reduceIte] at found
        cases found

/-- Exact success contract against independently bounded typed paths. -/
theorem ObjectType.objectAt_eq_some_iff (root : ObjectType) (indices : SubobjectPath)
    (object : ObjectType) :
    root.objectAt indices = some object ↔
      ∃ path : ObjectPath root object, path.indices = indices := by
  constructor
  · exact root.objectAt_complete indices object
  · rintro ⟨path, rfl⟩
    exact path.objectAt_indices

theorem ObjectPath.indices_injective {root object : ObjectType} :
    Function.Injective (@ObjectPath.indices root object) := by
  intro first
  induction first with
  | here =>
      intro second same
      cases second with
      | here => rfl
      | element _ _ => cases same
  | element index tail ih =>
      intro second same
      cases second with
      | here => cases same
      | element other otherTail =>
          have heads := (List.cons.inj same).1
          have tails := (List.cons.inj same).2
          have equalIndex : index = other := Fin.ext heads
          cases equalIndex
          have equalTail := ih tails
          cases equalTail
          rfl

theorem ObjectPath.type_eq_of_indices_eq {root firstType secondType : ObjectType}
    (first : ObjectPath root firstType) (second : ObjectPath root secondType)
    (same : first.indices = second.indices) : firstType = secondType := by
  apply Option.some.inj
  calc
    some firstType = root.objectAt first.indices := first.objectAt_indices.symm
    _ = root.objectAt second.indices := congrArg root.objectAt same
    _ = some secondType := second.objectAt_indices

theorem ObjectPath.heq_of_indices_eq {root firstType secondType : ObjectType}
    (first : ObjectPath root firstType) (second : ObjectPath root secondType)
    (same : first.indices = second.indices) : HEq first second := by
  have types := first.type_eq_of_indices_eq second same
  cases types
  exact heq_of_eq (indices_injective same)

/-- Composition preserves every raw index, including paths stopping at arrays. -/
def ObjectPath.append {root middle object : ObjectType}
    (first : ObjectPath root middle) (second : ObjectPath middle object) :
    ObjectPath root object :=
  match first with
  | .here => second
  | .element index tail => .element index (tail.append second)

@[simp] theorem ObjectPath.indices_append {root middle object : ObjectType}
    (first : ObjectPath root middle) (second : ObjectPath middle object) :
    (first.append second).indices = first.indices ++ second.indices := by
  induction first with
  | here => rfl
  | element index tail ih => simp only [append, indices, ih, List.cons_append]

def ScalarPath.toObjectPath {root : ObjectType} {kind : ScalarType} :
    ScalarPath root kind → ObjectPath root (.scalar kind)
  | .scalar => .here
  | .element index tail => .element index tail.toObjectPath

def ObjectPath.toScalarPath {root : ObjectType} {kind : ScalarType}
    (path : ObjectPath root (.scalar kind)) : ScalarPath root kind := by
  cases root with
  | scalar rootKind =>
      cases path with
      | here => exact .scalar
  | array element length =>
      cases path with
      | element index tail => exact .element index tail.toScalarPath

@[simp] theorem ScalarPath.indices_toObjectPath {root : ObjectType} {kind : ScalarType}
    (path : ScalarPath root kind) : path.toObjectPath.indices = path.indices := by
  induction path with
  | scalar => rfl
  | element index tail ih => simp only [toObjectPath, ObjectPath.indices, indices, ih]

@[simp] theorem ObjectPath.indices_toScalarPath {root : ObjectType} {kind : ScalarType}
    (path : ObjectPath root (.scalar kind)) : path.toScalarPath.indices = path.indices := by
  cases root with
  | scalar rootKind => cases path; rfl
  | array element length =>
      cases path with
      | element index tail =>
          change index.val :: tail.toScalarPath.indices = index.val :: tail.indices
          exact congrArg (List.cons index.val) tail.indices_toScalarPath

@[simp] theorem ScalarPath.toScalarPath_toObjectPath {root : ObjectType} {kind : ScalarType}
    (path : ScalarPath root kind) : path.toObjectPath.toScalarPath = path := by
  apply ScalarPath.indices_injective
  simp only [ObjectPath.indices_toScalarPath, indices_toObjectPath]

@[simp] theorem ObjectPath.toObjectPath_toScalarPath {root : ObjectType} {kind : ScalarType}
    (path : ObjectPath root (.scalar kind)) : path.toScalarPath.toObjectPath = path := by
  apply ObjectPath.indices_injective
  simp only [ScalarPath.indices_toObjectPath, indices_toScalarPath]

/-- Whole arrays are valid structural endpoints; the old scalar query still
requires a scalar endpoint and agrees exactly there, without reinterpreting it. -/
theorem ObjectType.objectAt_scalar_iff (root : ObjectType) (indices : SubobjectPath)
    (kind : ScalarType) :
    root.objectAt indices = some (.scalar kind) ↔ root.scalarAt indices = some kind := by
  constructor
  · intro found
    obtain ⟨path, rfl⟩ := root.objectAt_complete indices (.scalar kind) found
    simpa only [ObjectPath.indices_toScalarPath] using path.toScalarPath.scalarAt_indices
  · intro found
    obtain ⟨path, rfl⟩ := root.scalarAt_complete indices kind found
    simpa only [ScalarPath.indices_toObjectPath] using path.toObjectPath.objectAt_indices

/-- Start offset in supplied C bytes, with the size of the entire element as
array stride. This calculation says nothing about addresses or representations. -/
def ObjectPath.offsetBytes {target : Target} (layout : StorageLayout target)
    {root object : ObjectType} : ObjectPath root object → Nat
  | .here => 0
  | .element (element := elementType) index tail =>
      index.val * elementType.sizeBytes layout + tail.offsetBytes layout

theorem ObjectPath.offsetBytes_append {target : Target} (layout : StorageLayout target)
    {root middle object : ObjectType} (first : ObjectPath root middle)
    (second : ObjectPath middle object) :
    (first.append second).offsetBytes layout =
      first.offsetBytes layout + second.offsetBytes layout := by
  induction first with
  | here => exact (Nat.zero_add _).symm
  | element index tail ih =>
      simp only [append, offsetBytes, ih, Nat.add_assoc]

/-- Generic half-open extent bound. It also holds for raw zero-size arrays;
strict interior bounds require positive endpoint size as an explicit premise. -/
theorem ObjectPath.extent_bound {target : Target} (layout : StorageLayout target)
    {root object : ObjectType} (path : ObjectPath root object) :
    path.offsetBytes layout + object.sizeBytes layout ≤ root.sizeBytes layout := by
  induction path with
  | here => exact Nat.le_of_eq (Nat.zero_add _)
  | @element element object length index tail ih =>
      change (index.val * element.sizeBytes layout + tail.offsetBytes layout) +
        object.sizeBytes layout ≤ length * element.sizeBytes layout
      calc
        (index.val * element.sizeBytes layout + tail.offsetBytes layout) +
            object.sizeBytes layout =
            index.val * element.sizeBytes layout +
              (tail.offsetBytes layout + object.sizeBytes layout) := Nat.add_assoc _ _ _
        _ ≤ index.val * element.sizeBytes layout + element.sizeBytes layout :=
          Nat.add_le_add_left ih _
        _ = (index.val + 1) * element.sizeBytes layout := by
          rw [Nat.add_mul, Nat.one_mul]
        _ ≤ length * element.sizeBytes layout :=
          Nat.mul_le_mul_right _ index.isLt

theorem ObjectPath.start_bound {target : Target} (layout : StorageLayout target)
    {root object : ObjectType} (path : ObjectPath root object) :
    path.offsetBytes layout ≤ root.sizeBytes layout := by
  have bound := path.extent_bound layout
  omega

theorem ObjectPath.start_lt_of_positive {target : Target} (layout : StorageLayout target)
    {root object : ObjectType} (path : ObjectPath root object)
    (positive : 0 < object.sizeBytes layout) :
    path.offsetBytes layout < root.sizeBytes layout := by
  have bound := path.extent_bound layout
  omega

/-- Any mathematical frame lying within the selected subobject lies within
the root after translation. No memory-access or byte-read operation is defined. -/
theorem ObjectPath.frame_bound {target : Target} (layout : StorageLayout target)
    {root object : ObjectType} (path : ObjectPath root object) (start length : Nat)
    (inside : start + length ≤ object.sizeBytes layout) :
    path.offsetBytes layout + start + length ≤ root.sizeBytes layout := by
  have bound := path.extent_bound layout
  omega

theorem ObjectPath.extent_le_sizeMax {target : Target} (layout : StorageLayout target)
    {root object : ObjectType} (path : ObjectPath root object)
    (fits : root.sizeBytes layout ≤ layout.sizeMax) :
    path.offsetBytes layout + object.sizeBytes layout ≤ layout.sizeMax :=
  Nat.le_trans (path.extent_bound layout) fits

/-- Sibling subtree extents are ordered even for nested or zero-size raw types.
Equality of offsets is therefore not a path or object identity criterion. -/
theorem ObjectPath.sibling_extents {target : Target} (layout : StorageLayout target)
    {element firstType secondType : ObjectType} {length : Nat}
    (firstIndex secondIndex : Fin length) (before : firstIndex.val < secondIndex.val)
    (first : ObjectPath element firstType) (second : ObjectPath element secondType) :
    (ObjectPath.element firstIndex first).offsetBytes layout + firstType.sizeBytes layout ≤
      (ObjectPath.element secondIndex second).offsetBytes layout := by
  have bound := first.extent_bound layout
  have ordered : (firstIndex.val + 1) * element.sizeBytes layout ≤
      secondIndex.val * element.sizeBytes layout := Nat.mul_le_mul_right _ before
  rw [Nat.add_mul, Nat.one_mul] at ordered
  simp only [offsetBytes]
  omega

theorem ObjectType.alignmentBytes_positive {target : Target} (layout : StorageLayout target)
    (object : ObjectType) : 0 < object.alignmentBytes layout := by
  match object with
  | .scalar kind => exact (kind.layout layout).alignmentPositive
  | .array element _ => exact element.alignmentBytes_positive layout

theorem ObjectType.alignmentBytes_dvd_sizeBytes {target : Target}
    (layout : StorageLayout target) (object : ObjectType) :
    object.alignmentBytes layout ∣ object.sizeBytes layout := by
  match object with
  | .scalar kind => exact (kind.layout layout).alignmentDividesSize
  | .array element length =>
      obtain ⟨factor, same⟩ := element.alignmentBytes_dvd_sizeBytes layout
      refine ⟨length * factor, ?_⟩
      change length * element.sizeBytes layout =
        element.alignmentBytes layout * (length * factor)
      rw [same]
      exact Nat.mul_left_comm _ _ _

/-- Array descent preserves alignment under the supplied recursive layout. -/
theorem ObjectPath.alignmentBytes_eq {target : Target} (layout : StorageLayout target)
    {root object : ObjectType} (path : ObjectPath root object) :
    object.alignmentBytes layout = root.alignmentBytes layout := by
  induction path with
  | here => rfl
  | element index tail ih => exact ih

theorem ObjectPath.offsetBytes_aligned {target : Target} (layout : StorageLayout target)
    {root object : ObjectType} (path : ObjectPath root object) :
    root.alignmentBytes layout ∣ path.offsetBytes layout := by
  induction path with
  | here => exact Nat.dvd_zero _
  | @element element object length index tail ih =>
      obtain ⟨strideFactor, strideSame⟩ := element.alignmentBytes_dvd_sizeBytes layout
      obtain ⟨tailFactor, tailSame⟩ := ih
      refine ⟨index.val * strideFactor + tailFactor, ?_⟩
      change index.val * element.sizeBytes layout + tail.offsetBytes layout =
        element.alignmentBytes layout * (index.val * strideFactor + tailFactor)
      rw [strideSame, tailSame, Nat.mul_add, Nat.mul_left_comm index.val]

namespace Payload

/-- A projection of the same existing payload, with no new stored family and
no initialization, scalar-update interpreter, or source load operation. -/
def project {target : Target} {root object : ObjectType}
    (contents : Payload target root) (path : ObjectPath root object) : Payload target object :=
  match path with
  | .here => contents
  | .element index tail => project (contents index) tail

@[simp] theorem project_append {target : Target} {root middle object : ObjectType}
    (contents : Payload target root) (first : ObjectPath root middle)
    (second : ObjectPath middle object) :
    project contents (first.append second) = project (project contents first) second := by
  induction first with
  | here => rfl
  | element index tail ih => exact ih (contents := contents index) second

/-- The existing scalar lookup remains authoritative at every scalar endpoint. -/
@[simp] theorem project_toObjectPath {target : Target} {root : ObjectType} {kind : ScalarType}
    (contents : Payload target root) (path : ScalarPath root kind) :
    project contents path.toObjectPath = lookup contents path := by
  induction path with
  | scalar => rfl
  | element index tail ih => exact ih (contents := contents index)

theorem project_scalar {target : Target} {root : ObjectType} {kind : ScalarType}
    (contents : Payload target root) (path : ObjectPath root (.scalar kind)) :
    project contents path = lookup contents path.toScalarPath := by
  rw [← project_toObjectPath contents path.toScalarPath,
    ObjectPath.toObjectPath_toScalarPath]

/-- A scalar observation inside a projection is the existing root lookup along
the concatenated path. Values, absence, and every raw index are preserved. -/
theorem lookup_project {target : Target} {root object : ObjectType} {kind : ScalarType}
    (contents : Payload target root) (path : ObjectPath root object)
    (leaf : ScalarPath object kind) :
    lookup (project contents path) leaf =
      lookup contents (path.append leaf.toObjectPath).toScalarPath := by
  rw [← project_scalar, project_append, project_toObjectPath]

/-- Frame an entire selected subtree using the authoritative scalar update
law. The condition excludes every raw leaf path of that subtree. -/
theorem project_update_outside {target : Target} {root object : ObjectType}
    {writtenKind : ScalarType} (contents : Payload target root)
    (path : ObjectPath root object) (written : ScalarPath root writtenKind)
    (value : Option (ScalarValue target writtenKind))
    (outside : ∀ suffix : SubobjectPath, path.indices ++ suffix ≠ written.indices) :
    project (update contents written value) path = project contents path := by
  apply Payload.ext
  intro kind leaf
  rw [lookup_project, lookup_project]
  apply lookup_update_other
  simpa only [ObjectPath.indices_toScalarPath, ObjectPath.indices_append,
    ScalarPath.indices_toObjectPath] using outside leaf.indices

end Payload

end EDSL.Source.Memory
