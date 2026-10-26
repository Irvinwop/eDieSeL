/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Memory.Subobjects

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.SourceSubobjects

open Source Source.Memory

/- These contracts specify raw coordinate sets and observations of arbitrary
payloads. They do not compare fixture assignments or use a second interpreter. -/

/-- A rectangular scalar endpoint has exactly two in-bounds coordinates.
This independently excludes incomplete, overlong, and either one-past path. -/
theorem rectangular_scalar_coordinates (kind : ScalarType) (rows columns : Nat)
    (raw : SubobjectPath) :
    (ObjectType.array (.array (.scalar kind) columns) rows).objectAt raw =
        some (.scalar kind) ↔
      ∃ row column : Nat, raw = [row, column] ∧ row < rows ∧ column < columns := by
  constructor
  · intro found
    obtain ⟨path, same⟩ := ObjectType.objectAt_complete _ _ _ found
    cases path with
    | element row tail =>
        cases tail with
        | element column leaf =>
            cases leaf
            exact ⟨row.val, column.val, same.symm, row.isLt, column.isLt⟩
  · rintro ⟨row, column, rfl, rowBound, columnBound⟩
    exact (ObjectPath.element ⟨row, rowBound⟩
      (.element ⟨column, columnBound⟩ .here)).objectAt_indices

/-- The same raw tree also designates whole rows, with one coordinate. It does
not require a scalar endpoint or flatten a row into its first scalar leaf. -/
theorem rectangular_row_coordinates (kind : ScalarType) (rows columns : Nat)
    (raw : SubobjectPath) :
    (ObjectType.array (.array (.scalar kind) columns) rows).objectAt raw =
        some (.array (.scalar kind) columns) ↔
      ∃ row : Nat, raw = [row] ∧ row < rows := by
  constructor
  · intro found
    obtain ⟨path, same⟩ := ObjectType.objectAt_complete _ _ _ found
    cases path with
    | element row tail =>
        cases tail with
        | here => exact ⟨row.val, same.symm, row.isLt⟩
        | element _ leaf => cases leaf
  · rintro ⟨row, rfl, rowBound⟩
    exact (ObjectPath.element ⟨row, rowBound⟩ .here).objectAt_indices

/-- Successful queries on a raw zero array can only name that whole array. -/
theorem zero_array_only_root (element : ObjectType) (raw : SubobjectPath)
    (object : ObjectType)
    (found : (ObjectType.array element 0).objectAt raw = some object) :
    raw = [] ∧ object = .array element 0 := by
  obtain ⟨path, same⟩ := ObjectType.objectAt_complete _ _ _ found
  cases path with
  | here => exact ⟨same.symm, rfl⟩
  | element index _ => exact Fin.elim0 index

theorem zero_arrays_uncovered {target : Target} (dialect : Dialect)
    (layout : StorageLayout target) (element : ObjectType) :
    typeCovered dialect layout (.array element 0) = false := by
  cases dialect with
  | gnuC23 =>
      simp only [typeCovered, ObjectType.zeroArray_not_inC23Profile,
        Bool.and_false, Bool.false_and]
  | gnuCpp26 => exact cpp_typeCovered layout _

/-- Raw nested shapes in these contracts do not expand the shape profile. -/
theorem nested_arrays_uncovered {target : Target} (dialect : Dialect)
    (layout : StorageLayout target) (element : ObjectType) (outer inner : Nat) :
    typeCovered dialect layout (.array (.array element inner) outer) = false := by
  cases dialect with
  | gnuC23 => rfl
  | gnuCpp26 => exact cpp_typeCovered layout _

/-- For arbitrary contents and arbitrary scalar replacement, selecting a whole
sibling subtree observes exactly the same payload. This exercises the existing
scalar update, rather than replacing or mocking its behavior. -/
theorem sibling_payload_frame {target : Target} {element : ObjectType} {length : Nat}
    {kind : ScalarType} (contents : Payload target (.array element length))
    (selected written : Fin length) (different : selected ≠ written)
    (tail : ScalarPath element kind) (value : Option (ScalarValue target kind)) :
    Payload.project (Payload.update contents (.element written tail) value)
        (ObjectPath.element selected .here) =
      Payload.project contents (ObjectPath.element selected .here) := by
  apply Payload.project_update_outside
  intro suffix same
  change selected.val :: suffix = written.val :: tail.indices at same
  exact different (Fin.ext (List.cons.inj same).1)

/-- The existing scalar lookup gives the coordinate observation inside an
arbitrary row projection, including `none` and pointer-valued scalar leaves. -/
theorem row_scalar_observation {target : Target} {kind : ScalarType} {rows columns : Nat}
    (contents : Payload target (.array (.array (.scalar kind) columns) rows))
    (row : Fin rows) (column : Fin columns) :
    Payload.lookup (Payload.project contents (ObjectPath.element row .here))
        (.element column .scalar) =
      Payload.lookup contents (.element row (.element column .scalar)) := by
  exact Payload.lookup_project contents (ObjectPath.element row .here)
    (.element column .scalar)

end EDSL.Tests.SourceSubobjects
