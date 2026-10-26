/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Memory.Model

set_option autoImplicit false
set_option warningAsError true
namespace EDSL.Tests.SourceMemory
open EDSL.Source EDSL.Source.Memory

/- These are contracts of the raw typed contents layer, not implemented source
array operations. Nested arrays are intentionally outside its C23 shape profile.
The contents and values are arbitrary; no fixture assigns the expected result. -/
private abbrev Matrix (kind : ScalarType) (rows columns : Nat) : ObjectType :=
  .array (.array (.scalar kind) columns) rows

private def cell {kind : ScalarType} {rows columns : Nat}
    (row : Fin rows) (column : Fin columns) :
    ScalarPath (Matrix kind rows columns) kind :=
  .element row (.element column .scalar)

/-- Updating one nested-array leaf must preserve both an initialized same-row
sibling and an uninitialized different-row sibling, with no disjoint-root premise. -/
theorem nested_update_contract {target : Target} {kind : ScalarType} {rows columns : Nat}
    (contents : Payload target (Matrix kind rows columns))
    (row otherRow : Fin rows) (column otherColumn : Fin columns)
    (rowsDiffer : otherRow ≠ row) (columnsDiffer : otherColumn ≠ column)
    (oldValue replacement : ScalarValue target kind)
    (initialized : contents row otherColumn = some oldValue)
    (uninitialized : contents otherRow column = none) :
    let changed := Payload.update contents (cell row column) (some replacement)
    changed row column = some replacement ∧
      changed row otherColumn = some oldValue ∧
      changed otherRow column = none := by
  have selected := Payload.lookup_update_same contents (cell row column) (some replacement)
  have keptInitialized := Payload.lookup_update_other contents (cell row column)
    (cell row otherColumn) (some replacement) (by
      intro same
      have equalColumns : otherColumn.val = column.val :=
        (List.cons.inj (List.cons.inj same).2).1
      exact columnsDiffer (Fin.ext equalColumns))
  have keptUninitialized := Payload.lookup_update_other contents (cell row column)
    (cell otherRow column) (some replacement) (by
      intro same
      have equalRows : otherRow.val = row.val := (List.cons.inj same).1
      exact rowsDiffer (Fin.ext equalRows))
  exact ⟨selected, keptInitialized.trans initialized, keptUninitialized.trans uninitialized⟩

/-- Raw two-coordinate resolution succeeds exactly within the rectangular
bounds; the expected condition is independent of the resolver's control flow. -/
theorem matrix_resolution_iff (kind : ScalarType) (rows columns row column : Nat) :
    (Matrix kind rows columns).scalarAt [row, column] = some kind ↔
      row < rows ∧ column < columns := by
  by_cases rowInside : row < rows <;> by_cases columnInside : column < columns <;>
    simp [ObjectType.scalarAt, rowInside, columnInside]

/-- A well-bounded prefix naming an array and an overspecified scalar path are
both rejected. In-bounds indices do not excuse a malformed path shape. -/
theorem malformed_paths_rejected (kind : ScalarType) {rows columns : Nat}
    (row : Fin rows) (column : Fin columns) (extra : Nat) :
    (Matrix kind rows columns).scalarAt [row.val] = none ∧
      (Matrix kind rows columns).scalarAt [row.val, column.val, extra] = none ∧
      (ObjectType.scalar kind).scalarAt [extra] = none := by
  simp [ObjectType.scalarAt, row.isLt, column.isLt]

/-- Exactly one-past is already out of bounds for storage leaf resolution,
independently in either dimension; this does not forbid pointer formation. -/
theorem one_past_leaf_rejected (kind : ScalarType) {rows columns : Nat}
    (row : Fin rows) (column : Fin columns) :
    (Matrix kind rows columns).scalarAt [rows, column.val] = none ∧
      (Matrix kind rows columns).scalarAt [row.val, columns] = none := by
  simp [ObjectType.scalarAt, row.isLt]

/-- Generic nested payload laws must not silently admit nested-array source
execution through the initial C23 data-type shape profile. -/
theorem raw_shape_does_not_admit_nested_arrays (kind : ScalarType) (rows columns : Nat) :
    (Matrix kind rows columns).inC23Profile = false := rfl

end EDSL.Tests.SourceMemory
