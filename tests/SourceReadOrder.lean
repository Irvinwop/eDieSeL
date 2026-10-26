/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.ReadOrder

set_option autoImplicit false
namespace EDSL.Source.Objects.ReadOrder.Checks

/-- Actual loads of an authorized but uninitialized object and a missing object
stop with different diagnostics in the two orders, for either dialect. The registry
conditions are independent of execution. This checks the boundary where a tempting
extension of successful commutation would erase the first failure's identity. -/
theorem failed_reads_keep_priority {target : Target} {parameters : List IntType}
    {Environment : Type} {firstKind secondKind : ArithmeticType} (dialect : Dialect)
    (state : State target parameters Environment) (uninitializedRef : LValue firstKind)
    (missingRef : LValue secondKind) (permissions : Permissions)
    (registered : state.objects uninitializedRef.id = some {
      kind := firstKind, life := .live, reached := true, value := none,
      owner := state.actor, permissions := permissions })
    (readable : permissions.readable = true) (missing : state.objects missingRef.id = none) :
    let first := EffectM.ofOp (load dialect uninitializedRef)
    let second := EffectM.ofOp (load dialect missingRef)
    (pair first second).run state = (.error (uninitializedRead dialect), state, []) ∧
    (pair second first).run state = (.error (.invalidBinding .unknownObject), state, []) ∧
    ¬ Related Prod.swap ((pair first second).run state) ((pair second first).run state) := by
  dsimp only
  have uninitializedFailed :=
    load_uninitialized dialect state uninitializedRef permissions registered readable
  have missingFailed : load dialect missingRef state =
      (.error (.invalidBinding .unknownObject), state, []) := by
    simp only [load, missing, Op.reject]
  have forward :
      (pair (EffectM.ofOp (load dialect uninitializedRef))
        (EffectM.ofOp (load dialect missingRef))).run state =
      (.error (uninitializedRead dialect), state, []) := by
    change Op.bind (load dialect uninitializedRef) (fun left =>
      Op.bind (load dialect missingRef) (fun right => Op.pure (left, right))) state = _
    simp only [Op.bind, uninitializedFailed]
  have backward :
      (pair (EffectM.ofOp (load dialect missingRef))
        (EffectM.ofOp (load dialect uninitializedRef))).run state =
      (.error (.invalidBinding .unknownObject), state, []) := by
    change Op.bind (load dialect missingRef) (fun right =>
      Op.bind (load dialect uninitializedRef) (fun left => Op.pure (right, left))) state = _
    simp only [Op.bind, missingFailed]
  refine ⟨forward, backward, ?_⟩
  rw [forward, backward]
  intro related
  have sameDiagnostic := related.1
  cases dialect <;> cases sameDiagnostic

end EDSL.Source.Objects.ReadOrder.Checks

/- Transitive theorem dependency audit; these commands add no assumptions. -/
#print axioms EDSL.Source.Objects.load_contract
#print axioms EDSL.Source.Objects.ReadOrder.bind_error_left
#print axioms EDSL.Source.Objects.ReadOrder.bind_error_right
#print axioms EDSL.Source.Objects.ReadOrder.commute_success
#print axioms EDSL.Source.Objects.ReadOrder.load_load_diamond
#print axioms EDSL.Source.Objects.ReadOrder.load_load_alias
#print axioms EDSL.Source.Objects.ReadOrder.Checks.failed_reads_keep_priority
