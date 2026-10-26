/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.FunctionVC

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.FunctionVC.FailureValidation
open StateSyntax LifecycleContracts

/- Synthetic active-frame regressions. Arbitrary caller state/history is kept.
The duplicated cleanup plan deliberately lies outside the successful-entry
invariant; it checks the wrapper's exact failure carrier on malformed frames.
No raw observer/run normalization or execution oracle is used. -/

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable (dialect : Dialect) (policy : IntegerConversionPolicy)

private def writeThenRead (value : Value target .uint) : Stmt target [.uint] .uint :=
  .set .here (.literal value) (.ret (.param .here))

private def wrapper (value : Value target .uint) : Function target [] .uint :=
  ⟨dialect, policy, .body (.ret (.literal value))⟩

private def singleEntry (ref : LValue .uint) (value : Value target .uint) :
    FunctionEntry target [] .uint :=
  ⟨⟨[.uint], .cons ref .nil, Code.ofStmt (writeThenRead value)⟩,
    .nil, [.uint], .cons ref .nil⟩

private def duplicateEntry (ref : LValue .uint) (value : Value target .uint) :
    FunctionEntry target [] .uint :=
  { singleEntry ref value with localKinds := [.uint, .uint], localBindings := .cons ref (.cons ref .nil) }

/-- A permitted write followed by a denied read keeps the write and the live
object. Normal cleanup must not run on this body failure. -/
theorem retained_body_failure (state : State target parameters Environment) (ref : LValue .uint)
    (old : Option (Value target .uint)) (value : Value target .uint) (earlier : List Event)
    (registered : state.objects ref.id = some (liveObject .uint state.actor ⟨false, true⟩ old)) :
    ∃ steps, FunctionEval.observe (wrapper dialect policy value) steps
      (.active ⟨singleEntry ref value,
        startUnchecked (Code.ofStmt (writeThenRead value)) state earlier⟩) =
      .stopped (.denied .readPermission)
        (state.putObject ref.id (liveObject .uint state.actor ⟨false, true⟩ (some value)))
        (earlier ++ [.write ref.id .uint value.toInt]) := by
  let updated := state.putObject ref.id (liveObject .uint state.actor ⟨false, true⟩ (some value))
  have stored : store ref value state = (.ok (), updated, [.write ref.id .uint value.toInt]) := by
    simp [store, registered, liveObject, updated]
  have denied : load dialect ref updated = (.error (.denied .readPermission), updated, []) :=
    load_without_read_permission dialect updated ref _ (State.putObject_same state ref.id _) rfl rfl rfl rfl rfl
  have evaluated : StateEval.evalStmt dialect policy (.cons ref .nil) (writeThenRead value) state =
      (.error (.denied .readPermission), updated, [.write ref.id .uint value.toInt]) := by
    simp only [writeThenRead, StateEval.evalStmt, StateEval.evalExpr_literal, StateEval.evalExpr_var,
      Env.get_here, Op.bind, Op.pure, stored, denied, List.nil_append, List.append_nil]
  obtain ⟨steps, reached⟩ := FunctionEval.ofStmt_cleanup_reaches (wrapper dialect policy value)
    (singleEntry ref value) (writeThenRead value) rfl state earlier
  change _ = FunctionEval.settleResult (singleEntry ref value) earlier
    (StateEval.evalStmt dialect policy (.cons ref .nil) (writeThenRead value) state) at reached
  refine ⟨steps, ?_⟩
  rw [evaluated] at reached
  simpa only [FunctionEval.settleResult, singleEntry, updated] using reached

/-- The scalar is read successfully, then the duplicate plan ends one object
and fails on the second end. Only one slot is released and the return remains
stopped; all accepted write/read/end observations are retained in order. -/
theorem retained_cleanup_failure (state : State target parameters Environment) (ref : LValue .uint)
    (old : Option (Value target .uint)) (value : Value target .uint) (earlier : List Event)
    (registered : state.objects ref.id = some (liveObject .uint state.actor ⟨true, true⟩ old)) :
    ∃ steps, FunctionEval.observe (wrapper dialect policy value) steps
      (.active ⟨duplicateEntry ref value,
        startUnchecked (Code.ofStmt (writeThenRead value)) state earlier⟩) =
      .stopped (.invalidBinding .alreadyEnded)
        (endedState ref ⟨true, true⟩ (some value)
          (state.putObject ref.id (liveObject .uint state.actor ⟨true, true⟩ (some value))))
        (earlier ++ [.write ref.id .uint value.toInt, .read ref.id .uint value.toInt,
          .endLifetime ref.id .uint]) := by
  let updated := state.putObject ref.id (liveObject .uint state.actor ⟨true, true⟩ (some value))
  let final := endedState ref ⟨true, true⟩ (some value) updated
  have stored : store ref value state = (.ok (), updated, [.write ref.id .uint value.toInt]) := by
    simp [store, registered, liveObject, updated]
  have readable : CanLoad updated ref value := ⟨⟨true, true⟩, State.putObject_same state ref.id _, rfl⟩
  have loaded := load_contract dialect updated ref value readable
  have evaluated : StateEval.evalStmt dialect policy (.cons ref .nil) (writeThenRead value) state =
      (.ok value, updated, [.write ref.id .uint value.toInt, .read ref.id .uint value.toInt]) := by
    simp only [writeThenRead, StateEval.evalStmt, StateEval.evalExpr_literal, StateEval.evalExpr_var,
      Env.get_here, Op.bind, Op.pure, stored, loaded, List.nil_append, List.cons_append]
  have ended : endLifetime ref updated = (.ok (), final, [.endLifetime ref.id .uint]) :=
    endLifetime_eq ref updated ⟨true, true⟩ (some value) (State.putObject_same state ref.id _)
  have second : endLifetime ref final = (.error (.invalidBinding .alreadyEnded), final, []) :=
    endLifetime_alreadyEnded ref final _ (State.putObject_same updated ref.id _) rfl rfl
  have cleanup : FunctionEval.cleanup (duplicateEntry ref value) value updated =
      (.error (.invalidBinding .alreadyEnded), final, [.endLifetime ref.id .uint]) := by
    simp only [FunctionEval.cleanup, duplicateEntry, singleEntry, BlockEval.closeAll,
      Op.bind, Op.pure, ended, second, List.nil_append, List.append_nil]
  obtain ⟨steps, reached⟩ := FunctionEval.ofStmt_cleanup_reaches (wrapper dialect policy value)
    (duplicateEntry ref value) (writeThenRead value) rfl state earlier
  change _ = FunctionEval.settleResult (duplicateEntry ref value) earlier
    (StateEval.evalStmt dialect policy (.cons ref .nil) (writeThenRead value) state) at reached
  refine ⟨steps, ?_⟩
  rw [evaluated] at reached
  simp only [FunctionEval.settleResult, cleanup, List.append_assoc,
    List.cons_append, List.nil_append] at reached
  simpa only [duplicateEntry, singleEntry, final, updated] using reached

end EDSL.Source.Objects.Control.FunctionVC.FailureValidation
