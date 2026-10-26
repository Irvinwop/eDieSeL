/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.ExpressionVC
set_option autoImplicit false
open EDSL.Source EDSL.Source.Objects EDSL.Source.Objects.StateSyntax
namespace EDSL.Source.Objects.ExpressionVCChecks

private def u7 : Value Target.int32 .uint := ⟨7, by decide +kernel⟩
private def u11 : Value Target.int32 .uint := ⟨11, by decide +kernel⟩
private def u5 : Value Target.int32 .uint := ⟨5, by decide +kernel⟩
private def u0 : Value Target.int32 .uint := ⟨0, by decide +kernel⟩
private def initial : State Target.int32 [.uint] Nat where
  inputs := .cons ⟨99, by decide +kernel⟩ .nil
  environment := 23
  actor := 2
  next := 10
  automaticSlots := 6
  objects := fun id => if id = 3 then some {
    kind := .uint, life := .live, reached := true, value := some u7,
    owner := 2, permissions := ⟨true, true⟩ }
    else if id = 9 then some {
      kind := .uint, life := .live, reached := true, value := some u11,
      owner := 2, permissions := ⟨true, true⟩ } else none
private def environment : Env [.uint, .uint] := .cons ⟨3⟩ (.cons ⟨9⟩ .nil)
private def badEnvironment : Env [.uint, .uint] := .cons ⟨3⟩ (.cons ⟨404⟩ .nil)
private theorem canRead7 : CanLoad initial (⟨3⟩ : LValue .uint) u7 :=
  ⟨⟨true, true⟩, rfl, rfl⟩
private theorem canRead11 : CanLoad initial (⟨9⟩ : LValue .uint) u11 :=
  ⟨⟨true, true⟩, rfl, rfl⟩
private def sum : RHS Target.int32 [.uint, .uint] .uint :=
  .uadd (.param .here) (.param (.there .here))

-- Arithmetic reads current objects (7+11), not immutable inputs (99), and
-- retains the complete original state and ordered actual read observations.
theorem currentObjects : ExpressionVC.vcExpr .gnuModulo environment sum
    (fun original value final events => value.toInt = 18 ∧ final = original ∧
      events = [.read 3 .uint 7, .read 9 .uint 11]) initial := by
  change ∃ x, CanLoad initial (⟨3⟩ : LValue .uint) x ∧
    ∃ y, CanLoad initial (⟨9⟩ : LValue .uint) y ∧ _
  exact ⟨u7, canRead7, u11, canRead11, by decide +kernel, rfl, rfl⟩

-- Exercise the public exactness theorem on the independently specified result.
theorem currentObjectsActual (dialect : Dialect) : ∃ value final events,
    StateEval.evalExpr dialect .gnuModulo environment sum initial = (.ok value, final, events) ∧
    value.toInt = 18 ∧ final = initial ∧ events = [.read 3 .uint 7, .read 9 .uint 11] :=
  (ExpressionVC.vcExpr_iff dialect .gnuModulo environment sum _ initial).mp currentObjects

private def lazyRead (selectBad : Bool) : RHS Target.int32 [.uint, .uint] .uint :=
  .select (.literal (if selectBad then ⟨1, by decide +kernel⟩ else ⟨0, by decide +kernel⟩))
    (.param (.there .here)) (.uadd (.param .here) (.literal u5))

-- An unselected unknown object imposes no condition and emits no read event.
theorem skippedUnknown : ExpressionVC.vcExpr .gnuModulo badEnvironment (lazyRead false)
    (fun original value final events => value.toInt = 12 ∧ final = original ∧
      events = [.read 3 .uint 7]) initial := by
  change ∃ x, CanLoad initial (⟨3⟩ : LValue .uint) x ∧ _
  exact ⟨u7, canRead7, by decide +kernel, rfl, rfl⟩

-- Selecting the same object must reject, even for the trivial postcondition.
theorem demandedUnknown : ¬ ExpressionVC.vcExpr .gnuModulo badEnvironment (lazyRead true)
    (fun _ _ _ _ => True) initial := by
  change ¬ ∃ value, CanLoad initial (⟨404⟩ : LValue .uint) value ∧ True
  rintro ⟨_, ⟨_, registered, _⟩, _⟩
  cases registered

-- The condition itself performs a read. Reusing an object must produce both
-- reads, rather than caching or deduplicating observations across selection.
theorem repeatedDemand : ExpressionVC.vcExpr .gnuModulo environment
    (.select (.compare .eq .uint (.param .here) (.literal u7))
      (.param .here) (.udiv (.literal u7) (.literal u0)))
    (fun original value final events => value.toInt = 7 ∧ final = original ∧
      events = [.read 3 .uint 7, .read 3 .uint 7]) initial := by
  change ∃ x, CanLoad initial (⟨3⟩ : LValue .uint) x ∧ _
  refine ⟨u7, canRead7, ?_⟩
  change ∃ x, CanLoad initial (⟨3⟩ : LValue .uint) x ∧ _
  exact ⟨u7, canRead7, by decide +kernel, rfl, rfl⟩

private def uninitialized : State Target.int32 [.uint] Nat :=
  initial.putObject 9 {
    kind := .uint, life := .live, reached := true, value := none,
    owner := 2, permissions := ⟨true, true⟩ }

-- Actual failure identities and the accepted prefix survive an uninitialized
-- second read. C's UB and C++ erroneous production remain different Stops.
theorem cUninitialized : StateEval.evalExpr .gnuC23 .gnuModulo environment sum uninitialized =
    (.error (.undefined .uninitializedAutomaticRead), uninitialized, [.read 3 .uint 7]) := rfl
theorem cppUninitialized : StateEval.evalExpr .gnuCpp26 .gnuModulo environment sum uninitialized =
    (.error (.erroneous .uninitializedAutomaticRead), uninitialized, [.read 3 .uint 7]) := rfl
theorem rejectUninitialized : ¬ ExpressionVC.vcExpr .gnuModulo environment sum
    (fun _ _ _ _ => True) uninitialized := by
  intro condition
  exact ExpressionVC.no_failure_of_vcExpr .gnuCpp26 .gnuModulo environment sum _ uninitialized
    condition (.erroneous .uninitializedAutomaticRead) uninitialized [.read 3 .uint 7]
    cppUninitialized

private def divisionByZero : RHS Target.int32 [.uint, .uint] .uint :=
  .udiv (.param .here) (.literal u0)
theorem scalarFailure (dialect : Dialect) :
    StateEval.evalExpr dialect .gnuModulo environment divisionByZero initial =
      (.error (.scalar .divisionByZero), initial, [.read 3 .uint 7]) := rfl
theorem rejectScalarFailure : ¬ ExpressionVC.vcExpr .gnuModulo environment divisionByZero
    (fun _ _ _ _ => True) initial := by
  intro condition
  exact ExpressionVC.no_failure_of_vcExpr .gnuC23 .gnuModulo environment divisionByZero _ initial
    condition (.scalar .divisionByZero) initial [.read 3 .uint 7] (scalarFailure .gnuC23)

-- Raw expression demand is separate from public whole-syntax coverage.
theorem skipUnsupported : ExpressionVC.vcExpr .gnuModulo environment
    (.select (.literal (ty := .small .boolean) ⟨0, by decide +kernel⟩)
      (.unsupported .memoryAccess) (.uadd (.param .here) (.literal u5)))
    (fun _ value _ events => value.toInt = 12 ∧ events = [.read 3 .uint 7]) initial := by
  change ∃ x, CanLoad initial (⟨3⟩ : LValue .uint) x ∧ _
  exact ⟨u7, canRead7, by decide +kernel, rfl⟩
theorem rejectUnsupported : ¬ ExpressionVC.vcExpr .gnuModulo environment
    (.uadd (.param .here) (.unsupported .memoryAccess)) (fun _ _ _ _ => True) initial := by
  intro condition
  exact ExpressionVC.no_failure_of_vcExpr .gnuC23 .gnuModulo environment _ _ initial
    condition (.unsupported .memoryAccess) initial [.read 3 .uint 7] rfl

-- The same carrier must also handle a real mutating operation: the following
-- load sees the store, its events follow the write, and other state is framed.
theorem storeThenLoad :
    ((ExpressionVC.ofEffect (EffectM.ofOp (store (⟨9⟩ : LValue .uint) u5)) >>= fun _ =>
      ExpressionVC.ofEffect (EffectM.ofOp (load .gnuCpp26 (⟨9⟩ : LValue .uint)))) :
      ExpressionVC.M Target.int32 [.uint] Nat (Value Target.int32 .uint))
    (fun value final events => value.toInt = 5 ∧
      final.objects 3 = initial.objects 3 ∧ final.environment = initial.environment ∧
      events = [.write 9 .uint 5, .read 9 .uint 5]) initial := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end EDSL.Source.Objects.ExpressionVCChecks
