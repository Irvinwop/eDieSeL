/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.Contracts
import EDSL.Source.Objects.Control.Frames

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.Checks
open StateSyntax
attribute [local implicit_reducible] Value Target.modulus

/- Internal transition regressions. These make no source-standard C++26
forward-progress/yield, compiler, scope-cleanup or OS scheduling claim. -/
private def truth : Value Target.int32 (.small .boolean) := ⟨1, by decide +kernel⟩
private def one : Value Target.int32 .sint := ⟨1, by decide +kernel⟩
private def almostMax : Value Target.int32 .sint := ⟨2147483646, by decide +kernel⟩
private def maximum : Value Target.int32 .sint := ⟨2147483647, by decide +kernel⟩
private def bindings : Env [.sint] := .cons ⟨0⟩ .nil

private def initial : State Target.int32 [] Unit where
  inputs := .nil
  environment := ()
  actor := 0
  next := 1
  automaticSlots := 7
  objects := fun id => if id = 0 then some {
    kind := .sint, life := .live, reached := true, value := some almostMax,
    owner := 0, permissions := ⟨true, true⟩ } else none

private def incrementForever : Code Target.int32 [.sint] .sint :=
  .seq (.loop (.literal truth) (.assign .here (.sadd (.param .here) (.literal one))))
    (.ret (.param .here))

/-- Checking one accepted iteration is insufficient: the next guard/body reads
the updated object, overflows, and retains the first accepted write and trace.
No execution budget is converted into a source error or successful return. -/
theorem second_iteration_overflow :
    let afterOne := run .gnuC23 .gnuModulo bindings 3 (start incrementForever initial)
    let failed := run .gnuC23 .gnuModulo bindings 5 (start incrementForever initial)
    afterOne.status = .running ∧
    afterOne.state.objects 0 = some {
      kind := .sint, life := .live, reached := true, value := some maximum,
      owner := 0, permissions := ⟨true, true⟩ } ∧
    failed.status = .stopped (.scalar .signedAdditionOverflow) ∧
    failed.state = afterOne.state ∧
    failed.events = [.read 0 .sint 2147483646, .write 0 .sint 2147483647,
      .read 0 .sint 2147483647] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem first_iteration_does_not_establish_safety :
    ¬ NoFailure .gnuC23 .gnuModulo bindings (start incrementForever initial) := by
  intro safe
  exact safe 5 (.scalar .signedAdditionOverflow) second_iteration_overflow.2.2.1

/-- Coverage must inspect code following a divergent loop before any step,
rather than wait until execution happens to reach that code. -/
theorem unsupported_after_loop_preflight (state : State Target.int32 [] Unit) :
    let code : Code Target.int32 [] .sint :=
      .seq (.loop (.literal truth) .skip) (.unsupported .functionCall)
    (start code state).status = .stopped (.unsupported .functionCall) ∧
      (start code state).state = state ∧ (start code state).events = [] := by
  exact ⟨rfl, rfl, rfl⟩

/-- An unsupported marker in an unselected loop body is also a static refusal. -/
theorem unsupported_false_loop_preflight (state : State Target.int32 [] Unit) :
    let code : Code Target.int32 [] .sint :=
      .loop (.literal ⟨0, by decide +kernel⟩) (.unsupported .memoryAccess)
    (start code state).status = .stopped (.unsupported .memoryAccess) ∧
      (start code state).state = state ∧ (start code state).events = [] := by
  exact ⟨rfl, rfl, rfl⟩

end EDSL.Source.Objects.Control.Checks
