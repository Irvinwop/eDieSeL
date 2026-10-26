/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.EntryContracts

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.EntryQuotaChecks
open StateSyntax LifecycleContracts BlockContracts ParameterContracts

variable {target : Target} {Environment : Type}

private def mixed (dialect : Dialect) (policy : IntegerConversionPolicy)
    (value : Value target .uint) : Function target [.sint, .uint] .uint :=
  ⟨dialect, policy, .declare .sint none
    (.declare .uint (some (.literal value)) (.body (.ret (.literal value))))⟩

/-- Shortage occurs in complete local reservation, before either initializer.
It retains both initialized parameters and one pending local, without inventing
an object at the exhausted identity or rolling accepted effects back. -/
theorem shortage_before_local_initializers (dialect : Dialect) (policy : IntegerConversionPolicy)
    (signed : Value target .sint) (unsigned value : Value target .uint)
    (environment : Environment) (actor : Nat) :
    let values : CallInputs target [.sint, .uint] := .cons signed (.cons unsigned .nil)
    let initial := State.empty values environment actor 3
    let function := mixed dialect policy value
    let events := parameterEvents dialect actor 0 values ++ reserveEvents dialect 2 .sint actor
    ∃ final,
      FunctionEval.enterUnchecked function values initial =
        (.error (.denied .automaticStorageExhausted), final, events) ∧
      FunctionEval.start function initial = .stopped (.denied .automaticStorageExhausted) final events ∧
      final.next = 3 ∧ final.automaticSlots = 0 ∧
      final.objects 0 = some (liveObject .sint actor ⟨true, true⟩ (some signed)) ∧
      final.objects 1 = some (liveObject .uint actor ⟨true, true⟩ (some unsigned)) ∧
      final.objects 2 = some (pendingObject dialect .sint actor ⟨true, true⟩) ∧
      final.objects 3 = none ∧
      load dialect (⟨2⟩ : LValue .sint) final =
        (.error (match dialect with
          | .gnuC23 => .invalidBinding .declarationNotReached
          | .gnuCpp26 => .undefined .outsideLifetime), final, []) := by
  dsimp only
  let values : CallInputs target [.sint, .uint] := .cons signed (.cons unsigned .nil)
  let initial := State.empty values environment actor 3
  let function := mixed dialect policy value
  obtain ⟨bindings, entered, events, enteredEq, rfl, _, _, _, _, initialized, _, _, enteredWF,
      frozen, nextEq, slotsEq, outside, _, rfl⟩ := enterParameters_contract dialect values initial
        (State.empty_wellFormed values environment actor 3) (by change 2 ≤ 3; decide +kernel)
  have enteredNext : entered.next = 2 := by simpa only [initial, State.empty, List.length_cons, List.length_nil] using nextEq
  have enteredSlots : entered.automaticSlots = 1 := by
    change entered.automaticSlots + 2 = 3 at slotsEq
    omega
  have enteredActor : entered.actor = actor := frozen.2.2
  change entered.objects 0 = some (liveObject .sint actor ⟨true, true⟩ (some signed)) ∧
    entered.objects 1 = some (liveObject .uint actor ⟨true, true⟩ (some unsigned)) ∧ True at initialized
  let final := reservedState dialect .sint entered
  have ready : CanReserve entered := ⟨fresh_of_wellFormed entered enteredWF, by omega⟩
  have first := reserve_eq dialect .sint entered ready
  have finalSlots : final.automaticSlots = 0 := by
    simp only [final, reservedState, enteredSlots]
  have enteredAbsent : entered.objects 3 = none := by
    have absent := outside 3 (Or.inr (by change 2 ≤ 3; omega))
    simpa only [initial, State.empty] using absent
  have fresh : final.objects final.next = none := by
    simp [final, reservedState, State.putObject, enteredNext, enteredAbsent]
  have exhausted := reserve_exhausted dialect .uint (reservedState dialect .sint entered) fresh finalSlots
  have localFailure : (BlockEval.reserveAll dialect [.sint, .uint] entered :
      Result target [.sint, .uint] Environment _) =
      (.error (.denied .automaticStorageExhausted), final, reserveEvents dialect 2 .sint actor) := by
    simp only [BlockEval.reserveAll, Op.bind, Effects.Op.bind, first, exhausted, enteredNext, enteredActor,
      List.append_nil]
    rfl
  have actual : FunctionEval.enterUnchecked function values initial =
      (.error (.denied .automaticStorageExhausted), final,
        parameterEvents dialect actor 0 values ++ reserveEvents dialect 2 .sint actor) := by
    simp only [FunctionEval.enterUnchecked, function, mixed, DeclarationSpine.localKinds, Op.bind, Effects.Op.bind,
      enteredEq, localFailure]
    simp only [initial, State.empty]
  have supported : function.Supported := by
    exact function.firstUnsupported_none_iff.mp rfl
  refine ⟨final, actual, ?_, ?_, finalSlots, ?_, ?_, ?_, ?_, ?_⟩
  · have inputs : initial.inputs = values := rfl
    rw [FunctionEval.start_supported function initial supported, inputs, actual]
  · simp only [final, reservedState, enteredNext]
  · rw [show final.objects 0 = entered.objects 0 by simp [final, reservedState, State.putObject, enteredNext]]
    exact initialized.1
  · rw [show final.objects 1 = entered.objects 1 by simp [final, reservedState, State.putObject, enteredNext]]
    exact initialized.2.1
  · simp [final, reservedState, State.putObject, enteredNext, enteredActor]
  · have empty := outside 3 (Or.inr (by change 2 ≤ 3; omega))
    simpa [final, reservedState, State.putObject, enteredNext, initial, State.empty] using empty
  · have pending : final.objects 2 = some (pendingObject dialect .sint actor ⟨true, true⟩) := by
      simp [final, reservedState, State.putObject, enteredNext, enteredActor]
    cases dialect <;> simp [load, pending, pendingObject, Op.reject]

end EDSL.Source.Objects.Control.EntryQuotaChecks
