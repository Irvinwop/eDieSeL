/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Protocol
import EDSL.Source.Objects.AccessContracts
import EDSL.Source.Objects.LifecycleContracts

set_option autoImplicit false
namespace EDSL.Source.Objects.ObjectWP
open Protocol LifecycleContracts
variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {kind : ArithmeticType}

/-- Reading obligations are independent registry/authority/value data and the
postcondition on the exact unchanged state and read observation. -/
theorem wp_load (dialect : Dialect) (ref : LValue kind)
    (post : Post target parameters Environment (Value target kind.asIntType))
    (state : State target parameters Environment) :
    WP (load dialect ref) post state ↔ ∃ value,
      CanLoad state ref value ∧ post state value state [.read ref.id kind value.toInt] := by
  constructor
  · intro condition
    obtain ⟨value, finalState, events, execution, resultPost⟩ := (wp_iff _ _ _).mp condition
    have ready := (load_success_iff dialect state ref value).mp (congrArg Prod.fst execution)
    have actual := load_contract dialect state ref value ready
    rw [actual] at execution
    cases execution
    exact ⟨value, ready, resultPost⟩
  · rintro ⟨value, ready, resultPost⟩
    unfold WP
    rw [load_contract dialect state ref value ready]
    exact resultPost

/-- The write rule exposes old contents and current write permission; read
permission and old initialization are deliberately unrestricted. -/
theorem wp_store (ref : LValue kind) (value : Value target kind.asIntType)
    (post : Post target parameters Environment Unit)
    (state : State target parameters Environment) :
    WP (store ref value) post state ↔
      ∃ previous permissions,
        state.objects ref.id = some (liveObject kind state.actor permissions previous) ∧
        permissions.writable = true ∧
        post state () (state.putObject ref.id (liveObject kind state.actor permissions (some value)))
          [.write ref.id kind value.toInt] := by
  constructor
  · intro condition
    obtain ⟨returned, finalState, events, execution, resultPost⟩ := (wp_iff _ _ _).mp condition
    cases returned
    have ready := (store_success_iff state ref value).mp (congrArg Prod.fst execution)
    obtain ⟨previous, permissions, registered, writable, actual⟩ := store_contract state ref value ready
    rw [actual] at execution
    cases execution
    exact ⟨previous, permissions, registered, writable, resultPost⟩
  · rintro ⟨previous, permissions, registered, writable, resultPost⟩
    have actual : store ref value state = (.ok (),
        state.putObject ref.id (liveObject kind state.actor permissions (some value)),
        [.write ref.id kind value.toInt]) := by
      simp only [liveObject] at registered ⊢
      simp [store, registered, writable]
    unfold WP
    rw [actual]
    exact resultPost

/-- Complete freshness/quota obligations for one reservation. -/
theorem wp_reserve (dialect : Dialect) (kind : ArithmeticType)
    (post : Post target parameters Environment (LValue kind))
    (state : State target parameters Environment) :
    WP (reserve dialect kind) post state ↔ CanReserve state ∧
      post state ⟨state.next⟩ (reservedState dialect kind state)
        (reserveEvents dialect state.next kind state.actor) := by
  constructor
  · intro condition
    obtain ⟨reference, finalState, events, execution, resultPost⟩ := (wp_iff _ _ _).mp condition
    have ready := (reserve_admission_iff dialect kind state).mp
      ⟨reference, congrArg Prod.fst execution⟩
    have actual := reserve_eq dialect kind state ready
    rw [actual] at execution
    cases execution
    exact ⟨ready, resultPost⟩
  · rintro ⟨ready, resultPost⟩
    unfold WP
    rw [reserve_eq dialect kind state ready]
    exact resultPost

/-- Initialization obligations mention the prestate's pending typed record,
not a promised target execution. Vacuous initialization remains `none`. -/
theorem wp_initialize (dialect : Dialect) (ref : LValue kind)
    (value : Option (Value target kind.asIntType))
    (post : Post target parameters Environment Unit)
    (state : State target parameters Environment) :
    WP (Objects.initialize dialect ref value) post state ↔
      ∃ permissions, permissions.writable = true ∧
        state.objects ref.id = some (pendingObject dialect kind state.actor permissions) ∧
        post state () (initializedState ref permissions value state)
          (initializeEvents dialect ref.id kind (value.map Value.toInt)) := by
  constructor
  · intro condition
    obtain ⟨returned, finalState, events, execution, resultPost⟩ := (wp_iff _ _ _).mp condition
    cases returned
    have ready := (initialize_admission_iff dialect ref value state).mp (congrArg Prod.fst execution)
    obtain ⟨permissions, writable, registered⟩ := (canInitialize_iff_snapshot dialect ref state).mp ready
    have actual := initialize_eq dialect ref state permissions value registered writable
    rw [actual] at execution
    cases execution
    exact ⟨permissions, writable, registered, resultPost⟩
  · rintro ⟨permissions, writable, registered, resultPost⟩
    unfold WP
    rw [initialize_eq dialect ref state permissions value registered writable]
    exact resultPost

/-- Cleanup obligations require live/reached/owned typed records. Stored values
and permissions are unrestricted; every successful end returns one slot. -/
theorem wp_endLifetime (ref : LValue kind)
    (post : Post target parameters Environment Unit)
    (state : State target parameters Environment) :
    WP (endLifetime ref) post state ↔
      ∃ value permissions,
        state.objects ref.id = some (liveObject kind state.actor permissions value) ∧
        post state () (endedState ref permissions value state) [.endLifetime ref.id kind] := by
  constructor
  · intro condition
    obtain ⟨returned, finalState, events, execution, resultPost⟩ := (wp_iff _ _ _).mp condition
    cases returned
    have ready := (endLifetime_admission_iff ref state).mp (congrArg Prod.fst execution)
    obtain ⟨value, permissions, registered⟩ := (canEnd_iff_snapshot ref state).mp ready
    have actual := endLifetime_eq ref state permissions value registered
    rw [actual] at execution
    cases execution
    exact ⟨value, permissions, registered, resultPost⟩
  · rintro ⟨value, permissions, registered, resultPost⟩
    unfold WP
    rw [endLifetime_eq ref state permissions value registered]
    exact resultPost

/-- Scalar WP exposes all three outcomes; UB/unsupported give false. Exact
failure identity and retained prefix effects are properties of the raw carrier,
not successful-completion postconditions of this judgment. -/
theorem wp_liftScalar {α : Type} (outcome : Outcome α)
    (post : Post target parameters Environment α)
    (state : State target parameters Environment) :
    WP (EffectM.liftScalar (target := target) (parameters := parameters)
      (Environment := Environment) outcome).run post state ↔
      (match outcome with
      | .defined value => post state value state []
      | .undefined _ => False
      | .unsupported _ => False) := by
  cases outcome <;> rfl

end EDSL.Source.Objects.ObjectWP
