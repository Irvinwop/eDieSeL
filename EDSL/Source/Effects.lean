/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import Init

set_option autoImplicit false
namespace EDSL.Source.Effects

/-- Complete observation, including the state and events retained on failure. -/
abbrev Result (State Error Event α : Type) := Except Error α × State × List Event
abbrev Op (State Error Event α : Type) := State → Result State Error Event α

-- Reducible operations keep specialized adapters' operational simplification.
abbrev Op.pure {State Error Event α : Type} (value : α) : Op State Error Event α :=
  fun state => (.ok value, state, [])

abbrev Op.reject {State Error Event α : Type} (reason : Error) : Op State Error Event α :=
  fun state => (.error reason, state, [])

/-- The sole state/error/event bind. A failed prefix retains its actual state
and events; an accepted prefix appends the continuation's events in that order. -/
abbrev Op.bind {State Error Event α β : Type}
    (first : Op State Error Event α) (next : α → Op State Error Event β) :
    Op State Error Event β := fun state =>
  let (outcome, updated, events) := first state
  match outcome with
  | .error reason => (.error reason, updated, events)
  | .ok value =>
      let (result, finalState, moreEvents) := next value updated
      (result, finalState, events ++ moreEvents)

theorem Op.bind_error {State Error Event α β : Type}
    (first : Op State Error Event α) (next : α → Op State Error Event β)
    (state updated : State) (reason : Error) (events : List Event)
    (failed : first state = (.error reason, updated, events)) :
    Op.bind first next state = (.error reason, updated, events) := by
  simp only [Op.bind, failed]

/-- The suffix observation is arbitrary: success and failure keep exactly the
same final state and append every actual suffix event. No state invariant is used. -/
theorem Op.bind_ok {State Error Event α β : Type}
    (first : Op State Error Event α) (next : α → Op State Error Event β)
    (state updated finalState : State) (value : α) (result : Except Error β)
    (events moreEvents : List Event)
    (accepted : first state = (.ok value, updated, events))
    (following : next value updated = (result, finalState, moreEvents)) :
    Op.bind first next state = (result, finalState, events ++ moreEvents) := by
  simp only [Op.bind, accepted, following]

/-- A carrier only; source sequencing, scheduling and state invariants belong
to its adapters and clients. -/
structure EffectM (State Error Event α : Type) where
  run : Op State Error Event α

namespace EffectM

theorem ext {State Error Event α : Type} {first second : EffectM State Error Event α}
    (same : first.run = second.run) : first = second := by
  cases first
  cases second
  cases same
  rfl

instance {State Error Event : Type} : Monad (EffectM State Error Event) where
  pure value := ⟨Op.pure value⟩
  bind first next := ⟨Op.bind first.run (fun value => (next value).run)⟩

def ofOp {State Error Event α : Type} (operation : Op State Error Event α) :
    EffectM State Error Event α := ⟨operation⟩

theorem bind_pure_left {State Error Event α β : Type}
    (value : α) (next : α → EffectM State Error Event β) :
    (pure value >>= next) = next value := by
  apply ext
  funext state
  change Op.bind (Op.pure value) (fun value => (next value).run) state = (next value).run state
  unfold Op.bind Op.pure
  cases execution : (next value).run state with
  | mk outcome rest =>
      rcases rest with ⟨updated, events⟩
      simp only [execution, List.nil_append]

theorem bind_pure_right {State Error Event α : Type} (first : EffectM State Error Event α) :
    (first >>= pure) = first := by
  apply ext
  funext state
  change Op.bind first.run (fun value => Op.pure value) state = first.run state
  cases execution : first.run state with
  | mk outcome rest =>
      rcases rest with ⟨updated, events⟩
      cases outcome <;> simp [Op.bind, execution]

theorem bind_assoc {State Error Event α β γ : Type}
    (first : EffectM State Error Event α)
    (next : α → EffectM State Error Event β)
    (last : β → EffectM State Error Event γ) :
    ((first >>= next) >>= last) = (first >>= fun value => next value >>= last) := by
  apply ext
  funext state
  change Op.bind (Op.bind first.run (fun value => (next value).run))
      (fun value => (last value).run) state =
    Op.bind first.run (fun value => Op.bind (next value).run (fun result => (last result).run)) state
  cases execution : first.run state with
  | mk outcome rest =>
      rcases rest with ⟨updated, events⟩
      cases outcome with
      | error reason => simp [Op.bind, execution]
      | ok value =>
          cases following : (next value).run updated with
          | mk outcome rest =>
              rcases rest with ⟨followingState, followingEvents⟩
              cases outcome with
              | error reason => simp [Op.bind, execution, following]
              | ok result =>
                  cases final : (last result).run followingState with
                  | mk outcome rest =>
                      rcases rest with ⟨finalState, finalEvents⟩
                      simp [Op.bind, execution, following, final, List.append_assoc]

end EffectM
end EDSL.Source.Effects
