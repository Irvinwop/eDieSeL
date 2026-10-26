/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.Machine

set_option autoImplicit false
namespace EDSL.Source.Objects.Control
open StateSyntax

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {context : List ArithmeticType} {result : IntType}
variable (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)
local notation "Configuration" => Config target parameters Environment context result

@[simp] theorem run_zero (initial : Configuration) :
    run dialect policy bindings 0 initial = initial := rfl

@[simp] theorem run_succ (steps : Nat) (initial : Configuration) :
    run dialect policy bindings (steps + 1) initial =
      tick dialect policy bindings (run dialect policy bindings steps initial) := rfl

/-- Resuming the actual observer preserves every component of its configuration. -/
theorem run_add (first second : Nat) (initial : Configuration) :
    run dialect policy bindings (first + second) initial =
      run dialect policy bindings second (run dialect policy bindings first initial) := by
  induction second with
  | zero => rfl
  | succ second ih => simp only [Nat.add_succ, run_succ, ih]

/-- The front transition can be discharged before proving the remaining trace. -/
theorem run_succ_front (steps : Nat) (initial : Configuration) :
    run dialect policy bindings (steps + 1) initial =
      run dialect policy bindings steps (tick dialect policy bindings initial) := by
  rw [Nat.add_comm steps 1, run_add]
  rfl

theorem run_terminal (steps : Nat) (initial : Configuration) (terminal : Terminal initial) :
    run dialect policy bindings steps initial = initial := by
  induction steps with
  | zero => rfl
  | succ steps ih => rw [run_succ, ih, tick_terminal dialect policy bindings initial terminal]

/-- Observation after any terminal prefix is stable, including state/events. -/
theorem run_stable_of_terminal (initial : Configuration) (first second : Nat)
    (ordered : first ≤ second)
    (terminal : Terminal (run dialect policy bindings first initial)) :
    run dialect policy bindings second initial = run dialect policy bindings first initial := by
  have split : second = first + (second - first) := by omega
  rw [split, run_add, run_terminal dialect policy bindings _ _ terminal]

theorem terminal_endpoint_unique (initial : Configuration) (first second : Nat)
    (firstTerminal : Terminal (run dialect policy bindings first initial))
    (secondTerminal : Terminal (run dialect policy bindings second initial)) :
    run dialect policy bindings first initial = run dialect policy bindings second initial := by
  rcases Nat.le_total first second with ordered | ordered
  · exact (run_stable_of_terminal dialect policy bindings initial first second ordered firstTerminal).symm
  · exact run_stable_of_terminal dialect policy bindings initial second first ordered secondTerminal

namespace Reaches

theorem refl (initial : Configuration) : Reaches dialect policy bindings initial initial := ⟨0, rfl⟩

theorem step (initial : Configuration) :
    Reaches dialect policy bindings initial (tick dialect policy bindings initial) := ⟨1, rfl⟩

theorem trans (initial middle final : Configuration)
    (first : Reaches dialect policy bindings initial middle)
    (second : Reaches dialect policy bindings middle final) :
    Reaches dialect policy bindings initial final := by
  obtain ⟨firstSteps, firstRun⟩ := first
  obtain ⟨secondSteps, secondRun⟩ := second
  exact ⟨firstSteps + secondSteps, by rw [run_add, firstRun, secondRun]⟩

theorem terminal_unique (initial first second : Configuration)
    (firstReach : Reaches dialect policy bindings initial first)
    (secondReach : Reaches dialect policy bindings initial second)
    (firstTerminal : Terminal first) (secondTerminal : Terminal second) : first = second := by
  obtain ⟨firstSteps, rfl⟩ := firstReach
  obtain ⟨secondSteps, rfl⟩ := secondReach
  exact terminal_endpoint_unique dialect policy bindings initial firstSteps secondSteps
    firstTerminal secondTerminal

end Reaches

/-- The invariant is preserved by the existing transition, not another evaluator. -/
theorem run_invariant (invariant : Configuration → Prop) (initial : Configuration)
    (member : invariant initial)
    (preserved : ∀ config, invariant config → invariant (tick dialect policy bindings config))
    (steps : Nat) : invariant (run dialect policy bindings steps initial) := by
  induction steps with
  | zero => exact member
  | succ steps ih => exact preserved _ ih

/-- No termination premise: an invariant excluding stopped states proves safety
of every finite internal control prefix, including a divergent execution. -/
theorem noFailure_of_invariant (invariant : Configuration → Prop) (initial : Configuration)
    (member : invariant initial)
    (preserved : ∀ config, invariant config → invariant (tick dialect policy bindings config))
    (notStopped : ∀ config, invariant config → ∀ reason, config.status ≠ .stopped reason) :
    NoFailure dialect policy bindings initial := by
  intro steps reason
  exact notStopped _ (run_invariant dialect policy bindings invariant initial member preserved steps) reason

theorem noFailure_ubSafe (initial : Configuration)
    (safe : NoFailure dialect policy bindings initial) : UBSafe dialect policy bindings initial := by
  intro steps hasUB
  have excludes := safe steps
  cases status : (run dialect policy bindings steps initial).status with
  | running => simp only [status, HasUB] at hasUB
  | returned value => simp only [status, HasUB] at hasUB
  | fellThrough => simp only [status, HasUB] at hasUB
  | stopped reason => exact excludes reason status

theorem diverges_noFailure (initial : Configuration)
    (diverges : Diverges dialect policy bindings initial) : NoFailure dialect policy bindings initial := by
  intro steps reason stopped
  rw [diverges steps] at stopped
  cases stopped

theorem diverges_ubSafe (initial : Configuration)
    (diverges : Diverges dialect policy bindings initial) : UBSafe dialect policy bindings initial :=
  noFailure_ubSafe dialect policy bindings initial (diverges_noFailure dialect policy bindings initial diverges)

theorem noFailure_resume (initial : Configuration)
    (safe : NoFailure dialect policy bindings initial) (earlier : Nat) :
    NoFailure dialect policy bindings (run dialect policy bindings earlier initial) := by
  intro steps reason
  rw [← run_add]
  exact safe (earlier + steps) reason

theorem ubSafe_resume (initial : Configuration)
    (safe : UBSafe dialect policy bindings initial) (earlier : Nat) :
    UBSafe dialect policy bindings (run dialect policy bindings earlier initial) := by
  intro steps
  rw [← run_add]
  exact safe (earlier + steps)

/-- A finite value return excludes every stopped prefix because stops are
absorbing. Fallthrough is deliberately insufficient for a value-return proof. -/
theorem noFailure_of_returns (initial : Configuration) (steps : Nat) (value : Value target result)
    (returned : (run dialect policy bindings steps initial).status = .returned value) :
    NoFailure dialect policy bindings initial := by
  intro earlier reason stopped
  have returnTerminal : Terminal (run dialect policy bindings steps initial) := by
    simp only [Terminal, returned]
  have stopTerminal : Terminal (run dialect policy bindings earlier initial) := by
    simp only [Terminal, stopped]
  have same := terminal_endpoint_unique dialect policy bindings initial earlier steps
    stopTerminal returnTerminal
  have impossible := congrArg Config.status same
  rw [stopped, returned] at impossible
  cases impossible

/-- Whole-code preflight makes coverage a consequence of actual prefix safety. -/
theorem noFailure_start_supported (code : Code target context result)
    (initial : State target parameters Environment)
    (safe : NoFailure dialect policy bindings (start code initial)) : code.Supported := by
  cases scan : code.firstUnsupported with
  | none => exact code.firstUnsupported_none_iff.mp scan
  | some feature =>
      have excludes := safe 0 (.unsupported feature)
      simp only [run_zero, start, scan] at excludes
      exact False.elim (excludes rfl)

/-- A successful continuation of `perform` can only append observations when
it retains the accepted event field. Rejection retains those observations too. -/
theorem perform_events_append {α : Type} (operation : Op target parameters Environment α)
    (next : α → Configuration → Configuration) (initial : Configuration)
    (retains : ∀ value config, (next value config).events = config.events) :
    ∃ suffix, (perform operation next initial).events = initial.events ++ suffix := by
  rcases execution : operation initial.state with ⟨outcome, updated, observations⟩
  refine ⟨observations, ?_⟩
  cases outcome <;> simp only [perform, execution, retains]

/-- Every actual transition retains the entire earlier event history, including
effects accepted before a failing expression/store. -/
theorem tick_events_append (initial : Configuration) :
    ∃ suffix, (tick dialect policy bindings initial).events = initial.events ++ suffix := by
  cases status : initial.status with
  | returned value => exact ⟨[], by simp only [tick, status, List.append_nil]⟩
  | fellThrough => exact ⟨[], by simp only [tick, status, List.append_nil]⟩
  | stopped reason => exact ⟨[], by simp only [tick, status, List.append_nil]⟩
  | running =>
      cases control : initial.control with
      | nil => exact ⟨[], by simp only [tick, status, control, List.append_nil]⟩
      | cons code rest =>
          cases code <;> simp only [tick, status, control]
          all_goals first
          | (refine ⟨[], ?_⟩; simp only [List.append_nil] <;> rfl)
          | apply perform_events_append; intro value config; rfl

theorem run_events_append (steps : Nat) (initial : Configuration) :
    ∃ suffix, (run dialect policy bindings steps initial).events = initial.events ++ suffix := by
  induction steps with
  | zero => exact ⟨[], by simp only [run_zero, List.append_nil]⟩
  | succ steps ih =>
      obtain ⟨earlier, earlierEvents⟩ := ih
      obtain ⟨later, laterEvents⟩ := tick_events_append dialect policy bindings
        (run dialect policy bindings steps initial)
      exact ⟨earlier ++ later, by rw [run_succ, laterEvents, earlierEvents, List.append_assoc]⟩

theorem run_events_prefix (initial : Configuration) (first second : Nat) (ordered : first ≤ second) :
    ∃ suffix, (run dialect policy bindings second initial).events =
      (run dialect policy bindings first initial).events ++ suffix := by
  have split : second = first + (second - first) := by omega
  rw [split, run_add]
  exact run_events_append dialect policy bindings _ _

end EDSL.Source.Objects.Control
