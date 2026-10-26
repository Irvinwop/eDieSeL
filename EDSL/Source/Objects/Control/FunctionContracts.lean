/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.FunctionCompatibility
import EDSL.Source.Objects.Protocol

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.FunctionContracts
open StateSyntax FunctionEval

/-! Contracts for the internal function driver, including actual normal cleanup.
No source mapping, source-standard progress, OS or interference claim is made.
A stopped internal body is a failure even before the wrapper settles its status. -/

variable {target : Target} {parameters : List ArithmeticType} {result : IntType}
variable {stateParameters : List IntType} {Environment : Type}
local notation "Obs" => Observation target parameters stateParameters Environment result

/-- Includes a stopped body that the wrapper has not yet exposed as a terminal
observation, so an observation bound cannot hide a modeled error for one tick. -/
def HasFailure (reason : Stop) : Obs → Prop
  | .active frame => frame.config.status = .stopped reason
  | .stopped actual _ _ => actual = reason
  | _ => False

theorem failure_settles (function : Function target parameters result)
    (reason : Stop) (current : Obs) (failed : HasFailure reason current) :
    ∃ state events, FunctionEval.tick function current = .stopped reason state events := by
  cases current with
  | active frame =>
      change frame.config.status = .stopped reason at failed
      exact ⟨frame.config.state, frame.config.events, by simp only [FunctionEval.tick, failed]⟩
  | stopped actual state events => exact ⟨state, events, by cases failed; rfl⟩
  | returned value state events => contradiction
  | fellThrough state events => contradiction

/-- Any actual returned endpoint excludes even an unsettled body failure in
every finite prefix, including observations after completion. -/
theorem returned_excludes_failure (function : Function target parameters result)
    (current : Obs) (steps : Nat) (value : Value target result)
    (final : State target stateParameters Environment) (events : List Event)
    (returned : observe function steps current = .returned value final events) :
    ∀ prefixSteps reason, ¬ HasFailure reason (observe function prefixSteps current) := by
  intro prefixSteps reason failed
  obtain ⟨failedState, failedEvents, settled⟩ := failure_settles function reason _ failed
  have failure : observe function (prefixSteps + 1) current =
      .stopped reason failedState failedEvents := settled
  have same := FunctionCompatibility.terminal_endpoint_unique function current steps (prefixSteps + 1)
    (by rw [returned]; trivial) (by rw [failure]; trivial)
  rw [returned, failure] at same
  cases same

/-- Admission describes inputs/resources; actual execution, value return and
successful normal cleanup are conclusions. Post sees the entire event history. -/
def Verifies (function : Function target parameters result)
    (admitted : State target (VariableTypes parameters) Environment → Prop)
    (post : Protocol.Post target (VariableTypes parameters) Environment (Value target result)) : Prop :=
  ∀ initial, admitted initial → ∃ steps value final events,
    observe function steps (FunctionEval.start function initial) = .returned value final events ∧
      post initial value final events

def PrefixNoFailure (function : Function target parameters result)
    (admitted : State target (VariableTypes parameters) Environment → Prop) : Prop :=
  ∀ initial, admitted initial → ∀ steps reason,
    ¬ HasFailure reason (observe function steps (FunctionEval.start function initial))

structure Certificate (function : Function target parameters result)
    (admitted : State target (VariableTypes parameters) Environment → Prop)
    (post : Protocol.Post target (VariableTypes parameters) Environment (Value target result)) : Prop where
  useful : ∃ initial, admitted initial
  verified : Verifies function admitted post

variable {function : Function target parameters result}
variable {admitted : State target (VariableTypes parameters) Environment → Prop}
variable {post : Protocol.Post target (VariableTypes parameters) Environment (Value target result)}

theorem Verifies.noFailure (correct : Verifies function admitted post) :
    PrefixNoFailure function admitted := by
  intro initial permitted
  obtain ⟨steps, value, final, events, returned, _⟩ := correct initial permitted
  exact returned_excludes_failure function _ steps value final events returned

/-- A useful completed function cannot contain even unreachable unsupported
syntax: public preflight rejects it before entry effects. -/
theorem Certificate.supported (certificate : Certificate function admitted post) :
    function.Supported := by
  obtain ⟨initial, permitted⟩ := certificate.useful
  obtain ⟨steps, value, final, events, returned, _⟩ := certificate.verified initial permitted
  cases covered : function.firstUnsupported with
  | none => exact function.firstUnsupported_none_iff.mp covered
  | some feature =>
      rw [FunctionEval.start_unsupported function initial feature covered,
        observe_stopped] at returned
      cases returned


/-- Every finite source contract transports exactly to the resumable driver,
with no new per-program operational proof or additional input assumption. -/
theorem verifies_ofProgram_iff (program : StateSyntax.Program target parameters result)
    (admitted : State target (VariableTypes parameters) Environment → Prop)
    (post : Protocol.Post target (VariableTypes parameters) Environment (Value target result)) :
    Verifies (Function.ofProgram program) admitted post ↔
      Protocol.Verifies (BlockEval.runProgram program) admitted post := by
  constructor
  · intro correct initial permitted
    obtain ⟨steps, value, final, events, returned, resultPost⟩ := correct initial permitted
    have actual := (FunctionCompatibility.runProgram_terminal_iff program initial
      (.ok value, final, events)).mp ⟨steps, returned⟩
    exact ⟨value, final, events, actual, resultPost⟩
  · intro correct initial permitted
    obtain ⟨value, final, events, actual, resultPost⟩ := correct initial permitted
    obtain ⟨steps, returned⟩ := (FunctionCompatibility.runProgram_terminal_iff program initial
      (.ok value, final, events)).mpr actual
    exact ⟨steps, value, final, events, returned, resultPost⟩

/-- Existing useful finite certificates retain their complete independent
admission and postcondition, now including the observer's actual cleanup. -/
theorem Certificate.ofProgram (program : StateSyntax.Program target parameters result)
    (certificate : Protocol.Certificate (BlockEval.runProgram program) admitted post) :
    Certificate (Function.ofProgram program) admitted post :=
  ⟨certificate.useful, (verifies_ofProgram_iff program admitted post).mpr certificate.verified⟩

end EDSL.Source.Objects.Control.FunctionContracts
