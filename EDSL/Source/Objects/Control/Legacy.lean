/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.Trace

/-! Exact finite-body compatibility over an already bound object environment.
Declaration allocation/initialization, function entry and cleanup transport
remain future work. These internal control runs alone do not establish C/C++
forward progress or native execution correspondence. -/

set_option autoImplicit false
namespace EDSL.Source.Objects.Control
open StateSyntax

namespace Code

/-- The embedding preserves the exact whole-statement diagnostic, including
unsupported syntax in a branch which dynamic execution would skip. -/
theorem ofStmt_firstUnsupported {target : Target} {context : List ArithmeticType}
    {result : IntType} (statement : Stmt target context result) :
    (ofStmt statement).firstUnsupported = statement.firstUnsupported := by
  induction statement <;>
    simp only [ofStmt, firstUnsupported, Stmt.firstUnsupported, *] <;> rfl

end Code

namespace Legacy

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {context : List ArithmeticType} {result : IntType}

/-- The legacy carrier's success and failure retain their exact identity. -/
def statusOfOutcome : Except Stop (Value target result) → Status target result
  | .ok value => .returned value
  | .error reason => .stopped reason

/-- Agreement with the actual legacy result includes the entire object, input,
environment and resource state and every accepted observation, even on failure.
Pending control is administrative; a successful return discards it. -/
def Agrees (earlierEvents : List Event)
    (evaluation : Result target parameters Environment (Value target result))
    (final : Config target parameters Environment context result) : Prop :=
  final.status = statusOfOutcome evaluation.1 ∧
  final.state = evaluation.2.1 ∧
  final.events = earlierEvents ++ evaluation.2.2

theorem agrees_terminal (earlierEvents : List Event)
    (evaluation : Result target parameters Environment (Value target result))
    (final : Config target parameters Environment context result)
    (agreement : Agrees earlierEvents evaluation final) : Terminal final := by
  unfold Terminal
  rw [agreement.1]
  cases evaluation.1 <;> trivial

private theorem reaches_tick_then (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) (initial final : Config target parameters Environment context result)
    (reached : Reaches dialect policy bindings (tick dialect policy bindings initial) final) :
    Reaches dialect policy bindings initial final := by
  exact Reaches.trans dialect policy bindings initial _ final
    (Reaches.step dialect policy bindings initial) reached

/-- Assignment and the following body use the actual legacy effect composition.
The regrouping is the already proved effect-carrier associativity. -/
theorem evalStmt_set_assign {kind : ArithmeticType} (dialect : Dialect)
    (policy : IntegerConversionPolicy) (bindings : Env context) (index : Vars context kind)
    (value : RHS target context kind.asIntType) (next : Stmt target context result) :
    (StateEval.evalStmt dialect policy bindings (.set index value next) :
      Op target parameters Environment (Value target result)) =
    Op.bind (assign dialect policy bindings index value)
      (fun _ => StateEval.evalStmt dialect policy bindings next) := by
  exact (congrArg EffectM.run (EffectM.bind_assoc
    (EffectM.ofOp (StateEval.evalExpr dialect policy bindings value))
    (fun evaluated => EffectM.ofOp (store (bindings.get index) evaluated))
    (fun _ => EffectM.ofOp (StateEval.evalStmt dialect policy bindings next)))).symm

/-- Every finite legacy body has an actual finite machine execution, on every
state (including malformed states), with every exact failure retained. Earlier
observations and an arbitrary pending control continuation are permitted. -/
theorem evalStmt_reaches (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) (statement : Stmt target context result)
    (state : State target parameters Environment) (earlierEvents : List Event := [])
    (continuation : List (Code target context result) := []) :
    ∃ final, Reaches dialect policy bindings
      (startUnchecked (Code.ofStmt statement) state earlierEvents continuation) final ∧
      Agrees earlierEvents (StateEval.evalStmt dialect policy bindings statement state) final := by
  induction statement generalizing state earlierEvents continuation with
  | set index value next ih =>
      rcases computed : assign dialect policy bindings index value state with
        ⟨outcome, updated, observations⟩
      cases outcome with
      | error reason =>
          refine ⟨_, ⟨2, rfl⟩, ?_⟩
          simp [Agrees, statusOfOutcome, evalStmt_set_assign, Op.bind, computed,
            run, tick, startUnchecked, Code.ofStmt, perform]
      | ok evaluated =>
          obtain ⟨final, reached, agreement⟩ := ih updated (earlierEvents ++ observations) continuation
          refine ⟨final, ?_, ?_⟩
          · apply reaches_tick_then dialect policy bindings
            apply reaches_tick_then dialect policy bindings
            simpa only [tick, startUnchecked, Code.ofStmt, perform, computed] using reached
          · rcases following : StateEval.evalStmt dialect policy bindings next updated with
              ⟨outcome, finalState, moreEvents⟩
            simpa only [Agrees, evalStmt_set_assign, Op.bind, computed, following,
              List.append_assoc] using agreement
  | branch condition yes no ihYes ihNo =>
      rcases computed : StateEval.evalExpr dialect policy bindings condition state with
        ⟨outcome, updated, observations⟩
      cases outcome with
      | error reason =>
          refine ⟨_, ⟨1, rfl⟩, ?_⟩
          simp [Agrees, statusOfOutcome, StateEval.evalStmt, Op.bind, computed,
            run, tick, startUnchecked, Code.ofStmt, perform]
      | ok evaluated =>
          by_cases zero : evaluated.toInt = 0
          · obtain ⟨final, reached, agreement⟩ := ihNo updated (earlierEvents ++ observations) continuation
            refine ⟨final, ?_, ?_⟩
            · apply reaches_tick_then dialect policy bindings
              simpa only [tick, startUnchecked, Code.ofStmt, perform, computed, zero, ↓reduceIte]
                using reached
            · rcases following : StateEval.evalStmt dialect policy bindings no updated with
                ⟨outcome, finalState, moreEvents⟩
              simpa only [Agrees, StateEval.evalStmt, Op.bind, computed, zero, ↓reduceIte,
                following, List.append_assoc] using agreement
          · obtain ⟨final, reached, agreement⟩ := ihYes updated (earlierEvents ++ observations) continuation
            refine ⟨final, ?_, ?_⟩
            · apply reaches_tick_then dialect policy bindings
              simpa only [tick, startUnchecked, Code.ofStmt, perform, computed, zero, ↓reduceIte]
                using reached
            · rcases following : StateEval.evalStmt dialect policy bindings yes updated with
                ⟨outcome, finalState, moreEvents⟩
              simpa only [Agrees, StateEval.evalStmt, Op.bind, computed, zero, ↓reduceIte,
                following, List.append_assoc] using agreement
  | ret value =>
      rcases computed : StateEval.evalExpr dialect policy bindings value state with
        ⟨outcome, updated, observations⟩
      cases outcome <;> refine ⟨_, ⟨1, rfl⟩, ?_⟩ <;>
        simp [Agrees, statusOfOutcome, StateEval.evalStmt, computed,
          run, tick, startUnchecked, Code.ofStmt, perform]
  | unsupported feature =>
      refine ⟨_, ⟨1, rfl⟩, ?_⟩
      simp [Agrees, statusOfOutcome, StateEval.evalStmt, Op.reject,
        run, tick, startUnchecked, Code.ofStmt]

theorem statusOfOutcome_injective :
    Function.Injective (statusOfOutcome (target := target) (result := result)) := by
  intro first second same
  cases first <;> cases second <;> cases same <;> rfl

/-- Earlier observations cancel, so agreement identifies the full legacy result,
not only a value or a state projection. -/
theorem agrees_result_unique (earlierEvents : List Event)
    (first second : Result target parameters Environment (Value target result))
    (final : Config target parameters Environment context result)
    (firstAgreement : Agrees earlierEvents first final)
    (secondAgreement : Agrees earlierEvents second final) : first = second := by
  apply Prod.ext
  · exact statusOfOutcome_injective (firstAgreement.1.symm.trans secondAgreement.1)
  · apply Prod.ext
    · exact firstAgreement.2.1.symm.trans secondAgreement.2.1
    · exact List.append_cancel_left (firstAgreement.2.2.symm.trans secondAgreement.2.2)

/-- Every actual terminal execution has the canonical legacy outcome, complete
state and appended history. This converse follows from terminal uniqueness. -/
theorem evalStmt_terminal_agrees (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) (statement : Stmt target context result)
    (state : State target parameters Environment) (earlierEvents : List Event)
    (continuation : List (Code target context result))
    (final : Config target parameters Environment context result)
    (reached : Reaches dialect policy bindings
      (startUnchecked (Code.ofStmt statement) state earlierEvents continuation) final)
    (terminal : Terminal final) :
    Agrees earlierEvents (StateEval.evalStmt dialect policy bindings statement state) final := by
  obtain ⟨canonical, canonicalReach, agreement⟩ :=
    evalStmt_reaches dialect policy bindings statement state earlierEvents continuation
  have same := Reaches.terminal_unique dialect policy bindings _ final canonical
    reached canonicalReach terminal (agrees_terminal earlierEvents _ canonical agreement)
  rw [same]
  exact agreement

/-- Exact body-level compatibility in both directions, including every failure
and every malformed state. Agreement itself implies terminality. -/
theorem evalStmt_terminal_iff (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) (statement : Stmt target context result)
    (state : State target parameters Environment) (earlierEvents : List Event)
    (continuation : List (Code target context result))
    (evaluation : Result target parameters Environment (Value target result)) :
    (∃ final, Reaches dialect policy bindings
      (startUnchecked (Code.ofStmt statement) state earlierEvents continuation) final ∧
      Agrees earlierEvents evaluation final) ↔
    StateEval.evalStmt dialect policy bindings statement state = evaluation := by
  constructor
  · rintro ⟨final, reached, agreement⟩
    exact agrees_result_unique earlierEvents _ evaluation final
      (evalStmt_terminal_agrees dialect policy bindings statement state earlierEvents continuation
        final reached (agrees_terminal earlierEvents evaluation final agreement)) agreement
  · intro evaluated
    rw [← evaluated]
    exact evalStmt_reaches dialect policy bindings statement state earlierEvents continuation

/-- Public checked startup agrees with public whole-statement preflight. An
unsupported feature stops before any expression, store, or observation. -/
theorem runStmt_reaches (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) (statement : Stmt target context result)
    (state : State target parameters Environment) :
    ∃ final, Reaches dialect policy bindings (start (Code.ofStmt statement) state) final ∧
      Agrees [] (StateEval.runStmt dialect policy bindings statement state) final := by
  cases coverage : statement.firstUnsupported with
  | none =>
      simpa only [start, Code.ofStmt_firstUnsupported, StateEval.runStmt, coverage] using
        evalStmt_reaches dialect policy bindings statement state
  | some feature =>
      refine ⟨_, ⟨0, rfl⟩, ?_⟩
      simp [Agrees, statusOfOutcome, run, start, Code.ofStmt_firstUnsupported,
        StateEval.runStmt, coverage, Op.reject]

/-- The actual first unsupported diagnostic and the unchanged initial state and
empty history coincide on both public preflight boundaries. -/
theorem preflight_unsupported (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) (statement : Stmt target context result)
    (state : State target parameters Environment) (feature : UnsupportedFeature)
    (uncovered : statement.firstUnsupported = some feature) :
    start (Code.ofStmt statement) state =
      ⟨[Code.ofStmt statement], state, [], .stopped (.unsupported feature)⟩ ∧
    StateEval.runStmt dialect policy bindings statement state =
      (.error (.unsupported feature), state, []) := by
  constructor
  · exact start_unsupported _ state feature ((Code.ofStmt_firstUnsupported statement).trans uncovered)
  · exact StateEval.runStmt_unsupported dialect policy bindings statement feature uncovered state

theorem runStmt_terminal_agrees (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) (statement : Stmt target context result)
    (state : State target parameters Environment)
    (final : Config target parameters Environment context result)
    (reached : Reaches dialect policy bindings (start (Code.ofStmt statement) state) final)
    (terminal : Terminal final) :
    Agrees [] (StateEval.runStmt dialect policy bindings statement state) final := by
  obtain ⟨canonical, canonicalReach, agreement⟩ :=
    runStmt_reaches dialect policy bindings statement state
  have same := Reaches.terminal_unique dialect policy bindings _ final canonical
    reached canonicalReach terminal (agrees_terminal [] _ canonical agreement)
  rw [same]
  exact agreement

/-- The public bounded observer reaches exactly the result of the legacy
public runner, with eager coverage preserved in both directions. -/
theorem runStmt_terminal_iff (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) (statement : Stmt target context result)
    (state : State target parameters Environment)
    (evaluation : Result target parameters Environment (Value target result)) :
    (∃ final, Reaches dialect policy bindings (start (Code.ofStmt statement) state) final ∧
      Agrees [] evaluation final) ↔
    StateEval.runStmt dialect policy bindings statement state = evaluation := by
  constructor
  · rintro ⟨final, reached, agreement⟩
    exact agrees_result_unique [] _ evaluation final
      (runStmt_terminal_agrees dialect policy bindings statement state final reached
        (agrees_terminal [] evaluation final agreement)) agreement
  · intro evaluated
    rw [← evaluated]
    exact runStmt_reaches dialect policy bindings statement state

end Legacy
end EDSL.Source.Objects.Control
