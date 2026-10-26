/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.FunctionSyntax
import EDSL.Source.Objects.DeclarationEval
import EDSL.Source.Objects.Control.Legacy
import EDSL.Source.Objects.BlockEval

set_option autoImplicit false
namespace EDSL.Source.Objects.Control
open StateSyntax

/-! Internal function entry and normal-return cleanup for control bodies.
Reservation, initialization, expression evaluation and lifetime ending are the
existing object operations. The neutral declaration fold is also the finite
driver's initializer traversal. Step bounds below are observations, not
execution fuel, source errors or a termination assumption.

No exception unwinding or failed-entry reclamation is invented. Fallthrough is
an explicit internal endpoint. Prefix safety here does not establish source
C/C++ forward progress, scheduler fairness, native behavior or source mapping. -/

namespace DeclarationSpine
variable {target : Target} {parameters : List IntType} {Environment : Type}

/-- Exact specialization, on every state and even on failure: the generic
traversal agrees with the existing finite declaration evaluator. -/
theorem fold_ofDecls_eq (dialect : Dialect) (policy : IntegerConversionPolicy)
    {context : List ArithmeticType} {result : IntType}
    (declarations : Decls target context result) (bindings : Env context)
    (plan : Env (ofDecls (fun statement => statement) declarations).localKinds) :
    (fold dialect policy (fun statement environment =>
        StateEval.evalStmt dialect policy environment statement)
      (ofDecls (fun statement => statement) declarations) bindings plan :
        Op target parameters Environment (Value target result)) =
    BlockEval.evalDecls dialect policy declarations bindings
      (cast (congrArg Env (ofDecls_localKinds (fun statement => statement) declarations)) plan) := by
  unfold BlockEval.evalDecls
  rw [planOfDecls_eq_cast]
  simp only [cast_cast, cast_eq]

end DeclarationSpine

/-- A body and its complete active bindings after actual initializer execution. -/
structure PreparedBody (target : Target) (result : IntType) where
  context : List ArithmeticType
  bindings : Env context
  code : Code target context result

/-- Entry retains the original parameter/local plans for reverse-order normal
cleanup; bindings contain identities rather than cached expression values. -/
structure FunctionEntry (target : Target) (parameters : List ArithmeticType) (result : IntType)
    extends PreparedBody target result where
  parameterBindings : Env parameters
  localKinds : List ArithmeticType
  localBindings : Env localKinds

namespace Function
variable {target : Target} {parameters : List ArithmeticType} {result : IntType}

/-- Exact declaration and statement diagnostics survive finite-program embedding. -/
theorem ofProgram_firstUnsupported (program : StateSyntax.Program target parameters result) :
    (ofProgram program).firstUnsupported = program.firstUnsupported := by
  change (DeclarationSpine.ofDecls Code.ofStmt program.body).firstUnsupported
    Code.firstUnsupported = program.body.firstUnsupported
  generalize program.body = declarations
  clear program
  induction declarations with
  | body statement => exact Code.ofStmt_firstUnsupported statement
  | declare kind initial rest ih =>
      simp only [DeclarationSpine.ofDecls, DeclarationSpine.firstUnsupported,
        Decls.firstUnsupported, ih]
      rfl

theorem ofProgram_supported_iff (program : StateSyntax.Program target parameters result) :
    (ofProgram program).Supported ↔ program.Supported := by
  rw [← (ofProgram program).firstUnsupported_none_iff, ofProgram_firstUnsupported,
    program.firstUnsupported_eq_none_iff]

end Function

namespace FunctionEval
variable {target : Target} {parameters : List ArithmeticType} {result : IntType}
variable {stateParameters : List IntType} {Environment : Type}

/-- Finite entry preparation independent of control execution. All locals are
reserved before the generic fold evaluates the first initializer. -/
def enterUnchecked (function : Function target parameters result)
    (inputs : CallInputs target parameters) :
    Op target stateParameters Environment (FunctionEntry target parameters result) :=
  Op.bind (BlockEval.enterParameters function.dialect inputs) fun parameterBindings =>
  Op.bind (BlockEval.reserveAll function.dialect function.body.localKinds) fun localBindings =>
  Op.bind (DeclarationSpine.fold function.dialect function.conversions
    (fun {context} code bindings =>
      Op.pure (⟨context, bindings, code⟩ : PreparedBody target result))
    function.body parameterBindings localBindings) fun prepared =>
  Op.pure ⟨prepared, parameterBindings, function.body.localKinds, localBindings⟩

/-- Normal return ends locals in reverse declaration order, then parameters in
reverse parameter order. The scalar has already been evaluated. -/
def cleanup (entry : FunctionEntry target parameters result) (value : Value target result) :
    Op target stateParameters Environment (Value target result) :=
  Op.bind (BlockEval.closeAll entry.localBindings) fun _ =>
  Op.bind (BlockEval.closeAll entry.parameterBindings) fun _ => Op.pure value

structure Active (target : Target) (parameters : List ArithmeticType)
    (stateParameters : List IntType) (Environment : Type) (result : IntType) where
  entry : FunctionEntry target parameters result
  config : Config target stateParameters Environment entry.context result

/-- Public return means successful actual normal cleanup. Active control may
run indefinitely; observation exhaustion is represented by active, never error. -/
inductive Observation (target : Target) (parameters : List ArithmeticType)
    (stateParameters : List IntType) (Environment : Type) (result : IntType) where
  | active (frame : Active target parameters stateParameters Environment result)
  | returned (value : Value target result) (state : State target stateParameters Environment)
      (events : List Event)
  | stopped (reason : Stop) (state : State target stateParameters Environment) (events : List Event)
  | fellThrough (state : State target stateParameters Environment) (events : List Event)

/-- Full-tree coverage precedes every entry effect, including reservation. -/
def start (function : Function target parameters result)
    (initial : State target (VariableTypes parameters) Environment) :
    Observation target parameters (VariableTypes parameters) Environment result :=
  match function.firstUnsupported with
  | some feature => .stopped (.unsupported feature) initial []
  | none =>
    let (outcome, updated, observations) := enterUnchecked function initial.inputs initial
    match outcome with
    | .error reason => .stopped reason updated observations
    | .ok entry => .active ⟨entry, startUnchecked entry.code updated observations⟩

/-- Control stops retain all accepted effects. Cleanup executes only on normal
return, as in the accepted finite driver. Fallthrough is not given a fake value. -/
def tick (function : Function target parameters result) :
    Observation target parameters stateParameters Environment result →
    Observation target parameters stateParameters Environment result
  | .active frame =>
    match frame.config.status with
    | .running => .active { frame with config := Control.tick function.dialect function.conversions frame.entry.bindings frame.config }
    | .stopped reason => .stopped reason frame.config.state frame.config.events
    | .fellThrough => .fellThrough frame.config.state frame.config.events
    | .returned value =>
      let (outcome, updated, observations) := cleanup frame.entry value frame.config.state
      match outcome with
      | .error reason => .stopped reason updated (frame.config.events ++ observations)
      | .ok value => .returned value updated (frame.config.events ++ observations)
  | terminal => terminal

/-- Observe a finite prefix, including actual normal cleanup if reached. The
function syntax and its execution state carry no fuel/rank/invariant. -/
def observe (function : Function target parameters result) : Nat →
    Observation target parameters stateParameters Environment result →
    Observation target parameters stateParameters Environment result
  | 0, current => current
  | steps + 1, current => tick function (observe function steps current)

/-- Independent metadata/capacity entry condition, without a success premise. -/
def Entry (function : Function target parameters result)
    (initial : State target (VariableTypes parameters) Environment) : Prop :=
  initial.WellFormed ∧ parameters.length + function.body.localKinds.length ≤ initial.automaticSlots

/-- The resource precondition remains inhabited for arbitrary external inputs
and environment; no target execution result is assumed. -/
theorem entry_inhabited (function : Function target parameters result)
    (inputs : CallInputs target parameters) (environment : Environment) (actor : Nat) :
    ∃ initial, initial.inputs = inputs ∧ initial.environment = environment ∧ Entry function initial := by
  refine ⟨State.empty inputs environment actor
    (parameters.length + function.body.localKinds.length), rfl, rfl, ?_, Nat.le_refl _⟩
  exact State.empty_wellFormed inputs environment actor _

theorem ofProgram_entry_iff (program : StateSyntax.Program target parameters result)
    (initial : State target (VariableTypes parameters) Environment) :
    Entry (Function.ofProgram program) initial ↔ BlockEval.Entry program initial := by
  simp only [Entry, BlockEval.Entry, Function.ofProgram_localKinds, Decls.localKinds_length]

theorem start_unsupported (function : Function target parameters result)
    (initial : State target (VariableTypes parameters) Environment) (feature : UnsupportedFeature)
    (unsupported : function.firstUnsupported = some feature) :
    start function initial = .stopped (.unsupported feature) initial [] := by
  simp only [start, unsupported]

theorem start_supported (function : Function target parameters result)
    (initial : State target (VariableTypes parameters) Environment) (covered : function.Supported) :
    start function initial =
      let (outcome, updated, observations) := enterUnchecked function initial.inputs initial
      match outcome with
      | .error reason => .stopped reason updated observations
      | .ok entry => .active ⟨entry, startUnchecked entry.code updated observations⟩ := by
  simp only [start, function.firstUnsupported_none_iff.mpr covered]

@[simp] theorem observe_zero (function : Function target parameters result)
    (current : Observation target parameters stateParameters Environment result) :
    observe function 0 current = current := rfl

theorem observe_add (function : Function target parameters result) (first second : Nat)
    (current : Observation target parameters stateParameters Environment result) :
    observe function (first + second) current =
      observe function second (observe function first current) := by
  induction second with
  | zero => simp only [Nat.add_zero, observe]
  | succ second ih => exact congrArg (tick function) ih

/-- One observer step after an active internal endpoint executes its actual
cleanup (or records its stop/fallthrough); taking an internal terminal step
before this does not change that observation. -/
theorem tick_active_commutes (function : Function target parameters result)
    (frame : Active target parameters stateParameters Environment result) :
    tick function (tick function (.active frame)) =
      tick function (.active { frame with config := Control.tick function.dialect function.conversions frame.entry.bindings frame.config }) := by
  rcases frame with ⟨entry, config⟩
  rcases config with ⟨control, state, events, status⟩
  cases status with
  | running => rfl
  | stopped reason => rfl
  | fellThrough => rfl
  | returned value =>
      rcases execution : cleanup entry value state with ⟨outcome, final, observations⟩
      cases outcome <;> simp only [tick, Control.tick, execution]

/-- An internal prefix can be transported without assuming that earlier
iterations return. The extra observation step settles an actual endpoint. -/
theorem observe_active_settle (function : Function target parameters result) (steps : Nat)
    (frame : Active target parameters stateParameters Environment result) :
    observe function (steps + 1) (.active frame) =
      tick function (.active { frame with config := Control.run function.dialect function.conversions frame.entry.bindings steps frame.config }) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      change tick function (observe function (steps + 1) (.active frame)) = _
      rw [ih]
      exact tick_active_commutes function _

/-- Settle the exact finite effect result with the same normal cleanup; a
failed body retains its state/history and performs no cleanup. -/
def settleResult (entry : FunctionEntry target parameters result) (earlierEvents : List Event)
    (evaluation : Result target stateParameters Environment (Value target result)) :
    Observation target parameters stateParameters Environment result :=
  let (outcome, state, events) := evaluation
  match outcome with
  | .error reason => .stopped reason state (earlierEvents ++ events)
  | .ok value =>
      let (outcome, updated, observations) := cleanup entry value state
      match outcome with
      | .error reason => .stopped reason updated (earlierEvents ++ events ++ observations)
      | .ok value => .returned value updated (earlierEvents ++ events ++ observations)

/-- Exact internal endpoint agreement transports all accepted body and cleanup
effects, including cleanup failure, with no extra well-formedness hypothesis. -/
theorem observe_of_agreement (function : Function target parameters result)
    (frame : Active target parameters stateParameters Environment result)
    (final : Config target stateParameters Environment frame.entry.context result)
    (steps : Nat)
    (reached : Control.run function.dialect function.conversions frame.entry.bindings
      steps frame.config = final)
    (earlierEvents : List Event)
    (evaluation : Result target stateParameters Environment (Value target result))
    (agreement : Legacy.Agrees earlierEvents evaluation final) :
    observe function (steps + 1) (.active frame) =
      settleResult frame.entry earlierEvents evaluation := by
  rw [observe_active_settle, reached]
  rcases evaluation with ⟨outcome, state, events⟩
  cases outcome with
  | error reason =>
      simp only [Legacy.Agrees, Legacy.statusOfOutcome] at agreement
      simp only [tick, agreement.1, agreement.2.1, agreement.2.2, settleResult]
  | ok value =>
      simp only [Legacy.Agrees, Legacy.statusOfOutcome] at agreement
      simp only [tick, agreement.1, agreement.2.1, agreement.2.2, settleResult]

/-- A finite legacy body followed by actual normal cleanup has exactly the
function observation computed from its old result, including every failure.
This is body-and-cleanup transport, not yet whole-entry compatibility. -/
theorem ofStmt_cleanup_reaches (function : Function target parameters result)
    (entry : FunctionEntry target parameters result)
    (statement : Stmt target entry.context result) (code : entry.code = Code.ofStmt statement)
    (state : State target stateParameters Environment) (earlierEvents : List Event := []) :
    ∃ steps, observe function steps
        (.active ⟨entry, startUnchecked entry.code state earlierEvents⟩) =
      settleResult entry earlierEvents
        (StateEval.evalStmt function.dialect function.conversions entry.bindings statement state) := by
  obtain ⟨final, ⟨steps, reached⟩, agreement⟩ :=
    Legacy.evalStmt_reaches function.dialect function.conversions entry.bindings
      statement state earlierEvents
  refine ⟨steps + 1, ?_⟩
  apply observe_of_agreement function _ final steps _ earlierEvents _ agreement
  simpa only [code] using reached

/-- Every successful return is absorbing and includes cleanup's actual result. -/
theorem observe_returned (function : Function target parameters result) (steps : Nat)
    (value : Value target result) (state : State target stateParameters Environment)
    (events : List Event) :
    observe function steps (.returned value state events) = .returned value state events := by
  induction steps <;> simp_all [observe, tick]

theorem observe_stopped (function : Function target parameters result) (steps : Nat)
    (reason : Stop) (state : State target stateParameters Environment) (events : List Event) :
    observe function steps (.stopped reason state events) = .stopped reason state events := by
  induction steps <;> simp_all [observe, tick]

theorem observe_fellThrough (function : Function target parameters result) (steps : Nat)
    (state : State target stateParameters Environment) (events : List Event) :
    observe function steps (.fellThrough state events) = .fellThrough state events := by
  induction steps <;> simp_all [observe, tick]

end FunctionEval
end EDSL.Source.Objects.Control
