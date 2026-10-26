/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.Syntax
import EDSL.Source.Objects.StateEval

set_option autoImplicit false
namespace EDSL.Source.Objects.Control
open StateSyntax

/-- Fallthrough is a control endpoint, not an invented ISO UB classification or
a returned scalar. A function/value certificate must establish actual return. -/
inductive Status (target : Target) (result : IntType) where
  | running
  | returned (value : Value target result)
  | fellThrough
  | stopped (reason : Stop)

structure Config (target : Target) (parameters : List IntType) (Environment : Type)
    (context : List ArithmeticType) (result : IntType) where
  control : List (Code target context result)
  state : State target parameters Environment
  events : List Event
  status : Status target result

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {context : List ArithmeticType} {result : IntType}
abbrev Cfg := Config target parameters Environment context result

/-- Execute the actual effect carrier; rejection retains accepted state/events.
This administrative wrapper adds no source expression or object semantics. -/
def perform {α : Type} (operation : Op target parameters Environment α)
    (next : α → Cfg (target := target) (parameters := parameters)
      (Environment := Environment) (context := context) (result := result) →
      Cfg (target := target) (parameters := parameters) (Environment := Environment)
        (context := context) (result := result))
    (config : Cfg (target := target) (parameters := parameters) (Environment := Environment)
      (context := context) (result := result)) :
    Cfg (target := target) (parameters := parameters) (Environment := Environment)
      (context := context) (result := result) :=
  let (outcome, updated, observations) := operation config.state
  let accepted := { config with state := updated, events := config.events ++ observations }
  match outcome with
  | .error reason => { accepted with status := .stopped reason }
  | .ok value => next value accepted

/-- Assignment reuses the shared expression engine and the actual store
primitive. Evaluation precedes the write, including their failure observations. -/
def assign {kind : ArithmeticType} (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) (index : Vars context kind)
    (value : RHS target context kind.asIntType) : Op target parameters Environment Unit :=
  Op.bind (StateEval.evalExpr dialect policy bindings value)
    (fun evaluated => store (bindings.get index) evaluated)

/-- One deterministic control transition. A full expression is a single
transition at this boundary, with its complete internal effects preserved.
This is not a native C operand-order or scheduler-interference theorem. -/
def tick (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)
    (config : Cfg (target := target) (parameters := parameters) (Environment := Environment)
      (context := context) (result := result)) :
    Cfg (target := target) (parameters := parameters) (Environment := Environment)
      (context := context) (result := result) :=
  match config.status with
  | .returned _ | .fellThrough | .stopped _ => config
  | .running =>
    match config.control with
    | [] => { config with status := .fellThrough }
    | code :: rest =>
      match code with
      | .skip => { config with control := rest }
      | .seq first next => { config with control := first :: next :: rest }
      | .assign index value => perform (assign dialect policy bindings index value)
          (fun _ updated => { updated with control := rest }) config
      | .branch condition yes no =>
          perform (StateEval.evalExpr dialect policy bindings condition)
            (fun value updated => { updated with
              control := (if value.toInt = 0 then no else yes) :: rest }) config
      | .loop condition body =>
          perform (StateEval.evalExpr dialect policy bindings condition)
            (fun value updated => { updated with control :=
              if value.toInt = 0 then rest else body :: code :: rest }) config
      | .ret value =>
          perform (StateEval.evalExpr dialect policy bindings value)
            (fun returned updated => { updated with control := [], status := .returned returned }) config
      | .unsupported feature => { config with status := .stopped (.unsupported feature) }

/-- A bounded observer of the one transition function. Exhausting the bound
returns the actual still-running configuration; it is not source failure/fuel.
Reachability and divergence quantify over all finite observation lengths. -/
def run (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context) :
    Nat → Cfg (target := target) (parameters := parameters) (Environment := Environment)
      (context := context) (result := result) →
      Cfg (target := target) (parameters := parameters) (Environment := Environment)
        (context := context) (result := result)
  | 0, config => config
  | steps + 1, config => tick dialect policy bindings (run dialect policy bindings steps config)

def startUnchecked (code : Code target context result) (state : State target parameters Environment)
    (earlierEvents : List Event := []) (continuation : List (Code target context result) := []) :
    Config target parameters Environment context result :=
  ⟨code :: continuation, state, earlierEvents, .running⟩

/-- Whole-code unsupported preflight occurs before the first transition. -/
def start (code : Code target context result) (state : State target parameters Environment) :
    Config target parameters Environment context result :=
  match code.firstUnsupported with
  | none => startUnchecked code state
  | some feature => ⟨[code], state, [], .stopped (.unsupported feature)⟩

def Terminal (config : Config target parameters Environment context result) : Prop :=
  match config.status with | .running => False | _ => True

def Reaches (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)
    (initial final : Config target parameters Environment context result) : Prop :=
  ∃ steps, run dialect policy bindings steps initial = final

def HasUB : Status target result → Prop
  | .stopped (.scalar _) | .stopped (.undefined _) => True
  | _ => False

def UBSafe (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)
    (initial : Config target parameters Environment context result) : Prop :=
  ∀ steps, ¬ HasUB (run dialect policy bindings steps initial).status

/-- Stronger than UB safety: no finite prefix stops for erroneous production,
binding/resource refusal or unsupported code either. Divergence is permitted. -/
def NoFailure (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)
    (initial : Config target parameters Environment context result) : Prop :=
  ∀ steps reason, (run dialect policy bindings steps initial).status ≠ .stopped reason

def Diverges (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)
    (initial : Config target parameters Environment context result) : Prop :=
  ∀ steps, (run dialect policy bindings steps initial).status = .running

theorem start_supported (code : Code target context result) (state : State target parameters Environment)
    (supported : code.Supported) : start code state = startUnchecked code state := by
  simp only [start, code.firstUnsupported_none_iff.mpr supported]

theorem start_unsupported (code : Code target context result) (state : State target parameters Environment)
    (feature : UnsupportedFeature) (unsupported : code.firstUnsupported = some feature) :
    start code state = ⟨[code], state, [], .stopped (.unsupported feature)⟩ := by
  simp only [start, unsupported]

theorem tick_terminal (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)
    (config : Config target parameters Environment context result) (terminal : Terminal config) :
    tick dialect policy bindings config = config := by
  cases config with
  | mk control state events status =>
      cases status <;> first | contradiction | rfl

end EDSL.Source.Objects.Control
