/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.DeclarationEval
import EDSL.Source.Objects.LifecycleContracts

set_option autoImplicit false
namespace EDSL.Source.Objects.BlockEval
open StateSyntax

/-! A finite declaration-prefix driver. Formal parameters and locals are actual
objects. All local storage is reserved before the first initializer; only prior
bindings are visible to each initializer. A returned scalar is computed before
reverse-order scope cleanup. A terminal failure retains accepted effects: this
module does not model exception unwinding, pending-reservation reclamation or
native allocation. Automatic slots are abstract resources, not stack bytes. -/

variable {target : Target} {stateParameters : List IntType} {Environment : Type}

/-- Reserve the entire source-order prefix without evaluating any initializer. -/
def reserveAll (dialect : Dialect) : (kinds : List ArithmeticType) →
    Op target stateParameters Environment (Env kinds)
  | [] => Op.pure .nil
  | kind :: kinds => Op.bind (reserve dialect kind) fun reference =>
      Op.bind (reserveAll dialect kinds) fun tail => Op.pure (.cons reference tail)

/-- Allocate and initialize mutable formal objects from external call values.
No RHS resolver reads these external values after entry. -/
def enterParameters (dialect : Dialect) : {kinds : List ArithmeticType} →
    CallInputs target kinds → Op target stateParameters Environment (Env kinds)
  | [], .nil => Op.pure .nil
  | kind :: _, .cons value rest =>
      Op.bind (reserve dialect kind) fun reference =>
      Op.bind («initialize» dialect reference (some value)) fun _ =>
      Op.bind (enterParameters dialect rest) fun tail => Op.pure (.cons reference tail)

/-- End each successfully reached object once, in reverse source order. -/
def closeAll : {kinds : List ArithmeticType} → Env kinds →
    Op target stateParameters Environment Unit
  | [], .nil => Op.pure ()
  | _ :: _, .cons reference tail =>
      Op.bind (closeAll tail) fun _ => endLifetime reference

/-- Specialize the shared initializer fold to finite statements and an already
reserved complete plan. Only the terminal body interpreter is finite-specific. -/
def evalDecls (dialect : Dialect) (policy : IntegerConversionPolicy)
    {context : List ArithmeticType} {result : IntType}
    (declarations : Decls target context result) (environment : Env context)
    (plan : ReservationPlan declarations) : Op target stateParameters Environment (Value target result) :=
  Control.DeclarationSpine.fold dialect policy
    (fun statement bindings => StateEval.evalStmt dialect policy bindings statement)
    (Control.DeclarationSpine.ofDecls (fun statement => statement) declarations) environment
    (Control.DeclarationSpine.planOfDecls (fun statement => statement) declarations plan)

/-- Execute entry, block, and successful normal-return cleanup. This internal
operation has no coverage gate; runProgram supplies it before any allocation. -/
def execute {parameters : List ArithmeticType} {result : IntType}
    (program : StateSyntax.Program target parameters result)
    (inputs : CallInputs target parameters) :
    Op target stateParameters Environment (Value target result) :=
  Op.bind (enterParameters program.dialect inputs) fun parameters =>
  Op.bind (reserveAll program.dialect program.body.localKinds) fun locals =>
  Op.bind (evalDecls program.dialect program.conversions program.body parameters locals) fun value =>
  Op.bind (closeAll locals) fun _ =>
  Op.bind (closeAll parameters) fun _ => Op.pure value

/-- Public execution rejects unsupported syntax in the entire declaration and
statement tree before changing state, even if runtime branching would skip it. -/
def runProgram {parameters : List ArithmeticType} {result : IntType}
    (program : StateSyntax.Program target parameters result) :
    Op target (VariableTypes parameters) Environment (Value target result) := fun initial =>
  match program.firstUnsupported with
  | some feature => Op.reject (.unsupported feature) initial
  | none => execute program initial.inputs initial

/-- Independent entry resource condition, not a success/NoUB/postcondition
premise. For this no-interference, fresh-registry slice the total count is the
number of simultaneously required abstract automatic-object slots. -/
def Entry {parameters : List ArithmeticType} {result : IntType}
    (program : StateSyntax.Program target parameters result)
    (initial : State target (VariableTypes parameters) Environment) : Prop :=
  initial.WellFormed ∧ parameters.length + program.body.localCount ≤ initial.automaticSlots

@[simp] theorem reserveAll_nil (dialect : Dialect) :
    (reserveAll dialect [] : Op target stateParameters Environment _) = Op.pure .nil := rfl

@[simp] theorem closeAll_nil :
    (closeAll .nil : Op target stateParameters Environment Unit) = Op.pure () := rfl

/-- Coverage is a separate obligation and precedes even a resource refusal. -/
theorem unsupported_unchanged {parameters : List ArithmeticType} {result : IntType}
    (program : StateSyntax.Program target parameters result)
    (initial : State target (VariableTypes parameters) Environment)
    (feature : UnsupportedFeature) (unsupported : program.firstUnsupported = some feature) :
    runProgram program initial = (.error (.unsupported feature), initial, []) := by
  simp only [runProgram, unsupported, Op.reject]

theorem runProgram_supported {parameters : List ArithmeticType} {result : IntType}
    (program : StateSyntax.Program target parameters result)
    (initial : State target (VariableTypes parameters) Environment)
    (supported : program.Supported) :
    runProgram program initial = execute program initial.inputs initial := by
  simp only [runProgram, program.firstUnsupported_eq_none_iff.mpr supported]

/-- The independent entry domain is inhabited for every actual external input
and environment value. No program execution or result is used as admission. -/
theorem entry_inhabited {parameters : List ArithmeticType} {result : IntType}
    (program : StateSyntax.Program target parameters result)
    (inputs : CallInputs target parameters) (environment : Environment) (actor : Nat) :
    ∃ initial, initial.inputs = inputs ∧ initial.environment = environment ∧ Entry program initial := by
  refine ⟨State.empty inputs environment actor (parameters.length + program.body.localCount),
    rfl, rfl, ?_, Nat.le_refl _⟩
  exact State.empty_wellFormed inputs environment actor _

end EDSL.Source.Objects.BlockEval
