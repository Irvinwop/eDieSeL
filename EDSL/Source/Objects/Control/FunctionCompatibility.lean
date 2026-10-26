/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.FunctionEval

set_option autoImplicit false
namespace EDSL.Source.Objects.Control
open StateSyntax

/-! Exact compatibility of finite function entry, body and normal cleanup.
The state and event carrier is the existing object semantics. No well-formedness,
successful execution or safety premise is imposed on the initial state. These
results do not establish source-standard loop/progress or native correspondence. -/

namespace FunctionCompatibility

private theorem bind_assoc {target : Target} {parameters : List IntType}
    {Environment α β γ : Type} (first : Op target parameters Environment α)
    (next : α → Op target parameters Environment β)
    (last : β → Op target parameters Environment γ) :
    Op.bind (Op.bind first next) last =
      Op.bind first (fun value => Op.bind (next value) last) :=
  congrArg EffectM.run (EffectM.bind_assoc (EffectM.ofOp first)
    (fun value => EffectM.ofOp (next value)) (fun value => EffectM.ofOp (last value)))

private theorem pure_bind {target : Target} {parameters : List IntType}
    {Environment α β : Type} (value : α) (next : α → Op target parameters Environment β) :
    Op.bind (Op.pure value) next = next value :=
  congrArg EffectM.run (EffectM.bind_pure_left value
    (fun value => EffectM.ofOp (next value)))

/-- A terminal body in any language, together with its actual active bindings. -/
structure Prepared (target : Target) (Body : List ArithmeticType → IntType → Type)
    (result : IntType) where
  context : List ArithmeticType
  bindings : Env context
  body : Body context result

namespace Prepared
variable {target : Target} {Body OtherBody : List ArithmeticType → IntType → Type}
variable {result : IntType} {parameters : List IntType} {Environment α : Type}

def map (translate : ∀ {context result}, Body context result → OtherBody context result)
    (prepared : Prepared target Body result) : Prepared target OtherBody result :=
  ⟨prepared.context, prepared.bindings, translate prepared.body⟩

def eval (interpret : ∀ {context}, Body context result → Env context →
    Op target parameters Environment α) (prepared : Prepared target Body result) :
    Op target parameters Environment α :=
  interpret prepared.body prepared.bindings

end Prepared
end FunctionCompatibility

namespace DeclarationSpine
open FunctionCompatibility
variable {target : Target} {Body : List ArithmeticType → IntType → Type}
variable {parameters : List IntType} {Environment α β : Type}

/-- Binding after the initializer fold is the same operation as binding only
at its terminal body. All errors and accepted effects use actual Op composition. -/
theorem fold_bind (dialect : Dialect) (policy : IntegerConversionPolicy)
    {result : IntType}
    (onBody : ∀ {context}, Body context result → Env context →
      Op target parameters Environment α)
    (next : α → Op target parameters Environment β)
    {context : List ArithmeticType} (declarations : DeclarationSpine target Body context result)
    (bindings : Env context) (plan : Env declarations.localKinds) :
    Op.bind (fold dialect policy onBody declarations bindings plan) next =
      fold dialect policy (fun body environment => Op.bind (onBody body environment) next)
        declarations bindings plan := by
  induction declarations with
  | body code => rfl
  | declare kind initial rest ih =>
      cases plan with
      | cons reference tail =>
          simp only [fold]
          rw [bind_assoc]
          congr 1
          funext value
          rw [bind_assoc]
          congr 1
          funext ignored
          exact ih onBody (bindings.extend reference) tail

/-- Preparing a body and then interpreting it fuses with the initializer fold. -/
theorem fold_prepared_eval (dialect : Dialect) (policy : IntegerConversionPolicy)
    {result : IntType}
    (interpret : ∀ {context}, Body context result → Env context →
      Op target parameters Environment α)
    {context : List ArithmeticType} (declarations : DeclarationSpine target Body context result)
    (bindings : Env context) (plan : Env declarations.localKinds) :
    Op.bind (fold dialect policy (fun {context} body environment =>
      Op.pure (⟨context, environment, body⟩ : Prepared target Body result))
      declarations bindings plan) (Prepared.eval interpret) =
      fold dialect policy interpret declarations bindings plan := by
  rw [fold_bind]
  simp only [pure_bind, Prepared.eval]

/-- Fold the existing declarations using an arbitrary translated body language.
Only the type-level reservation-plan equality is transported. -/
def foldOfDecls (dialect : Dialect) (policy : IntegerConversionPolicy)
    (translate : ∀ {context result}, Stmt target context result → Body context result)
    {result : IntType}
    (onBody : ∀ {context}, Body context result → Env context →
      Op target parameters Environment α)
    {context : List ArithmeticType} (declarations : Decls target context result)
    (bindings : Env context) (plan : Env declarations.localKinds) :
    Op target parameters Environment α :=
  fold dialect policy onBody (ofDecls translate declarations) bindings
    (cast (congrArg Env (ofDecls_localKinds translate declarations).symm) plan)

private theorem cast_env_cons {first second : List ArithmeticType} {kind : ArithmeticType}
    (same : first = second) (reference : LValue kind) (tail : Env first) :
    cast (congrArg Env (congrArg (List.cons kind) same)) (.cons reference tail) =
      .cons reference (cast (congrArg Env same) tail) := by
  cases same
  rfl

/-- Translating only the body commutes with the declaration fold. -/
theorem foldOfDecls_translate (dialect : Dialect) (policy : IntegerConversionPolicy)
    (translate : ∀ {context result}, Stmt target context result → Body context result)
    {result : IntType}
    (onBody : ∀ {context}, Body context result → Env context →
      Op target parameters Environment α)
    {context : List ArithmeticType} (declarations : Decls target context result)
    (bindings : Env context) (plan : Env declarations.localKinds) :
    foldOfDecls dialect policy translate onBody declarations bindings plan =
      foldOfDecls dialect policy (fun statement => statement)
        (fun statement environment => onBody (translate statement) environment)
        declarations bindings plan := by
  induction declarations with
  | body statement => rfl
  | declare kind initial rest ih =>
      cases plan with
      | cons reference tail =>
          have converted (tr : ∀ {context result}, Stmt target context result →
              Body context result) :
              cast (congrArg Env (ofDecls_localKinds tr
                (Decls.declare kind initial rest)).symm) (.cons reference tail) =
              .cons reference (cast (congrArg Env (ofDecls_localKinds tr rest).symm) tail) :=
            cast_env_cons (ofDecls_localKinds tr rest).symm reference tail
          have convertedId := cast_env_cons
            (ofDecls_localKinds (fun statement => statement) rest).symm reference tail
          unfold foldOfDecls
          rw [converted translate, show
            cast (congrArg Env (ofDecls_localKinds (fun statement => statement)
              (Decls.declare kind initial rest)).symm) (.cons reference tail) = _ from convertedId]
          cases initial <;> simp only [ofDecls, fold]
          all_goals
            congr 1
            funext value
            congr 1
            funext ignored
            exact ih onBody (bindings.extend reference) tail

theorem foldOfDecls_evalStmt (dialect : Dialect) (policy : IntegerConversionPolicy)
    {context : List ArithmeticType} {result : IntType}
    (declarations : Decls target context result) (bindings : Env context)
    (plan : Env declarations.localKinds) :
    (foldOfDecls dialect policy (fun statement => statement)
      (fun statement environment => StateEval.evalStmt dialect policy environment statement)
      declarations bindings plan : Op target parameters Environment (Value target result)) =
      BlockEval.evalDecls dialect policy declarations bindings plan := by
  unfold foldOfDecls
  rw [fold_ofDecls_eq]
  simp only [cast_cast, cast_eq]

theorem foldOfDecls_bind (dialect : Dialect) (policy : IntegerConversionPolicy)
    (translate : ∀ {context result}, Stmt target context result → Body context result)
    {result : IntType}
    (onBody : ∀ {context}, Body context result → Env context →
      Op target parameters Environment α)
    (next : α → Op target parameters Environment β)
    {context : List ArithmeticType} (declarations : Decls target context result)
    (bindings : Env context) (plan : Env declarations.localKinds) :
    Op.bind (foldOfDecls dialect policy translate onBody declarations bindings plan) next =
      foldOfDecls dialect policy translate
        (fun body environment => Op.bind (onBody body environment) next)
        declarations bindings plan := by
  exact fold_bind dialect policy onBody next _ _ _

theorem foldOfDecls_prepared_eval (dialect : Dialect) (policy : IntegerConversionPolicy)
    (translate : ∀ {context result}, Stmt target context result → Body context result)
    {result : IntType}
    (interpret : ∀ {context}, Body context result → Env context →
      Op target parameters Environment α)
    {context : List ArithmeticType} (declarations : Decls target context result)
    (bindings : Env context) (plan : Env declarations.localKinds) :
    Op.bind (foldOfDecls dialect policy translate (fun {context} body environment =>
      Op.pure (⟨context, environment, body⟩ : Prepared target Body result))
      declarations bindings plan) (Prepared.eval interpret) =
      foldOfDecls dialect policy translate interpret declarations bindings plan := by
  exact fold_prepared_eval dialect policy interpret _ _ _

/-- Body preparation commutes with arbitrary terminal-body translation. -/
theorem foldOfDecls_prepared_map (dialect : Dialect) (policy : IntegerConversionPolicy)
    (translate : ∀ {context result}, Stmt target context result → Body context result)
    {context : List ArithmeticType} {result : IntType}
    (declarations : Decls target context result) (bindings : Env context)
    (plan : Env declarations.localKinds) :
    (Op.bind (foldOfDecls dialect policy (fun statement => statement)
      (fun {context} body environment =>
        Op.pure (⟨context, environment, body⟩ : Prepared target (Stmt target) result))
      declarations bindings plan) (fun prepared => Op.pure (prepared.map translate)) :
        Op target parameters Environment (Prepared target Body result)) =
      foldOfDecls dialect policy translate (fun {context} body environment =>
        Op.pure (⟨context, environment, body⟩ : Prepared target Body result))
        declarations bindings plan := by
  rw [foldOfDecls_bind, foldOfDecls_translate dialect policy translate]
  simp only [pure_bind, Prepared.map]

end DeclarationSpine

namespace FunctionCompatibility
variable {target : Target} {parameters : List ArithmeticType} {result : IntType}
variable {stateParameters : List IntType} {Environment : Type}

/-- A finite prepared entry retaining the original statement as a witness for
the existing body-compatibility theorem, and the actual cleanup plans. -/
structure FiniteEntry (target : Target) (parameters : List ArithmeticType) (result : IntType)
    extends Prepared target (Stmt target) result where
  parameterBindings : Env parameters
  localKinds : List ArithmeticType
  localBindings : Env localKinds

def FiniteEntry.toFunctionEntry (entry : FiniteEntry target parameters result) :
    FunctionEntry target parameters result :=
  ⟨⟨entry.context, entry.bindings, Code.ofStmt entry.body⟩,
    entry.parameterBindings, entry.localKinds, entry.localBindings⟩

/-- The same actual entry operations, retaining the finite body before its
embedding. This operation has no preflight gate or admission premise. -/
def prepareProgram (program : StateSyntax.Program target parameters result)
    (inputs : CallInputs target parameters) :
    Op target stateParameters Environment (FiniteEntry target parameters result) :=
  Op.bind (BlockEval.enterParameters program.dialect inputs) fun parameterBindings =>
  Op.bind (BlockEval.reserveAll program.dialect program.body.localKinds) fun localBindings =>
  Op.bind (DeclarationSpine.foldOfDecls program.dialect program.conversions
    (fun statement => statement) (fun {context} statement bindings =>
      Op.pure (⟨context, bindings, statement⟩ : Prepared target (Stmt target) result))
    program.body parameterBindings localBindings) fun prepared =>
  Op.pure ⟨prepared, parameterBindings, program.body.localKinds, localBindings⟩

private theorem reserve_transport {α : Type} (dialect : Dialect)
    {first second : List ArithmeticType} (same : first = second)
    (next : Env first → Op target stateParameters Environment α) :
    Op.bind (BlockEval.reserveAll dialect first) next =
      Op.bind (BlockEval.reserveAll dialect second)
        (fun plan => next (cast (congrArg Env same.symm) plan)) := by
  cases same
  rfl

private theorem entry_transport (prepared : PreparedBody target result)
    (parameterBindings : Env parameters) {first second : List ArithmeticType}
    (same : first = second) (plan : Env second) :
    (⟨prepared, parameterBindings, first, cast (congrArg Env same.symm) plan⟩ :
      FunctionEntry target parameters result) =
      ⟨prepared, parameterBindings, second, plan⟩ := by
  cases same
  rfl

/-- Exact entry operation equality, including entry errors and their effects. -/
theorem enterUnchecked_ofProgram (program : StateSyntax.Program target parameters result)
    (inputs : CallInputs target parameters) :
    (FunctionEval.enterUnchecked (Function.ofProgram program) inputs :
      Op target stateParameters Environment (FunctionEntry target parameters result)) =
      Op.bind (prepareProgram program inputs) (fun entry => Op.pure entry.toFunctionEntry) := by
  unfold FunctionEval.enterUnchecked Function.ofProgram prepareProgram
  simp only [bind_assoc, pure_bind]
  congr 1
  funext parameterBindings
  rw [reserve_transport program.dialect
    (DeclarationSpine.ofDecls_localKinds Code.ofStmt program.body)]
  congr 1
  funext localBindings
  change Op.bind (DeclarationSpine.foldOfDecls program.dialect program.conversions Code.ofStmt
    (fun {context} code bindings =>
      Op.pure (⟨context, bindings, code⟩ : PreparedBody target result))
    program.body parameterBindings localBindings) _ = _
  rw [DeclarationSpine.foldOfDecls_bind, DeclarationSpine.foldOfDecls_translate,
    DeclarationSpine.foldOfDecls_bind]
  simp only [pure_bind]
  congr 1
  funext context statement bindings
  apply congrArg Op.pure
  exact entry_transport _ parameterBindings
    (DeclarationSpine.ofDecls_localKinds Code.ofStmt program.body) localBindings

/-- Preparing the finite body, evaluating it, and actually cleaning up is the
old unchecked execution operation, on every state including any failure. -/
theorem execute_eq_prepare (program : StateSyntax.Program target parameters result)
    (inputs : CallInputs target parameters) :
    (BlockEval.execute program inputs :
      Op target stateParameters Environment (Value target result)) =
      Op.bind (prepareProgram program inputs) (fun entry =>
        Op.bind (StateEval.evalStmt program.dialect program.conversions entry.bindings entry.body)
          (FunctionEval.cleanup entry.toFunctionEntry)) := by
  unfold BlockEval.execute prepareProgram
  simp only [bind_assoc, pure_bind]
  congr 1
  funext parameterBindings
  congr 1
  funext localBindings
  change Op.bind (BlockEval.evalDecls program.dialect program.conversions program.body
      parameterBindings localBindings) _ =
    Op.bind (DeclarationSpine.foldOfDecls program.dialect program.conversions
      (fun statement => statement) (fun {context} statement bindings =>
        Op.pure (⟨context, bindings, statement⟩ : Prepared target (Stmt target) result))
      program.body parameterBindings localBindings)
      (fun prepared => Op.bind
        (Prepared.eval (fun statement bindings =>
          StateEval.evalStmt program.dialect program.conversions bindings statement) prepared)
        (fun value => Op.bind (BlockEval.closeAll localBindings) fun _ =>
          Op.bind (BlockEval.closeAll parameterBindings) fun _ => Op.pure value))
  conv =>
    rhs
    rw [← bind_assoc, DeclarationSpine.foldOfDecls_prepared_eval,
      DeclarationSpine.foldOfDecls_evalStmt]

/-- An exact finite-driver result, with neither an active nor fallthrough case. -/
def ofResult (evaluation : Result target stateParameters Environment (Value target result)) :
    FunctionEval.Observation target parameters stateParameters Environment result :=
  match evaluation with
  | (.error reason, state, events) => .stopped reason state events
  | (.ok value, state, events) => .returned value state events

def prepend {α : Type} (events : List Event)
    (evaluation : Result target stateParameters Environment α) :
    Result target stateParameters Environment α :=
  (evaluation.1, evaluation.2.1, events ++ evaluation.2.2)

/-- Settling body and cleanup is precisely the original effect bind, including
its failure outcome and all earlier, body and cleanup observations. -/
theorem settleResult_eq_bind (entry : FunctionEntry target parameters result)
    (earlierEvents : List Event)
    (body : Op target stateParameters Environment (Value target result))
    (state : State target stateParameters Environment) :
    FunctionEval.settleResult entry earlierEvents (body state) =
      ofResult (prepend earlierEvents (Op.bind body (FunctionEval.cleanup entry) state)) := by
  rcases evaluation : body state with ⟨outcome, updated, events⟩
  cases outcome with
  | error reason => simp only [FunctionEval.settleResult, Op.bind, Effects.Op.bind, evaluation, prepend, ofResult]
  | ok value =>
      rcases cleaned : FunctionEval.cleanup entry value updated with ⟨outcome, final, moreEvents⟩
      cases outcome <;> simp only [FunctionEval.settleResult, Op.bind, Effects.Op.bind, evaluation, cleaned,
        prepend, ofResult, List.append_assoc]

/-- Full public entry-to-return compatibility for every finite program and
every initial state. Preflight, entry/body/cleanup failures, returned values,
the complete state and the complete event history coincide exactly. -/
theorem runProgram_reaches (program : StateSyntax.Program target parameters result)
    (initial : State target (VariableTypes parameters) Environment) :
    ∃ steps, FunctionEval.observe (Function.ofProgram program) steps
      (FunctionEval.start (Function.ofProgram program) initial) =
      ofResult (BlockEval.runProgram program initial) := by
  cases coverage : program.firstUnsupported with
  | some feature =>
      refine ⟨0, ?_⟩
      simp only [FunctionEval.observe, FunctionEval.start, Function.ofProgram_firstUnsupported,
        coverage, BlockEval.runProgram, Op.reject, ofResult]
  | none =>
      rcases prepared : prepareProgram program initial.inputs initial with
        ⟨outcome, updated, events⟩
      cases outcome with
      | error reason =>
          refine ⟨0, ?_⟩
          simp only [FunctionEval.observe, FunctionEval.start,
            Function.ofProgram_firstUnsupported, coverage, enterUnchecked_ofProgram,
            BlockEval.runProgram, execute_eq_prepare, Op.bind, Effects.Op.bind, prepared, ofResult]
      | ok entry =>
          obtain ⟨steps, reached⟩ := FunctionEval.ofStmt_cleanup_reaches
            (Function.ofProgram program) entry.toFunctionEntry entry.body rfl updated events
          refine ⟨steps, ?_⟩
          have starting : FunctionEval.start (Function.ofProgram program) initial =
              .active ⟨entry.toFunctionEntry,
                startUnchecked entry.toFunctionEntry.code updated events⟩ := by
            simp only [FunctionEval.start, Function.ofProgram_firstUnsupported, coverage,
              enterUnchecked_ofProgram, Op.bind, Effects.Op.bind, prepared, Op.pure, List.append_nil]
          rw [starting, reached, settleResult_eq_bind]
          simp only [BlockEval.runProgram, coverage, execute_eq_prepare, Op.bind, Effects.Op.bind, prepared]
          rfl

/-- Function endpoints absorb observation; active observation exhaustion is
excluded. Fallthrough remains a distinct internal endpoint. -/
def Terminal : FunctionEval.Observation target parameters stateParameters Environment result → Prop
  | .active _ => False
  | .returned _ _ _ | .stopped _ _ _ | .fellThrough _ _ => True

theorem ofResult_terminal
    (evaluation : Result target stateParameters Environment (Value target result)) :
    Terminal (ofResult (parameters := parameters) evaluation) := by
  rcases evaluation with ⟨outcome, state, events⟩
  cases outcome <;> trivial

theorem ofResult_injective :
    _root_.Function.Injective
      (ofResult (target := target) (parameters := parameters)
        (stateParameters := stateParameters) (Environment := Environment) (result := result)) := by
  rintro ⟨first, firstState, firstEvents⟩ ⟨second, secondState, secondEvents⟩ same
  cases first <;> cases second <;> cases same <;> rfl

theorem observe_terminal (function : Function target parameters result) (steps : Nat)
    (current : FunctionEval.Observation target parameters stateParameters Environment result)
    (terminal : Terminal current) : FunctionEval.observe function steps current = current := by
  cases current with
  | active frame => exact False.elim terminal
  | returned value state events => exact FunctionEval.observe_returned function steps value state events
  | stopped reason state events => exact FunctionEval.observe_stopped function steps reason state events
  | fellThrough state events => exact FunctionEval.observe_fellThrough function steps state events

theorem observe_stable_of_terminal (function : Function target parameters result)
    (current : FunctionEval.Observation target parameters stateParameters Environment result)
    (first second : Nat) (ordered : first ≤ second)
    (terminal : Terminal (FunctionEval.observe function first current)) :
    FunctionEval.observe function second current = FunctionEval.observe function first current := by
  have split : second = first + (second - first) := by omega
  rw [split, FunctionEval.observe_add, observe_terminal function _ _ terminal]

/-- Generic uniqueness includes the entire observation, rather than only the
returned scalar or stopped reason. -/
theorem terminal_endpoint_unique (function : Function target parameters result)
    (current : FunctionEval.Observation target parameters stateParameters Environment result)
    (first second : Nat)
    (firstTerminal : Terminal (FunctionEval.observe function first current))
    (secondTerminal : Terminal (FunctionEval.observe function second current)) :
    FunctionEval.observe function first current = FunctionEval.observe function second current := by
  rcases Nat.le_total first second with ordered | ordered
  · exact (observe_stable_of_terminal function current first second ordered firstTerminal).symm
  · exact observe_stable_of_terminal function current second first ordered secondTerminal

/-- Every terminal observation of an embedded finite program is its old public
driver result; in particular it cannot fall through or change a failure. -/
theorem runProgram_terminal_eq (program : StateSyntax.Program target parameters result)
    (initial : State target (VariableTypes parameters) Environment) (steps : Nat)
    (final : FunctionEval.Observation target parameters (VariableTypes parameters) Environment result)
    (reached : FunctionEval.observe (Function.ofProgram program) steps
      (FunctionEval.start (Function.ofProgram program) initial) = final)
    (terminal : Terminal final) : final = ofResult (BlockEval.runProgram program initial) := by
  obtain ⟨canonicalSteps, canonical⟩ := runProgram_reaches program initial
  have same := terminal_endpoint_unique (Function.ofProgram program)
    (FunctionEval.start (Function.ofProgram program) initial) steps canonicalSteps
    (reached.symm ▸ terminal) (canonical.symm ▸ ofResult_terminal _)
  exact reached.symm.trans (same.trans canonical)

/-- Exact whole-program compatibility in both directions, with no independent
admission, execution-success or safety hypothesis. -/
theorem runProgram_terminal_iff (program : StateSyntax.Program target parameters result)
    (initial : State target (VariableTypes parameters) Environment)
    (evaluation : Result target (VariableTypes parameters) Environment (Value target result)) :
    (∃ steps, FunctionEval.observe (Function.ofProgram program) steps
      (FunctionEval.start (Function.ofProgram program) initial) = ofResult evaluation) ↔
      BlockEval.runProgram program initial = evaluation := by
  constructor
  · rintro ⟨steps, reached⟩
    exact ofResult_injective
      (runProgram_terminal_eq program initial steps _ reached (ofResult_terminal evaluation)).symm
  · intro evaluated
    rw [← evaluated]
    exact runProgram_reaches program initial

end FunctionCompatibility
end EDSL.Source.Objects.Control
