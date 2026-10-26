/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.FunctionContracts
import EDSL.Source.Objects.Control.StructuredVC
import EDSL.Source.Objects.BlockVC
import EDSL.Source.Objects.ParameterContracts

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.FunctionVC
open StateSyntax Protocol

/-! Structural function obligations for the existing declaration fold, control
machine and normal cleanup. No expression interpreter or bounded execution is
part of the generator. Whole-tree support is an independent preflight premise.
Annotations supply invariants/ranks; admission must independently describe
inputs, resources and registry metadata. This is an internal, sequential object
semantics result, not a frontend, source-progress, OS or compiler theorem. -/

variable {target : Target} {stateParameters : List IntType} {Environment : Type}
variable {parameters : List ArithmeticType} {result : IntType}

/-- A generic logical fold over the actual typed declaration spine. The only
primitive leaf introduced by a declaration is its actual initialization WP;
optional RHS obligations come from the existing expression VC engine. -/
def vcFold {Body : List ArithmeticType → IntType → Type} {α : Type}
    (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bodyVC : ∀ {context}, Body context result → Env context →
      Post target stateParameters Environment α → State target stateParameters Environment → Prop) :
    {context : List ArithmeticType} →
    (declarations : DeclarationSpine target Body context result) → Env context →
    Env declarations.localKinds → Post target stateParameters Environment α →
    State target stateParameters Environment → Prop
  | _, .body code, bindings, _, post => bodyVC code bindings post
  | _, .declare _ initial rest, bindings, plan, post =>
    match plan with
    | .cons reference tail =>
      BlockVC.vcInitializer policy bindings initial
        (fun original value middle reads =>
          WP («initialize» dialect reference value)
            (fun _ _ updated starts =>
              vcFold (Body := Body) dialect policy bodyVC rest (bindings.extend reference) tail
                (fun _ answer final suffix => post original answer final (reads ++ (starts ++ suffix)))
                updated) middle)

@[simp] theorem vcFold_body {Body : List ArithmeticType → IntType → Type} {α : Type}
    (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bodyVC : ∀ {context}, Body context result → Env context →
      Post target stateParameters Environment α → State target stateParameters Environment → Prop)
    {context : List ArithmeticType} (code : Body context result) (bindings : Env context)
    (plan : Env (DeclarationSpine.body code).localKinds)
    (post : Post target stateParameters Environment α) (state : State target stateParameters Environment) :
    vcFold (Body := Body) dialect policy bodyVC (.body code) bindings plan post state = bodyVC code bindings post state := rfl

@[simp] theorem vcFold_declare {Body : List ArithmeticType → IntType → Type} {α : Type}
    (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bodyVC : ∀ {context}, Body context result → Env context →
      Post target stateParameters Environment α → State target stateParameters Environment → Prop)
    {context : List ArithmeticType} (kind : ArithmeticType)
    (initial : Option (RHS target context kind.asIntType))
    (rest : DeclarationSpine target Body (kind :: context) result) (bindings : Env context)
    (reference : LValue kind) (tail : Env rest.localKinds)
    (post : Post target stateParameters Environment α) (state : State target stateParameters Environment) :
    vcFold (Body := Body) dialect policy bodyVC (.declare kind initial rest) bindings (.cons reference tail) post state =
      BlockVC.vcInitializer policy bindings initial
        (fun original value middle reads =>
          WP («initialize» dialect reference value)
            (fun _ _ updated starts =>
              vcFold (Body := Body) dialect policy bodyVC rest (bindings.extend reference) tail
                (fun _ answer final suffix => post original answer final (reads ++ (starts ++ suffix)))
                updated) middle) state := by
  cases initial <;> rfl

/-- Exact generic fold fusion at the logical level, including all initializer
effects. The terminal language/operation is arbitrary; no control run is used. -/
theorem vcFold_iff_wp {Body : List ArithmeticType → IntType → Type} {α : Type}
    (dialect : Dialect) (policy : IntegerConversionPolicy)
    (onBody : ∀ {context}, Body context result → Env context → Op target stateParameters Environment α)
    (bodyVC : ∀ {context}, Body context result → Env context →
      Post target stateParameters Environment α → State target stateParameters Environment → Prop)
    (correct : ∀ {context} (code : Body context result) bindings post state,
      bodyVC code bindings post state ↔ WP (onBody code bindings) post state)
    {context : List ArithmeticType} (declarations : DeclarationSpine target Body context result)
    (bindings : Env context) (plan : Env declarations.localKinds)
    (post : Post target stateParameters Environment α) (state : State target stateParameters Environment) :
    vcFold (Body := Body) dialect policy bodyVC declarations bindings plan post state ↔
      WP (declarations.fold dialect policy onBody bindings plan) post state := by
  induction declarations generalizing post state with
  | body code => exact correct code bindings post state
  | declare kind initial rest ih =>
      cases plan with
      | cons reference tail =>
          cases initial <;>
            simp only [vcFold, BlockVC.vcInitializer_iff_wp dialect, DeclarationSpine.fold,
              wp_bind, wp_pure, List.append_nil]
          · apply wp_congr
            intro original ignored updated starts
            exact ih onBody bodyVC correct _ tail _ updated
          · apply wp_congr
            intro original value middle reads
            apply wp_congr
            intro ignored ignoredUnit updated starts
            exact ih onBody bodyVC correct _ tail _ updated

/-- Function specialization of the generic logical fold, with a stable
constructor API for the dependently typed prepared-body continuation. -/
def vcPrepare (dialect : Dialect) (policy : IntegerConversionPolicy)
    {context : List ArithmeticType} (declarations : FunctionDeclarations target context result)
    (bindings : Env context) (plan : Env declarations.localKinds)
    (post : Post target stateParameters Environment (PreparedBody target result))
    (state : State target stateParameters Environment) : Prop :=
  vcFold (Body := Code target) dialect policy
    (fun {context} code environment terminal current =>
      terminal current (⟨context, environment, code⟩ : PreparedBody target result) current [])
    declarations bindings plan post state

@[simp] theorem vcPrepare_body (dialect : Dialect) (policy : IntegerConversionPolicy)
    {context : List ArithmeticType} (code : Code target context result) (bindings : Env context)
    (plan : Env []) (post : Post target stateParameters Environment (PreparedBody target result))
    (state : State target stateParameters Environment) :
    vcPrepare dialect policy (.body code) bindings plan post state =
      post state ⟨context, bindings, code⟩ state [] := rfl

@[simp] theorem vcPrepare_declare (dialect : Dialect) (policy : IntegerConversionPolicy)
    {context : List ArithmeticType} (kind : ArithmeticType)
    (initial : Option (RHS target context kind.asIntType))
    (rest : FunctionDeclarations target (kind :: context) result) (bindings : Env context)
    (reference : LValue kind) (tail : Env rest.localKinds)
    (post : Post target stateParameters Environment (PreparedBody target result))
    (state : State target stateParameters Environment) :
    vcPrepare dialect policy (.declare kind initial rest) bindings (.cons reference tail) post state =
      BlockVC.vcInitializer policy bindings initial
        (fun original value middle reads => WP («initialize» dialect reference value)
          (fun _ _ updated starts => vcPrepare dialect policy rest (bindings.extend reference) tail
            (fun _ prepared final suffix => post original prepared final (reads ++ (starts ++ suffix)))
            updated) middle) state := by
  cases initial <;> rfl

theorem vcPrepare_iff_wp (dialect : Dialect) (policy : IntegerConversionPolicy)
    {context : List ArithmeticType} (declarations : FunctionDeclarations target context result)
    (bindings : Env context) (plan : Env declarations.localKinds)
    (post : Post target stateParameters Environment (PreparedBody target result))
    (state : State target stateParameters Environment) :
    vcPrepare dialect policy declarations bindings plan post state ↔
      WP (declarations.fold dialect policy
        (fun {context} code environment => Op.pure (⟨context, environment, code⟩ : PreparedBody target result))
        bindings plan) post state :=
  vcFold_iff_wp (Body := Code target) dialect policy
    (fun {context} code environment => Op.pure (⟨context, environment, code⟩ : PreparedBody target result))
    (fun {context} code environment terminal current =>
      terminal current (⟨context, environment, code⟩ : PreparedBody target result) current [])
    (fun _ _ _ _ => Iff.rfl) declarations bindings plan post state

/-- Normal cleanup computes the scalar first, closes locals in reverse order,
then parameters in reverse order. The post sees the complete earlier history. -/
def vcCleanup {locals : List ArithmeticType} (localBindings : Env locals)
    (parameterBindings : Env parameters) (value : Value target result)
    (post : Value target result → StructuredVC.Assertion target stateParameters Environment) :
    StructuredVC.Assertion target stateParameters Environment := fun state earlier =>
  WP (BlockEval.closeAll localBindings) (fun _ _ afterLocals localEvents =>
    WP (BlockEval.closeAll parameterBindings) (fun _ _ final parameterEvents =>
      post value final (earlier ++ (localEvents ++ parameterEvents))) afterLocals) state

theorem vcCleanup_iff_wp (entry : FunctionEntry target parameters result) (value : Value target result)
    (post : Value target result → StructuredVC.Assertion target stateParameters Environment)
    (state : State target stateParameters Environment) (earlier : List Event) :
    vcCleanup entry.localBindings entry.parameterBindings value post state earlier ↔
      WP (FunctionEval.cleanup entry value)
        (fun _ returned final suffix => post returned final (earlier ++ suffix)) state := by
  simp only [vcCleanup, FunctionEval.cleanup, wp_bind, wp_pure, List.append_nil]

/-- Live cleanup authority transports across an exact registry/world frame. -/
theorem liveBindings_transport {kinds : List ArithmeticType} (bindings : Env kinds)
    (before after : State target stateParameters Environment)
    (actor : after.actor = before.actor)
    (frame : ∀ id ∈ bindings.ids, after.objects id = before.objects id)
    (live : BlockContracts.LiveBindings before bindings) :
    BlockContracts.LiveBindings after bindings := by
  induction bindings with
  | nil => trivial
  | cons reference tail ih =>
      refine ⟨?_, ih (fun id member => frame id (List.mem_cons_of_mem _ member)) live.2⟩
      obtain ⟨value, permissions, registered⟩ :=
        (LifecycleContracts.canEnd_iff_snapshot reference before).mp live.1
      apply (LifecycleContracts.canEnd_iff_snapshot reference after).mpr
      exact ⟨value, permissions, by rw [frame reference.id (List.mem_cons_self), actor]; exact registered⟩

/-- Generic two-plan lifecycle contract. All premises concern current registry
metadata, distinct identities and live ownership. Actual reverse cleanup,
restored slots, tombstones and caller framing are conclusions. -/
theorem cleanup_contract (entry : FunctionEntry target parameters result) (value : Value target result)
    (state : State target stateParameters Environment) (metadata : state.WellFormed)
    (localUnique : entry.localBindings.Unique) (parameterUnique : entry.parameterBindings.Unique)
    (disjoint : ∀ id ∈ entry.parameterBindings.ids, id ∉ entry.localBindings.ids)
    (localsLive : BlockContracts.LiveBindings state entry.localBindings)
    (parametersLive : BlockContracts.LiveBindings state entry.parameterBindings) :
    ∃ final,
      FunctionEval.cleanup entry value state =
        (.ok value, final, BlockContracts.closingEvents entry.localBindings ++
          BlockContracts.closingEvents entry.parameterBindings) ∧
      LifecycleContracts.Frozen state final ∧ final.next = state.next ∧
      final.automaticSlots = state.automaticSlots + entry.localKinds.length + parameters.length ∧
      final.WellFormed ∧
      BlockContracts.EndedBindings state.actor final entry.localBindings ∧
      BlockContracts.EndedBindings state.actor final entry.parameterBindings ∧
      (∀ id, id ∉ entry.localBindings.ids → id ∉ entry.parameterBindings.ids →
        final.objects id = state.objects id) := by
  obtain ⟨middle, closeLocals, frozenL, nextL, slotsL, metaL, endedL, frameL⟩ :=
    BlockContracts.closeAll_contract entry.localBindings state metadata localUnique localsLive
  have liveP := liveBindings_transport entry.parameterBindings state middle frozenL.2.2
    (fun id member => frameL id (disjoint id member)) parametersLive
  obtain ⟨final, closeParameters, frozenP, nextP, slotsP, metaP, endedP, frameP⟩ :=
    BlockContracts.closeAll_contract entry.parameterBindings middle metaL parameterUnique liveP
  refine ⟨final, ?_, ⟨frozenP.1.trans frozenL.1, frozenP.2.1.trans frozenL.2.1,
    frozenP.2.2.trans frozenL.2.2⟩, nextP.trans nextL, ?_, metaP, ?_, ?_, ?_⟩
  · simp only [FunctionEval.cleanup, Op.bind, Effects.Op.bind, closeLocals, closeParameters, Op.pure, List.append_nil]
  · rw [slotsP, slotsL]
  · apply BlockContracts.endedBindings_transport entry.localBindings state.actor middle final _ endedL
    intro id member
    apply frameP id
    intro inParameters
    exact disjoint id inParameters member
  · rw [← frozenL.2.2]
    exact endedP
  · intro id outsideL outsideP
    exact (frameP id outsideP).trans (frameL id outsideL)

/-- An annotation family may depend on the caller prestate and on the actual
prepared code/bindings. It is proof data, never an execution input. -/
abbrev Annotations (target : Target) (parameters : List ArithmeticType) (result : IntType)
    (Environment : Type) :=
  State target (VariableTypes parameters) Environment →
    (prepared : PreparedBody target result) →
      StructuredVC.Annotation (parameters := VariableTypes parameters)
        (Environment := Environment) prepared.code

/-- Structural entry layer with an arbitrary prepared-body contract. Clients
can compose segments separately, or instantiate it with generated control VCs.
The operation-level leaves are parameter entry, reservation and initialization. -/
def vcEntry (function : Function target parameters result)
    (post : Post target (VariableTypes parameters) Environment (FunctionEntry target parameters result))
    (initial : State target (VariableTypes parameters) Environment) : Prop :=
  WP (BlockEval.enterParameters function.dialect initial.inputs)
    (fun original parameterBindings afterParameters parameterEvents =>
      WP (BlockEval.reserveAll function.dialect function.body.localKinds)
        (fun _ localBindings afterReserve reserveEvents =>
          vcPrepare function.dialect function.conversions
            function.body parameterBindings localBindings
            (fun _ prepared middle initializerEvents =>
              post original ⟨prepared, parameterBindings, function.body.localKinds, localBindings⟩
                middle (parameterEvents ++ (reserveEvents ++ initializerEvents)))
            afterReserve) afterParameters) initial

theorem vcEntry_iff_wp (function : Function target parameters result)
    (post : Post target (VariableTypes parameters) Environment (FunctionEntry target parameters result))
    (initial : State target (VariableTypes parameters) Environment) :
    vcEntry function post initial ↔ WP (FunctionEval.enterUnchecked function initial.inputs) post initial := by
  unfold vcEntry FunctionEval.enterUnchecked
  simp only [wp_bind, wp_pure, List.append_nil]
  apply wp_congr
  intro original parameterBindings afterParameters parameterEvents
  apply wp_congr
  intro ignored localBindings afterReserve reserveEvents
  exact vcPrepare_iff_wp function.dialect function.conversions function.body parameterBindings localBindings _ afterReserve

/-- Backward continuation composition fuses with the existing operational fold
law. This also permits a terminal operation without another declaration walk. -/
theorem vcPrepare_bind_iff_wp {α : Type} (dialect : Dialect) (policy : IntegerConversionPolicy)
    {context : List ArithmeticType} (declarations : FunctionDeclarations target context result)
    (bindings : Env context) (plan : Env declarations.localKinds)
    (next : PreparedBody target result → Op target stateParameters Environment α)
    (post : Post target stateParameters Environment α) (state : State target stateParameters Environment) :
    vcPrepare dialect policy declarations bindings plan
      (fun original prepared middle earlier => WP (next prepared)
        (fun _ answer final suffix => post original answer final (earlier ++ suffix)) middle) state ↔
      WP (declarations.fold dialect policy (fun {context} code environment =>
        Op.bind (Op.pure (⟨context, environment, code⟩ : PreparedBody target result)) next) bindings plan)
        post state := by
  rw [← DeclarationSpine.fold_bind, wp_bind]
  exact vcPrepare_iff_wp dialect policy declarations bindings plan _ state

/-- Entry obligations use actual parameter and reservation operations and the
structural initializer fold. The terminal clause generates StructuredVC for
the actual prepared body; its return continuation demands actual cleanup. -/
def vcExecute (function : Function target parameters result)
    (annotations : Annotations target parameters result Environment)
    (post : Post target (VariableTypes parameters) Environment (Value target result))
    (initial : State target (VariableTypes parameters) Environment) : Prop :=
  vcEntry function (fun original entry middle earlier =>
    StructuredVC.vc function.conversions entry.bindings (annotations original entry.toPreparedBody)
      (fun _ _ => False)
      (fun value => vcCleanup entry.localBindings entry.parameterBindings value (post original))
      middle earlier) initial

/-- The generated entry formula reaches the *actual* FunctionEntry, retaining
the exact parameter/local plans and event prefix used by the wrapper. -/
theorem vcExecute_iff_entry (function : Function target parameters result)
    (annotations : Annotations target parameters result Environment)
    (post : Post target (VariableTypes parameters) Environment (Value target result))
    (initial : State target (VariableTypes parameters) Environment) :
    vcExecute function annotations post initial ↔
      WP (FunctionEval.enterUnchecked function initial.inputs)
        (fun original entry middle earlier =>
          StructuredVC.vc function.conversions entry.bindings
            (annotations original entry.toPreparedBody) (fun _ _ => False)
            (fun value => vcCleanup entry.localBindings entry.parameterBindings value (post original))
            middle earlier) initial :=
  vcEntry_iff_wp function _ initial

/-- Finite compositional control completion lifts through real cleanup to the
public returned observation. An internal Code return alone is insufficient. -/
theorem observe_of_segment (function : Function target parameters result)
    (entry : FunctionEntry target parameters result)
    (initial : State target stateParameters Environment) (earlier : List Event)
    (post : Value target result → StructuredVC.Assertion target stateParameters Environment)
    (progress : StructuredVC.Segment function.dialect function.conversions entry.bindings entry.code
      (fun _ _ => False)
      (fun value => vcCleanup entry.localBindings entry.parameterBindings value post) initial earlier) :
    ∃ steps value final events,
      FunctionEval.observe function steps
        (.active ⟨entry, startUnchecked entry.code initial earlier⟩) = .returned value final events ∧
      post value final events := by
  obtain ⟨steps, exit, middle, history, member, reached⟩ := progress
  cases exit with
  | next => exact member.elim
  | returned value =>
      obtain ⟨answer, final, suffix, closed, resultPost⟩ :=
        (wp_iff _ _ _).mp ((vcCleanup_iff_wp entry value post middle history).mp member)
      refine ⟨steps + 1, answer, final, history ++ suffix, ?_, resultPost⟩
      rw [FunctionEval.observe_active_settle]
      have actual := reached []
      simp only [actual, StructuredVC.endpoint, FunctionEval.tick, closed]

/-- Body failure is retained without starting cleanup, even when a cleanup
plan could otherwise fail. No metadata or successful-result premise is needed. -/
theorem observe_body_failure (function : Function target parameters result)
    (frame : FunctionEval.Active target parameters stateParameters Environment result)
    (steps : Nat) (reason : Stop) (state : State target stateParameters Environment) (events : List Event)
    (reached : run function.dialect function.conversions frame.entry.bindings steps frame.config =
      ⟨[], state, events, .stopped reason⟩) :
    FunctionEval.observe function (steps + 1) (.active frame) = .stopped reason state events := by
  rw [FunctionEval.observe_active_settle, reached]
  rfl

/-- Cleanup failure follows the evaluated return and retains accepted body and
partial cleanup effects; it is a stopped observation, never a public return. -/
theorem observe_cleanup_failure (function : Function target parameters result)
    (frame : FunctionEval.Active target parameters stateParameters Environment result)
    (steps : Nat) (value : Value target result)
    (middle final : State target stateParameters Environment) (bodyEvents suffix : List Event)
    (reason : Stop)
    (reached : run function.dialect function.conversions frame.entry.bindings steps frame.config =
      ⟨[], middle, bodyEvents, .returned value⟩)
    (failed : FunctionEval.cleanup frame.entry value middle = (.error reason, final, suffix)) :
    FunctionEval.observe function (steps + 1) (.active frame) =
      .stopped reason final (bodyEvents ++ suffix) := by
  rw [FunctionEval.observe_active_settle, reached]
  simp only [FunctionEval.tick, failed]

/-- A compositional function rule for independently proved structural segments.
Its entry obligations still traverse the typed declarations; body completion
and cleanup are conclusions of the supplied local VC/segment proofs. -/
theorem verifies_of_entry_vc (function : Function target parameters result)
    (supported : function.Supported)
    (admitted : State target (VariableTypes parameters) Environment → Prop)
    (post : Post target (VariableTypes parameters) Environment (Value target result))
    (obligations : ∀ initial, admitted initial → vcEntry function
      (fun original entry middle earlier =>
        StructuredVC.Segment function.dialect function.conversions entry.bindings entry.code
          (fun _ _ => False)
          (fun value => vcCleanup entry.localBindings entry.parameterBindings value (post original))
          middle earlier) initial) :
    FunctionContracts.Verifies function admitted post := by
  intro initial permitted
  obtain ⟨entry, middle, earlier, entered, segment⟩ := (wp_iff _ _ _).mp
    ((vcEntry_iff_wp function _ initial).mp (obligations initial permitted))
  obtain ⟨steps, value, final, events, returned, resultPost⟩ :=
    observe_of_segment function entry middle earlier (post initial) segment
  refine ⟨steps, value, final, events, ?_, resultPost⟩
  rw [FunctionEval.start_supported function initial supported, entered]
  exact returned

/-- Full-function total correctness. Admission is independently supplied;
support scans the entire function before any entry effects. -/
theorem verifies_of_vc (function : Function target parameters result)
    (annotations : Annotations target parameters result Environment)
    (supported : function.Supported)
    (admitted : State target (VariableTypes parameters) Environment → Prop)
    (post : Post target (VariableTypes parameters) Environment (Value target result))
    (obligations : ∀ initial, admitted initial → vcExecute function annotations post initial) :
    FunctionContracts.Verifies function admitted post := by
  intro initial permitted
  obtain ⟨entry, middle, earlier, entered, bodyVC⟩ := (wp_iff _ _ _).mp
    ((vcExecute_iff_entry function annotations post initial).mp (obligations initial permitted))
  have segment := StructuredVC.vc_sound function.dialect function.conversions entry.bindings
    (annotations initial entry.toPreparedBody) _ _ middle earlier bodyVC
  obtain ⟨steps, value, final, events, returned, resultPost⟩ :=
    observe_of_segment function entry middle earlier (post initial) segment
  refine ⟨steps, value, final, events, ?_, resultPost⟩
  rw [FunctionEval.start_supported function initial supported, entered]
  exact returned

theorem certificate_of_vc (function : Function target parameters result)
    (annotations : Annotations target parameters result Environment)
    (supported : function.Supported)
    (admitted : State target (VariableTypes parameters) Environment → Prop)
    (post : Post target (VariableTypes parameters) Environment (Value target result))
    (useful : ∃ initial, admitted initial)
    (obligations : ∀ initial, admitted initial → vcExecute function annotations post initial) :
    FunctionContracts.Certificate function admitted post :=
  ⟨useful, verifies_of_vc function annotations supported admitted post obligations⟩

end EDSL.Source.Objects.Control.FunctionVC
