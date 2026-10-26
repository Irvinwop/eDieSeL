/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.FunctionVC
import EDSL.Source.Objects.ParameterContracts

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.EntryContracts
open StateSyntax LifecycleContracts BlockContracts ParameterContracts

/-! Checked preparation of literal/absent declaration prefixes. The witness
below refines the existing declaration spine; it supplies construction/proof
data only. Execution is exclusively FunctionEval.enterUnchecked and the shared
DeclarationSpine.fold. General expression initializers remain unrestricted in
those operations and in FunctionVC.

Admissions concern caller metadata, abstract object slots and typed values.
The terminal Code is arbitrary: entry neither executes it nor requires its
support, definedness, termination or postcondition. Whole-code coverage belongs
to the separate public start/verification rules. The model's external world and
actor are frozen; no interference, OS, layout, ABI or native claim is made. -/

variable {target : Target} {stateParameters : List IntType} {Environment : Type}

/-- Typed optional contents in declaration order. Absence is not a zero. -/
inductive InitialValues (target : Target) : List ArithmeticType → Type where
  | nil : InitialValues target []
  | cons {kind : ArithmeticType} {kinds : List ArithmeticType}
      (value : Option (Value target kind.asIntType)) (rest : InitialValues target kinds) :
      InitialValues target (kind :: kinds)

namespace InitialValues

def get {kinds : List ArithmeticType} (values : InitialValues target kinds)
    {kind : ArithmeticType} (index : Vars kinds kind) : Option (Value target kind.asIntType) :=
  match values with
  | .nil => nomatch index
  | .cons (kind := .sint) value tail =>
      match kind, index with
      | .sint, .here => value
      | .sint, .there index => get tail index
      | .uint, .there index => get tail index
  | .cons (kind := .uint) value tail =>
      match kind, index with
      | .uint, .here => value
      | .sint, .there index => get tail index
      | .uint, .there index => get tail index

end InitialValues

/-- A typed refinement of the actual shared syntax, with any terminal language.
There is deliberately no operation, state transformation or body interpreter. -/
inductive LiteralInitializers {Body : List ArithmeticType → IntType → Type} :
    {context : List ArithmeticType} → {result : IntType} →
    DeclarationSpine target Body context result → Type where
  | body {context : List ArithmeticType} {result : IntType} (code : Body context result) :
      LiteralInitializers (.body code)
  | declare {context : List ArithmeticType} {result : IntType} (kind : ArithmeticType)
      (value : Option (Value target kind.asIntType))
      {rest : DeclarationSpine target Body (kind :: context) result}
      (tail : LiteralInitializers rest) :
      LiteralInitializers (.declare kind (value.map Expr.literal) rest)

namespace LiteralInitializers
variable {Body : List ArithmeticType → IntType → Type}
variable {context : List ArithmeticType} {result : IntType}
variable {declarations : DeclarationSpine target Body context result}

def values : {context : List ArithmeticType} → {result : IntType} →
    {declarations : DeclarationSpine target Body context result} →
    LiteralInitializers declarations → InitialValues target declarations.localKinds
  | _, _, _, .body _ => .nil
  | _, _, _, .declare _ value tail => .cons value tail.values

end LiteralInitializers

/-- Exact matching, reached/live, owned records with both permissions. -/
def LocalRecords (owner : Nat) (state : State target stateParameters Environment) :
    {kinds : List ArithmeticType} → Env kinds → InitialValues target kinds → Prop
  | [], .nil, .nil => True
  | kind :: _, .cons reference tail, .cons value rest =>
      state.objects reference.id = some (liveObject kind owner ⟨true, true⟩ value) ∧
      LocalRecords owner state tail rest

theorem localRecords_get {kinds : List ArithmeticType} (bindings : Env kinds)
    (values : InitialValues target kinds) (owner : Nat)
    (state : State target stateParameters Environment)
    (records : LocalRecords owner state bindings values)
    {kind : ArithmeticType} (index : Vars kinds kind) :
    state.objects (bindings.get index).id =
      some (liveObject kind owner ⟨true, true⟩ (values.get index)) := by
  induction bindings with
  | nil => cases index
  | @cons head kinds reference bindings ih =>
      cases values with
      | cons value rest =>
          cases head <;> cases kind <;> cases index
          all_goals first | exact records.1 | exact ih rest records.2 _

/-- A present value admits a read; any optional value admits a write. -/
theorem localRecords_access {kinds : List ArithmeticType} (bindings : Env kinds)
    (values : InitialValues target kinds) (state : State target stateParameters Environment)
    (records : LocalRecords state.actor state bindings values)
    {kind : ArithmeticType} (index : Vars kinds kind) :
    CanStore state (bindings.get index) ∧
      (∀ value, values.get index = some value → CanLoad state (bindings.get index) value) := by
  have registered := localRecords_get bindings values state.actor state records index
  refine ⟨⟨values.get index, ⟨true, true⟩, registered, rfl⟩, ?_⟩
  intro value present
  exact ⟨⟨true, true⟩, by rw [present] at registered; exact registered, rfl⟩

/-- Absent initializers really retain the dialect's uninitialized-read error. -/
theorem localRecords_absent {kinds : List ArithmeticType} (dialect : Dialect)
    (bindings : Env kinds) (values : InitialValues target kinds)
    (state : State target stateParameters Environment)
    (records : LocalRecords state.actor state bindings values)
    {kind : ArithmeticType} (index : Vars kinds kind) (absent : values.get index = none) :
    load dialect (bindings.get index) state =
      (.error (uninitializedRead dialect), state, []) := by
  have registered := localRecords_get bindings values state.actor state records index
  rw [absent] at registered
  exact load_uninitialized dialect state (bindings.get index) ⟨true, true⟩ registered rfl

theorem localRecords_live {kinds : List ArithmeticType} (bindings : Env kinds)
    (values : InitialValues target kinds) (state : State target stateParameters Environment)
    (records : LocalRecords state.actor state bindings values) : LiveBindings state bindings := by
  induction bindings with
  | nil => cases values; trivial
  | cons reference tail ih =>
      cases values with
      | cons value rest =>
          exact ⟨(canEnd_iff_snapshot reference state).mpr ⟨value, ⟨true, true⟩, records.1⟩,
            ih rest records.2⟩

private theorem pendingBindings_transport {kinds : List ArithmeticType} (bindings : Env kinds)
    (dialect : Dialect) (owner : Nat) (before after : State target stateParameters Environment)
    (frame : ∀ id ∈ bindings.ids, after.objects id = before.objects id)
    (pending : PendingBindings dialect owner before bindings) :
    PendingBindings dialect owner after bindings := by
  induction bindings with
  | nil => trivial
  | cons reference tail ih =>
      exact ⟨(frame reference.id List.mem_cons_self).trans pending.1,
        ih (fun id member => frame id (List.mem_cons_of_mem _ member)) pending.2⟩

/-- Binding/code construction only: the same contexts extended in source order
as the real fold. It neither evaluates initializers nor touches a state. -/
def prepared {context : List ArithmeticType} {result : IntType}
    (declarations : FunctionDeclarations target context result) (bindings : Env context)
    (plan : Env declarations.localKinds) : PreparedBody target result :=
  match declarations with
  | .body code => ⟨_, bindings, code⟩
  | .declare _ _ rest =>
      match plan with
      | .cons reference tail => prepared rest (bindings.extend reference) tail

theorem prepared_context {context : List ArithmeticType} {result : IntType}
    (declarations : FunctionDeclarations target context result) (bindings : Env context)
    (plan : Env declarations.localKinds) :
    (prepared declarations bindings plan).context = declarations.finalContext := by
  induction declarations with
  | body code => rfl
  | declare kind initial rest ih => cases plan with | cons reference tail => exact ih _ _

theorem prepared_ids {context : List ArithmeticType} {result : IntType}
    (declarations : FunctionDeclarations target context result) (bindings : Env context)
    (plan : Env declarations.localKinds) :
    (prepared declarations bindings plan).bindings.ids = plan.ids.reverse ++ bindings.ids := by
  induction declarations with
  | body code => cases plan; rfl
  | declare kind initial rest ih =>
      cases plan with
      | cons reference tail =>
          change (prepared rest (bindings.extend reference) tail).bindings.ids = _
          simpa only [Env.ids, List.reverse_cons, List.append_assoc,
            List.singleton_append] using ih (bindings.extend reference) tail

theorem prepared_unique {context : List ArithmeticType} {result : IntType}
    (declarations : FunctionDeclarations target context result) (bindings : Env context)
    (plan : Env declarations.localKinds) (boundUnique : bindings.Unique) (planUnique : plan.Unique)
    (disjoint : ∀ id ∈ bindings.ids, id ∉ plan.ids) :
    (prepared declarations bindings plan).bindings.Unique := by
  induction declarations with
  | body code => exact boundUnique
  | declare kind initial rest ih =>
      cases plan with
      | cons reference tail =>
          obtain ⟨fresh, tailUnique⟩ := (Env.unique_extend_iff tail reference).mp planUnique
          apply ih (bindings.extend reference) tail
          · apply (Env.unique_extend_iff bindings reference).mpr
            refine ⟨?_, boundUnique⟩
            intro member
            exact disjoint reference.id member List.mem_cons_self
          · exact tailUnique
          · intro id member
            simp only [Env.ids, List.mem_cons] at member
            rcases member with same | member
            · exact same ▸ fresh
            · exact fun tailMember => disjoint id member (List.mem_cons_of_mem _ tailMember)

/-- The initialization event specification lists primitive events only. -/
def initializationEvents (dialect : Dialect) : {kinds : List ArithmeticType} →
    Env kinds → InitialValues target kinds → List Event
  | [], .nil, .nil => []
  | kind :: _, .cons reference tail, .cons value rest =>
      initializeEvents dialect reference.id kind (value.map Value.toInt) ++
        initializationEvents dialect tail rest

structure PreparationFacts {kinds : List ArithmeticType} (values : InitialValues target kinds)
    (plan : Env kinds) (before after : State target stateParameters Environment) : Prop where
  metadata : after.WellFormed
  frozen : Frozen before after
  next : after.next = before.next
  slots : after.automaticSlots = before.automaticSlots
  records : LocalRecords before.actor after plan values
  outside : ∀ id, id ∉ plan.ids → after.objects id = before.objects id

/-- One proof for every length and type sequence. Success follows from pending
metadata and uniqueness, without admitting any operation result or Code fact. -/
theorem prepare_contract (dialect : Dialect) (policy : IntegerConversionPolicy)
    {context : List ArithmeticType} {result : IntType}
    {declarations : FunctionDeclarations target context result}
    (literal : LiteralInitializers declarations) (bindings : Env context)
    (plan : Env declarations.localKinds) (state : State target stateParameters Environment)
    (metadata : state.WellFormed) (unique : plan.Unique)
    (pending : PendingBindings dialect state.actor state plan) :
    ∃ final,
      DeclarationSpine.fold dialect policy
        (fun {context} code environment =>
          Op.pure (⟨context, environment, code⟩ : PreparedBody target result))
        declarations bindings plan state =
          (.ok (prepared declarations bindings plan), final,
            initializationEvents dialect plan literal.values) ∧
      PreparationFacts literal.values plan state final := by
  induction literal generalizing state with
  | body code =>
      cases plan
      exact ⟨state, rfl, metadata, ⟨rfl, rfl, rfl⟩, rfl, rfl, trivial, fun _ _ => rfl⟩
  | @declare context result kind value rest literal ih =>
      cases plan with
      | cons reference tail =>
          obtain ⟨fresh, tailUnique⟩ := (Env.unique_extend_iff tail reference).mp unique
          let middle := initializedState reference ⟨true, true⟩ value state
          have middleMeta : middle.WellFormed := initializedState_wellFormed dialect reference
            state ⟨true, true⟩ value metadata pending.1
          have pendingTail : PendingBindings dialect middle.actor middle tail :=
            pendingBindings_transport tail dialect state.actor state middle
              (fun id member => State.putObject_other state reference.id id _ (by
                intro same; exact fresh (same ▸ member))) pending.2
          obtain ⟨final, executed, facts⟩ := ih (bindings.extend reference) tail middle
            middleMeta tailUnique pendingTail
          refine ⟨final, ?_, facts.metadata, facts.frozen, facts.next, facts.slots, ?_, ?_⟩
          · dsimp only [middle] at executed
            dsimp only [Op.pure] at executed
            cases value <;>
              simp only [DeclarationSpine.fold, Option.map, StateEval.evalExpr_literal,
                Op.bind, Effects.Op.bind, Op.pure, List.nil_append,
                initialize_eq dialect reference state ⟨true, true⟩ _ pending.1 rfl,
                executed, prepared, LiteralInitializers.values] <;> rfl
          · exact ⟨(facts.outside reference.id fresh).trans (State.putObject_same state reference.id _),
              facts.records⟩
          · intro id outside
            have different : id ≠ reference.id := by
              intro same; exact outside (by simp only [Env.ids, List.mem_cons]; exact Or.inl same)
            have tailOutside : id ∉ tail.ids := fun member =>
              outside (List.mem_cons_of_mem _ member)
            exact (facts.outside id tailOutside).trans
              (State.putObject_other state reference.id id _ different)

private theorem initializedBindings_transport {kinds : List ArithmeticType} (bindings : Env kinds)
    (values : CallInputs target kinds) (owner : Nat)
    (before after : State target stateParameters Environment)
    (frame : ∀ id ∈ bindings.ids, after.objects id = before.objects id)
    (records : InitializedBindings owner before bindings values) :
    InitializedBindings owner after bindings values := by
  induction bindings with
  | nil => cases values; trivial
  | cons reference tail ih =>
      cases values with
      | cons value rest =>
          exact ⟨(frame reference.id List.mem_cons_self).trans records.1,
            ih rest (fun id member => frame id (List.mem_cons_of_mem _ member)) records.2⟩

variable {parameters : List ArithmeticType} {result : IntType}

/-- Canonical entry data, with source-order reservation plans. Prepared active
bindings contain locals in reverse order followed by the parameters. -/
def entryFor (function : Function target parameters result) (base : Nat) :
    FunctionEntry target parameters result :=
  let parameterPlan := reservationEnv base parameters
  let localPlan := reservationEnv (base + parameters.length) function.body.localKinds
  ⟨prepared function.body parameterPlan localPlan,
    parameterPlan, function.body.localKinds, localPlan⟩

theorem entryFor_context (function : Function target parameters result) (base : Nat) :
    (entryFor function base).context = function.body.localKinds.reverse ++ parameters := by
  exact (prepared_context function.body _ _).trans function.body.finalContext_eq

theorem entryFor_ids (function : Function target parameters result) (base : Nat) :
    (entryFor function base).bindings.ids =
      (entryFor function base).localBindings.ids.reverse ++
        (entryFor function base).parameterBindings.ids :=
  prepared_ids function.body _ _

theorem entryFor_disjoint (function : Function target parameters result) (base : Nat) :
    ∀ id ∈ (entryFor function base).parameterBindings.ids,
      id ∉ (entryFor function base).localBindings.ids := by
  intro id parameterMember localMember
  have parameterBound := reservationEnv_bounds base parameters id parameterMember
  have localBound := reservationEnv_bounds (base + parameters.length) function.body.localKinds id localMember
  omega

/-- Exact event specification, without a second execution traversal. -/
def entryEvents (function : Function target parameters result)
    (literal : LiteralInitializers function.body) (values : CallInputs target parameters)
    (actor base : Nat) : List Event :=
  parameterEvents function.dialect actor base values ++
    (reservationEvents function.dialect actor (base + parameters.length) function.body.localKinds ++
      initializationEvents function.dialect (entryFor function base).localBindings literal.values)

/-- Reusable post-entry facts. Every field follows from metadata/capacity and
the literal witness. No target-body execution is an admission or a field. -/
structure EntryFacts (function : Function target parameters result)
    (literal : LiteralInitializers function.body) (values : CallInputs target parameters)
    (before after : State target stateParameters Environment) : Prop where
  metadata : after.WellFormed
  frozen : Frozen before after
  next : after.next = before.next + parameters.length + function.body.localKinds.length
  slots : after.automaticSlots + (parameters.length + function.body.localKinds.length) =
    before.automaticSlots
  parameterRecords : InitializedBindings after.actor after
    (entryFor function before.next).parameterBindings values
  localRecords : LocalRecords after.actor after
    (entryFor function before.next).localBindings literal.values
  parameterUnique : (entryFor function before.next).parameterBindings.Unique
  localUnique : (entryFor function before.next).localBindings.Unique
  bindingsUnique : (entryFor function before.next).bindings.Unique
  disjoint : ∀ id ∈ (entryFor function before.next).parameterBindings.ids,
    id ∉ (entryFor function before.next).localBindings.ids
  parameterFresh : ∀ id ∈ (entryFor function before.next).parameterBindings.ids, before.objects id = none
  localFresh : ∀ id ∈ (entryFor function before.next).localBindings.ids, before.objects id = none
  outside : ∀ id, id < before.next ∨
    before.next + parameters.length + function.body.localKinds.length ≤ id →
      after.objects id = before.objects id
  caller : ∀ id object, before.objects id = some object → after.objects id = some object

/-- Complete successful entry is a conclusion, for any Code (including an
unsupported or nonterminating body), both dialects, and arbitrary typed inputs.
The caller state input telescope need not equal the formal parameter telescope. -/
theorem enter_contract (function : Function target parameters result)
    (literal : LiteralInitializers function.body) (values : CallInputs target parameters)
    (state : State target stateParameters Environment) (metadata : state.WellFormed)
    (capacity : parameters.length + function.body.localKinds.length ≤ state.automaticSlots) :
    ∃ final,
      FunctionEval.enterUnchecked function values state =
        (.ok (entryFor function state.next), final,
          entryEvents function literal values state.actor state.next) ∧
      EntryFacts function literal values state final := by
  let parameterState := parametersState function.dialect values state
  have parameterMeta : parameterState.WellFormed :=
    parametersState_wellFormed function.dialect values state metadata
  have parameterCap : parameters.length ≤ state.automaticSlots := by omega
  have parameterSlots := parametersState_slots function.dialect values state parameterCap
  have parameterNext : parameterState.next = state.next + parameters.length :=
    parametersState_next function.dialect values state
  have parameterFrozen : Frozen state parameterState := parametersState_frozen function.dialect values state
  let reserved := reservedAllState function.dialect function.body.localKinds parameterState
  have reserveMeta : reserved.WellFormed :=
    reservedAllState_wellFormed function.dialect function.body.localKinds parameterState parameterMeta
  have reserveCap : function.body.localKinds.length ≤ parameterState.automaticSlots := by
    change parameterState.automaticSlots + parameters.length = state.automaticSlots at parameterSlots
    omega
  have reserveNext : reserved.next = parameterState.next + function.body.localKinds.length :=
    reservedAllState_next function.dialect function.body.localKinds parameterState
  have reserveSlots := reservedAllState_slots function.dialect function.body.localKinds parameterState reserveCap
  have reserveFrozen : Frozen parameterState reserved :=
    reservedAllState_frozen function.dialect function.body.localKinds parameterState
  have pending : PendingBindings function.dialect reserved.actor reserved
      (reservationEnv parameterState.next function.body.localKinds) := by
    rw [reserveFrozen.2.2]
    exact reservedAllState_pending function.dialect function.body.localKinds parameterState
  obtain ⟨final, initialized, facts⟩ := prepare_contract function.dialect function.conversions literal
    (reservationEnv state.next parameters) (reservationEnv parameterState.next function.body.localKinds)
    reserved reserveMeta (reservationEnv_unique _ _) pending
  have frozen : Frozen state final :=
    ⟨facts.frozen.1.trans (reserveFrozen.1.trans parameterFrozen.1),
      facts.frozen.2.1.trans (reserveFrozen.2.1.trans parameterFrozen.2.1),
      facts.frozen.2.2.trans (reserveFrozen.2.2.trans parameterFrozen.2.2)⟩
  have outside : ∀ id, id < state.next ∨
      state.next + parameters.length + function.body.localKinds.length ≤ id →
        final.objects id = state.objects id := by
    intro id bound
    have reserveBound : id < parameterState.next ∨
        parameterState.next + function.body.localKinds.length ≤ id := by omega
    have notLocal : id ∉ (reservationEnv parameterState.next function.body.localKinds).ids := by
      intro member
      have localBound := reservationEnv_bounds parameterState.next function.body.localKinds id member
      omega
    exact (facts.outside id notLocal).trans
      ((reservedAllState_outside function.dialect function.body.localKinds parameterState id reserveBound).trans
        (parametersState_outside function.dialect values state id (by omega)))
  refine ⟨final, ?_, facts.metadata, frozen, ?_, ?_, ?_, ?_,
    reservationEnv_unique _ _, reservationEnv_unique _ _, ?_,
    entryFor_disjoint function state.next, reservationEnv_fresh parameters state metadata, ?_,
    outside, ?_⟩
  · have enteredParameters := enterParameters_eq function.dialect values state metadata parameterCap
    have reservedLocals := reserveAll_eq function.dialect function.body.localKinds
      parameterState parameterMeta reserveCap
    change BlockEval.enterParameters function.dialect values state = _ at enteredParameters
    change BlockEval.reserveAll function.dialect function.body.localKinds parameterState = _ at reservedLocals
    dsimp only [reserved, parameterState] at reservedLocals initialized
    dsimp only [Op.pure] at initialized
    simp only [FunctionEval.enterUnchecked, Op.bind, Effects.Op.bind, enteredParameters, reservedLocals, initialized,
      Op.pure, List.append_nil]
    change (Except.ok _, final, _) = _
    rw [show (parametersState function.dialect values state).next = state.next + parameters.length
      from parameterNext]
    rw [show (parametersState function.dialect values state).actor = state.actor from parameterFrozen.2.2]
    rfl
  · have next := facts.next
    omega
  · change reserved.automaticSlots + function.body.localKinds.length = parameterState.automaticSlots at reserveSlots
    change parameterState.automaticSlots + parameters.length = state.automaticSlots at parameterSlots
    have slots := facts.slots
    omega
  · rw [frozen.2.2]
    apply initializedBindings_transport (reservationEnv state.next parameters) values state.actor
      parameterState final _ (parametersState_initialized function.dialect values state)
    intro id member
    have bound := reservationEnv_bounds state.next parameters id member
    have notLocal : id ∉ (reservationEnv parameterState.next function.body.localKinds).ids := by
      intro localMember
      have localBound := reservationEnv_bounds parameterState.next function.body.localKinds id localMember
      omega
    exact (facts.outside id notLocal).trans
      (reservedAllState_outside function.dialect function.body.localKinds parameterState id (Or.inl (by omega)))
  · change LocalRecords final.actor final
      (reservationEnv (state.next + parameters.length) function.body.localKinds) literal.values
    rw [← parameterNext, facts.frozen.2.2]
    exact facts.records
  · exact prepared_unique function.body _ _ (reservationEnv_unique _ _)
      (reservationEnv_unique _ _) (entryFor_disjoint function state.next)
  · intro id member
    have bound := reservationEnv_bounds (state.next + parameters.length) function.body.localKinds id member
    cases registered : state.objects id with
    | none => rfl
    | some object => have old := (metadata id object registered).1; omega
  · intro id object registered
    exact (outside id (Or.inl (metadata id object registered).1)).trans registered

/-- Ready-to-use access admissions for every actual formal parameter. -/
theorem EntryFacts.parameter_access {function : Function target parameters result}
    {literal : LiteralInitializers function.body} {values : CallInputs target parameters}
    {before after : State target stateParameters Environment}
    (facts : EntryFacts function literal values before after)
    {kind : ArithmeticType} (index : Vars parameters kind) :
    CanLoad after ((entryFor function before.next).parameterBindings.get index) (values.get index) ∧
      CanStore after ((entryFor function before.next).parameterBindings.get index) :=
  initializedBindings_access _ values after facts.parameterRecords index

/-- Cleanup authority follows even for genuinely uninitialized locals. This
describes the prepared state; a body must separately preserve its authority. -/
theorem EntryFacts.cleanup {function : Function target parameters result}
    {literal : LiteralInitializers function.body} {values : CallInputs target parameters}
    {before after : State target stateParameters Environment}
    (facts : EntryFacts function literal values before after) :
    LiveBindings after (entryFor function before.next).localBindings ∧
      LiveBindings after (entryFor function before.next).parameterBindings :=
  ⟨localRecords_live _ literal.values after facts.localRecords,
    initializedBindings_live _ values after facts.parameterRecords⟩

/-- Direct composition into the existing entry VC. The continuation receives
only proved entry facts; support and all body/return obligations remain its job. -/
theorem vcEntry_of_literals (function : Function target parameters result)
    (literal : LiteralInitializers function.body)
    (post : Protocol.Post target (VariableTypes parameters) Environment (FunctionEntry target parameters result))
    (state : State target (VariableTypes parameters) Environment) (metadata : state.WellFormed)
    (capacity : parameters.length + function.body.localKinds.length ≤ state.automaticSlots)
    (continuation : ∀ final, EntryFacts function literal state.inputs state final →
      post state (entryFor function state.next) final
        (entryEvents function literal state.inputs state.actor state.next)) :
    FunctionVC.vcEntry function post state := by
  obtain ⟨final, entered, facts⟩ := enter_contract function literal state.inputs state metadata capacity
  apply (FunctionVC.vcEntry_iff_wp function post state).mpr
  exact (Protocol.wp_iff _ _ _).mpr ⟨_, final, _, entered, continuation final facts⟩

end EDSL.Source.Objects.Control.EntryContracts
