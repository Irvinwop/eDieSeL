/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.BlockEquations
import EDSL.Source.Objects.AccessContracts
import EDSL.Source.Objects.Protocol

set_option autoImplicit false
namespace EDSL.Source.Objects.CopyIncrement
open StateSyntax LifecycleContracts
attribute [local implicit_reducible] Value Target.modulus Decls.localKinds

variable {target : Target} {Environment : Type}

def one (target : Target) : Value target .uint :=
  ⟨1, by
    apply Nat.one_lt_two_pow
    have minimum := target.atLeast16
    omega⟩

/-- A mutable formal is copied into a separately allocated local. Its increment
is a full assignment; return observes the updated local through an object read. -/
def program (target : Target) (dialect : Dialect) :
    StateSyntax.Program target [.uint] .uint where
  dialect := dialect
  conversions := .gnuModulo
  body := .declare .uint (some (.param .here))
    (.body (.set .here (.uadd (.param .here) (.literal (one target))) (.ret (.param .here))))

/-- Independent unsigned contract: one mathematical increment with at most one
carry. It does not mention the evaluator's remainder operation. -/
def BoundedIncrement (input result : Value target .uint) : Prop :=
  ∃ carry : Nat, carry ≤ 1 ∧ result.val + carry * target.modulus = input.val + 1

/-- Metadata and abstract capacity only, with no execution, result or NoUB premise. -/
def Admission (initial : State target [.uint] Environment) : Prop :=
  initial.WellFormed ∧ 2 ≤ initial.automaticSlots

def incremented (input : Value target .uint) : Value target .uint :=
  ⟨(input.val + 1) % target.modulus, Nat.mod_lt _ target.modulus_pos⟩

def tombstone (input : Value target .uint) (actor : Nat) : Object target :=
  { liveObject .uint actor ⟨true, true⟩ (some input) with life := .ended }

/-- Exact normal-return registry: parameter and local identities stay distinct,
retain their contents, and have ended lifetimes. Old identities are retained. -/
def finalState (initial : State target [.uint] Environment) : State target [.uint] Environment :=
  let input := initial.inputs.get .here
  { (initial.putObject (initial.next + 1) (tombstone (incremented input) initial.actor)).putObject
      initial.next (tombstone input initial.actor) with
    next := initial.next + 2 }

def events (dialect : Dialect) (initial : State target [.uint] Environment) : List Event :=
  let input := initial.inputs.get .here
  let result := incremented input
  reserveEvents dialect initial.next .uint initial.actor ++
  initializeEvents dialect initial.next .uint (some input.toInt) ++
  reserveEvents dialect (initial.next + 1) .uint initial.actor ++
  [.read initial.next .uint input.toInt] ++
  initializeEvents dialect (initial.next + 1) .uint (some input.toInt) ++
  [.read (initial.next + 1) .uint input.toInt,
   .write (initial.next + 1) .uint result.toInt,
   .read (initial.next + 1) .uint result.toInt,
   .endLifetime (initial.next + 1) .uint,
   .endLifetime initial.next .uint]

theorem supported (dialect : Dialect) : (program target dialect).Supported := by
  simp [program, StateSyntax.Program.Supported, Expr.Supported]

theorem fresh_at_or_above (initial : State target [.uint] Environment)
    (wellFormed : initial.WellFormed) (id : Nat) (bound : initial.next ≤ id) :
    initial.objects id = none := by
  cases registered : initial.objects id with
  | none => rfl
  | some object =>
      have oldBound := (wellFormed id object registered).1
      omega

theorem incremented_bounded (input : Value target .uint) :
    BoundedIncrement input (incremented input) := by
  refine ⟨(input.val + 1) / target.modulus, ?_, Nat.mod_add_div' _ _⟩
  have modulusLarge : 1 < target.modulus := (one target).isLt
  have bound : input.val + 1 < 2 * target.modulus := by have representable := input.isLt; omega
  have carryBound := (Nat.div_lt_iff_lt_mul target.modulus_pos).mpr bound
  omega

/-- Arithmetic, caller frame, fresh identities, restored quota, old-object frame,
and explicit final tombstones. None of these conditions occurs in Admission. -/
def Post (initial : State target [.uint] Environment) (result : Value target .uint)
    (final : State target [.uint] Environment) (_events : List Event) : Prop :=
  BoundedIncrement (initial.inputs.get .here) result ∧
  final.inputs = initial.inputs ∧ final.environment = initial.environment ∧
  final.actor = initial.actor ∧ final.next = initial.next + 2 ∧
  final.automaticSlots = initial.automaticSlots ∧
  (∀ id, id < initial.next → final.objects id = initial.objects id) ∧
  final.objects initial.next = some (tombstone (initial.inputs.get .here) initial.actor) ∧
  final.objects (initial.next + 1) = some (tombstone result initial.actor) ∧
  final.WellFormed

theorem finalState_old_objects (initial : State target [.uint] Environment)
    (id : Nat) (old : id < initial.next) :
    (finalState initial).objects id = initial.objects id := by
  have other0 : id ≠ initial.next := by omega
  have other1 : id ≠ initial.next + 1 := by omega
  simp only [finalState, State.putObject, other0, other1, ↓reduceIte]

theorem finalState_parameter (initial : State target [.uint] Environment) :
    (finalState initial).objects initial.next =
      some (tombstone (initial.inputs.get .here) initial.actor) := by
  simp only [finalState, State.putObject, ↓reduceIte]

theorem finalState_local (initial : State target [.uint] Environment) :
    (finalState initial).objects (initial.next + 1) =
      some (tombstone (incremented (initial.inputs.get .here)) initial.actor) := by
  have other : initial.next + 1 ≠ initial.next := by omega
  simp only [finalState, State.putObject, other, ↓reduceIte]

theorem tombstone_wellFormed (input : Value target .uint) (actor : Nat) :
    (tombstone input actor).WellFormed := by
  simp [tombstone, liveObject, Object.WellFormed]

theorem finalState_wellFormed (initial : State target [.uint] Environment)
    (wellFormed : initial.WellFormed) : (finalState initial).WellFormed := by
  intro id object registered
  by_cases parameter : id = initial.next
  · subst id
    rw [finalState_parameter] at registered
    cases registered
    exact ⟨by simp only [finalState]; omega, tombstone_wellFormed _ _⟩
  · by_cases localObject : id = initial.next + 1
    · subst id
      rw [finalState_local] at registered
      cases registered
      exact ⟨by simp only [finalState]; omega, tombstone_wellFormed _ _⟩
    · have old : initial.objects id = some object := by
        simpa only [finalState, State.putObject, parameter, localObject, ↓reduceIte] using registered
      obtain ⟨bound, metadata⟩ := wellFormed id object old
      exact ⟨by simp only [finalState]; omega, metadata⟩

theorem finalState_post (initial : State target [.uint] Environment)
    (wellFormed : initial.WellFormed) (trace : List Event) :
    Post initial (incremented (initial.inputs.get .here)) (finalState initial) trace := by
  exact ⟨incremented_bounded _, rfl, rfl, rfl, rfl, rfl,
    finalState_old_objects initial, finalState_parameter initial, finalState_local initial,
    finalState_wellFormed initial wellFormed⟩


/-- Shared-driver execution from independent metadata and two abstract slots. -/
theorem run_eq (dialect : Dialect) (initial : State target [.uint] Environment)
    (admitted : Admission initial) :
    BlockEval.runProgram (program target dialect) initial =
      (.ok (incremented (initial.inputs.get .here)), finalState initial, events dialect initial) := by
  let input := initial.inputs.get .here
  let result := incremented input
  let permission : Permissions := ⟨true, true⟩
  let parameter : LValue .uint := ⟨initial.next⟩
  let localObject : LValue .uint := ⟨initial.next + 1⟩
  let reservedParameter := reservedState dialect .uint initial
  let entered := initializedState parameter permission (some input) reservedParameter
  let reservedLocal := reservedState dialect .uint entered
  let initializedLocal := initializedState localObject permission (some input) reservedLocal
  let storedLocal := initializedState localObject permission (some result) initializedLocal
  let endedLocal := endedState localObject permission (some result) storedLocal
  let endedParameter := endedState parameter permission (some input) endedLocal
  have reserveParameter := reserve_eq dialect .uint initial
    ⟨fresh_of_wellFormed initial admitted.1, by have capacity := admitted.2; omega⟩
  have parameterPending : reservedParameter.objects parameter.id =
      some (pendingObject dialect .uint reservedParameter.actor permission) := by
    simp [reservedParameter, reservedState, parameter, permission, State.putObject]
  have initializeParameter := initialize_eq dialect parameter reservedParameter permission
    (some input) parameterPending rfl
  have enteredWF : entered.WellFormed := initializedState_wellFormed dialect parameter
    reservedParameter permission (some input)
    (reservedState_wellFormed dialect .uint initial admitted.1) parameterPending
  have reserveLocal := reserve_eq dialect .uint entered
    ⟨fresh_of_wellFormed entered enteredWF, by
      have capacity := admitted.2
      dsimp [entered, initializedState, reservedParameter, reservedState, State.putObject]
      omega⟩
  have localPending : reservedLocal.objects localObject.id =
      some (pendingObject dialect .uint reservedLocal.actor permission) := by
    simp [reservedLocal, reservedState, entered, initializedState, reservedParameter,
      reservedState, parameter, localObject, permission, State.putObject]
  have initializeLocal := initialize_eq dialect localObject reservedLocal permission
    (some input) localPending rfl
  have parameterReady : CanLoad reservedLocal parameter input := by
    refine ⟨permission, ?_, rfl⟩
    simp [reservedLocal, reservedState, entered, initializedState, reservedParameter,
      reservedState, parameter, permission, liveObject, State.putObject]
  have readParameter := load_contract dialect reservedLocal parameter input parameterReady
  have localReady : CanLoad initializedLocal localObject input := by
    exact ⟨permission, by simp [initializedLocal, initializedState, liveObject, State.putObject], rfl⟩
  have readLocal := load_contract dialect initializedLocal localObject input localReady
  have storeLocal : store localObject result initializedLocal =
      (.ok (), storedLocal, [.write localObject.id .uint result.toInt]) := by
    have registered : initializedLocal.objects localObject.id =
        some (liveObject .uint initializedLocal.actor permission (some input)) := by
      simp [initializedLocal, initializedState, State.putObject]
    simp [store, registered, liveObject, permission, storedLocal, initializedState]
  have storedReady : CanLoad storedLocal localObject result := by
    exact ⟨permission, by simp [storedLocal, initializedState, liveObject, State.putObject], rfl⟩
  have readResult := load_contract dialect storedLocal localObject result storedReady
  have endLocal := endLifetime_eq localObject storedLocal permission (some result)
    (by simp [storedLocal, initializedState, State.putObject])
  have endParameter := endLifetime_eq parameter endedLocal permission (some input) (by
    simp [endedLocal, endedState, storedLocal, initializedState, initializedLocal,
      reservedLocal, reservedState, entered, reservedParameter, parameter, localObject,
      permission, State.putObject])
  have incrementExpr : StateEval.evalExpr dialect .gnuModulo
      (Env.cons localObject (Env.cons parameter .nil))
      (.uadd (.param .here) (.literal (one target))) initializedLocal =
        (.ok result, initializedLocal, [.read localObject.id .uint input.toInt]) := by
    change Op.bind (load dialect localObject) (fun current =>
      Op.bind (Op.pure (one target)) (fun added =>
        (EffectM.liftScalar (unsignedAdd target current added)).run)) initializedLocal = _
    simp only [Op.bind, Effects.Op.bind, readLocal, Op.pure, EffectM.liftScalar, EffectM.scalarOutcome]
    rfl
  have bodyStatement : StateEval.evalStmt dialect .gnuModulo
      (Env.cons localObject (Env.cons parameter .nil))
      (.set .here (.uadd (.param .here) (.literal (one target))) (.ret (.param .here)))
      initializedLocal =
      (.ok result, storedLocal,
        [.read localObject.id .uint input.toInt,
         .write localObject.id .uint result.toInt,
         .read localObject.id .uint result.toInt]) := by
    simp only [StateEval.evalStmt, Op.bind, Effects.Op.bind, incrementExpr, Env.get_here,
      storeLocal, StateEval.evalExpr_var, readResult]
    rfl
  dsimp only [initializedLocal] at bodyStatement
  have bodyExecution : BlockEval.evalDecls dialect .gnuModulo (program target dialect).body
      (Env.cons parameter .nil) (Env.cons localObject .nil) reservedLocal =
      (.ok result, storedLocal,
        [.read parameter.id .uint input.toInt] ++
        initializeEvents dialect localObject.id .uint (some input.toInt) ++
        [.read localObject.id .uint input.toInt,
         .write localObject.id .uint result.toInt,
         .read localObject.id .uint result.toInt]) := by
    change Op.bind (Op.bind (load dialect parameter) (fun value => Op.pure (some value)))
      (fun value => Op.bind (Objects.initialize dialect localObject value)
        (fun _ => StateEval.evalStmt dialect .gnuModulo
          (Env.cons localObject (Env.cons parameter .nil))
          (.set .here (.uadd (.param .here) (.literal (one target))) (.ret (.param .here)))))
      reservedLocal = _
    simp only [Op.bind, Effects.Op.bind, readParameter, Op.pure, initializeLocal, bodyStatement,
      Option.map_some, List.append_nil, List.append_assoc]
  have inputForm : initial.inputs = .cons input .nil := by
    dsimp only [input]
    cases initial.inputs with
    | cons supplied rest => cases rest; rfl
  dsimp only [parameter, reservedParameter] at initializeParameter
  have entryExecution : BlockEval.enterParameters (kinds := [.uint]) dialect initial.inputs initial =
      (.ok (Env.cons parameter .nil), entered,
        reserveEvents dialect parameter.id .uint initial.actor ++
          initializeEvents dialect parameter.id .uint (some input.toInt)) := by
    rw [inputForm]
    change Op.bind (reserve dialect .uint) (fun reference =>
      Op.bind (Objects.initialize dialect reference (some input)) (fun _ =>
        Op.bind (Op.pure Env.nil) (fun tail => Op.pure (Env.cons reference tail)))) initial = _
    simp only [Op.bind, Effects.Op.bind, reserveParameter, initializeParameter, Op.pure, parameter,
      Option.map_some, List.append_nil]
    rfl
  have reserveExecution : BlockEval.reserveAll dialect [.uint] entered =
      (.ok (Env.cons localObject .nil), reservedLocal,
        reserveEvents dialect localObject.id .uint initial.actor) := by
    rw [BlockEval.reserveAll_cons, BlockEval.reserveAll_nil]
    simp only [Op.bind, Effects.Op.bind, reserveLocal, Op.pure, List.append_nil]
    rfl
  have localCleanup : BlockEval.closeAll (Env.cons localObject .nil) storedLocal =
      (.ok (), endedLocal, [.endLifetime localObject.id .uint]) := by
    change Op.bind (Op.pure ()) (fun _ => endLifetime localObject) storedLocal = _
    simp only [Op.bind, Effects.Op.bind, Op.pure, endLocal, List.nil_append]
    rfl
  have parameterCleanup : BlockEval.closeAll (Env.cons parameter .nil) endedLocal =
      (.ok (), endedParameter, [.endLifetime parameter.id .uint]) := by
    change Op.bind (Op.pure ()) (fun _ => endLifetime parameter) endedLocal = _
    simp only [Op.bind, Effects.Op.bind, Op.pure, endParameter, List.nil_append]
    rfl
  have finalSame : endedParameter = finalState initial := by
    dsimp [endedParameter, endedState, endedLocal, storedLocal, initializedLocal,
      reservedLocal, entered, initializedState, reservedParameter, reservedState,
      finalState, tombstone, parameter, localObject, permission, State.putObject]
    have quota : initial.automaticSlots - 1 - 1 + 1 + 1 = initial.automaticSlots := by
      have capacity := admitted.2
      omega
    simp only [quota]
    congr 1
    funext query
    by_cases first : query = initial.next <;>
      by_cases second : query = initial.next + 1 <;>
        simp [first, second, liveObject, input, result]
  rw [BlockEval.runProgram_supported (program target dialect) initial (supported dialect)]
  change Op.bind (BlockEval.enterParameters (kinds := [.uint]) dialect initial.inputs)
    (fun parameters => Op.bind (BlockEval.reserveAll dialect [.uint])
      (fun locals => Op.bind (BlockEval.evalDecls dialect .gnuModulo
        (program target dialect).body parameters locals) (fun value =>
          Op.bind (BlockEval.closeAll locals) (fun _ =>
            Op.bind (BlockEval.closeAll parameters) (fun _ => Op.pure value))))) initial = _
  simp only [Op.bind, Effects.Op.bind, entryExecution, reserveExecution, bodyExecution,
    localCleanup, parameterCleanup, Op.pure, List.append_nil]
  rw [finalSame]
  simp only [events, parameter, localObject, input, result, List.append_assoc]
  rfl

/-- All typed call values are admitted when metadata and two slots permit entry.
This proves successful source execution and the independent postcondition. -/
theorem verified (dialect : Dialect) :
    ∀ initial : State target [.uint] Environment, Admission initial →
      ∃ result final trace,
        BlockEval.runProgram (program target dialect) initial = (.ok result, final, trace) ∧
          Post initial result final trace := by
  intro initial admitted
  exact ⟨_, _, _, run_eq dialect initial admitted,
    finalState_post initial admitted.1 (events dialect initial)⟩

/-- Every stop is excluded by proved completion, including scalar/object UB,
C++ erroneous production, resource or authority refusals and unsupported syntax. -/
theorem no_failure (dialect : Dialect) (initial : State target [.uint] Environment)
    (admitted : Admission initial) (reason : Stop)
    (final : State target [.uint] Environment) (trace : List Event) :
    BlockEval.runProgram (program target dialect) initial ≠ (.error reason, final, trace) := by
  rw [run_eq dialect initial admitted]
  intro impossible
  cases impossible

/-- Actual caller values and an environment witness give a useful independent
entry domain; arbitrary empty environment types are never used as evidence. -/
theorem admission_inhabited (input : Value target .uint) (environment : Environment)
    (actor : Nat) : ∃ initial : State target [.uint] Environment,
      Admission initial ∧ initial.inputs.get .here = input ∧ initial.environment = environment := by
  refine ⟨State.empty (.cons input .nil) environment actor 2, ?_, rfl, rfl⟩
  exact ⟨State.empty_wellFormed _ _ _ _, Nat.le_refl _⟩

/-- A useful certificate requires an actual environment value, then quantifies
over every admitted caller state and every representable unsigned input. -/
theorem certificate (dialect : Dialect) (environment : Environment) :
    Protocol.Certificate (Environment := Environment) (BlockEval.runProgram (program target dialect)) Admission Post where
  useful := by
    obtain ⟨initial, allowed, _, _⟩ := admission_inhabited (one target) environment 0
    exact ⟨initial, allowed⟩
  verified := verified dialect

end EDSL.Source.Objects.CopyIncrement
