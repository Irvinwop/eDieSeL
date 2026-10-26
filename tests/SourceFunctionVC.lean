/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.EntryContracts
import EDSL.Source.Objects.Control.Division

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.FunctionVC.EntryDivisionValidation
open StateSyntax Protocol StructuredVC LifecycleContracts BlockContracts ParameterContracts
attribute [local implicit_reducible] Value Target.modulus

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable (dialect : Dialect) (policy : IntegerConversionPolicy)

/- Reuse the old client's *local* arithmetic, expression and object lemmas.
No old control-run, progress, return or certificate theorem is used here.
The mathematical postcondition and caller frame are the existing independent
division specification. There is no tick/perform/run unfolding in this client.
-/
private def invariant (n d : Value target .uint) (q r dRef : LValue .uint)
    (original : State target parameters Environment) : Assertion target parameters Environment :=
  fun state _ => ∃ qv rv, Division.Frame q r original state ∧ Division.Holds state q qv ∧ Division.Holds state r rv ∧
    CanLoad state dRef d ∧ Division.Invariant n d qv rv ∧ state.WellFormed

private def annotation (n d : Value target .uint) (q r dRef : LValue .uint)
    (original : State target parameters Environment) : Annotation (parameters := parameters)
      (Environment := Environment) (.seq (Division.loop target) (.ret (.param Division.qVar))) :=
  .seq (.loop (invariant n d q r dRef original)
    (fun state events => Division.rank r (Division.header state events)) (.seq .assign .assign)) .ret

theorem loop_segment (n d : Value target .uint) (q r dRef : LValue .uint)
    (qr : q.id ≠ r.id) (qd : q.id ≠ dRef.id) (rd : r.id ≠ dRef.id) (positive : 0 < d.val)
    (original state : State target parameters Environment) (earlier : List Event)
    (qv rv : Value target .uint) (frame : Division.Frame q r original state)
    (hq : Division.Holds state q qv) (hr : Division.Holds state r rv) (hd : CanLoad state dRef d)
    (reconstruction : Division.Invariant n d qv rv) (metadata : state.WellFormed) :
    Segment dialect policy (Division.bindings q r dRef) (.seq (Division.loop target) (.ret (.param Division.qVar)))
      (fun _ _ => False) (fun value final events => Division.Post n d q r dRef original value final events ∧
        final.WellFormed ∧ ∃ historyPrefix, events = historyPrefix ++ [.read q.id .uint value.toInt])
      state earlier := by
  apply vc_sound dialect policy (Division.bindings q r dRef) (annotation n d q r dRef original)
  change invariant n d q r dRef original state earlier ∧ _
  refine ⟨⟨qv, rv, frame, hq, hr, hd, reconstruction, metadata⟩, ?_⟩
  intro current history member
  obtain ⟨qNow, rNow, callerFrame, heldQ, heldR, readD, numeric, currentMetadata⟩ := member
  apply (expression_iff dialect policy (Division.bindings q r dRef) (Division.condition target) _ current history).mpr
  refine ⟨compareValues .ge rNow d, current,
    [.read r.id .uint rNow.toInt, .read dRef.id .uint d.toInt],
    Division.eval_condition dialect policy q r dRef current rNow d heldR readD, ?_⟩
  by_cases guard : d.val ≤ rNow.val
  · have nonzero : (compareValues .ge rNow d).toInt ≠ 0 :=
      (compareValues_nonzero_iff .ge rNow d).mpr (Int.ofNat_le.mpr guard)
    simp only [nonzero, ↓reduceIte]
    obtain ⟨fits, decreases, preserved⟩ := Division.iteration_arithmetic n d qNow rNow positive numeric guard
    let rNext := Division.subValue rNow d
    let qNext := Division.succValue qNow fits
    let middle := Division.put current r rNext
    let final := Division.put middle q qNext
    have middleQ : Division.Holds middle q qNow := Division.put_holds_other current r q rNext qNow qr heldQ
    have finalQ : Division.Holds final q qNext := Division.put_holds middle q qNext
    have finalR : Division.Holds final r rNext :=
      Division.put_holds_other middle q r qNext rNext (Ne.symm qr) (Division.put_holds current r rNext)
    have finalD : CanLoad final dRef d :=
      Division.put_canLoad_other middle q dRef qNext d (Ne.symm qd)
        (Division.put_canLoad_other current r dRef rNext d (Ne.symm rd) readD)
    have finalFrame : Division.Frame q r original final :=
      callerFrame.trans ((Division.put_frame q r r current rNext (Or.inr rfl)).trans
        (Division.put_frame q r q middle qNext (Or.inl rfl)))
    have middleMetadata : middle.WellFormed := by
      have preserved := store_preserves_wellFormed current r rNext currentMetadata
      rw [Division.store_ready current r rNext (Division.holds_ready current r rNow heldR)] at preserved
      exact preserved
    have finalMetadata : final.WellFormed := by
      have preserved := store_preserves_wellFormed middle q qNext middleMetadata
      rw [Division.store_ready middle q qNext (Division.holds_ready middle q qNow middleQ)] at preserved
      exact preserved
    change expression policy (Division.bindings q r dRef) (.usub (.param Division.rVar) (.param Division.dVar)) _ current _
    apply (expression_iff dialect policy (Division.bindings q r dRef) _ _ current _).mpr
    refine ⟨rNext, current, [.read r.id .uint rNow.toInt, .read dRef.id .uint d.toInt],
      Division.eval_subtract dialect policy q r dRef current rNow d heldR readD guard, ?_⟩
    apply (write_iff r rNext _ current _).mpr
    apply (wp_iff _ _ _).mpr
    refine ⟨(), middle, [.write r.id .uint rNext.toInt],
      Division.store_ready current r rNext (Division.holds_ready current r rNow heldR), ?_⟩
    change expression policy (Division.bindings q r dRef)
      (.uadd (.param Division.qVar) (.literal (Division.one target))) _ middle _
    apply (expression_iff dialect policy (Division.bindings q r dRef) _ _ middle _).mpr
    refine ⟨qNext, middle, [.read q.id .uint qNow.toInt],
      Division.eval_increment dialect policy q r dRef middle qNow middleQ fits, ?_⟩
    apply (write_iff q qNext _ middle _).mpr
    apply (wp_iff _ _ _).mpr
    refine ⟨(), final, [.write q.id .uint qNext.toInt],
      Division.store_ready middle q qNext (Division.holds_ready middle q qNow middleQ), ?_⟩
    refine ⟨⟨qNext, rNext, finalFrame, finalQ, finalR, finalD, preserved, finalMetadata⟩, ?_⟩
    rw [Division.rank_header r final _ rNext finalR, Division.rank_header r current _ rNow heldR]
    exact decreases
  · have zero : (compareValues .ge rNow d).toInt = 0 := by
      apply (compareValues_zero_iff .ge rNow d).mpr
      change ¬(d.val : Int) ≤ (rNow.val : Int)
      omega
    simp only [zero, ↓reduceIte]
    change expression policy (Division.bindings q r dRef) (.param Division.qVar) _ current _
    apply (expression_iff dialect policy (Division.bindings q r dRef) _ _ current _).mpr
    refine ⟨qNow, current, [.read q.id .uint qNow.toInt],
      Division.eval_var dialect policy q r dRef Division.qVar current qNow (Division.holds_load current q qNow heldQ), ?_⟩
    exact ⟨⟨rNow, numeric, by omega, heldQ, heldR, readD, callerFrame⟩, currentMetadata, _, rfl⟩

/-- A supported write after return checks actual continuation discard. If it
ran, it would overwrite the divisor before parameter cleanup. -/
def functionCode (target : Target) : Code target Division.Context .uint :=
  .seq (.seq (Division.loop target) (.ret (.param Division.qVar)))
    (.assign Division.dVar (.literal (Division.zero target)))

def function (n : Value target .uint) (dialect : Dialect) (policy : IntegerConversionPolicy) :
    Function target [.uint] .uint :=
  ⟨dialect, policy,
    .declare .uint (some (.literal n))
      (.declare .uint (some (.literal (Division.zero target))) (.body (functionCode target)))⟩

theorem function_supported (n : Value target .uint) : (function n dialect policy).Supported := by
  simp [function, Function.Supported, functionCode, Division.loop, Division.body,
    Division.condition, Expr.Supported]

def functionEntry (q r dRef : LValue .uint) : FunctionEntry target [.uint] .uint :=
  ⟨⟨Division.Context, Division.bindings q r dRef, functionCode target⟩,
    .cons dRef .nil, [.uint, .uint], .cons r (.cons q .nil)⟩

/-- A source-independent mathematical/caller contract. Every old caller object
survives exactly, all three slots return, fresh identities remain tombstones,
and the returned value was read before q/r/divisor reverse cleanup. -/
def FullPost (n : Value target .uint) :
    Protocol.Post target [.uint] Environment (Value target .uint) := fun initial value final events =>
  ∃ remainder : Value target .uint,
    n.val = (initial.inputs.get .here).val * value.val + remainder.val ∧
    remainder.val < (initial.inputs.get .here).val ∧
    Frozen initial final ∧ final.next = initial.next + 3 ∧
    final.automaticSlots = initial.automaticSlots ∧ final.WellFormed ∧
    (∀ id object, initial.objects id = some object → final.objects id = some object) ∧
    EndedBindings initial.actor final (reservationEnv initial.next [.uint, .uint, .uint]) ∧
    ∃ historyPrefix, events = historyPrefix ++
      [.read (initial.next + 2) .uint value.toInt,
        .endLifetime (initial.next + 2) .uint,
        .endLifetime (initial.next + 1) .uint,
        .endLifetime initial.next .uint]

def Admitted (initial : State target [.uint] Environment) : Prop :=
  initial.WellFormed ∧ 3 ≤ initial.automaticSlots ∧ 0 < (initial.inputs.get .here).val

private theorem holds_canEnd (state : State target parameters Environment) (ref : LValue .uint)
    (value : Value target .uint) (held : Division.Holds state ref value) : CanEnd ref state :=
  (canEnd_iff_snapshot ref state).mpr ⟨some value, ⟨true, true⟩, held⟩

private theorem load_canEnd (state : State target parameters Environment) (ref : LValue .uint)
    (value : Value target .uint) (readable : CanLoad state ref value) : CanEnd ref state := by
  obtain ⟨permissions, registered, _⟩ := readable
  exact (canEnd_iff_snapshot ref state).mpr ⟨some value, permissions, registered⟩

theorem body_cleanup_segment (n d : Value target .uint)
    (initial : State target [.uint] Environment) (original : State target [.uint] Environment)
    (q r dRef : LValue .uint) (earlier : List Event)
    (hqId : q.id = initial.next + 2) (hrId : r.id = initial.next + 1)
    (hdId : dRef.id = initial.next) (input : initial.inputs.get .here = d)
    (positive : 0 < d.val) (initialMetadata : initial.WellFormed)
    (metadata : original.WellFormed) (frozen : Frozen initial original)
    (next : original.next = initial.next + 3)
    (slots : original.automaticSlots + 3 = initial.automaticSlots)
    (caller : ∀ id object, initial.objects id = some object → original.objects id = some object)
    (hq : Division.Holds original q (Division.zero target))
    (hr : Division.Holds original r n) (hd : CanLoad original dRef d) :
    Segment dialect policy (Division.bindings q r dRef) (functionCode target)
      (fun _ _ => False)
      (fun value => vcCleanup (.cons r (.cons q .nil)) (.cons dRef .nil) value (FullPost n initial))
      original earlier := by
  have qr : q.id ≠ r.id := by omega
  have qd : q.id ≠ dRef.id := by omega
  have rd : r.id ≠ dRef.id := by omega
  apply Segment.seq
  apply (loop_segment dialect policy n d q r dRef qr qd rd positive original original earlier
    (Division.zero target) n (Division.Frame.refl q r original) hq hr hd
    (by simp [Division.Invariant, Division.zero]) metadata).mono
  · intro state events impossible
    exact impossible.elim
  · intro value state history correct
    obtain ⟨⟨remainder, reconstruction, bound, heldQ, heldR, readD, frame⟩,
      currentMetadata, historyPrefix, historyEq⟩ := correct
    let entry : FunctionEntry target [.uint] .uint := functionEntry q r dRef
    have localsUnique : entry.localBindings.Unique := by
      simp [entry, functionEntry, Env.Unique, Env.ids, Ne.symm qr]
    have parametersUnique : entry.parameterBindings.Unique := by
      simp [entry, functionEntry, Env.Unique, Env.ids]
    have disjoint : ∀ id ∈ entry.parameterBindings.ids, id ∉ entry.localBindings.ids := by
      simp only [entry, functionEntry, Env.ids, List.mem_cons, List.not_mem_nil, or_false]
      intro id same
      subst id
      simp [Ne.symm qd, Ne.symm rd]
    obtain ⟨final, closed, cleanupFrozen, cleanupNext, cleanupSlots, finalMetadata,
      endedL, endedP, cleanupFrame⟩ := cleanup_contract entry value state currentMetadata
        localsUnique parametersUnique disjoint
        ⟨holds_canEnd state r remainder heldR, holds_canEnd state q value heldQ, trivial⟩
        ⟨load_canEnd state dRef d readD, trivial⟩
    apply (vcCleanup_iff_wp entry value (FullPost n initial) state history).mpr
    apply (wp_iff _ _ _).mpr
    refine ⟨value, final, closingEvents entry.localBindings ++ closingEvents entry.parameterBindings,
      closed, remainder, ?_, ?_, ?_, ?_, ?_, finalMetadata, ?_, ?_, ?_⟩
    · rw [input]
      exact reconstruction
    · rw [input]
      exact bound
    · exact ⟨cleanupFrozen.1.trans (frame.world.inputs.trans frozen.1),
        cleanupFrozen.2.1.trans (frame.world.environment.trans frozen.2.1),
        cleanupFrozen.2.2.trans (frame.world.actor.trans frozen.2.2)⟩
    · exact cleanupNext.trans (frame.world.next.trans next)
    · simp only [entry, functionEntry, List.length_cons, List.length_nil] at cleanupSlots
      rw [frame.world.automaticSlots] at cleanupSlots
      omega
    · intro id object registered
      have oldBound := (initialMetadata id object registered).1
      have dq : id ≠ q.id := by omega
      have dr : id ≠ r.id := by omega
      have dd : id ≠ dRef.id := by omega
      have outL : id ∉ entry.localBindings.ids := by simp [entry, functionEntry, Env.ids, dr, dq]
      have outP : id ∉ entry.parameterBindings.ids := by simp [entry, functionEntry, Env.ids, dd]
      exact (cleanupFrame id outL outP).trans ((frame.outside id dq dr).trans (caller id object registered))
    · rw [frame.world.actor, frozen.2.2] at endedL endedP
      simp only [entry, functionEntry, EndedBindings] at endedL endedP
      simp only [reservationEnv, EndedBindings, Nat.add_assoc]
      rw [← hqId, ← hrId, ← hdId]
      exact ⟨endedP.1, endedL.1, endedL.2⟩
    · refine ⟨historyPrefix, ?_⟩
      simp only [historyEq, entry, functionEntry, closingEvents, List.nil_append,
        List.append_assoc, List.cons_append, hqId, hrId, hdId]

theorem entry_obligations (n : Value target .uint) (initial : State target [.uint] Environment)
    (admitted : Admitted initial) :
    vcEntry (function n dialect policy)
      (fun original entry middle earlier =>
        Segment dialect policy entry.bindings entry.code (fun _ _ => False)
          (fun value => vcCleanup entry.localBindings entry.parameterBindings value (FullPost n original))
          middle earlier) initial := by
  obtain ⟨metadata, capacity, positive⟩ := admitted
  let literal : EntryContracts.LiteralInitializers (function n dialect policy).body :=
    .declare .uint (some n)
      (.declare .uint (some (Division.zero target)) (.body (functionCode target)))
  apply EntryContracts.vcEntry_of_literals (function n dialect policy) literal _ initial metadata capacity
  intro middle facts
  have locals := facts.localRecords
  have parameter := facts.parameter_access (kind := .uint) .here
  exact body_cleanup_segment dialect policy n (initial.inputs.get .here) initial middle
    ⟨initial.next + 2⟩ ⟨initial.next + 1⟩ ⟨initial.next⟩ _ rfl rfl rfl rfl positive metadata
    facts.metadata facts.frozen facts.next facts.slots facts.caller locals.2.1 locals.1 parameter.1

/-- Actual FunctionEval.start/observe return, after real reverse cleanup, for
arbitrary caller registries, targets, dialects, conversions and positive input
divisors. No observer normalization, legacy run certificate or target-success
admission is used. -/
theorem verified (n : Value target .uint) :
    FunctionContracts.Verifies (function n dialect policy) Admitted (FullPost (Environment := Environment) n) :=
  verifies_of_entry_vc (function n dialect policy) (function_supported dialect policy n)
    Admitted (FullPost n) (entry_obligations dialect policy n)

theorem no_failure (n : Value target .uint) :
    FunctionContracts.PrefixNoFailure (function n dialect policy) (Admitted (Environment := Environment)) :=
  (verified dialect policy n).noFailure

theorem useful (n : Value target .uint) (environment : Environment) (actor : Nat) :
    FunctionContracts.Certificate (function n dialect policy) Admitted (FullPost (Environment := Environment) n) := by
  refine ⟨?_, verified dialect policy n⟩
  refine ⟨State.empty (.cons (Division.one target) .nil) environment actor 3,
    State.empty_wellFormed _ _ _ _, Nat.le_refl 3, ?_⟩
  change 0 < 1
  decide

/-- For divisor one and arbitrary representable numerator, the actual cleaned
return is exactly n. This includes arbitrarily many loop iterations within the
target range, with no observation bound in the admission. -/
theorem divisor_one_observation (n : Value target .uint) (environment : Environment) (actor : Nat) :
    let initial := State.empty (.cons (Division.one target) .nil) environment actor 3
    ∃ steps final events,
      FunctionEval.observe (function n dialect policy) steps
        (FunctionEval.start (function n dialect policy) initial) = .returned n final events ∧
      FullPost n initial n final events := by
  let initial := State.empty (.cons (Division.one target) .nil) environment actor 3
  have admitted : Admitted initial :=
    ⟨State.empty_wellFormed _ _ _ _, Nat.le_refl 3, by change 0 < 1; decide⟩
  obtain ⟨steps, value, final, events, observed, correct⟩ := verified dialect policy n initial admitted
  have numeric := correct
  obtain ⟨remainder, reconstruction, bound, _⟩ := numeric
  change n.val = 1 * value.val + remainder.val at reconstruction
  change remainder.val < 1 at bound
  have same : value = n := by apply Fin.ext; omega
  subst value
  exact ⟨steps, final, events, observed, correct⟩

end EDSL.Source.Objects.Control.FunctionVC.EntryDivisionValidation
