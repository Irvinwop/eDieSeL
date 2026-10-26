/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.Contracts
import EDSL.Source.Objects.Control.Frames
import EDSL.Source.Objects.Control.Rules

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.Division
open StateSyntax
attribute [local implicit_reducible] Value Target.modulus

/-! Repeated-subtraction division at the already-bound internal control boundary.
The numerator is a typed entry value, used as the literal in `r = n`; q, r and
d are independent object bindings. No function entry/cleanup, native execution,
source-standard forward progress, interference or OS refinement is claimed.
-/

variable {target : Target} {parameters : List IntType} {Environment : Type}

def zero (target : Target) : Value target .uint := ⟨0, target.modulus_pos⟩

def one (target : Target) : Value target .uint :=
  ⟨1, by
    apply Nat.one_lt_two_pow
    have minimum := target.atLeast16
    omega⟩

/-- Independent mathematical invariant; neither division nor execution occurs. -/
def Invariant (n d q r : Value target .uint) : Prop :=
  n.val = d.val * q.val + r.val

/-- The true guard forces a representable increment, strict rank decrease and
preservation of reconstruction. No future completion is among the hypotheses. -/
theorem iteration_arithmetic (n d q r : Value target .uint)
    (positive : 0 < d.val) (invariant : Invariant n d q r)
    (guard : d.val ≤ r.val) :
    q.val + 1 < target.modulus ∧ r.val - d.val < r.val ∧
      n.val = d.val * (q.val + 1) + (r.val - d.val) := by
  have one_le : 1 ≤ d.val := positive
  have increment_le_product : q.val + 1 ≤ d.val * (q.val + 1) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (q.val + 1) one_le
  have product_le : d.val * (q.val + 1) ≤ n.val := by
    rw [Nat.mul_succ]
    change n.val = d.val * q.val + r.val at invariant
    omega
  refine ⟨Nat.lt_of_le_of_lt (Nat.le_trans increment_le_product product_le) n.isLt,
    by omega, ?_⟩
  rw [Nat.mul_succ]
  change n.val = d.val * q.val + r.val at invariant
  omega

def subValue (r d : Value target .uint) : Value target .uint :=
  ⟨r.val - d.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) r.isLt⟩

def succValue (q : Value target .uint) (fits : q.val + 1 < target.modulus) :
    Value target .uint := ⟨q.val + 1, fits⟩

theorem unsignedSub_no_borrow (r d : Value target .uint) (guard : d.val ≤ r.val) :
    unsignedSub target r d = .defined (subValue r d) := by
  unfold unsignedSub
  congr 1
  apply Fin.ext
  change (r.val + target.modulus - d.val) % target.modulus = r.val - d.val
  have shifted : r.val + target.modulus - d.val =
      (r.val - d.val) + target.modulus := by omega
  rw [shifted, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) r.isLt)

theorem unsignedAdd_no_wrap (q : Value target .uint) (fits : q.val + 1 < target.modulus) :
    unsignedAdd target q (one target) = .defined (succValue q fits) := by
  unfold unsignedAdd
  congr 1
  apply Fin.ext
  change (q.val + 1) % target.modulus = q.val + 1
  exact Nat.mod_eq_of_lt fits

abbrev Context : List ArithmeticType := [.uint, .uint, .uint]
abbrev qVar : Vars Context .uint := .here
abbrev rVar : Vars Context .uint := .there .here
abbrev dVar : Vars Context .uint := .there (.there .here)

def bindings (q r d : LValue .uint) : Env Context := .cons q (.cons r (.cons d .nil))

def condition (target : Target) : RHS target Context (.small .boolean) :=
  .compare .ge .uint (.param rVar) (.param dVar)

def body (target : Target) : Code target Context .uint :=
  .seq (.assign rVar (.usub (.param rVar) (.param dVar)))
    (.assign qVar (.uadd (.param qVar) (.literal (one target))))

def loop (target : Target) : Code target Context .uint := .loop (condition target) (body target)

/-- `q=0; r=n; while(r>=d){r=r-d; q=q+1;} return q`.
No observation length, rank or invariant is an executable annotation. -/
def code (n : Value target .uint) : Code target Context .uint :=
  .seq (.assign qVar (.literal (zero target)))
    (.seq (.assign rVar (.literal n)) (.seq (loop target) (.ret (.param qVar))))

theorem supported (n : Value target .uint) : (code n).Supported := by
  simp [code, loop, body, condition, Expr.Supported]

/-- A reached, live, owned uint object; no restriction on its old contents. -/
def cell (target : Target) (actor : Nat) (value : Option (Value target .uint)) : Object target :=
  ⟨.uint, .live, true, value, actor, ⟨true, true⟩⟩

def Ready (state : State target parameters Environment) (ref : LValue .uint) : Prop :=
  ∃ old, state.objects ref.id = some (cell target state.actor old)

def Holds (state : State target parameters Environment) (ref : LValue .uint)
    (value : Value target .uint) : Prop :=
  state.objects ref.id = some (cell target state.actor (some value))

/-- Only input/resource facts: independent bindings, current authority and d>0.
Old q/r contents may be uninitialized. The rest of the caller state is arbitrary. -/
structure Admission (q r dRef : LValue .uint) (d : Value target .uint)
    (initial : State target parameters Environment) : Prop where
  qr : q.id ≠ r.id
  qd : q.id ≠ dRef.id
  rd : r.id ≠ dRef.id
  qReady : Ready initial q
  rReady : Ready initial r
  denominator : CanLoad initial dRef d
  positive : 0 < d.val

/-- Exact accepted store update, not another execution function. -/
def put (state : State target parameters Environment) (ref : LValue .uint)
    (value : Value target .uint) : State target parameters Environment :=
  state.putObject ref.id (cell target state.actor (some value))

theorem holds_ready (state : State target parameters Environment) (ref : LValue .uint)
    (value : Value target .uint) (held : Holds state ref value) : Ready state ref :=
  ⟨some value, held⟩

theorem holds_load (state : State target parameters Environment) (ref : LValue .uint)
    (value : Value target .uint) (held : Holds state ref value) : CanLoad state ref value :=
  ⟨⟨true, true⟩, held, rfl⟩

theorem store_ready (state : State target parameters Environment) (ref : LValue .uint)
    (value : Value target .uint) (ready : Ready state ref) :
    store ref value state = (.ok (), put state ref value, [.write ref.id .uint value.toInt]) := by
  obtain ⟨old, registered⟩ := ready
  simp [store, registered, cell, put]

theorem put_holds (state : State target parameters Environment) (ref : LValue .uint)
    (value : Value target .uint) : Holds (put state ref value) ref value := by
  exact State.putObject_same _ _ _

theorem put_holds_other (state : State target parameters Environment) (ref other : LValue .uint)
    (value old : Value target .uint) (different : other.id ≠ ref.id)
    (held : Holds state other old) : Holds (put state ref value) other old := by
  exact (State.putObject_other _ _ _ _ different).trans held

theorem put_ready_other (state : State target parameters Environment) (ref other : LValue .uint)
    (value : Value target .uint) (different : other.id ≠ ref.id) (ready : Ready state other) :
    Ready (put state ref value) other := by
  obtain ⟨old, held⟩ := ready
  exact ⟨old, (State.putObject_other _ _ _ _ different).trans held⟩

theorem put_canLoad_other (state : State target parameters Environment) (ref other : LValue .uint)
    (value old : Value target .uint) (different : other.id ≠ ref.id)
    (readable : CanLoad state other old) : CanLoad (put state ref value) other old := by
  obtain ⟨permissions, held, read⟩ := readable
  exact ⟨permissions, (State.putObject_other _ _ _ _ different).trans held, read⟩

/-- The caller world is unchanged and every registry entry except q/r is exact,
including absent entries, tombstones, unrelated ownership, and d itself. -/
structure Frame (q r : LValue .uint) (before after : State target parameters Environment) : Prop where
  world : WorldFrame before after
  outside : ∀ id, id ≠ q.id → id ≠ r.id → after.objects id = before.objects id

theorem Frame.refl (q r : LValue .uint) (state : State target parameters Environment) :
    Frame q r state state := ⟨WorldFrame.refl state, fun _ _ _ => rfl⟩

theorem Frame.trans {q r : LValue .uint} {first middle final : State target parameters Environment}
    (earlier : Frame q r first middle) (later : Frame q r middle final) : Frame q r first final :=
  ⟨earlier.world.trans later.world,
    fun id hq hr => (later.outside id hq hr).trans (earlier.outside id hq hr)⟩

theorem put_frame (q r ref : LValue .uint) (state : State target parameters Environment)
    (value : Value target .uint) (selected : ref = q ∨ ref = r) : Frame q r state (put state ref value) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro id hq hr
  rcases selected with rfl | rfl
  · exact State.putObject_other _ _ _ _ hq
  · exact State.putObject_other _ _ _ _ hr

/- These small equations expose only the outer shared expression constructor.
The leaves are discharged using actual object load contracts, not a program
interpreter or a whole-routine unfolding of the expression engine. -/
private theorem eval_uadd {context : List ArithmeticType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (env : Env context)
    (left right : RHS target context .uint) (state : State target parameters Environment)
    (x y z : Value target .uint) (le re : List Event)
    (leftRun : StateEval.evalExpr dialect policy env left state = (.ok x, state, le))
    (rightRun : StateEval.evalExpr dialect policy env right state = (.ok y, state, re))
    (scalar : unsignedAdd target x y = .defined z) :
    StateEval.evalExpr dialect policy env (.uadd left right) state = (.ok z, state, le ++ re) := by
  change Op.bind (StateEval.evalExpr dialect policy env left)
    (fun a => Op.bind (StateEval.evalExpr dialect policy env right)
      (fun b => (EffectM.liftScalar (unsignedAdd target a b)).run)) state = _
  simp only [Op.bind, Effects.Op.bind, leftRun, rightRun, scalar, EffectM.run_liftScalar,
    EffectM.scalarOutcome, List.append_nil]

private theorem eval_usub {context : List ArithmeticType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (env : Env context)
    (left right : RHS target context .uint) (state : State target parameters Environment)
    (x y z : Value target .uint) (le re : List Event)
    (leftRun : StateEval.evalExpr dialect policy env left state = (.ok x, state, le))
    (rightRun : StateEval.evalExpr dialect policy env right state = (.ok y, state, re))
    (scalar : unsignedSub target x y = .defined z) :
    StateEval.evalExpr dialect policy env (.usub left right) state = (.ok z, state, le ++ re) := by
  change Op.bind (StateEval.evalExpr dialect policy env left)
    (fun a => Op.bind (StateEval.evalExpr dialect policy env right)
      (fun b => (EffectM.liftScalar (unsignedSub target a b)).run)) state = _
  simp only [Op.bind, Effects.Op.bind, leftRun, rightRun, scalar, EffectM.run_liftScalar,
    EffectM.scalarOutcome, List.append_nil]

private theorem eval_compare {context : List ArithmeticType}
    (dialect : Dialect) (policy : IntegerConversionPolicy) (env : Env context)
    (operation : ComparisonOp) (left right : RHS target context .uint)
    (state : State target parameters Environment) (x y : Value target .uint) (le re : List Event)
    (leftRun : StateEval.evalExpr dialect policy env left state = (.ok x, state, le))
    (rightRun : StateEval.evalExpr dialect policy env right state = (.ok y, state, re)) :
    StateEval.evalExpr dialect policy env (.compare operation .uint left right) state =
      (.ok (compareValues operation x y), state, le ++ re) := by
  change Op.bind (StateEval.evalExpr dialect policy env left)
    (fun a => Op.bind (StateEval.evalExpr dialect policy env right)
      (fun b => Op.pure (compareValues operation a b))) state = _
  simp only [Op.bind, Effects.Op.bind, leftRun, rightRun, Op.pure, List.append_nil]

theorem eval_var (dialect : Dialect) (policy : IntegerConversionPolicy)
    (q r dRef : LValue .uint) (index : Vars Context .uint)
    (state : State target parameters Environment) (value : Value target .uint)
    (readable : CanLoad state ((bindings q r dRef).get index) value) :
    StateEval.evalExpr dialect policy (bindings q r dRef) (.param index) state =
      (.ok value, state, [.read ((bindings q r dRef).get index).id .uint value.toInt]) := by
  rw [StateEval.evalExpr_var]
  exact load_contract (kind := .uint) dialect state ((bindings q r dRef).get index) value readable

theorem eval_condition (dialect : Dialect) (policy : IntegerConversionPolicy)
    (q r dRef : LValue .uint) (state : State target parameters Environment)
    (rv dv : Value target .uint) (hr : Holds state r rv) (hd : CanLoad state dRef dv) :
    StateEval.evalExpr dialect policy (bindings q r dRef) (condition target) state =
      (.ok (compareValues .ge rv dv), state,
        [.read r.id .uint rv.toInt, .read dRef.id .uint dv.toInt]) :=
  eval_compare dialect policy (bindings q r dRef) .ge (.param rVar) (.param dVar) state rv dv _ _
    (eval_var dialect policy q r dRef rVar state rv (holds_load state r rv hr))
    (eval_var dialect policy q r dRef dVar state dv hd)

theorem eval_subtract (dialect : Dialect) (policy : IntegerConversionPolicy)
    (q r dRef : LValue .uint) (state : State target parameters Environment)
    (rv dv : Value target .uint) (hr : Holds state r rv) (hd : CanLoad state dRef dv)
    (guard : dv.val ≤ rv.val) :
    StateEval.evalExpr dialect policy (bindings q r dRef) (.usub (.param rVar) (.param dVar)) state =
      (.ok (subValue rv dv), state, [.read r.id .uint rv.toInt, .read dRef.id .uint dv.toInt]) :=
  eval_usub dialect policy (bindings q r dRef) (.param rVar) (.param dVar) state rv dv _ _ _
    (eval_var dialect policy q r dRef rVar state rv (holds_load state r rv hr))
    (eval_var dialect policy q r dRef dVar state dv hd) (unsignedSub_no_borrow rv dv guard)

theorem eval_increment (dialect : Dialect) (policy : IntegerConversionPolicy)
    (q r dRef : LValue .uint) (state : State target parameters Environment)
    (qv : Value target .uint) (hq : Holds state q qv) (fits : qv.val + 1 < target.modulus) :
    StateEval.evalExpr dialect policy (bindings q r dRef)
      (.uadd (.param qVar) (.literal (one target))) state =
      (.ok (succValue qv fits), state, [.read q.id .uint qv.toInt]) := by
  simpa only [List.append_nil, bindings, Env.get] using
    eval_uadd dialect policy (bindings q r dRef) (.param qVar) (.literal (one target))
      state qv (one target) (succValue qv fits) _ []
      (eval_var dialect policy q r dRef qVar state qv (holds_load state q qv hq))
      rfl (unsignedAdd_no_wrap qv fits)

abbrev Configuration (target : Target) (parameters : List IntType) (Environment : Type) :=
  Config target parameters Environment Context .uint

private theorem tick_seq (dialect : Dialect) (policy : IntegerConversionPolicy)
    (env : Env Context) (first next : Code target Context .uint)
    (rest : List (Code target Context .uint)) (state : State target parameters Environment)
    (events : List Event) :
    tick dialect policy env (⟨.seq first next :: rest, state, events, .running⟩ :
      Configuration target parameters Environment) =
        ⟨first :: next :: rest, state, events, .running⟩ := rfl

private theorem tick_assign (dialect : Dialect) (policy : IntegerConversionPolicy)
    (env : Env Context) (index : Vars Context .uint) (expression : RHS target Context .uint)
    (rest : List (Code target Context .uint)) (state : State target parameters Environment)
    (events reads : List Event) (value : Value target .uint)
    (evaluation : StateEval.evalExpr dialect policy env expression state = (.ok value, state, reads))
    (ready : Ready state (env.get index)) :
    tick dialect policy env (⟨.assign index expression :: rest, state, events, .running⟩ :
      Configuration target parameters Environment) =
        ⟨rest, put state (env.get index) value,
          events ++ (reads ++ [.write (env.get index).id .uint value.toInt]), .running⟩ := by
  simp only [tick, perform, assign, Op.bind, Effects.Op.bind, evaluation, store_ready state _ value ready]

private theorem tick_loop (dialect : Dialect) (policy : IntegerConversionPolicy)
    (env : Env Context) (test : RHS target Context (.small .boolean))
    (body : Code target Context .uint) (rest : List (Code target Context .uint))
    (state : State target parameters Environment) (events reads : List Event)
    (value : Value target (.small .boolean))
    (evaluation : StateEval.evalExpr dialect policy env test state = (.ok value, state, reads)) :
    tick dialect policy env (⟨.loop test body :: rest, state, events, .running⟩ :
      Configuration target parameters Environment) =
        ⟨if value.toInt = 0 then rest else body :: .loop test body :: rest,
          state, events ++ reads, .running⟩ := by
  simp only [tick, perform, evaluation]

private theorem tick_return (dialect : Dialect) (policy : IntegerConversionPolicy)
    (env : Env Context) (expression : RHS target Context .uint)
    (rest : List (Code target Context .uint)) (state : State target parameters Environment)
    (events reads : List Event) (value : Value target .uint)
    (evaluation : StateEval.evalExpr dialect policy env expression state = (.ok value, state, reads)) :
    tick dialect policy env (⟨.ret expression :: rest, state, events, .running⟩ :
      Configuration target parameters Environment) =
        ⟨[], state, events ++ reads, .returned value⟩ := by
  simp only [tick, perform, evaluation]

def header (state : State target parameters Environment) (events : List Event) :
    Configuration target parameters Environment :=
  ⟨[loop target, .ret (.param qVar)], state, events, .running⟩

def iterationEvents (q r dRef : LValue .uint) (qv rv dv : Value target .uint)
    (fits : qv.val + 1 < target.modulus) : List Event :=
  [.read r.id .uint rv.toInt, .read dRef.id .uint dv.toInt,
   .read r.id .uint rv.toInt, .read dRef.id .uint dv.toInt,
   .write r.id .uint (subValue rv dv).toInt,
   .read q.id .uint qv.toInt, .write q.id .uint (succValue qv fits).toInt]

/-- Every true iteration actually finishes: guard, sequence expansion, and two
successful assignments. The four is a local trace witness, never semantic fuel.
Both reads of r/d and the read of q are the shared object operations. -/
theorem iteration_run (dialect : Dialect) (policy : IntegerConversionPolicy)
    (q r dRef : LValue .uint) (state : State target parameters Environment)
    (events : List Event) (qv rv dv : Value target .uint)
    (qr : q.id ≠ r.id) (hq : Holds state q qv) (hr : Holds state r rv)
    (hd : CanLoad state dRef dv) (guard : dv.val ≤ rv.val)
    (fits : qv.val + 1 < target.modulus) :
    run dialect policy (bindings q r dRef) 4 (header state events) =
      header (put (put state r (subValue rv dv)) q (succValue qv fits))
        (events ++ iterationEvents q r dRef qv rv dv fits) := by
  let env := bindings q r dRef
  let nextR := put state r (subValue rv dv)
  have envR : env.get rVar = r := rfl
  have envQ : env.get qVar = q := rfl
  have nonzero : (compareValues .ge rv dv).toInt ≠ 0 := by
    apply (compareValues_nonzero_iff .ge rv dv).mpr
    exact Int.ofNat_le.mpr guard
  have first : tick dialect policy env (header state events) =
      (⟨[body target, loop target, .ret (.param qVar)], state,
        events ++ [.read r.id .uint rv.toInt, .read dRef.id .uint dv.toInt], .running⟩ :
          Configuration target parameters Environment) := by
    unfold header loop
    rw [tick_loop dialect policy env (condition target) (body target) _ state events _ _
      (eval_condition dialect policy q r dRef state rv dv hr hd)]
    simp only [nonzero, ↓reduceIte]
  have middleQ : Holds nextR q qv := put_holds_other state r q _ qv qr hq
  change run dialect policy env (3 + 1) (header state events) = _
  rw [run_succ_front, first]
  change run dialect policy env (2 + 1) _ = _
  rw [run_succ_front]
  simp only [body]
  rw [tick_seq]
  change run dialect policy env (1 + 1) _ = _
  rw [run_succ_front, tick_assign dialect policy env rVar _ _ state _ _ _
    (eval_subtract dialect policy q r dRef state rv dv hr hd guard) (holds_ready state r rv hr), envR]
  change run dialect policy env (0 + 1) _ = _
  rw [run_succ_front, tick_assign dialect policy env qVar _ _ nextR _ _ _
    (eval_increment dialect policy q r dRef nextR qv middleQ fits)
    (holds_ready nextR q qv middleQ), envQ, run_zero]
  simp only [nextR, header, iterationEvents, List.append_assoc, List.cons_append, List.nil_append]

/-- A false guard and the actual q-object read return in two transitions. -/
theorem exit_run (dialect : Dialect) (policy : IntegerConversionPolicy)
    (q r dRef : LValue .uint) (state : State target parameters Environment)
    (events : List Event) (qv rv dv : Value target .uint)
    (hq : Holds state q qv) (hr : Holds state r rv) (hd : CanLoad state dRef dv)
    (guard : rv.val < dv.val) :
    run dialect policy (bindings q r dRef) 2 (header state events) =
      (⟨[], state, events ++
        [.read r.id .uint rv.toInt, .read dRef.id .uint dv.toInt, .read q.id .uint qv.toInt],
          .returned qv⟩ : Configuration target parameters Environment) := by
  let env := bindings q r dRef
  have isZero : (compareValues .ge rv dv).toInt = 0 := by
    apply (compareValues_zero_iff .ge rv dv).mpr
    change ¬(dv.val : Int) ≤ (rv.val : Int)
    omega
  have first : tick dialect policy env (header state events) =
      (⟨[.ret (.param qVar)], state,
        events ++ [.read r.id .uint rv.toInt, .read dRef.id .uint dv.toInt], .running⟩ :
          Configuration target parameters Environment) := by
    unfold header loop
    rw [tick_loop dialect policy env (condition target) (body target) _ state events _ _
      (eval_condition dialect policy q r dRef state rv dv hr hd)]
    simp only [isZero, ↓reduceIte]
  change run dialect policy env (1 + 1) (header state events) = _
  rw [run_succ_front, first]
  change run dialect policy env (0 + 1) _ = _
  rw [run_succ_front, tick_return dialect policy env (.param qVar) [] state _ _ qv
    (eval_var dialect policy q r dRef qVar state qv (holds_load state q qv hq)), run_zero]
  simp only [bindings, Env.get, List.append_assoc, List.cons_append, List.nil_append]

/-- Independent numeric contract with the real returned q, final remainder
object, unchanged denominator, and caller frame. Events remain those of run. -/
def Post (n d : Value target .uint) (q r dRef : LValue .uint) :
    Protocol.Post target parameters Environment (Value target .uint) :=
  fun original result final _ => ∃ remainder : Value target .uint,
    n.val = d.val * result.val + remainder.val ∧ remainder.val < d.val ∧
    Holds final q result ∧ Holds final r remainder ∧ CanLoad final dRef d ∧
    Frame q r original final

/-- Annotation only at loop headers. Resources and reconstruction are maintained
by proved steps; neither termination nor the final remainder bound is assumed. -/
def Header (n d : Value target .uint) (q r dRef : LValue .uint)
    (original : State target parameters Environment)
    (config : Configuration target parameters Environment) : Prop :=
  ∃ state events qv rv, config = header state events ∧
    Frame q r original state ∧ Holds state q qv ∧ Holds state r rv ∧
    CanLoad state dRef d ∧ Invariant n d qv rv

/-- Total proof annotation on configurations. Executable control never queries
this registry projection; Header supplies its interpretation as the current r. -/
def rank (r : LValue .uint) (config : Configuration target parameters Environment) : Nat :=
  match config.state.objects r.id with
  | none => 0
  | some object => match object.value with
    | none => 0
    | some value => value.toInt.toNat

theorem rank_header (r : LValue .uint) (state : State target parameters Environment)
    (events : List Event) (rv : Value target .uint) (held : Holds state r rv) :
    rank r (header state events) = rv.val := by
  unfold Holds at held
  simp only [rank, header, held, cell, ArithmeticType.asIntType, Value.toInt, Int.toNat_natCast]

/-- A concrete instantiation of the shared finite-progress rule. True guards
have the actual four-tick endpoint, not just a conditional decrease theorem. -/
theorem loop_progress (dialect : Dialect) (policy : IntegerConversionPolicy)
    (n d : Value target .uint) (q r dRef : LValue .uint)
    (qr : q.id ≠ r.id) (qd : q.id ≠ dRef.id) (rd : r.id ≠ dRef.id)
    (positive : 0 < d.val) :
    FiniteProgress (parameters := parameters) (Environment := Environment)
      dialect policy (bindings q r dRef) (Header n d q r dRef) (rank r)
      (Post n d q r dRef) := by
  intro original config member
  rcases member with ⟨state, events, qv, rv, rfl, frame, hq, hr, hd, invariant⟩
  by_cases guard : d.val ≤ rv.val
  · obtain ⟨fits, decreases, reconstruction⟩ := iteration_arithmetic n d qv rv positive invariant guard
    let qNext := succValue qv fits
    let rNext := subValue rv d
    let middle := put state r rNext
    let final := put middle q qNext
    have nextQ : Holds final q qNext := put_holds middle q qNext
    have nextR : Holds final r rNext :=
      put_holds_other middle q r qNext rNext (Ne.symm qr) (put_holds state r rNext)
    have nextD : CanLoad final dRef d :=
      put_canLoad_other middle q dRef qNext d (Ne.symm qd)
        (put_canLoad_other state r dRef rNext d (Ne.symm rd) hd)
    have nextFrame : Frame q r original final :=
      frame.trans ((put_frame q r r state rNext (Or.inr rfl)).trans
        (put_frame q r q middle qNext (Or.inl rfl)))
    refine ⟨4, Or.inr ?_⟩
    rw [iteration_run dialect policy q r dRef state events qv rv d qr hq hr hd guard fits]
    constructor
    · exact ⟨final, events ++ iterationEvents q r dRef qv rv d fits, qNext, rNext,
        rfl, nextFrame, nextQ, nextR, nextD, reconstruction⟩
    · rw [rank_header r final _ rNext nextR, rank_header r state events rv hr]
      exact decreases
  · have less : rv.val < d.val := by omega
    have execution := exit_run dialect policy q r dRef state events qv rv d hq hr hd less
    refine ⟨2, Or.inl ⟨qv, ?_, ?_⟩⟩
    · rw [execution]
    · rw [execution]
      exact ⟨rv, invariant, less, hq, hr, hd, frame⟩

/-- All loop-header states satisfying the resource/invariant facts actually
return, by strong induction on the current remainder through the shared rule. -/
theorem loop_returns (dialect : Dialect) (policy : IntegerConversionPolicy)
    (n d : Value target .uint) (q r dRef : LValue .uint)
    (qr : q.id ≠ r.id) (qd : q.id ≠ dRef.id) (rd : r.id ≠ dRef.id)
    (positive : 0 < d.val) (original state : State target parameters Environment)
    (events : List Event) (qv rv : Value target .uint)
    (frame : Frame q r original state) (hq : Holds state q qv) (hr : Holds state r rv)
    (hd : CanLoad state dRef d) (invariant : Invariant n d qv rv) :
    ∃ steps value,
      (run dialect policy (bindings q r dRef) steps (header state events)).status = .returned value ∧
      Post n d q r dRef original value
        (run dialect policy (bindings q r dRef) steps (header state events)).state
        (run dialect policy (bindings q r dRef) steps (header state events)).events :=
  returns_of_finiteProgress dialect policy (bindings q r dRef) (Header n d q r dRef) (rank r)
    (loop_progress dialect policy n d q r dRef qr qd rd positive) original (header state events)
    ⟨state, events, qv, rv, rfl, frame, hq, hr, hd, invariant⟩

/-- Initialization is five concrete transitions, with no reads of old q/r.
The entry value n is already typed, and r receives it without conversion. -/
theorem initialize_run (dialect : Dialect) (policy : IntegerConversionPolicy)
    (n : Value target .uint) (q r dRef : LValue .uint)
    (initial : State target parameters Environment) (qr : q.id ≠ r.id)
    (hq : Ready initial q) (hr : Ready initial r) :
    run dialect policy (bindings q r dRef) 5 (start (code n) initial) =
      header (put (put initial q (zero target)) r n)
        [.write q.id .uint (zero target).toInt, .write r.id .uint n.toInt] := by
  let env := bindings q r dRef
  let middle := put initial q (zero target)
  have envQ : env.get qVar = q := rfl
  have envR : env.get rVar = r := rfl
  have middleReady : Ready middle r := put_ready_other initial q r _ (Ne.symm qr) hr
  rw [start_supported (code n) initial (supported n)]
  simp only [code, startUnchecked]
  change run dialect policy env (4 + 1) _ = _
  rw [run_succ_front, tick_seq]
  change run dialect policy env (3 + 1) _ = _
  rw [run_succ_front, tick_assign dialect policy env qVar (.literal (zero target)) _ initial [] []
    (zero target) rfl hq, envQ]
  change run dialect policy env (2 + 1) _ = _
  rw [run_succ_front, tick_seq]
  change run dialect policy env (1 + 1) _ = _
  rw [run_succ_front, tick_assign dialect policy env rVar (.literal n) _ middle _ [] n rfl middleReady, envR]
  change run dialect policy env (0 + 1) _ = _
  rw [run_succ_front, tick_seq, run_zero]
  simp only [middle, header, List.nil_append, List.cons_append]

/-- All typed numerators and positive typed denominators, every dialect and
integer conversion policy, all nonaliasing authorized bindings, and arbitrary
remaining caller state have an actual finite value return with reconstruction,
strict final remainder and the full caller/world frame. This is a body-level
internal control contract, before any function/scope cleanup transport. -/
theorem verified (dialect : Dialect) (policy : IntegerConversionPolicy)
    (n d : Value target .uint) (q r dRef : LValue .uint) :
    Verifies (parameters := parameters) (Environment := Environment)
      dialect policy (bindings q r dRef) (code n) (Admission q r dRef d) (Post n d q r dRef) := by
  intro initial admitted
  let middle := put initial q (zero target)
  let initialized := put middle r n
  let events : List Event := [.write q.id .uint (zero target).toInt, .write r.id .uint n.toInt]
  have initializedQ : Holds initialized q (zero target) :=
    put_holds_other middle r q n (zero target) admitted.qr (put_holds initial q (zero target))
  have initializedR : Holds initialized r n := put_holds middle r n
  have initializedD : CanLoad initialized dRef d :=
    put_canLoad_other middle r dRef n d (Ne.symm admitted.rd)
      (put_canLoad_other initial q dRef (zero target) d (Ne.symm admitted.qd) admitted.denominator)
  have frame : Frame q r initial initialized :=
    (put_frame q r q initial (zero target) (Or.inl rfl)).trans
      (put_frame q r r middle n (Or.inr rfl))
  have invariant : Invariant n d (zero target) n := by
    simp only [Invariant, zero, Nat.mul_zero, Nat.zero_add]
  have entry := initialize_run dialect policy n q r dRef initial admitted.qr admitted.qReady admitted.rReady
  obtain ⟨steps, value, returned, resultPost⟩ :=
    loop_returns dialect policy n d q r dRef admitted.qr admitted.qd admitted.rd admitted.positive
      initial initialized events (zero target) n frame initializedQ initializedR initializedD invariant
  refine ⟨5 + steps, value, ?_, ?_⟩
  · rw [run_add, entry]
    exact returned
  · rw [run_add, entry]
    exact resultPost

/-- The independent domain is inhabited by installing three actual live
objects over any supplied caller state, with no execution or outcome premise. -/
theorem admission_inhabited (q r dRef : LValue .uint) (d : Value target .uint)
    (qr : q.id ≠ r.id) (qd : q.id ≠ dRef.id) (rd : r.id ≠ dRef.id)
    (positive : 0 < d.val) (caller : State target parameters Environment) :
    ∃ initial : State target parameters Environment, Admission q r dRef d initial := by
  let first := put caller q (zero target)
  let second := put first r (zero target)
  let initial := put second dRef d
  have hq : Holds initial q (zero target) :=
    put_holds_other second dRef q d (zero target) qd
      (put_holds_other first r q (zero target) (zero target) qr (put_holds caller q (zero target)))
  have hr : Holds initial r (zero target) :=
    put_holds_other second dRef r d (zero target) rd (put_holds first r (zero target))
  exact ⟨initial, qr, qd, rd, holds_ready initial q _ hq, holds_ready initial r _ hr,
    holds_load initial dRef d (put_holds second dRef d), positive⟩

private theorem cell_wellFormed (actor : Nat) (value : Option (Value target .uint)) :
    (cell target actor value).WellFormed := by
  constructor <;> intro impossible <;> cases impossible

private theorem put_wellFormed (state : State target parameters Environment)
    (ref : LValue .uint) (value : Value target .uint)
    (wellFormed : state.WellFormed) (bound : ref.id < state.next) :
    (put state ref value).WellFormed := by
  intro id object registered
  by_cases same : id = ref.id
  · subst id
    have equal : cell target state.actor (some value) = object :=
      Option.some.inj ((State.putObject_same _ _ _).symm.trans registered)
    subst object
    exact ⟨bound, cell_wellFormed state.actor (some value)⟩
  · exact wellFormed id object ((State.putObject_other _ _ _ _ same).symm.trans registered)

/-- A populated, well-formed admission witness at arbitrary distinct
identities, given actual input/environment values. No safety/success fact is
used, and fresh identity is above every installed object. -/
theorem wellFormed_admission_inhabited (q r dRef : LValue .uint) (d : Value target .uint)
    (qr : q.id ≠ r.id) (qd : q.id ≠ dRef.id) (rd : r.id ≠ dRef.id)
    (positive : 0 < d.val) (inputs : Inputs target parameters) (environment : Environment)
    (actor capacity : Nat) :
    ∃ initial : State target parameters Environment,
      Admission q r dRef d initial ∧ initial.WellFormed ∧
      initial.inputs = inputs ∧ initial.environment = environment ∧ initial.actor = actor := by
  let base : State target parameters Environment :=
    { State.empty inputs environment actor capacity with next := q.id + r.id + dRef.id + 1 }
  let first := put base q (zero target)
  let second := put first r (zero target)
  let initial := put second dRef d
  have hq : Holds initial q (zero target) :=
    put_holds_other second dRef q d (zero target) qd
      (put_holds_other first r q (zero target) (zero target) qr (put_holds base q (zero target)))
  have hr : Holds initial r (zero target) :=
    put_holds_other second dRef r d (zero target) rd (put_holds first r (zero target))
  have baseWF : base.WellFormed := by
    intro id object registered
    cases registered
  have qBound : q.id < base.next := by dsimp [base]; omega
  have rBound : r.id < first.next := by dsimp [first, put, State.putObject, base]; omega
  have dBound : dRef.id < second.next := by dsimp [second, first, put, State.putObject, base]; omega
  have firstWF := put_wellFormed base q (zero target) baseWF qBound
  have secondWF := put_wellFormed first r (zero target) firstWF rBound
  refine ⟨initial, ⟨qr, qd, rd, holds_ready initial q _ hq, holds_ready initial r _ hr,
    holds_load initial dRef d (put_holds second dRef d), positive⟩,
    put_wellFormed second dRef d secondWF dBound, rfl, rfl, rfl⟩

/-- Every old object record retains all metadata. Non-q/r records are already
preserved exactly by Frame; this also covers old q/r with arbitrary contents. -/
theorem post_old_metadata (n d : Value target .uint) (q r dRef : LValue .uint)
    (original final : State target parameters Environment) (result : Value target .uint)
    (events : List Event) (admitted : Admission q r dRef d original)
    (post : Post n d q r dRef original result final events)
    (id : Nat) (old : Object target) (registered : original.objects id = some old) :
    ∃ current, final.objects id = some current ∧ SameAccessMetadata old current := by
  obtain ⟨remainder, _, _, hq, hr, _, frame⟩ := post
  by_cases isQ : id = q.id
  · subst id
    obtain ⟨previous, earlier⟩ := admitted.qReady
    have equal : cell target original.actor previous = old := Option.some.inj (earlier.symm.trans registered)
    subst old
    refine ⟨cell target final.actor (some result), hq, ?_⟩
    simp only [SameAccessMetadata, cell, frame.world.actor, and_self]
  · by_cases isR : id = r.id
    · subst id
      obtain ⟨previous, earlier⟩ := admitted.rReady
      have equal : cell target original.actor previous = old := Option.some.inj (earlier.symm.trans registered)
      subst old
      refine ⟨cell target final.actor (some remainder), hr, ?_⟩
      simp only [SameAccessMetadata, cell, frame.world.actor, and_self]
    · exact ⟨old, (frame.outside id isQ isR).trans registered, rfl, rfl, rfl, rfl, rfl⟩

/-- An actual caller-state witness supplies values for potentially empty state
indices. Useful admission is constructed rather than assumed as success. -/
theorem certificate (dialect : Dialect) (policy : IntegerConversionPolicy)
    (n d : Value target .uint) (q r dRef : LValue .uint)
    (qr : q.id ≠ r.id) (qd : q.id ≠ dRef.id) (rd : r.id ≠ dRef.id)
    (positive : 0 < d.val) (caller : State target parameters Environment) :
    Certificate (parameters := parameters) (Environment := Environment)
      dialect policy (bindings q r dRef) (code n) (Admission q r dRef d) (Post n d q r dRef) := by
  obtain ⟨initial, admitted, _⟩ := wellFormed_admission_inhabited q r dRef d qr qd rd positive
    caller.inputs caller.environment caller.actor caller.automaticSlots
  exact ⟨⟨initial, admitted⟩, verified dialect policy n d q r dRef⟩

end EDSL.Source.Objects.Control.Division
