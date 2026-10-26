/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.AccessContracts
import EDSL.Source.Objects.Effects
import Init.Data.List.Perm

set_option autoImplicit false
namespace EDSL.Source.Objects.ReadOrder

/- Internal, successful read-only composition at one frozen state. These laws
do not establish C operand sequencing or a source/native memory correspondence.
Actor, inputs and environment are part of that entire state; no interference,
volatile access, atomics, mutation or scheduler transitions are modeled here.
Lazy selection must still demand only its selected subexpressions. -/

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {α β : Type}

/-- Collect two results using the existing EffectM bind, without a new evaluator.
The second computation is independent of the first computation's returned value. -/
def pair (first : EffectM target parameters Environment α)
    (second : EffectM target parameters Environment β) :
    EffectM target parameters Environment (α × β) := do
  let left ← first
  let right ← second
  pure (left, right)

/-- Compare values through an explicit projection, the whole state by equality,
and both complete traces by List.Perm. Error identities are retained by Except.map;
this relation does not normalize failure priority or erase repeated reads. -/
def Related (project : β → α) (first : Result target parameters Environment α)
    (second : Result target parameters Environment β) : Prop :=
  first.1 = second.1.map project ∧ first.2.1 = second.2.1 ∧
    List.Perm first.2.2 second.2.2

/-- A failed prefix retains its actual state and events and skips the continuation.
This internal execution law makes no read-only assumption. -/
theorem bind_error_left (first : EffectM target parameters Environment α)
    (next : α → EffectM target parameters Environment β)
    (state updated : State target parameters Environment) (reason : Stop)
    (events : List Event) (failed : first.run state = (.error reason, updated, events)) :
    (first >>= next).run state = (.error reason, updated, events) := by
  change Op.bind first.run (fun value => (next value).run) state = _
  simp only [Op.bind, failed]

/-- A later failure retains its own final state and all prefix and failure events.
Accepted effects are not rolled back and failure events are not discarded. -/
theorem bind_error_right (first : EffectM target parameters Environment α)
    (next : α → EffectM target parameters Environment β)
    (state updated finalState : State target parameters Environment) (value : α)
    (reason : Stop) (events moreEvents : List Event)
    (accepted : first.run state = (.ok value, updated, events))
    (failed : (next value).run updated = (.error reason, finalState, moreEvents)) :
    (first >>= next).run state = (.error reason, finalState, events ++ moreEvents) := by
  change Op.bind first.run (fun value => (next value).run) state = _
  simp only [Op.bind, accepted, failed]

private theorem pair_success (first : EffectM target parameters Environment α)
    (second : EffectM target parameters Environment β)
    (state : State target parameters Environment) (left : α) (right : β)
    (leftEvents rightEvents : List Event)
    (leftReady : first.run state = (.ok left, state, leftEvents))
    (rightReady : second.run state = (.ok right, state, rightEvents)) :
    (pair first second).run state =
      (.ok (left, right), state, leftEvents ++ rightEvents) := by
  change Op.bind first.run (fun left =>
    Op.bind second.run (fun right => Op.pure (left, right))) state = _
  simp only [Op.bind, Op.pure, leftReady, rightReady, List.append_nil]

/-- INTERNAL composition lemma, not source admission. Both executions must succeed
at the SAME state and preserve that entire state. Access clients must first derive
these execution facts from independent contracts, as load_load_diamond does below.
Each order has its own trace; their concatenations are related by permutation,
with reversed returned pairs compared through Prod.swap. No trace equality is used.
For read-only use, clients must also establish that the events are reads; arbitrary
EffectM traces alone carry no C sequencing or external-observation guarantee. -/
theorem commute_success (first : EffectM target parameters Environment α)
    (second : EffectM target parameters Environment β)
    (state : State target parameters Environment) (left : α) (right : β)
    (leftEvents rightEvents : List Event)
    (leftReady : first.run state = (.ok left, state, leftEvents))
    (rightReady : second.run state = (.ok right, state, rightEvents)) :
    (pair first second).run state =
      (.ok (left, right), state, leftEvents ++ rightEvents) ∧
    (pair second first).run state =
      (.ok (right, left), state, rightEvents ++ leftEvents) ∧
    Related Prod.swap ((pair first second).run state) ((pair second first).run state) := by
  have forward := pair_success first second state left right leftEvents rightEvents
    leftReady rightReady
  have backward := pair_success second first state right left rightEvents leftEvents
    rightReady leftReady
  refine ⟨forward, backward, ?_⟩
  rw [forward, backward]
  exact ⟨rfl, rfl, List.perm_append_comm⟩

/-- Concrete load-load diamond from independent registry/owner/read/initialization
conditions in the original state. Kinds, typed values, references and every state
field are arbitrary. There is no distinct-ID premise: compatible aliasing is allowed,
and both occurrences of an aliased read remain in the event multiset. The one dialect
is explicit. These primitive facts do not admit a source program or reorder failures. -/
theorem load_load_diamond {leftKind rightKind : ArithmeticType} (dialect : Dialect)
    (state : State target parameters Environment)
    (leftRef : LValue leftKind) (rightRef : LValue rightKind)
    (leftValue : Value target leftKind.asIntType)
    (rightValue : Value target rightKind.asIntType)
    (leftReady : CanLoad state leftRef leftValue)
    (rightReady : CanLoad state rightRef rightValue) :
    (pair (EffectM.ofOp (load dialect leftRef))
      (EffectM.ofOp (load dialect rightRef))).run state =
        (.ok (leftValue, rightValue), state,
          [.read leftRef.id leftKind leftValue.toInt,
           .read rightRef.id rightKind rightValue.toInt]) ∧
    (pair (EffectM.ofOp (load dialect rightRef))
      (EffectM.ofOp (load dialect leftRef))).run state =
        (.ok (rightValue, leftValue), state,
          [.read rightRef.id rightKind rightValue.toInt,
           .read leftRef.id leftKind leftValue.toInt]) ∧
    Related Prod.swap
      ((pair (EffectM.ofOp (load dialect leftRef))
        (EffectM.ofOp (load dialect rightRef))).run state)
      ((pair (EffectM.ofOp (load dialect rightRef))
        (EffectM.ofOp (load dialect leftRef))).run state) := by
  exact commute_success (EffectM.ofOp (load dialect leftRef))
    (EffectM.ofOp (load dialect rightRef)) state leftValue rightValue
    [.read leftRef.id leftKind leftValue.toInt] [.read rightRef.id rightKind rightValue.toInt]
    (load_contract dialect state leftRef leftValue leftReady)
    (load_contract dialect state rightRef rightValue rightReady)

/-- Same-object specialization: one independent readiness condition suffices, and
the trace contains two read occurrences rather than a deduplicated observation. -/
theorem load_load_alias {kind : ArithmeticType} (dialect : Dialect)
    (state : State target parameters Environment) (ref : LValue kind)
    (value : Value target kind.asIntType) (ready : CanLoad state ref value) :
    (pair (EffectM.ofOp (load dialect ref)) (EffectM.ofOp (load dialect ref))).run state =
      (.ok (value, value), state,
        [.read ref.id kind value.toInt, .read ref.id kind value.toInt]) :=
  (load_load_diamond dialect state ref ref value value ready ready).1

end EDSL.Source.Objects.ReadOrder
