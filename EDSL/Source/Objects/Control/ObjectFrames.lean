/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.Frames
import EDSL.Source.Objects.Control.StructuredVC
import EDSL.Source.Objects.LifecycleContracts
import EDSL.Source.Objects.BlockContracts

set_option autoImplicit false
namespace EDSL.Source.Objects.Control
open StateSyntax

/-! Frames for the current ordinary-object control fragment. No allocation,
lifetime-ending, calls or interference occur inside Code. These laws do not
extend to future effects without their own checked preservation rules. -/

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {context : List ArithmeticType} {result : IntType} {α β : Type}

/-- A body can change the values of its bound objects. Existing object metadata
and every object outside those bindings are preserved. Registry well-formedness
is preserved when it held before the body. -/
structure ObjectFrame (bindings : Env context)
    (before after : State target parameters Environment) : Prop where
  world : WorldFrame before after
  metadata : ∀ id old, before.objects id = some old →
    ∃ current, after.objects id = some current ∧ SameAccessMetadata old current
  outside : ∀ id, id ∉ bindings.ids → after.objects id = before.objects id
  wellFormed : before.WellFormed → after.WellFormed

theorem ObjectFrame.refl (bindings : Env context) (state : State target parameters Environment) :
    ObjectFrame bindings state state :=
  ⟨WorldFrame.refl state, fun _ old registered => ⟨old, registered, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ _ => rfl, fun metadata => metadata⟩

theorem ObjectFrame.trans {bindings : Env context}
    {first middle final : State target parameters Environment}
    (before : ObjectFrame bindings first middle) (after : ObjectFrame bindings middle final) :
    ObjectFrame bindings first final := by
  refine ⟨before.world.trans after.world, ?_, ?_, fun wellFormed => after.wellFormed (before.wellFormed wellFormed)⟩
  · intro id old registered
    obtain ⟨intermediate, present, firstMeta⟩ := before.metadata id old registered
    obtain ⟨current, finalPresent, secondMeta⟩ := after.metadata id intermediate present
    exact ⟨current, finalPresent, secondMeta.1.trans firstMeta.1,
      secondMeta.2.1.trans firstMeta.2.1, secondMeta.2.2.1.trans firstMeta.2.2.1,
      secondMeta.2.2.2.1.trans firstMeta.2.2.2.1, secondMeta.2.2.2.2.trans firstMeta.2.2.2.2⟩
  · intro id absent
    exact (after.outside id absent).trans (before.outside id absent)

private def PreservesObjects (bindings : Env context)
    (operation : Op target parameters Environment α) : Prop :=
  ∀ state, ObjectFrame bindings state (operation state).2.1

private theorem preservesObjects_bind (bindings : Env context)
    (first : Op target parameters Environment α) (next : α → Op target parameters Environment β)
    (firstFrame : PreservesObjects bindings first) (nextFrame : ∀ value, PreservesObjects bindings (next value)) :
    PreservesObjects bindings (Op.bind first next) := by
  intro state
  rcases execution : first state with ⟨outcome, middle, observations⟩
  have earlier : ObjectFrame bindings state middle := by simpa only [execution] using firstFrame state
  cases outcome with
  | error reason => simpa only [Op.bind, execution] using earlier
  | ok value =>
      simp only [Op.bind, execution]
      exact earlier.trans (nextFrame value middle)

private theorem expression_objects (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) {type : IntType} (expression : RHS target context type) :
    PreservesObjects (parameters := parameters) (Environment := Environment)
      bindings (StateEval.evalExpr dialect policy bindings expression) := by
  intro state
  rw [StateEval.evalExpr_preserves_state]
  exact ObjectFrame.refl bindings state

private theorem store_objects {kind : ArithmeticType} (bindings : Env context)
    (ref : LValue kind) (value : Value target kind.asIntType) (member : ref.id ∈ bindings.ids) :
    PreservesObjects (parameters := parameters) (Environment := Environment) bindings (store ref value) := by
  intro state
  refine ⟨store_worldFrame ref value state, store_preserves_metadata state ref value, ?_,
    store_preserves_wellFormed state ref value⟩
  intro id outside
  apply (store_preserves_frame state ref value).2.2.2.2.2
  intro same
  apply outside
  simpa only [same] using member

private theorem assign_objects {kind : ArithmeticType} (dialect : Dialect)
    (policy : IntegerConversionPolicy) (bindings : Env context) (index : Vars context kind)
    (value : RHS target context kind.asIntType) :
    PreservesObjects (parameters := parameters) (Environment := Environment)
      bindings (assign dialect policy bindings index value) :=
  preservesObjects_bind bindings _ _ (expression_objects dialect policy bindings value)
    (fun evaluated => store_objects bindings (bindings.get index) evaluated (Env.get_id_mem bindings index))

private theorem perform_objects (bindings : Env context)
    (operation : Op target parameters Environment α)
    (next : α → Config target parameters Environment context result → Config target parameters Environment context result)
    (operationFrame : PreservesObjects bindings operation)
    (nextFrame : ∀ value config, ObjectFrame bindings config.state (next value config).state)
    (initial : Config target parameters Environment context result) :
    ObjectFrame bindings initial.state (perform operation next initial).state := by
  rcases execution : operation initial.state with ⟨outcome, updated, observations⟩
  have earlier : ObjectFrame bindings initial.state updated := by simpa only [execution] using operationFrame initial.state
  cases outcome with
  | error reason => simpa only [perform, execution] using earlier
  | ok value =>
      simp only [perform, execution]
      exact earlier.trans (nextFrame value {initial with state := updated, events := initial.events ++ observations})

/-- Every tick preserves metadata and the registry outside the bound identities,
including actual failure prefixes; no safety/termination assumption is used. -/
theorem tick_objectFrame (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) (initial : Config target parameters Environment context result) :
    ObjectFrame bindings initial.state (tick dialect policy bindings initial).state := by
  cases initial with
  | mk control state events status =>
      cases status with
      | returned value => exact ObjectFrame.refl bindings state
      | fellThrough => exact ObjectFrame.refl bindings state
      | stopped reason => exact ObjectFrame.refl bindings state
      | running =>
          cases control with
          | nil => exact ObjectFrame.refl bindings state
          | cons code rest =>
              cases code with
              | skip => exact ObjectFrame.refl bindings state
              | seq first next => exact ObjectFrame.refl bindings state
              | unsupported feature => exact ObjectFrame.refl bindings state
              | assign index value =>
                  apply perform_objects bindings _ _ (assign_objects dialect policy bindings index value)
                  intro evaluated config
                  exact ObjectFrame.refl bindings config.state
              | branch condition yes no =>
                  apply perform_objects bindings _ _ (expression_objects dialect policy bindings condition)
                  intro evaluated config
                  exact ObjectFrame.refl bindings config.state
              | loop condition body =>
                  apply perform_objects bindings _ _ (expression_objects dialect policy bindings condition)
                  intro evaluated config
                  exact ObjectFrame.refl bindings config.state
              | ret value =>
                  apply perform_objects bindings _ _ (expression_objects dialect policy bindings value)
                  intro evaluated config
                  exact ObjectFrame.refl bindings config.state

theorem run_objectFrame (dialect : Dialect) (policy : IntegerConversionPolicy)
    (bindings : Env context) (steps : Nat) (initial : Config target parameters Environment context result) :
    ObjectFrame bindings initial.state (run dialect policy bindings steps initial).state := by
  induction steps with
  | zero => exact ObjectFrame.refl bindings initial.state
  | succ steps ih => exact ih.trans (tick_objectFrame dialect policy bindings _)


/-- Value writes cannot revoke the ability to end a previously live owned
object. No assumption about the object's old or new initialized value is used. -/
theorem ObjectFrame.canEnd {bindings : Env context}
    {before after : State target parameters Environment} (frame : ObjectFrame bindings before after)
    {kind : ArithmeticType} (ref : LValue kind) (ready : LifecycleContracts.CanEnd ref before) :
    LifecycleContracts.CanEnd ref after := by
  obtain ⟨old, registered, kindEq, lifeEq, reachedEq, ownerEq⟩ := ready
  obtain ⟨current, found, same⟩ := frame.metadata ref.id old registered
  exact ⟨current, found, same.1.trans kindEq, same.2.1.trans lifeEq,
    same.2.2.1.trans reachedEq, same.2.2.2.1.trans (ownerEq.trans frame.world.actor.symm)⟩

/-- Actual normal-cleanup admissions survive every ordinary body prefix, even
when that body's values change. Plan uniqueness/disjointness remain separate. -/
theorem ObjectFrame.liveBindings {bindings : Env context}
    {before after : State target parameters Environment} (frame : ObjectFrame bindings before after)
    {kinds : List ArithmeticType} (plan : Env kinds)
    (live : BlockContracts.LiveBindings before plan) : BlockContracts.LiveBindings after plan := by
  induction plan with
  | nil => trivial
  | cons ref tail ih => exact ⟨frame.canEnd ref live.1, ih live.2⟩

/-- Add the generic frame to an actual compositional segment. Program proofs
retain their independent mathematical posts without reproving metadata/frame
invariants at every branch or loop iteration. -/
theorem StructuredVC.Segment.with_objectFrame
    (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)
    {code : Code target context result}
    {normal : StructuredVC.Assertion target parameters Environment}
    {returned : Value target result → StructuredVC.Assertion target parameters Environment}
    {initial : State target parameters Environment} {earlier : List Event}
    (segment : StructuredVC.Segment dialect policy bindings code normal returned initial earlier) :
    StructuredVC.Segment dialect policy bindings code
      (fun final events => normal final events ∧ ObjectFrame bindings initial final)
      (fun value final events => returned value final events ∧ ObjectFrame bindings initial final)
      initial earlier := by
  obtain ⟨steps, exit, final, events, member, execution⟩ := segment
  have frame := run_objectFrame dialect policy bindings steps (startUnchecked code initial earlier)
  rw [execution []] at frame
  refine ⟨steps, exit, final, events, ?_, execution⟩
  cases exit <;> exact ⟨member, frame⟩

end EDSL.Source.Objects.Control
