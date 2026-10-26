/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.Contracts
import EDSL.Source.Objects.ExpressionVC

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.StructuredVC
open StateSyntax Protocol LifecycleContracts

/-! Structural total-correctness obligations for the existing internal machine.

`vc` traverses control syntax, using the shared `ExpressionVC` traversal and
explicit object-store obligations. Its two continuations distinguish finishing
a chunk from returning out of all enclosing control. `Segment` soundness gives
actual finite runs with arbitrary caller continuations and earlier events.
Loop annotations are proof data only; erasing them changes no executable code.

Coverage is deliberately separate from path obligations: use `Code.Supported`
when transferring a segment to `start`. Admissions remain independent caller
input/resource predicates; generated obligations are separate proof premises.
This module establishes no native/GNU forward-progress or function-cleanup
claim. Soundness is one-way: no control-level weakestness/completeness theorem
or automated proof, invariant or rank synthesis is provided. Quantification
over a loop invariant may require strengthening it. Loop-free syntax needs
only constructor annotations; loops in `vc` require natural-number ranks.
-/

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {context : List ArithmeticType} {result : IntType}
local notation "Store" => State target parameters Environment
local notation "Configuration" => Config target parameters Environment context result

abbrev Assertion (target : Target) (parameters : List IntType) (Environment : Type) :=
  State target parameters Environment → List Event → Prop

/-- A chunk's normal exit resumes its caller; it is not machine fallthrough.
Return discards the complete caller continuation. -/
inductive Exit (target : Target) (result : IntType) where
  | next
  | returned (value : Value target result)

def endpoint (exit : Exit target result) (rest : List (Code target context result))
    (state : Store) (events : List Event) : Configuration :=
  match exit with
  | .next => ⟨rest, state, events, .running⟩
  | .returned value => ⟨[], state, events, .returned value⟩

def accepts (normal : Assertion target parameters Environment)
    (returned : Value target result → Assertion target parameters Environment) :
    Exit target result → Assertion target parameters Environment
  | .next => normal
  | .returned value => returned value

/-- One finite chunk execution, uniformly in the unevaluated caller stack.
The state and event fields are the actual ones, not projections or snapshots.
No stopped endpoint or exhausted observation bound counts as completion. -/
def Segment (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)
    (code : Code target context result) (normal : Assertion target parameters Environment)
    (returned : Value target result → Assertion target parameters Environment)
    (initial : Store) (earlier : List Event) : Prop :=
  ∃ steps exit final events, accepts normal returned exit final events ∧
    ∀ rest, run dialect policy bindings steps (startUnchecked code initial earlier rest) =
      endpoint exit rest final events

variable (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)

/-- The shared expression transformer, with the caller's complete history. -/
def expression {type : IntType} (value : RHS target context type)
    (post : Value target type → Assertion target parameters Environment) :
    Assertion target parameters Environment :=
  fun initial earlier => ExpressionVC.vcExpr policy bindings value
    (fun _ evaluated final events => post evaluated final (earlier ++ events)) initial

theorem expression_iff {type : IntType} (value : RHS target context type)
    (post : Value target type → Assertion target parameters Environment)
    (initial : Store) (earlier : List Event) :
    expression policy bindings value post initial earlier ↔
      ∃ evaluated final events,
        StateEval.evalExpr dialect policy bindings value initial = (.ok evaluated, final, events) ∧
        post evaluated final (earlier ++ events) :=
  ExpressionVC.vcExpr_iff dialect policy bindings value _ initial

include dialect in
theorem expression_mono {type : IntType} (value : RHS target context type)
    (first next : Value target type → Assertion target parameters Environment)
    (entails : ∀ evaluated final events, first evaluated final events → next evaluated final events)
    (initial : Store) (earlier : List Event) :
    expression policy bindings value first initial earlier →
      expression policy bindings value next initial earlier := by
  intro condition
  obtain ⟨evaluated, final, events, execution, member⟩ :=
    (expression_iff dialect policy bindings value first initial earlier).mp condition
  exact (expression_iff dialect policy bindings value next initial earlier).mpr
    ⟨evaluated, final, events, execution, entails _ _ _ member⟩

/-- Store obligations expose registry membership, owner/kind and write
authority. They do not assume the assignment's success or a source NoUB fact. -/
def write {kind : ArithmeticType} (reference : LValue kind)
    (value : Value target kind.asIntType) (post : Assertion target parameters Environment) :
    Assertion target parameters Environment := fun initial earlier =>
  ∃ previous permissions,
    initial.objects reference.id = some (liveObject kind initial.actor permissions previous) ∧
    permissions.writable = true ∧
    post (initial.putObject reference.id (liveObject kind initial.actor permissions (some value)))
      (earlier ++ [.write reference.id kind value.toInt])

theorem write_iff {kind : ArithmeticType} (reference : LValue kind)
    (value : Value target kind.asIntType) (post : Assertion target parameters Environment)
    (initial : Store) (earlier : List Event) :
    write reference value post initial earlier ↔
      WP (store reference value) (fun _ _ final events => post final (earlier ++ events)) initial := by
  exact (ObjectWP.wp_store reference value
    (fun _ _ final events => post final (earlier ++ events)) initial).symm

def assignment {kind : ArithmeticType} (index : Vars context kind)
    (value : RHS target context kind.asIntType)
    (post : Assertion target parameters Environment) : Assertion target parameters Environment :=
  expression policy bindings value (fun evaluated => write (bindings.get index) evaluated post)

theorem assignment_iff {kind : ArithmeticType} (index : Vars context kind)
    (value : RHS target context kind.asIntType) (post : Assertion target parameters Environment)
    (initial : Store) (earlier : List Event) :
    assignment policy bindings index value post initial earlier ↔
      WP (assign dialect policy bindings index value)
        (fun _ _ final events => post final (earlier ++ events)) initial := by
  unfold assignment expression assign
  rw [ExpressionVC.vcExpr_iff_wp dialect, wp_bind]
  apply wp_congr
  intro original evaluated middle reads
  simpa only [List.append_assoc] using
    (write_iff (bindings.get index) evaluated post middle (earlier ++ reads))

/-! Exact one-transition laws. These retain arbitrary successful operation
state, arbitrary prior events and the full caller stack. Clients can use the
structural rules below without unfolding `tick`, `perform` or `Op.bind`. -/

theorem step_skip (rest : List (Code target context result)) (state : Store) (events : List Event) :
    tick dialect policy bindings (startUnchecked .skip state events rest) =
      endpoint .next rest state events := rfl

theorem step_sequence (first next : Code target context result)
    (rest : List (Code target context result)) (state : Store) (events : List Event) :
    tick dialect policy bindings (startUnchecked (.seq first next) state events rest) =
      startUnchecked first state events (next :: rest) := rfl

theorem step_assignment {kind : ArithmeticType} (index : Vars context kind)
    (value : RHS target context kind.asIntType) (rest : List (Code target context result))
    (initial final : Store) (earlier events : List Event)
    (execution : assign dialect policy bindings index value initial = (.ok (), final, events)) :
    tick dialect policy bindings (startUnchecked (.assign index value) initial earlier rest) =
      endpoint .next rest final (earlier ++ events) := by
  simp only [tick, startUnchecked, perform, execution, endpoint]

theorem step_branch (condition : RHS target context (.small .boolean))
    (yes no : Code target context result) (rest : List (Code target context result))
    (initial final : Store) (earlier events : List Event)
    (value : Value target (.small .boolean))
    (execution : StateEval.evalExpr dialect policy bindings condition initial =
      (.ok value, final, events)) :
    tick dialect policy bindings (startUnchecked (.branch condition yes no) initial earlier rest) =
      startUnchecked (if value.toInt = 0 then no else yes) final (earlier ++ events) rest := by
  simp only [tick, startUnchecked, perform, execution]

theorem step_loop (condition : RHS target context (.small .boolean))
    (body : Code target context result) (rest : List (Code target context result))
    (initial final : Store) (earlier events : List Event)
    (value : Value target (.small .boolean))
    (execution : StateEval.evalExpr dialect policy bindings condition initial =
      (.ok value, final, events)) :
    tick dialect policy bindings (startUnchecked (.loop condition body) initial earlier rest) =
      (⟨if value.toInt = 0 then rest else body :: .loop condition body :: rest,
        final, earlier ++ events, .running⟩ : Configuration) := by
  simp only [tick, startUnchecked, perform, execution]

theorem step_return (value : RHS target context result)
    (rest : List (Code target context result)) (initial final : Store) (earlier events : List Event)
    (evaluated : Value target result)
    (execution : StateEval.evalExpr dialect policy bindings value initial =
      (.ok evaluated, final, events)) :
    tick dialect policy bindings (startUnchecked (.ret value) initial earlier rest) =
      endpoint (.returned evaluated) rest final (earlier ++ events) := by
  simp only [tick, startUnchecked, perform, execution, endpoint]

namespace Segment

variable {dialect policy bindings}
variable {normal : Assertion target parameters Environment}
variable {returned : Value target result → Assertion target parameters Environment}
variable {initial : State target parameters Environment} {earlier : List Event}

theorem mono {code : Code target context result}
    (progress : Segment dialect policy bindings code normal returned initial earlier)
    {nextNormal : Assertion target parameters Environment}
    {nextReturned : Value target result → Assertion target parameters Environment}
    (onNext : ∀ final events, normal final events → nextNormal final events)
    (onReturn : ∀ value final events, returned value final events → nextReturned value final events) :
    Segment dialect policy bindings code nextNormal nextReturned initial earlier := by
  obtain ⟨steps, exit, final, events, member, execution⟩ := progress
  refine ⟨steps, exit, final, events, ?_, execution⟩
  cases exit with
  | next => exact onNext _ _ member
  | returned value => exact onReturn _ _ _ member

theorem skip (member : normal initial earlier) :
    Segment dialect policy bindings (.skip : Code target context result) normal returned initial earlier :=
  ⟨1, .next, initial, earlier, member,
    fun rest => step_skip dialect policy bindings rest initial earlier⟩

theorem assign {kind : ArithmeticType} (index : Vars context kind)
    (value : RHS target context kind.asIntType)
    (condition : assignment policy bindings index value normal initial earlier) :
    Segment dialect policy bindings (.assign index value) normal returned initial earlier := by
  obtain ⟨ignored, final, events, execution, member⟩ :=
    (wp_iff _ _ _).mp ((assignment_iff dialect policy bindings index value normal initial earlier).mp condition)
  cases ignored
  exact ⟨1, .next, final, earlier ++ events, member,
    fun rest => step_assignment dialect policy bindings index value rest initial final earlier events execution⟩

theorem ret (value : RHS target context result)
    (condition : expression policy bindings value returned initial earlier) :
    Segment dialect policy bindings (.ret value) normal returned initial earlier := by
  obtain ⟨evaluated, final, events, execution, member⟩ :=
    (expression_iff dialect policy bindings value returned initial earlier).mp condition
  exact ⟨1, .returned evaluated, final, earlier ++ events, member,
    fun rest => step_return dialect policy bindings value rest initial final earlier events evaluated execution⟩

/-- The second chunk is proved only at a normal exit of the first. Early
return propagates unchanged, including its state and complete event history. -/
theorem seq (first next : Code target context result)
    (progress : Segment dialect policy bindings first
      (fun state events => Segment dialect policy bindings next normal returned state events)
      returned initial earlier) :
    Segment dialect policy bindings (.seq first next) normal returned initial earlier := by
  obtain ⟨firstSteps, exit, middle, events, member, firstRun⟩ := progress
  cases exit with
  | next =>
      obtain ⟨nextSteps, exit, final, allEvents, resultPost, nextRun⟩ := member
      refine ⟨firstSteps + nextSteps + 1, exit, final, allEvents, resultPost, ?_⟩
      intro rest
      rw [run_succ_front, step_sequence, run_add, firstRun]
      exact nextRun rest
  | returned value =>
      refine ⟨firstSteps + 1, .returned value, middle, events, member, ?_⟩
      intro rest
      rw [run_succ_front, step_sequence, firstRun]
      rfl

theorem branch (condition : RHS target context (.small .boolean))
    (yes no : Code target context result)
    (progress : expression policy bindings condition
      (fun value state events => Segment dialect policy bindings
        (if value.toInt = 0 then no else yes) normal returned state events) initial earlier) :
    Segment dialect policy bindings (.branch condition yes no) normal returned initial earlier := by
  obtain ⟨value, middle, reads, execution, member⟩ :=
    (expression_iff dialect policy bindings condition _ initial earlier).mp progress
  obtain ⟨steps, exit, final, events, resultPost, selectedRun⟩ := member
  refine ⟨steps + 1, exit, final, events, resultPost, ?_⟩
  intro rest
  rw [run_succ_front, step_branch dialect policy bindings condition yes no rest initial middle
    earlier reads value execution]
  exact selectedRun rest

/-- A loop-header invariant plus a well-founded rank and *actual finite body
progress*. The body either returns immediately or reaches another header with
the invariant and a strictly smaller rank. A conditional decrease theorem
without the `Segment` witness cannot discharge this premise. Guard effects
are included before the body; the rank compares complete header observations.
-/
theorem loop {Rank : Type} (condition : RHS target context (.small .boolean))
    (body : Code target context result) (invariant : Assertion target parameters Environment)
    (rank : Store → List Event → Rank) (less : Rank → Rank → Prop) (wellFounded : WellFounded less)
    (progress : ∀ state history, invariant state history →
      expression policy bindings condition (fun value middle accepted =>
        if value.toInt = 0 then normal middle accepted else
          Segment dialect policy bindings body
            (fun final events => invariant final events ∧ less (rank final events) (rank state history))
            returned middle accepted) state history)
    (member : invariant initial earlier) :
    Segment dialect policy bindings (.loop condition body) normal returned initial earlier := by
  have completes : ∀ bound, ∀ state history, rank state history = bound → invariant state history →
      Segment dialect policy bindings (.loop condition body) normal returned state history := by
    intro bound
    induction bound using wellFounded.induction with
    | h bound smaller =>
        intro state history ranked retained
        obtain ⟨value, middle, reads, guardRun, bodyProgress⟩ :=
          (expression_iff dialect policy bindings condition _ state history).mp
            (progress state history retained)
        by_cases zero : value.toInt = 0
        · have resultPost : normal middle (history ++ reads) := by
            simpa only [zero, ↓reduceIte] using bodyProgress
          refine ⟨1, .next, middle, history ++ reads, resultPost, ?_⟩
          intro rest
          simpa only [run, endpoint, zero, ↓reduceIte] using
            step_loop dialect policy bindings condition body rest state middle history reads value guardRun
        · have completedBody : Segment dialect policy bindings body
              (fun final events => invariant final events ∧ less (rank final events) (rank state history))
              returned middle (history ++ reads) := by
            simpa only [zero, ↓reduceIte] using bodyProgress
          obtain ⟨bodySteps, exit, nextState, events, bodyPost, bodyRun⟩ := completedBody
          cases exit with
          | next =>
              have decreased : less (rank nextState events) bound := by
                simpa only [ranked] using bodyPost.2
              obtain ⟨tailSteps, exit, final, allEvents, resultPost, tailRun⟩ :=
                smaller _ decreased nextState events rfl bodyPost.1
              refine ⟨bodySteps + tailSteps + 1, exit, final, allEvents, resultPost, ?_⟩
              intro rest
              rw [run_succ_front, step_loop dialect policy bindings condition body rest state middle
                history reads value guardRun]
              simp only [zero, ↓reduceIte]
              rw [run_add]
              change run dialect policy bindings tailSteps
                (run dialect policy bindings bodySteps
                  (startUnchecked body middle (history ++ reads) (.loop condition body :: rest))) = _
              rw [bodyRun]
              exact tailRun rest
          | returned value =>
              refine ⟨bodySteps + 1, .returned value, nextState, events, bodyPost, ?_⟩
              intro rest
              rw [run_succ_front, step_loop dialect policy bindings condition body rest state middle
                history reads _ guardRun]
              simp only [zero, ↓reduceIte]
              exact bodyRun (.loop condition body :: rest)
  exact completes _ initial earlier rfl member

/-- Resume arbitrary caller control from a normal exit, or accept an early
return without running any caller instruction. Both segments are actual runs. -/
theorem resume {code : Code target context result}
    (progress : Segment dialect policy bindings code normal returned initial earlier)
    (rest : List (Code target context result)) (post : Configuration → Prop)
    (onNext : ∀ state events, normal state events → ∃ final,
      Reaches dialect policy bindings (endpoint .next rest state events) final ∧ post final)
    (onReturn : ∀ value state events, returned value state events →
      post (endpoint (.returned value) rest state events)) :
    ∃ final, Reaches dialect policy bindings (startUnchecked code initial earlier rest) final ∧ post final := by
  obtain ⟨steps, exit, state, events, member, execution⟩ := progress
  have earlierReach : Reaches dialect policy bindings (startUnchecked code initial earlier rest)
      (endpoint exit rest state events) := ⟨steps, execution rest⟩
  cases exit with
  | next =>
      obtain ⟨final, tail, resultPost⟩ := onNext state events member
      exact ⟨final, Reaches.trans dialect policy bindings _ _ _ earlierReach tail, resultPost⟩
  | returned value => exact ⟨_, earlierReach, onReturn value state events member⟩

/-- Closing the caller stack requires an additional fallthrough transition at
a normal exit. Fallthrough carries no invented return value. -/
theorem close {code : Code target context result}
    (progress : Segment dialect policy bindings code normal returned initial earlier) :
    ∃ steps final, run dialect policy bindings steps (startUnchecked code initial earlier) = final ∧
      match final.status with
      | .fellThrough => normal final.state final.events
      | .returned value => returned value final.state final.events
      | _ => False := by
  obtain ⟨steps, exit, state, events, member, execution⟩ := progress
  cases exit with
  | next =>
      refine ⟨steps + 1, ⟨[], state, events, .fellThrough⟩, ?_, member⟩
      rw [run_succ, execution []]
      rfl
  | returned value =>
      exact ⟨steps, endpoint (.returned value) [] state events, execution [], member⟩

/-- Finite completion excludes divergence even when its only possible exit is
normal chunk completion. This also applies to a proposed loop-body segment. -/
theorem not_diverges {code : Code target context result}
    (progress : Segment dialect policy bindings code normal returned initial earlier) :
    ¬ Diverges dialect policy bindings (startUnchecked code initial earlier) := by
  intro divergent
  obtain ⟨steps, final, execution, resultPost⟩ := progress.close
  have running : final.status = .running := by
    simpa only [execution] using divergent steps
  simp only [running] at resultPost

end Segment

/-- Structural annotations indexed by the *existing* `Code`. Only loops add
logical data. There is no second executable control or expression language.
Natural ranks suffice for `vc`; `Segment.loop` also accepts arbitrary
well-founded relations. Annotation and invariant synthesis are not provided. -/
inductive Annotation : Code target context result → Type where
  | skip : Annotation .skip
  | assign {kind : ArithmeticType} {index : Vars context kind}
      {value : RHS target context kind.asIntType} : Annotation (.assign index value)
  | seq {first next : Code target context result}
      (before : Annotation first) (after : Annotation next) : Annotation (.seq first next)
  | branch {condition : RHS target context (.small .boolean)} {yes no : Code target context result}
      (positive : Annotation yes) (negative : Annotation no) : Annotation (.branch condition yes no)
  | loop {condition : RHS target context (.small .boolean)} {body : Code target context result}
      (invariant : Assertion target parameters Environment)
      (rank : State target parameters Environment → List Event → Nat)
      (bodyAnnotation : Annotation body) : Annotation (.loop condition body)
  | ret {value : RHS target context result} : Annotation (.ret value)
  | unsupported {feature : UnsupportedFeature} : Annotation (.unsupported feature)

/-- Backward structural formula generation. Skip exposes the normal post;
assignment computes RHS and write obligations; sequence substitutes the next
formula only into normal exits; branching demands its selected arm. Loops
generate invariant entry, guard, finite body, preservation and rank obligations.
Unsupported paths generate `False`. No clause invokes `run` or `Segment`.
-/
def vc (policy : IntegerConversionPolicy) (bindings : Env context) {code : Code target context result}
    (annotation : Annotation (parameters := parameters) (Environment := Environment) code)
    (normal : Assertion target parameters Environment)
    (returned : Value target result → Assertion target parameters Environment) :
    Assertion target parameters Environment :=
  match annotation with
  | .skip => normal
  | .assign (index := index) (value := value) => assignment policy bindings index value normal
  | .seq before after => vc policy bindings before (vc policy bindings after normal returned) returned
  | .branch (condition := condition) positive negative =>
      expression policy bindings condition (fun value state events =>
        if value.toInt = 0 then vc policy bindings negative normal returned state events
        else vc policy bindings positive normal returned state events)
  | .loop (condition := condition) invariant rank bodyAnnotation => fun initial earlier =>
      invariant initial earlier ∧ ∀ state history, invariant state history →
        expression policy bindings condition (fun value middle accepted =>
          if value.toInt = 0 then normal middle accepted else
            vc policy bindings bodyAnnotation
              (fun final events => invariant final events ∧ rank final events < rank state history)
              returned middle accepted) state history
  | .ret (value := value) => expression policy bindings value returned
  | .unsupported => fun _ _ => False

/-- Checked soundness: generated obligations discharge actual finite machine
segments, uniformly over every caller continuation and its prior history. -/
theorem vc_sound {code : Code target context result}
    (annotation : Annotation (parameters := parameters) (Environment := Environment) code)
    (normal : Assertion target parameters Environment)
    (returned : Value target result → Assertion target parameters Environment)
    (initial : Store) (earlier : List Event)
    (condition : vc policy bindings annotation normal returned initial earlier) :
    Segment dialect policy bindings code normal returned initial earlier := by
  induction annotation generalizing normal returned initial earlier with
  | skip => exact Segment.skip condition
  | assign => exact Segment.assign _ _ condition
  | seq before after beforeIH afterIH =>
      apply Segment.seq
      exact (beforeIH _ _ _ _ condition).mono
        (fun state events member => afterIH normal returned state events member)
        (fun _ _ _ member => member)
  | branch positive negative positiveIH negativeIH =>
      apply Segment.branch
      apply expression_mono dialect policy bindings _ _ _ ?_ initial earlier condition
      intro value state events member
      by_cases zero : value.toInt = 0
      · simpa only [zero, ↓reduceIte] using
          negativeIH normal returned state events (by simpa only [vc, zero, ↓reduceIte] using member)
      · simpa only [zero, ↓reduceIte] using
          positiveIH normal returned state events (by simpa only [vc, zero, ↓reduceIte] using member)
  | loop invariant rank bodyAnnotation bodyIH =>
      apply Segment.loop _ _ invariant rank Nat.lt Nat.lt_wfRel.wf ?_ condition.1
      intro state history member
      apply expression_mono dialect policy bindings _ _ _ ?_ state history (condition.2 state history member)
      intro value middle accepted bodyCondition
      by_cases zero : value.toInt = 0
      · simpa only [zero, ↓reduceIte] using bodyCondition
      · simp only [zero, ↓reduceIte] at bodyCondition ⊢
        exact bodyIH _ returned middle accepted bodyCondition
  | ret => exact Segment.ret _ condition
  | unsupported => exact condition.elim

/-- Whole-code support is a separate static premise, including unreachable
arms and tails. The admission is supplied independently of these obligations.
The impossible normal post requires a genuine value return, not fallthrough. -/
theorem verifies_of_vc {code : Code target context result}
    (annotation : Annotation (parameters := parameters) (Environment := Environment) code)
    (supported : code.Supported) (admitted : Store → Prop)
    (post : Protocol.Post target parameters Environment (Value target result))
    (obligations : ∀ initial, admitted initial → vc policy bindings annotation
      (fun _ _ => False) (fun value final events => post initial value final events) initial []) :
    Verifies dialect policy bindings code admitted post := by
  intro initial permitted
  obtain ⟨steps, exit, final, events, member, execution⟩ :=
    vc_sound dialect policy bindings annotation _ _ initial [] (obligations initial permitted)
  cases exit with
  | next => exact member.elim
  | returned value =>
      have actual := execution []
      rw [← start_supported code initial supported] at actual
      exact ⟨steps, value, by rw [actual]; rfl, by simpa only [actual, endpoint, accepts] using member⟩

end EDSL.Source.Objects.Control.StructuredVC
