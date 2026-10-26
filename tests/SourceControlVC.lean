/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.StructuredVC

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.StructuredVC.Validation
open StateSyntax LifecycleContracts

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {context : List ArithmeticType} {result : IntType}
variable (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)

/- A returning arm must bypass a divergent alternative, the enclosing loop,
and a divergent sequence tail. A zero rank is intentional: early return must
not incur a spurious decrease obligation. The expected return and unmodified
caller world/history specify behavior independently of the generated formula. -/
private def spin (truth : Value target (.small .boolean)) : Code target context result :=
  .loop (.literal truth) .skip

private def spinAnnotation (truth : Value target (.small .boolean)) :
    Annotation (parameters := parameters) (Environment := Environment)
      (spin (context := context) (result := result) truth) :=
  .loop (fun _ _ => True) (fun _ _ => 0) .skip

private def early (truth : Value target (.small .boolean)) (value : Value target result) :
    Code target context result :=
  .seq (.loop (.literal truth)
    (.branch (.literal truth) (.ret (.literal value)) (spin truth))) (spin truth)

private def earlyAnnotation (truth : Value target (.small .boolean)) (value : Value target result)
    (original : State target parameters Environment) (earlier : List Event) : Annotation
      (parameters := parameters) (Environment := Environment) (early (context := context) truth value) :=
  .seq (.loop (fun state events => state = original ∧ events = earlier) (fun _ _ => 0)
    (.branch .ret (spinAnnotation truth))) (spinAnnotation truth)

theorem early_return_keeps_caller (truth : Value target (.small .boolean))
    (nonzero : truth.toInt ≠ 0) (value : Value target result)
    (original : State target parameters Environment) (earlier : List Event)
    (rest : List (Code target context result)) :
    ∃ steps, run dialect policy bindings steps (startUnchecked (early truth value) original earlier rest) =
      ⟨[], original, earlier, .returned value⟩ := by
  have formula : vc policy bindings (earlyAnnotation truth value original earlier)
      (fun _ _ => False) (fun returned final events =>
        returned = value ∧ final = original ∧ events = earlier) original earlier := by
    change (original = original ∧ earlier = earlier) ∧ _
    refine ⟨⟨rfl, rfl⟩, ?_⟩
    intro state events member
    rcases member with ⟨rfl, rfl⟩
    simp only [vc, expression, ExpressionVC.vcExpr_literal, nonzero, ↓reduceIte, List.append_nil]
    trivial
  obtain ⟨steps, exit, final, events, member, execution⟩ :=
    vc_sound dialect policy bindings _ _ _ original earlier formula
  cases exit with
  | next => exact member.elim
  | returned actual =>
      rcases member with ⟨rfl, rfl, rfl⟩
      exact ⟨steps, execution rest⟩

/- Copying through two actual object loads and a store checks that the RHS
reads the source, the return reads the updated destination, write permission
is sufficient even with uninitialized old contents, and all three events
remain ordered after arbitrary prior history. Aliasing is allowed. -/
private abbrev CopyContext : List ArithmeticType := [.uint, .uint]
private abbrev destination : Vars CopyContext .uint := .here
private abbrev source : Vars CopyContext .uint := .there .here
private def copyCode : Code target CopyContext .uint :=
  .seq (.assign destination (.param source)) (.ret (.param destination))

theorem copy_reads_updated_destination (destinationRef sourceRef : LValue .uint)
    (original : State target parameters Environment) (earlier : List Event)
    (value : Value target .uint) (previous : Option (Value target .uint))
    (permissions : Permissions) (readable : permissions.readable = true)
    (writable : permissions.writable = true)
    (destinationReady : original.objects destinationRef.id =
      some (liveObject .uint original.actor permissions previous))
    (sourceReady : CanLoad original sourceRef value)
    (rest : List (Code target CopyContext .uint)) :
    ∃ steps, run dialect policy (.cons destinationRef (.cons sourceRef .nil)) steps
      (startUnchecked copyCode original earlier rest) =
      ⟨[], original.putObject destinationRef.id (liveObject .uint original.actor permissions (some value)),
        earlier ++ [.read sourceRef.id .uint value.toInt, .write destinationRef.id .uint value.toInt,
          .read destinationRef.id .uint value.toInt], .returned value⟩ := by
  let env : Env CopyContext := .cons destinationRef (.cons sourceRef .nil)
  let updated := original.putObject destinationRef.id (liveObject .uint original.actor permissions (some value))
  let trace := earlier ++ [.read sourceRef.id .uint value.toInt, .write destinationRef.id .uint value.toInt,
    .read destinationRef.id .uint value.toInt]
  let annotation : Annotation (parameters := parameters) (Environment := Environment)
    (copyCode (target := target)) := .seq .assign .ret
  have formula : vc policy env annotation (fun _ _ => False)
      (fun returned final events => returned = value ∧ final = updated ∧ events = trace) original earlier := by
    change expression policy env (.param source) _ original earlier
    unfold expression
    rw [ExpressionVC.vcExpr_var]
    refine ⟨value, sourceReady, ?_⟩
    change write destinationRef value _ original (earlier ++ [.read sourceRef.id .uint value.toInt])
    refine ⟨previous, permissions, destinationReady, writable, ?_⟩
    change expression policy env (.param destination) _ updated _
    unfold expression
    rw [ExpressionVC.vcExpr_var]
    refine ⟨value, ⟨permissions, State.putObject_same original destinationRef.id _, readable⟩, ?_⟩
    exact ⟨rfl, rfl, by simp only [trace, List.append_assoc, List.cons_append, List.nil_append]; rfl⟩
  obtain ⟨steps, exit, final, events, member, execution⟩ :=
    vc_sound dialect policy env annotation _ _ original earlier formula
  cases exit with
  | next => exact member.elim
  | returned actual =>
      rcases member with ⟨rfl, rfl, rfl⟩
      exact ⟨steps, execution rest⟩

/- Coverage includes unreachable tails even though the structural path formula
correctly ignores them following an early return. No `start` certificate may
be obtained from that path formula without a separate coverage proof. -/
theorem unreachable_unsupported_is_separate (feature : UnsupportedFeature)
    (value : Value target result) (original : State target parameters Environment) :
    let code : Code target context result := .seq (.ret (.literal value)) (.unsupported feature)
    vc policy bindings (Annotation.seq Annotation.ret Annotation.unsupported :
      Annotation (parameters := parameters) (Environment := Environment) code)
      (fun _ _ => False) (fun returned _ _ => returned = value) original [] ∧ ¬ code.Supported := by
  exact ⟨by simp only [vc, expression, ExpressionVC.vcExpr_literal], by simp⟩

/- The existing machine's divergence theorem is an independent oracle: no
choice of loop annotations can turn a spinning body into a finite segment. -/
include dialect in
theorem divergent_body_rejected (truth : Value target (.small .boolean)) (nonzero : truth.toInt ≠ 0)
    (annotation : Annotation (parameters := parameters) (Environment := Environment)
      (spin (context := context) (result := result) truth))
    (original : State target parameters Environment) :
    ¬ vc policy bindings annotation (fun _ _ => True) (fun _ _ _ => True) original [] := by
  intro formula
  have segment := vc_sound dialect policy bindings annotation _ _ original [] formula
  apply segment.not_diverges
  have divergent := loop_skip_diverges (result := result) dialect policy bindings truth nonzero original
  rw [start_supported _ _ (by trivial)] at divergent
  exact divergent

/- A normally completed chunk has an actual fallthrough endpoint. Its accepted
normal post cannot provide the return required by `Verifies`. -/
theorem fallthrough_cannot_certify_return (original : State target parameters Environment)
    (post : Protocol.Post target parameters Environment (Value target result)) :
    ¬ Verifies dialect policy bindings (.skip : Code target context result) (fun _ => True) post := by
  intro verified
  have segment : Segment dialect policy bindings (.skip : Code target context result)
      (fun _ _ => True) (fun _ _ _ => False) original [] := Segment.skip True.intro
  obtain ⟨normalSteps, final, actual, normalPost⟩ := segment.close
  have falls : final.status = .fellThrough := by
    cases status : final.status <;> simp_all
  obtain ⟨returnSteps, value, returned, _⟩ := verified original True.intro
  rw [start_supported _ _ (by trivial)] at returned
  have same := terminal_endpoint_unique dialect policy bindings
    (startUnchecked (.skip : Code target context result) original)
    normalSteps returnSteps (by simp only [Terminal, actual, falls])
    (by simp only [Terminal, returned])
  have impossible := congrArg Config.status same
  rw [actual, falls, returned] at impossible
  cases impossible

end EDSL.Source.Objects.Control.StructuredVC.Validation
