/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.StructuredVC

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.StructuredVC
open StateSyntax

/-! Proof annotations and consequence rules for reusable control verification.
Hints are untrusted data: all generated obligations still require checked proofs.
They never change executable code or justify source-standard loop progress. -/

structure LoopHint (target : Target) (parameters : List IntType) (Environment : Type) where
  invariant : Assertion target parameters Environment
  rank : State target parameters Environment → List Event → Nat

/-- Annotate the control tree from explicit loop hints. This constructs only
proof data; it neither synthesizes a valid invariant nor discharges any VC. -/
def Annotation.ofLoopHints {target : Target} {parameters : List IntType} {Environment : Type}
    {context : List ArithmeticType} {result : IntType}
    (hints : RHS target context (.small .boolean) → Code target context result →
      LoopHint target parameters Environment) :
    (code : Code target context result) → Annotation (parameters := parameters) (Environment := Environment) code
  | .skip => .skip
  | .assign _ _ => .assign
  | .seq first next => .seq (ofLoopHints hints first) (ofLoopHints hints next)
  | .branch _ yes no => .branch (ofLoopHints hints yes) (ofLoopHints hints no)
  | .loop condition body =>
      .loop (hints condition body).invariant (hints condition body).rank (ofLoopHints hints body)
  | .ret _ => .ret
  | .unsupported _ => .unsupported

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {context : List ArithmeticType} {result : IntType}
variable (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)
include dialect

/-- A weaker required post cannot create a new store obligation. Current
registry membership, ownership and write authority remain unchanged. -/
theorem assignment_mono {kind : ArithmeticType} (index : Vars context kind)
    (value : RHS target context kind.asIntType)
    (first next : Assertion target parameters Environment)
    (entails : ∀ state events, first state events → next state events)
    (initial : State target parameters Environment) (earlier : List Event) :
    assignment policy bindings index value first initial earlier →
      assignment policy bindings index value next initial earlier := by
  apply expression_mono dialect policy bindings value
  intro evaluated state events condition
  obtain ⟨previous, permissions, registered, writable, member⟩ := condition
  exact ⟨previous, permissions, registered, writable, entails _ _ member⟩

/-- Consequence for generated formulas. Normal continuation and early return
posts can both be weakened while the supplied loop invariants/ranks stay fixed.
This is formula-level composition, not an assumption of successful execution. -/
theorem vc_mono {code : Code target context result}
    (annotation : Annotation (parameters := parameters) (Environment := Environment) code)
    (normalFirst normalNext : Assertion target parameters Environment)
    (returnedFirst returnedNext : Value target result → Assertion target parameters Environment)
    (normalEntails : ∀ state events, normalFirst state events → normalNext state events)
    (returnedEntails : ∀ value state events, returnedFirst value state events → returnedNext value state events)
    (initial : State target parameters Environment) (earlier : List Event) :
    vc policy bindings annotation normalFirst returnedFirst initial earlier →
      vc policy bindings annotation normalNext returnedNext initial earlier := by
  induction annotation generalizing normalFirst normalNext returnedFirst returnedNext initial earlier with
  | skip => exact normalEntails initial earlier
  | assign => exact assignment_mono dialect policy bindings _ _ normalFirst normalNext normalEntails initial earlier
  | @seq first next before after beforeIH afterIH =>
      apply beforeIH
      · intro state events condition
        exact afterIH normalFirst normalNext returnedFirst returnedNext normalEntails returnedEntails state events condition
      · exact returnedEntails
  | @branch condition yes no positive negative positiveIH negativeIH =>
      apply expression_mono dialect policy bindings condition
      intro value state events member
      by_cases zero : value.toInt = 0
      · have selected := negativeIH normalFirst normalNext returnedFirst returnedNext normalEntails returnedEntails state events
        simpa only [zero, ↓reduceIte] using selected (by simpa only [zero, ↓reduceIte] using member)
      · have selected := positiveIH normalFirst normalNext returnedFirst returnedNext normalEntails returnedEntails state events
        simpa only [zero, ↓reduceIte] using selected (by simpa only [zero, ↓reduceIte] using member)
  | @loop condition body invariant rank bodyAnnotation bodyIH =>
      rintro ⟨member, progress⟩
      refine ⟨member, ?_⟩
      intro state history retained
      apply expression_mono dialect policy bindings condition _ _ ?_ state history (progress state history retained)
      intro value middle events checked
      by_cases zero : value.toInt = 0
      · simpa only [zero, ↓reduceIte] using
          normalEntails middle events (by simpa only [zero, ↓reduceIte] using checked)
      · have bodyCondition : vc policy bindings bodyAnnotation
            (fun final allEvents => invariant final allEvents ∧ rank final allEvents < rank state history)
            returnedFirst middle events := by simpa only [zero, ↓reduceIte] using checked
        have weakened := bodyIH _ _ returnedFirst returnedNext (fun _ _ h => h) returnedEntails middle events bodyCondition
        simpa only [zero, ↓reduceIte] using weakened
  | ret => exact expression_mono dialect policy bindings _ returnedFirst returnedNext returnedEntails initial earlier
  | unsupported => exact False.elim

end EDSL.Source.Objects.Control.StructuredVC
