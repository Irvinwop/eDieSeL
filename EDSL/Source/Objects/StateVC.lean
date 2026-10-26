/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Protocol
import EDSL.Source.Objects.StateEval
import EDSL.Source.Objects.ExpressionVC

set_option autoImplicit false

namespace EDSL.Source.Objects.StateVC

open StateSyntax Protocol

/-! Structural verification conditions for finite object-backed statements.
Expression conditions wrap the actual shared expression computation; no second
expression semantics is introduced. Assignment uses the actual store primitive.
All postconditions retain the original initial state and concatenate the actual
read, write and selected continuation events. Internal read order is not a claim
about native C/C++ operand sequencing. Allocation and scope cleanup are separate.
-/

variable {target : Target} {stateParameters : List IntType} {Environment : Type}
    {context : List ArithmeticType} {result : IntType}

/-- A structural statement VC generator. Only the selected branch is demanded,
while the public `vcRun` separately requires whole-statement coverage. RHS conditions
use the shared expression traversal in its predicate-transformer carrier,
exposing independent read snapshots and scalar obligations. -/
def vcStmt (dialect : Dialect) (policy : IntegerConversionPolicy)
    (environment : Env context) : Stmt target context result →
    Post target stateParameters Environment (Value target result) →
    State target stateParameters Environment → Prop
  | .set index value next, post =>
      ExpressionVC.vcExpr policy environment value
        (fun original evaluated middle readEvents =>
          WP (store (environment.get index) evaluated)
            (fun _ _ updated writeEvents =>
              vcStmt dialect policy environment next
                (fun _ returned final suffix =>
                  post original returned final (readEvents ++ (writeEvents ++ suffix))) updated)
            middle)
  | .branch condition yes no, post =>
      ExpressionVC.vcExpr policy environment condition
        (fun original evaluated middle readEvents =>
          if evaluated.toInt = 0 then
            vcStmt dialect policy environment no
              (fun _ returned final suffix => post original returned final (readEvents ++ suffix))
              middle
          else
            vcStmt dialect policy environment yes
              (fun _ returned final suffix => post original returned final (readEvents ++ suffix))
              middle)
  | .ret value, post => ExpressionVC.vcExpr policy environment value post
  | .unsupported _, _ => fun _ => False

/-- Structural conditions are exact for actual finite statement execution,
including complete final state and event history. -/
theorem vcStmt_iff_wp (dialect : Dialect) (policy : IntegerConversionPolicy)
    (environment : Env context) (statement : Stmt target context result)
    (post : Post target stateParameters Environment (Value target result))
    (initial : State target stateParameters Environment) :
    vcStmt dialect policy environment statement post initial ↔
      WP (StateEval.evalStmt dialect policy environment statement) post initial := by
  induction statement generalizing post initial with
  | set index value next ih =>
      simp only [vcStmt, StateEval.evalStmt, ExpressionVC.vcExpr_iff_wp dialect, wp_bind, ih]
  | branch condition yes no yesIH noIH =>
      simp only [vcStmt, StateEval.evalStmt, ExpressionVC.vcExpr_iff_wp dialect, wp_bind, wp_ite, yesIH, noIH]
  | ret value => exact ExpressionVC.vcExpr_iff_wp dialect policy environment value post initial
  | unsupported feature => rfl

/-- Public whole-statement preflight plus structural execution conditions.
Coverage includes every RHS and both branches, even when execution skips one. -/
def vcRun (dialect : Dialect) (policy : IntegerConversionPolicy)
    (environment : Env context) (statement : Stmt target context result)
    (post : Post target stateParameters Environment (Value target result))
    (initial : State target stateParameters Environment) : Prop :=
  statement.Supported ∧ vcStmt dialect policy environment statement post initial

/-- Whole-body preflight is part of exactness, not an assumption silently dropped
from lazy statement verification. -/
theorem vcRun_iff_wp (dialect : Dialect) (policy : IntegerConversionPolicy)
    (environment : Env context) (statement : Stmt target context result)
    (post : Post target stateParameters Environment (Value target result))
    (initial : State target stateParameters Environment) :
    vcRun dialect policy environment statement post initial ↔
      WP (StateEval.runStmt dialect policy environment statement) post initial := by
  unfold vcRun StateEval.runStmt
  cases coverage : statement.firstUnsupported with
  | none =>
      have supported := statement.firstUnsupported_eq_none_iff.mp coverage
      simp only [supported, true_and]
      exact vcStmt_iff_wp dialect policy environment statement post initial
  | some feature =>
      have unsupported : ¬ statement.Supported := by
        intro supported
        have absent := statement.firstUnsupported_eq_none_iff.mpr supported
        rw [coverage] at absent
        cases absent
      simp only [unsupported, false_and]
      exact ⟨False.elim, fun impossible => (wp_reject _ _ _ impossible).elim⟩

/-- Independently supplied admissions discharge generated conditions. The
judgment never inserts success, definedness or the postcondition into admission. -/
theorem verifies_iff_vcRun (dialect : Dialect) (policy : IntegerConversionPolicy)
    (environment : Env context) (statement : Stmt target context result)
    (admitted : State target stateParameters Environment → Prop)
    (post : Post target stateParameters Environment (Value target result)) :
    Protocol.Verifies (StateEval.runStmt dialect policy environment statement) admitted post ↔
      ∀ initial, admitted initial → vcRun dialect policy environment statement post initial := by
  rw [verifies_iff_wp]
  simp only [vcRun_iff_wp]

/-- A useful certificate requires a genuine admitted initial state, with all
execution obligations proved from the structural VCs. -/
theorem certificate (dialect : Dialect) (policy : IntegerConversionPolicy)
    (environment : Env context) (statement : Stmt target context result)
    (admitted : State target stateParameters Environment → Prop)
    (post : Post target stateParameters Environment (Value target result))
    (useful : ∃ initial, admitted initial)
    (conditions : ∀ initial, admitted initial →
      vcRun dialect policy environment statement post initial) :
    Protocol.Certificate (StateEval.runStmt dialect policy environment statement) admitted post :=
  ⟨useful, (verifies_iff_vcRun dialect policy environment statement admitted post).mpr conditions⟩

/-- Postcondition consequence is proved through the exactness theorem; the
structural generator does not insert the requested result into its premises. -/
theorem vcStmt_mono (dialect : Dialect) (policy : IntegerConversionPolicy)
    (environment : Env context) (statement : Stmt target context result)
    (first second : Post target stateParameters Environment (Value target result))
    (entails : ∀ original value final events,
      first original value final events → second original value final events)
    (initial : State target stateParameters Environment) :
    vcStmt dialect policy environment statement first initial →
      vcStmt dialect policy environment statement second initial := by
  rw [vcStmt_iff_wp, vcStmt_iff_wp]
  exact wp_mono _ first second entails initial

/-- An exact characterization of useful statement certificates. An empty state
domain cannot pass this condition even if its generated VCs hold vacuously. -/
theorem certificate_iff (dialect : Dialect) (policy : IntegerConversionPolicy)
    (environment : Env context) (statement : Stmt target context result)
    (admitted : State target stateParameters Environment → Prop)
    (post : Post target stateParameters Environment (Value target result)) :
    Protocol.Certificate (StateEval.runStmt dialect policy environment statement) admitted post ↔
      (∃ initial, admitted initial) ∧
      ∀ initial, admitted initial → vcRun dialect policy environment statement post initial := by
  constructor
  · intro checked
    exact ⟨checked.useful,
      (verifies_iff_vcRun dialect policy environment statement admitted post).mp checked.verified⟩
  · rintro ⟨useful, conditions⟩
    exact certificate dialect policy environment statement admitted post useful conditions

/-- All scalar UB, object UB, C++ erroneous results, authority/resource refusals
and binding/coverage failures are excluded separately by their Stop constructor.
This conclusion is derived from VCs under admission, not assumed at entry. -/
theorem no_failure_of_vcRun (dialect : Dialect) (policy : IntegerConversionPolicy)
    (environment : Env context) (statement : Stmt target context result)
    (admitted : State target stateParameters Environment → Prop)
    (post : Post target stateParameters Environment (Value target result))
    (conditions : ∀ initial, admitted initial →
      vcRun dialect policy environment statement post initial)
    (initial : State target stateParameters Environment) (permitted : admitted initial)
    (reason : Stop) (final : State target stateParameters Environment) (events : List Event) :
    StateEval.runStmt dialect policy environment statement initial ≠ (.error reason, final, events) :=
  ((verifies_iff_vcRun dialect policy environment statement admitted post).mpr conditions).no_failure
    initial permitted reason final events

end EDSL.Source.Objects.StateVC
