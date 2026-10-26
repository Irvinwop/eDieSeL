/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.Rules

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.RulesValidation
open StateSyntax

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {context : List ArithmeticType} {result : IntType}
variable (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)
local notation "Configuration" => Config target parameters Environment context result

/- Independent behavior under test: return from the selected branch exits the
loop and the whole chunk. Both the unselected branch and the later continuation
diverge. The two progress phases force one strict-rank segment followed by an
early-return segment. Arbitrary earlier events must survive their composition.
-/
private def spinning (truth : Value target (.small .boolean)) : Code target context result :=
  .loop (.literal truth) .skip

private def loopPart (truth : Value target (.small .boolean)) (value : Value target result) :
    Code target context result :=
  .loop (.literal truth) (.branch (.literal truth) (.ret (.literal value)) (spinning truth))

private def chunk (truth : Value target (.small .boolean)) (value : Value target result) :
    Code target context result :=
  .seq (loopPart truth value) (spinning truth)

private def entryRank (config : Configuration) : Nat :=
  match config.control with
  | .seq _ _ :: _ => 1
  | _ => 0

private def phases (truth : Value target (.small .boolean)) (value : Value target result)
    (earlier : List Event) (original : State target parameters Environment)
    (config : Configuration) : Prop :=
  config = startUnchecked (chunk truth value) original earlier ∨
  config = startUnchecked (loopPart truth value) original earlier [spinning truth]

private theorem progress (truth : Value target (.small .boolean)) (nonzero : truth.toInt ≠ 0)
    (value : Value target result) (earlier : List Event) :
    FiniteProgress dialect policy bindings
      (phases (parameters := parameters) (Environment := Environment) truth value earlier) entryRank
      (fun original _ final events => final = original ∧ events = earlier) := by
  intro original config member
  rcases member with rfl | rfl
  · refine ⟨1, Or.inr ⟨Or.inr rfl, ?_⟩⟩
    exact Nat.zero_lt_succ 0
  · have execution : run dialect policy bindings 3
        (startUnchecked (loopPart truth value) original earlier [spinning truth]) =
        (⟨[], original, earlier, .returned value⟩ : Configuration) := by
      simp [run, startUnchecked, loopPart, tick, perform, StateEval.evalExpr_literal,
        Op.pure, nonzero]
    refine ⟨3, Or.inl ⟨value, ?_, ?_⟩⟩
    · rw [execution]
    · rw [execution]
      exact ⟨rfl, rfl⟩

theorem early_return_keeps_history
    (truth : Value target (.small .boolean)) (nonzero : truth.toInt ≠ 0)
    (value : Value target result) (earlier : List Event)
    (original : State target parameters Environment) :
    ∃ steps returned,
      (run dialect policy bindings steps (startUnchecked (chunk truth value) original earlier)).status =
        .returned returned ∧
      (run dialect policy bindings steps (startUnchecked (chunk truth value) original earlier)).state = original ∧
      (run dialect policy bindings steps (startUnchecked (chunk truth value) original earlier)).events = earlier :=
  returns_of_finiteProgress dialect policy bindings (phases truth value earlier) entryRank
    (progress dialect policy bindings truth nonzero value earlier) original _ (Or.inl rfl)

theorem early_return_certificate
    (truth : Value target (.small .boolean)) (nonzero : truth.toInt ≠ 0)
    (value : Value target result) (witness : State target parameters Environment) :
    Certificate dialect policy bindings (chunk truth value)
      (fun (_ : State target parameters Environment) => True)
      (fun original _ final events => final = original ∧ events = []) := by
  apply Certificate.of_finiteProgress dialect policy bindings ⟨witness, True.intro⟩
    (phases truth value []) entryRank
  · intro original _
    have supported : (chunk truth value : Code target context result).Supported := by
      trivial
    rw [start_supported _ _ supported]
    exact Or.inl rfl
  · exact progress dialect policy bindings truth nonzero value []

/- Independent negative oracle: the checked machine proves this source loop
divergent. No invariant/rank covering its entry can meet FiniteProgress, even
when its post is completely unrestricted. This checks rejection of divergence
rather than conditioning decrease on completed iterations.
-/
theorem spinning_rejects_progress
    (truth : Value target (.small .boolean)) (nonzero : truth.toInt ≠ 0)
    (invariant : State target parameters Environment → Configuration → Prop)
    (rank : Configuration → Nat) (original : State target parameters Environment)
    (member : invariant original (start (spinning truth) original)) :
    ¬ FiniteProgress dialect policy bindings invariant rank (fun _ _ _ _ => True) := by
  intro completed
  exact FiniteProgress.not_diverges dialect policy bindings completed original _ member
    (loop_skip_diverges dialect policy bindings truth nonzero original)

/- A true outer iteration enters a divergent inner loop and never completes.
The actual three-phase machine invariant is independent of the proposed rank.
No FiniteProgress annotation covering this entry is possible, even though a
decrease condition imposed only on completed outer iterations would be vacuous.
-/
theorem divergent_body_rejects_progress
    (truth : Value target (.small .boolean)) (nonzero : truth.toInt ≠ 0)
    (invariant : State target parameters Environment → Configuration → Prop)
    (rank : Configuration → Nat) (original : State target parameters Environment)
    (member : invariant original
      (start (.loop (.literal truth) (spinning truth)) original)) :
    ¬ FiniteProgress dialect policy bindings invariant rank (fun _ _ _ _ => True) := by
  let outer : Code target context result := .loop (.literal truth) (spinning truth)
  let header : Configuration := startUnchecked outer original
  let body : Configuration := startUnchecked (spinning truth) original [] [outer]
  let skip : Configuration := startUnchecked .skip original [] [spinning truth, outer]
  have entry : start outer original = header := start_supported _ _ (by trivial)
  have enterBody : tick dialect policy bindings header = body := by
    simp [header, body, outer, startUnchecked, tick, perform, StateEval.evalExpr_literal,
      Op.pure, nonzero]
  have enterSkip : tick dialect policy bindings body = skip := by
    simp [body, skip, spinning, startUnchecked, tick, perform, StateEval.evalExpr_literal,
      Op.pure, nonzero]
  have repeatBody : tick dialect policy bindings skip = body := rfl
  have stays : ∀ steps, run dialect policy bindings steps header = header ∨
      run dialect policy bindings steps header = body ∨
      run dialect policy bindings steps header = skip := by
    apply run_invariant dialect policy bindings
      (fun config => config = header ∨ config = body ∨ config = skip) header
    · exact Or.inl rfl
    · intro config phase
      rcases phase with rfl | rfl | rfl
      · exact Or.inr (Or.inl enterBody)
      · exact Or.inr (Or.inr enterSkip)
      · exact Or.inr (Or.inl repeatBody)
  have divergent : Diverges dialect policy bindings (start outer original) := by
    intro steps
    rw [entry]
    rcases stays steps with phase | phase | phase <;> rw [phase] <;> rfl
  intro completed
  exact FiniteProgress.not_diverges dialect policy bindings completed original _ member divergent

/- All consequences must use the checked contract layer. -/
example (truth : Value target (.small .boolean)) (nonzero : truth.toInt ≠ 0)
    (value : Value target result) (witness : State target parameters Environment) :
    PrefixNoFailure dialect policy bindings (chunk truth value)
      (fun (_ : State target parameters Environment) => True) :=
  (early_return_certificate dialect policy bindings truth nonzero value witness).verified.noFailure

example (truth : Value target (.small .boolean)) (nonzero : truth.toInt ≠ 0)
    (value : Value target result) (witness : State target parameters Environment) :
    (chunk truth value : Code target context result).Supported :=
  (early_return_certificate dialect policy bindings truth nonzero value witness).supported

end EDSL.Source.Objects.Control.RulesValidation
