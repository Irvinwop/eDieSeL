/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.Trace
import EDSL.Source.Objects.Protocol

set_option autoImplicit false
namespace EDSL.Source.Objects.Control
open StateSyntax

/-! These are judgments of the internal control machine on already-bound
objects. They do not establish native execution, source-standard loop validity
or forward progress, function completion, or scope/resource cleanup. Admissions
describe independent caller inputs/resources; target definedness, success and
postconditions must be proved by separate step/expression/VC obligations.
-/

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {context : List ArithmeticType} {result : IntType}
variable (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)
local notation "Configuration" => Config target parameters Environment context result

/-- UB exclusion on every finite internal prefix; other stops remain possible. -/
def PrefixUBSafe (code : Code target context result)
    (admitted : State target parameters Environment → Prop) : Prop :=
  ∀ initial, admitted initial → UBSafe dialect policy bindings (start code initial)

/-- Every finite prefix excludes all stopped reasons. This permits both
divergence and normal control fallthrough; it does not assert a value return. -/
def PrefixNoFailure (code : Code target context result)
    (admitted : State target parameters Environment → Prop) : Prop :=
  ∀ initial, admitted initial → NoFailure dialect policy bindings (start code initial)

/-- Only actual returned endpoints incur a postcondition obligation. No safety
or termination premise is hidden in this partial-correctness judgment. -/
def PartiallyVerifies (code : Code target context result)
    (admitted : State target parameters Environment → Prop)
    (post : Protocol.Post target parameters Environment (Value target result)) : Prop :=
  ∀ initial, admitted initial → ∀ steps value,
    (run dialect policy bindings steps (start code initial)).status = .returned value →
    post initial value (run dialect policy bindings steps (start code initial)).state
      (run dialect policy bindings steps (start code initial)).events

/-- Actual finite value completion with its original state, final state and
complete events. A bound exhausted while running and a fellThrough endpoint
cannot witness this judgment. This is not function/scope completion. -/
def Verifies (code : Code target context result)
    (admitted : State target parameters Environment → Prop)
    (post : Protocol.Post target parameters Environment (Value target result)) : Prop :=
  ∀ initial, admitted initial → ∃ steps value,
    (run dialect policy bindings steps (start code initial)).status = .returned value ∧
    post initial value (run dialect policy bindings steps (start code initial)).state
      (run dialect policy bindings steps (start code initial)).events

/-- Usefulness prevents a prefix claim from hiding unsupported code behind an
empty state domain. The safety field is stronger than UB exclusion alone. -/
structure PrefixCertificate (code : Code target context result)
    (admitted : State target parameters Environment → Prop) : Prop where
  useful : ∃ initial, admitted initial
  noFailure : PrefixNoFailure dialect policy bindings code admitted

structure PartialCertificate (code : Code target context result)
    (admitted : State target parameters Environment → Prop)
    (post : Protocol.Post target parameters Environment (Value target result)) : Prop where
  «prefix» : PrefixCertificate dialect policy bindings code admitted
  correct : PartiallyVerifies dialect policy bindings code admitted post

/-- The admission witness is input/resource evidence, not an assumed execution
or postcondition. Finite return is established by the separate proof field. -/
structure Certificate (code : Code target context result)
    (admitted : State target parameters Environment → Prop)
    (post : Protocol.Post target parameters Environment (Value target result)) : Prop where
  useful : ∃ initial, admitted initial
  verified : Verifies dialect policy bindings code admitted post

variable {dialect policy bindings}
variable {code : Code target context result}
variable {admitted : State target parameters Environment → Prop}
variable {post : Protocol.Post target parameters Environment (Value target result)}

theorem PrefixNoFailure.ubSafe (safe : PrefixNoFailure dialect policy bindings code admitted) :
    PrefixUBSafe dialect policy bindings code admitted := by
  intro initial permitted
  exact noFailure_ubSafe dialect policy bindings _ (safe initial permitted)

theorem PrefixNoFailure.supported (safe : PrefixNoFailure dialect policy bindings code admitted)
    (useful : ∃ initial, admitted initial) : code.Supported := by
  obtain ⟨initial, permitted⟩ := useful
  exact noFailure_start_supported dialect policy bindings code initial (safe initial permitted)

theorem PrefixCertificate.supported
    (certificate : PrefixCertificate dialect policy bindings code admitted) : code.Supported :=
  certificate.noFailure.supported certificate.useful

theorem PrefixCertificate.ubSafe (certificate : PrefixCertificate dialect policy bindings code admitted) :
    PrefixUBSafe dialect policy bindings code admitted := certificate.noFailure.ubSafe

theorem Verifies.noFailure (verified : Verifies dialect policy bindings code admitted post) :
    PrefixNoFailure dialect policy bindings code admitted := by
  intro initial permitted
  obtain ⟨steps, value, returned, _⟩ := verified initial permitted
  exact noFailure_of_returns dialect policy bindings _ steps value returned

theorem Verifies.ubSafe (verified : Verifies dialect policy bindings code admitted post) :
    PrefixUBSafe dialect policy bindings code admitted := verified.noFailure.ubSafe

theorem Verifies.supported (verified : Verifies dialect policy bindings code admitted post)
    (useful : ∃ initial, admitted initial) : code.Supported := verified.noFailure.supported useful

/-- All observations of a returned endpoint agree with the completed endpoint,
including the value, whole state and events, even at different observation bounds. -/
theorem Verifies.partial (verified : Verifies dialect policy bindings code admitted post) :
    PartiallyVerifies dialect policy bindings code admitted post := by
  intro initial permitted steps value returned
  obtain ⟨actualSteps, actualValue, actualReturned, actualPost⟩ := verified initial permitted
  have firstTerminal : Terminal (run dialect policy bindings steps (start code initial)) := by
    simp only [Terminal, returned]
  have secondTerminal : Terminal (run dialect policy bindings actualSteps (start code initial)) := by
    simp only [Terminal, actualReturned]
  have same := terminal_endpoint_unique dialect policy bindings (start code initial) steps actualSteps
    firstTerminal secondTerminal
  have values := congrArg Config.status same
  rw [returned, actualReturned] at values
  have valueSame : value = actualValue := Status.returned.inj values
  subst actualValue
  rw [same]
  exact actualPost

theorem Verifies.no_fallthrough (verified : Verifies dialect policy bindings code admitted post)
    (initial : State target parameters Environment) (permitted : admitted initial) (steps : Nat) :
    (run dialect policy bindings steps (start code initial)).status ≠ .fellThrough := by
  intro fellThrough
  obtain ⟨actualSteps, value, returned, _⟩ := verified initial permitted
  have firstTerminal : Terminal (run dialect policy bindings steps (start code initial)) := by
    simp only [Terminal, fellThrough]
  have secondTerminal : Terminal (run dialect policy bindings actualSteps (start code initial)) := by
    simp only [Terminal, returned]
  have same := terminal_endpoint_unique dialect policy bindings (start code initial) steps actualSteps
    firstTerminal secondTerminal
  have impossible := congrArg Config.status same
  rw [fellThrough, returned] at impossible
  cases impossible

theorem Certificate.prefix (certificate : Certificate dialect policy bindings code admitted post) :
    PrefixCertificate dialect policy bindings code admitted :=
  ⟨certificate.useful, certificate.verified.noFailure⟩

theorem Certificate.partial (certificate : Certificate dialect policy bindings code admitted post) :
    PartialCertificate dialect policy bindings code admitted post :=
  ⟨certificate.prefix, certificate.verified.partial⟩

theorem Certificate.supported (certificate : Certificate dialect policy bindings code admitted post) :
    code.Supported := certificate.prefix.supported

theorem Certificate.ubSafe (certificate : Certificate dialect policy bindings code admitted post) :
    PrefixUBSafe dialect policy bindings code admitted := certificate.verified.ubSafe

theorem PartialCertificate.supported
    (certificate : PartialCertificate dialect policy bindings code admitted post) : code.Supported :=
  certificate.prefix.supported

theorem no_prefixCertificate_empty :
    ¬ PrefixCertificate dialect policy bindings code (fun (_ : State target parameters Environment) => False) := by
  intro certificate
  obtain ⟨_, impossible⟩ := certificate.useful
  exact impossible

theorem no_certificate_empty :
    ¬ Certificate dialect policy bindings code (fun (_ : State target parameters Environment) => False) post := by
  intro certificate
  obtain ⟨_, impossible⟩ := certificate.useful
  exact impossible

theorem PartiallyVerifies.mono (verified : PartiallyVerifies dialect policy bindings code admitted post)
    (next : Protocol.Post target parameters Environment (Value target result))
    (entails : ∀ initial value final events, post initial value final events → next initial value final events) :
    PartiallyVerifies dialect policy bindings code admitted next := by
  intro initial permitted steps value returned
  exact entails _ _ _ _ (verified initial permitted steps value returned)

theorem Verifies.mono (verified : Verifies dialect policy bindings code admitted post)
    (next : Protocol.Post target parameters Environment (Value target result))
    (entails : ∀ initial value final events, post initial value final events → next initial value final events) :
    Verifies dialect policy bindings code admitted next := by
  intro initial permitted
  obtain ⟨steps, value, returned, resultPost⟩ := verified initial permitted
  exact ⟨steps, value, returned, entails _ _ _ _ resultPost⟩

variable (dialect policy bindings)

/-- Initial membership, actual-step preservation and exclusion of stopped
states suffice. No rank, observation bound, return, or termination is assumed. -/
theorem prefixNoFailure_of_invariant
    (invariant : State target parameters Environment → Configuration → Prop)
    (member : ∀ initial, admitted initial → invariant initial (start code initial))
    (preserved : ∀ initial, admitted initial → ∀ config, invariant initial config →
      invariant initial (tick dialect policy bindings config))
    (notStopped : ∀ initial, admitted initial → ∀ config, invariant initial config →
      ∀ reason, config.status ≠ .stopped reason) :
    PrefixNoFailure dialect policy bindings code admitted := by
  intro initial permitted
  exact noFailure_of_invariant dialect policy bindings (invariant initial) (start code initial)
    (member initial permitted) (preserved initial permitted) (notStopped initial permitted)

theorem PrefixCertificate.of_invariant (useful : ∃ initial, admitted initial)
    (invariant : State target parameters Environment → Configuration → Prop)
    (member : ∀ initial, admitted initial → invariant initial (start code initial))
    (preserved : ∀ initial, admitted initial → ∀ config, invariant initial config →
      invariant initial (tick dialect policy bindings config))
    (notStopped : ∀ initial, admitted initial → ∀ config, invariant initial config →
      ∀ reason, config.status ≠ .stopped reason) :
    PrefixCertificate dialect policy bindings code admitted :=
  ⟨useful, prefixNoFailure_of_invariant dialect policy bindings invariant member preserved notStopped⟩

theorem partiallyVerifies_of_invariant
    (invariant : State target parameters Environment → Configuration → Prop)
    (member : ∀ initial, admitted initial → invariant initial (start code initial))
    (preserved : ∀ initial, admitted initial → ∀ config, invariant initial config →
      invariant initial (tick dialect policy bindings config))
    (returnedPost : ∀ initial, admitted initial → ∀ config, invariant initial config →
      ∀ value, config.status = .returned value → post initial value config.state config.events) :
    PartiallyVerifies dialect policy bindings code admitted post := by
  intro initial permitted steps value returned
  exact returnedPost initial permitted _
    (run_invariant dialect policy bindings (invariant initial) (start code initial)
      (member initial permitted) (preserved initial permitted) steps) value returned

/-- This rule combines finite return evidence with separately proved partial
correctness. Neither obligation is placed into the program's admission. -/
theorem verifies_of_partial_and_returns
    (correct : PartiallyVerifies dialect policy bindings code admitted post)
    (returns : ∀ initial, admitted initial → ∃ steps value,
      (run dialect policy bindings steps (start code initial)).status = .returned value) :
    Verifies dialect policy bindings code admitted post := by
  intro initial permitted
  obtain ⟨steps, value, returned⟩ := returns initial permitted
  exact ⟨steps, value, returned, correct initial permitted steps value returned⟩

/-- Reuse an actual shared expression proof. Static expression coverage remains
a separate obligation because expression execution can skip syntax. -/
theorem verifies_ret (expression : RHS target context result) (supported : expression.Supported)
    (verified : Protocol.Verifies (StateEval.evalExpr dialect policy bindings expression) admitted post) :
    Verifies dialect policy bindings (.ret expression) admitted post := by
  intro initial permitted
  obtain ⟨value, final, events, execution, resultPost⟩ := verified initial permitted
  have executed : run dialect policy bindings 1 (start (.ret expression) initial) =
      (⟨[], final, events, .returned value⟩ : Configuration) := by
    rw [start_supported (.ret expression) initial supported]
    simp only [run_succ, run_zero, startUnchecked, tick, perform, execution, List.nil_append]
  exact ⟨1, value, by rw [executed], by simpa only [executed] using resultPost⟩

theorem certificate_ret (expression : RHS target context result) (supported : expression.Supported)
    (certificate : Protocol.Certificate (StateEval.evalExpr dialect policy bindings expression) admitted post) :
    Certificate dialect policy bindings (.ret expression) admitted post :=
  ⟨certificate.useful, verifies_ret dialect policy bindings expression supported certificate.verified⟩

/-- A nonempty, independent `True` admission works for every actual state. The
post specifies a value, exact state preservation and no observations. -/
theorem literal_certificate (value : Value target result) (witness : State target parameters Environment) :
    Certificate dialect policy bindings (.ret (.literal value))
      (fun (_ : State target parameters Environment) => True)
      (fun initial returned final events => returned = value ∧ final = initial ∧ events = []) := by
  apply certificate_ret dialect policy bindings (.literal value) (by trivial)
  exact ⟨⟨witness, True.intro⟩, by
    intro initial _
    exact ⟨value, initial, [], rfl, rfl, rfl, rfl⟩⟩

/-- A two-phase internal control invariant proves divergence without executing
an unbounded evaluator. This is not a C/C++ forward-progress or loop-validity
claim; source profile review is separate, including C++26 yield behavior. -/
theorem loop_skip_diverges (truth : Value target (.small .boolean)) (nonzero : truth.toInt ≠ 0)
    (initial : State target parameters Environment) :
    Diverges dialect policy bindings (start (.loop (.literal truth) (.skip : Code target context result)) initial) := by
  let code : Code target context result := .loop (.literal truth) .skip
  let first : Configuration := startUnchecked code initial
  let second : Configuration := { first with control := [.skip, code] }
  have covered : code.Supported := by trivial
  have entry : start code initial = first := start_supported code initial covered
  have firstStep : tick dialect policy bindings first = second := by
    simp [first, second, code, startUnchecked, tick, perform, StateEval.evalExpr_literal, Op.pure, nonzero]
  have secondStep : tick dialect policy bindings second = first := rfl
  have phases : ∀ steps, run dialect policy bindings steps first = first ∨
      run dialect policy bindings steps first = second := by
    apply run_invariant dialect policy bindings (fun config => config = first ∨ config = second) first
    · exact Or.inl rfl
    · intro config phase
      rcases phase with rfl | rfl
      · exact Or.inr firstStep
      · exact Or.inl secondStep
  intro steps
  change (run dialect policy bindings steps (start code initial)).status = .running
  rw [entry]
  rcases phases steps with phase | phase <;> rw [phase] <;> rfl

/-- A useful safe divergent control example with no target property in its
admission. It establishes internal finite-prefix safety only. -/
theorem loop_skip_prefixCertificate (truth : Value target (.small .boolean)) (nonzero : truth.toInt ≠ 0)
    (witness : State target parameters Environment) :
    PrefixCertificate dialect policy bindings (.loop (.literal truth) (.skip : Code target context result))
      (fun (_ : State target parameters Environment) => True) := by
  refine ⟨⟨witness, True.intro⟩, ?_⟩
  intro initial _
  exact diverges_noFailure dialect policy bindings _
    (loop_skip_diverges dialect policy bindings truth nonzero initial)

/-- Prefix safety does not entail finite value completion, even for a nonempty
independent admission and a postcondition as weak as `True`. -/
theorem loop_skip_not_verifies (truth : Value target (.small .boolean)) (nonzero : truth.toInt ≠ 0)
    (useful : ∃ initial, admitted initial) :
    ¬ Verifies dialect policy bindings (.loop (.literal truth) (.skip : Code target context result))
      admitted post := by
  intro verified
  obtain ⟨initial, permitted⟩ := useful
  obtain ⟨steps, value, returned, _⟩ := verified initial permitted
  have running := loop_skip_diverges (result := result) dialect policy bindings truth nonzero initial steps
  rw [running] at returned
  cases returned

end EDSL.Source.Objects.Control
