/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.PureEmbedding

set_option autoImplicit false
namespace EDSL.Source.Objects.Protocol

variable {target : Target} {parameters : List IntType} {Environment α β : Type}
abbrev Post (target : Target) (parameters : List IntType) (Environment α : Type) :=
  State target parameters Environment → α →
    State target parameters Environment → List Event → Prop

/-- Successful completion includes actual state and complete event history.
It rules out erroneous production and model/resource refusal as well as UB.
This is an operation-level judgment, not a source-program syntax certificate. -/
def Verifies (operation : Op target parameters Environment α)
    (admitted : State target parameters Environment → Prop)
    (post : Post target parameters Environment α) : Prop :=
  ∀ initial, admitted initial → ∃ value final events,
    operation initial = (.ok value, final, events) ∧ post initial value final events

/-- Exact actual-operation condition. Structural source VCs may compose these
laws later; this definition is not an automatic stateful source VC generator. -/
def WP (operation : Op target parameters Environment α)
    (post : Post target parameters Environment α) (initial : State target parameters Environment) : Prop :=
  match operation initial with
  | (.error _, _, _) => False
  | (.ok value, final, events) => post initial value final events

theorem wp_iff (operation : Op target parameters Environment α)
    (post : Post target parameters Environment α) (initial : State target parameters Environment) :
    WP operation post initial ↔ ∃ value final events,
      operation initial = (.ok value, final, events) ∧ post initial value final events := by
  constructor
  · intro condition
    cases execution : operation initial with
    | mk result rest =>
        rcases rest with ⟨final, events⟩
        cases result with
        | error reason => simp only [WP, execution] at condition
        | ok value => exact ⟨value, final, events, rfl, by simpa only [WP, execution] using condition⟩
  · rintro ⟨value, final, events, execution, resultPost⟩
    simpa only [WP, execution] using resultPost

theorem verifies_iff_wp (operation : Op target parameters Environment α)
    (admitted : State target parameters Environment → Prop)
    (post : Post target parameters Environment α) :
    Verifies operation admitted post ↔ ∀ initial, admitted initial → WP operation post initial := by
  simp only [Verifies, wp_iff]

theorem wp_pure (value : α) (post : Post target parameters Environment α)
    (initial : State target parameters Environment) :
    WP (Op.pure value) post initial ↔ post initial value initial [] := Iff.rfl

theorem wp_reject (reason : Stop) (post : Post target parameters Environment α)
    (initial : State target parameters Environment) :
    ¬ WP (Op.reject reason) post initial := fun contradiction => contradiction

/-- Composition keeps the original prestate and concatenates actual event
histories. The intermediate post is not a target-definedness input premise. -/
theorem wp_bind (first : Op target parameters Environment α)
    (next : α → Op target parameters Environment β)
    (post : Post target parameters Environment β) (initial : State target parameters Environment) :
    WP (Op.bind first next) post initial ↔
      WP first (fun original value middle earlierEvents =>
        WP (next value) (fun _ result final suffix => post original result final (earlierEvents ++ suffix)) middle)
        initial := by
  cases execution : first initial with
  | mk result rest =>
      rcases rest with ⟨middle, earlierEvents⟩
      cases result with
      | error reason => simp [WP, Op.bind, Effects.Op.bind, execution]
      | ok value =>
          cases following : next value middle with
          | mk result rest =>
              rcases rest with ⟨final, suffix⟩
              cases result <;> simp [WP, Op.bind, Effects.Op.bind, execution, following]

/-- Replacing a postcondition by a pointwise equivalent one preserves the
actual operation condition without changing state or event observations. -/
theorem wp_congr (operation : Op target parameters Environment α)
    (first second : Post target parameters Environment α)
    (equivalent : ∀ initial value final events,
      first initial value final events ↔ second initial value final events)
    (initial : State target parameters Environment) :
    WP operation first initial ↔ WP operation second initial := by
  simp only [wp_iff]
  constructor
  · rintro ⟨value, final, events, execution, resultPost⟩
    exact ⟨value, final, events, execution, (equivalent _ _ _ _).mp resultPost⟩
  · rintro ⟨value, final, events, execution, resultPost⟩
    exact ⟨value, final, events, execution, (equivalent _ _ _ _).mpr resultPost⟩

/-- Strengthening a proved postcondition is an ordinary entailment obligation. -/
theorem wp_mono (operation : Op target parameters Environment α)
    (first second : Post target parameters Environment α)
    (entails : ∀ initial value final events,
      first initial value final events → second initial value final events)
    (initial : State target parameters Environment) :
    WP operation first initial → WP operation second initial := by
  intro condition
  obtain ⟨value, final, events, execution, resultPost⟩ := (wp_iff _ _ _).mp condition
  exact (wp_iff _ _ _).mpr ⟨value, final, events, execution, entails _ _ _ _ resultPost⟩

/-- Choice is lazy: only the operation chosen by this condition is demanded. -/
theorem wp_ite (condition : Prop) [Decidable condition]
    (yes no : Op target parameters Environment α)
    (post : Post target parameters Environment α)
    (initial : State target parameters Environment) :
    WP (if condition then yes else no) post initial ↔
      if condition then WP yes post initial else WP no post initial := by
  split <;> rfl

/-- A useful operation certificate cannot quantify over an empty state domain. -/
structure Certificate (operation : Op target parameters Environment α)
    (admitted : State target parameters Environment → Prop)
    (post : Post target parameters Environment α) : Prop where
  useful : ∃ initial, admitted initial
  verified : Verifies operation admitted post

theorem no_certificate_empty (operation : Op target parameters Environment α)
    (post : Post target parameters Environment α) :
    ¬ Certificate operation (fun _ => False) post := by
  intro certificate
  obtain ⟨_, impossible⟩ := certificate.useful
  exact impossible

/-- Verified successful execution excludes each concrete failure reason;
no useful-state witness is needed for this conditional consequence. -/
theorem Verifies.no_failure {operation : Op target parameters Environment α}
    {admitted : State target parameters Environment → Prop}
    {post : Post target parameters Environment α}
    (verified : Verifies operation admitted post)
    (initial : State target parameters Environment) (permitted : admitted initial)
    (reason : Stop) (final : State target parameters Environment) (events : List Event) :
    operation initial ≠ (.error reason, final, events) := by
  obtain ⟨value, actualFinal, actualEvents, execution, _⟩ := verified initial permitted
  rw [execution]
  intro impossible
  cases impossible

theorem Certificate.no_failure {operation : Op target parameters Environment α}
    {admitted : State target parameters Environment → Prop}
    {post : Post target parameters Environment α} (certificate : Certificate operation admitted post)
    (initial : State target parameters Environment) (permitted : admitted initial)
    (reason : Stop) (final : State target parameters Environment) (events : List Event) :
    operation initial ≠ (.error reason, final, events) :=
  certificate.verified.no_failure initial permitted reason final events

/-- Existing pure certificates transfer with exact state/event frame. An actual
environment value supplies a state witness rather than an empty quantification. -/
theorem pure_certificate {resultType : IntType} (program : Program target parameters resultType)
    (admitted : Inputs target parameters → Prop)
    (post : Inputs target parameters → Value target resultType → Prop)
    (certificate : Source.Certificate program admitted post) (environment : Environment) :
    Certificate (PureEmbedding.evalProgram (Environment := Environment) program).run
      (fun initial => admitted initial.inputs)
      (fun initial value final events =>
        final = initial ∧ events = [] ∧ post initial.inputs value) where
  useful := by
    obtain ⟨inputs, permitted⟩ := certificate.useful
    exact ⟨State.empty inputs environment 0 0, permitted⟩
  verified := by
    intro initial permitted
    obtain ⟨value, execution, resultPost⟩ :=
      PureEmbedding.verifies_embeds program admitted post certificate.verified initial permitted
    exact ⟨value, initial, [], execution, rfl, rfl, resultPost⟩

end EDSL.Source.Objects.Protocol
