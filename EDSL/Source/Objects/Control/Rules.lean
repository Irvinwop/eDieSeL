/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.Contracts

set_option autoImplicit false
namespace EDSL.Source.Objects.Control
open StateSyntax

/-! Sound proof annotations for the existing internal control machine.
The rank never participates in `Code`, `tick`, or expression evaluation.
Admissions remain independent input/resource predicates; actual execution and
postcondition obligations belong in the logical progress premise below.
These rules do not establish function cleanup, source-standard forward
progress/infinite-loop validity, or scheduler fairness. Annotation synthesis,
exactness and completeness are separate from the soundness proved here.
-/

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable {context : List ArithmeticType} {result : IntType}
variable (dialect : Dialect) (policy : IntegerConversionPolicy) (bindings : Env context)
local notation "Configuration" => Config target parameters Environment context result

/-- Every invariant configuration has an actual finite execution segment:
either it returns with the original postcondition, or its endpoint retains
the invariant and strictly decreases a natural rank. In particular, existence
of a completed segment is required, not just decrease *if* a body completes.
The invariant need only hold at these segment boundaries. Entire actual event
histories are retained in the configurations and in the returned postcondition.
-/
def FiniteProgress
    (invariant : State target parameters Environment → Configuration → Prop)
    (rank : Configuration → Nat)
    (post : Protocol.Post target parameters Environment (Value target result)) : Prop :=
  ∀ original config, invariant original config → ∃ steps,
    (∃ value, (run dialect policy bindings steps config).status = .returned value ∧
      post original value (run dialect policy bindings steps config).state
        (run dialect policy bindings steps config).events) ∨
    (invariant original (run dialect policy bindings steps config) ∧
      rank (run dialect policy bindings steps config) < rank config)

variable {code : Code target context result}
variable {admitted : State target parameters Environment → Prop}
variable {post : Protocol.Post target parameters Environment (Value target result)}

/-- Strong induction composes the witnessed segments of the actual machine.
Early return ends the induction even when enclosing control has continuations.
No bound is supplied to executable code, and the original state is fixed for
every segment while its actual final world and complete events are preserved.
-/
theorem returns_of_finiteProgress
    (invariant : State target parameters Environment → Configuration → Prop)
    (rank : Configuration → Nat)
    (progress : FiniteProgress dialect policy bindings invariant rank post)
    (original : State target parameters Environment) (config : Configuration)
    (member : invariant original config) :
    ∃ steps value, (run dialect policy bindings steps config).status = .returned value ∧
      post original value (run dialect policy bindings steps config).state
        (run dialect policy bindings steps config).events := by
  have terminates : ∀ bound, ∀ current : Configuration, rank current = bound →
      invariant original current →
      ∃ steps value, (run dialect policy bindings steps current).status = .returned value ∧
        post original value (run dialect policy bindings steps current).state
          (run dialect policy bindings steps current).events := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound smaller =>
        intro current ranked retained
        obtain ⟨first, finished | ⟨nextMember, decreased⟩⟩ := progress original current retained
        · obtain ⟨value, returned, resultPost⟩ := finished
          exact ⟨first, value, returned, resultPost⟩
        · have lower : rank (run dialect policy bindings first current) < bound := by
            simpa only [ranked] using decreased
          obtain ⟨second, value, returned, resultPost⟩ :=
            smaller _ lower _ rfl nextMember
          refine ⟨first + second, value, ?_, ?_⟩
          · rw [run_add]
            exact returned
          · rw [run_add]
            exact resultPost
  exact terminates _ config rfl member

/-- Initial invariant admission plus actual finite progress proves the existing
total internal contract. In particular, target safety/success/postconditions
are not added to `admitted`. Use checked `Verifies.noFailure`, `.ubSafe`,
`.partial`, and `.supported` for their respective consequences.
-/
theorem verifies_of_finiteProgress
    (invariant : State target parameters Environment → Configuration → Prop)
    (rank : Configuration → Nat)
    (member : ∀ initial, admitted initial → invariant initial (start code initial))
    (progress : FiniteProgress dialect policy bindings invariant rank post) :
    Verifies dialect policy bindings code admitted post := by
  intro initial permitted
  exact returns_of_finiteProgress dialect policy bindings invariant rank progress initial
    (start code initial) (member initial permitted)

/-- A useful independent admission also yields the checked certificate, whose
existing projections derive prefix safety and whole-code coverage.
-/
theorem Certificate.of_finiteProgress (useful : ∃ initial, admitted initial)
    (invariant : State target parameters Environment → Configuration → Prop)
    (rank : Configuration → Nat)
    (member : ∀ initial, admitted initial → invariant initial (start code initial))
    (progress : FiniteProgress dialect policy bindings invariant rank post) :
    Certificate dialect policy bindings code admitted post :=
  ⟨useful, verifies_of_finiteProgress dialect policy bindings invariant rank member progress⟩

/-- A divergent configuration cannot satisfy these progress obligations and
invariant membership, even with an unrestricted postcondition. This also
excludes a divergent body hidden between two proposed loop headers.
-/
theorem FiniteProgress.not_diverges
    {invariant : State target parameters Environment → Configuration → Prop}
    {rank : Configuration → Nat}
    (progress : FiniteProgress dialect policy bindings invariant rank post)
    (original : State target parameters Environment) (config : Configuration)
    (member : invariant original config) :
    ¬ Diverges dialect policy bindings config := by
  intro divergent
  obtain ⟨steps, value, returned, _⟩ :=
    returns_of_finiteProgress dialect policy bindings invariant rank progress original config member
  rw [divergent steps] at returned
  cases returned

end EDSL.Source.Objects.Control
