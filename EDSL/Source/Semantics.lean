/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Semantics
import EDSL.Source.Eval

set_option autoImplicit false

namespace EDSL.Source

/-- The generic interface exposes exactly the actual executable outcome. -/
def semantics (target : Target) (parameters : List IntType) (result : IntType) :
    EDSL.Semantics (Program target parameters result) (Inputs target parameters)
      (Outcome (Value target result)) where
  behaves program inputs observation := eval program inputs = observation

theorem hasBehavior {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result)
    (admitted : Inputs target parameters → Prop) :
    EDSL.HasBehavior (semantics target parameters result) program admitted := by
  intro inputs _
  exact ⟨eval program inputs, rfl⟩

theorem behavior_unique {target : Target} {parameters : List IntType} {result : IntType}
    {program : Program target parameters result} {inputs : Inputs target parameters}
    {first second : Outcome (Value target result)}
    (hfirst : (semantics target parameters result).behaves program inputs first)
    (hsecond : (semantics target parameters result).behaves program inputs second) :
    first = second := hfirst.symm.trans hsecond

/-- Verification requires an actual successful evaluation for every admitted
external valuation, together with an independently supplied result predicate.
No UB-freedom/definedness premise is accepted in place of that execution proof. -/
def Verifies {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result)
    (admitted : Inputs target parameters → Prop)
    (post : Inputs target parameters → Value target result → Prop) : Prop :=
  ∀ inputs, admitted inputs →
    ∃ value, eval program inputs = .defined value ∧ post inputs value

/-- Completion safety for this finite fragment: there must be a defined result.
This intentionally rejects unsupported outcomes as well as UB. -/
def NoUB {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result)
    (admitted : Inputs target parameters → Prop) : Prop :=
  ∀ inputs, admitted inputs → ∃ value, eval program inputs = .defined value

theorem Verifies.noUB {target : Target} {parameters : List IntType} {result : IntType}
    {program : Program target parameters result} {admitted : Inputs target parameters → Prop}
    {post : Inputs target parameters → Value target result → Prop}
    (verified : Verifies program admitted post) : NoUB program admitted := by
  intro inputs permitted
  obtain ⟨value, execution, _⟩ := verified inputs permitted
  exact ⟨value, execution⟩

theorem Verifies.excludesUB {target : Target} {parameters : List IntType} {result : IntType}
    {program : Program target parameters result} {admitted : Inputs target parameters → Prop}
    {post : Inputs target parameters → Value target result → Prop}
    (verified : Verifies program admitted post) (inputs : Inputs target parameters)
    (permitted : admitted inputs) (reason : UBReason) :
    eval program inputs ≠ .undefined reason := by
  obtain ⟨value, execution⟩ := verified.noUB inputs permitted
  rw [execution]
  intro impossible
  cases impossible

theorem Verifies.excludesUnsupported
    {target : Target} {parameters : List IntType} {result : IntType}
    {program : Program target parameters result} {admitted : Inputs target parameters → Prop}
    {post : Inputs target parameters → Value target result → Prop}
    (verified : Verifies program admitted post) (inputs : Inputs target parameters)
    (permitted : admitted inputs) (feature : UnsupportedFeature) :
    eval program inputs ≠ .unsupported feature := by
  obtain ⟨value, execution⟩ := verified.noUB inputs permitted
  rw [execution]
  intro impossible
  cases impossible

theorem Verifies.satisfies {target : Target} {parameters : List IntType} {result : IntType}
    {program : Program target parameters result} {admitted : Inputs target parameters → Prop}
    {post : Inputs target parameters → Value target result → Prop}
    (verified : Verifies program admitted post) :
    EDSL.Satisfies (semantics target parameters result) program admitted
      (fun inputs observation => match observation with
        | .defined value => post inputs value
        | .undefined _ => False
        | .unsupported _ => False) := by
  intro inputs permitted observation behavior
  obtain ⟨value, execution, resultPost⟩ := verified inputs permitted
  have same : observation = .defined value := behavior.symm.trans execution
  cases same
  exact resultPost

end EDSL.Source
