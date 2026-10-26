/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Semantics

set_option autoImplicit false

namespace EDSL.Source

/-- A usable source claim needs an inhabited input domain and a proof of actual
source execution plus the independently stated contract. Conditional `Verifies`
remains useful internally; an empty domain cannot produce this certificate.
Domain and contract independence still require specification review. -/
structure Certificate {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result)
    (admitted : Inputs target parameters → Prop)
    (post : Inputs target parameters → Value target result → Prop) : Prop where
  useful : ∃ inputs, admitted inputs
  verified : Verifies program admitted post

theorem Certificate.noUB {target : Target} {parameters : List IntType} {result : IntType}
    {program : Program target parameters result} {admitted : Inputs target parameters → Prop}
    {post : Inputs target parameters → Value target result → Prop}
    (certificate : Certificate program admitted post) : NoUB program admitted :=
  certificate.verified.noUB

theorem Certificate.defined_behavior
    {target : Target} {parameters : List IntType} {result : IntType}
    {program : Program target parameters result} {admitted : Inputs target parameters → Prop}
    {post : Inputs target parameters → Value target result → Prop}
    (certificate : Certificate program admitted post) :
    ∃ inputs value, admitted inputs ∧ eval program inputs = .defined value ∧ post inputs value := by
  obtain ⟨inputs, permitted⟩ := certificate.useful
  obtain ⟨value, execution, resultPost⟩ := certificate.verified inputs permitted
  exact ⟨inputs, value, permitted, execution, resultPost⟩

theorem no_certificate_for_empty_domain
    {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result)
    (post : Inputs target parameters → Value target result → Prop) :
    ¬ Certificate program (fun _ => False) post := by
  intro certificate
  obtain ⟨_, impossible⟩ := certificate.useful
  exact impossible

end EDSL.Source
