/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.VCGen

set_option autoImplicit false

namespace EDSL.Source

/-- Program success means complete modeled syntax and actual raw execution.
Coverage checking is a tool phase; it does not execute either select arm. -/
theorem eval_defined_iff {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result) (inputs : Inputs target parameters)
    (value : Value target result) :
    eval program inputs = .defined value ↔
      program.body.Supported ∧
        evalExpr program.conversions inputs program.body = .defined value := by
  cases coverage : program.body.firstUnsupported <;>
    simp [eval, Expr.Supported, coverage]

theorem eval_of_supported {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result) (inputs : Inputs target parameters)
    (supported : program.body.Supported) :
    eval program inputs = evalExpr program.conversions inputs program.body := by
  change program.body.firstUnsupported = none at supported
  simp only [eval, supported]

/-- Inhabitation makes whole-body coverage a consequence of every public
certificate, including coverage of branches never executed on its inputs. -/
theorem Certificate.supported {target : Target} {parameters : List IntType} {result : IntType}
    {program : Program target parameters result} {admitted : Inputs target parameters → Prop}
    {post : Inputs target parameters → Value target result → Prop}
    (certificate : Certificate program admitted post) : program.body.Supported := by
  obtain ⟨inputs, permitted⟩ := certificate.useful
  obtain ⟨value, execution, _⟩ := certificate.verified inputs permitted
  exact ((eval_defined_iff program inputs value).mp execution).1

theorem Certificate.raw_verified {target : Target} {parameters : List IntType} {result : IntType}
    {program : Program target parameters result} {admitted : Inputs target parameters → Prop}
    {post : Inputs target parameters → Value target result → Prop}
    (certificate : Certificate program admitted post) :
    ∀ inputs, admitted inputs → ∃ value,
      evalExpr program.conversions inputs program.body = .defined value ∧ post inputs value := by
  intro inputs permitted
  obtain ⟨value, execution, resultPost⟩ := certificate.verified inputs permitted
  exact ⟨value, ((eval_defined_iff program inputs value).mp execution).2, resultPost⟩

theorem no_certificate_with_unsupported
    {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result) (admitted : Inputs target parameters → Prop)
    (post : Inputs target parameters → Value target result → Prop)
    (feature : UnsupportedFeature) (coverage : program.body.firstUnsupported = some feature) :
    ¬ Certificate program admitted post := by
  intro certificate
  have supported := certificate.supported
  change program.body.firstUnsupported = none at supported
  rw [coverage] at supported
  cases supported

/-- Public certification combines structural coverage, nonvacuity, and exact
raw execution VCs. An unselected modeled UB arm need not satisfy a runtime VC. -/
theorem certificate_iff_supported_useful_raw_vc
    {target : Target} {parameters : List IntType} {result : IntType}
    (program : Program target parameters result) (admitted : Inputs target parameters → Prop)
    (post : Inputs target parameters → Value target result → Prop) :
    Certificate program admitted post ↔
      program.body.Supported ∧ (∃ inputs, admitted inputs) ∧
        ∀ inputs, admitted inputs →
          vcExpr program.conversions inputs program.body (post inputs) := by
  constructor
  · intro certificate
    refine ⟨certificate.supported, certificate.useful, ?_⟩
    intro inputs permitted
    obtain ⟨value, execution, resultPost⟩ := certificate.raw_verified inputs permitted
    apply (vcExpr_iff program.conversions inputs program.body (post inputs)).mpr
    exact (Outcome.requires_iff _ _).mpr ⟨value, execution, resultPost⟩
  · rintro ⟨supported, useful, condition⟩
    apply certificate_of_vc useful
    intro inputs permitted
    change program.body.firstUnsupported = none at supported
    change (match program.body.firstUnsupported with
      | none => vcExpr program.conversions inputs program.body (post inputs)
      | some _ => False)
    rw [supported]
    exact condition inputs permitted

end EDSL.Source
