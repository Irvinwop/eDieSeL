/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Certificate
import EDSL.Source.Examples

set_option autoImplicit false

namespace EDSL.Source.Examples

/-- All typed inputs remain covered; the witness proves that admission is useful,
without restricting the universal arithmetic and definedness theorem. -/
theorem add_certificate (target : Target) (dialect : Dialect) :
    Certificate (add target dialect) (fun _ => True)
      (fun inputs result => ModularSum target
        (inputs.get .here) (inputs.get (.there .here)) result) where
  useful := ⟨.cons ⟨0, target.modulus_pos⟩ (.cons ⟨0, target.modulus_pos⟩ .nil), trivial⟩
  verified := add_verified target dialect

/-- No result specification can certify this actual zero-division body on all
inputs. This is a safety failure even when the result predicate permits anything. -/
theorem divideByZero_not_certified (target : Target) (dialect : Dialect)
    (post : Inputs target [.uint] → Value target .uint → Prop) :
    ¬ Certificate (divideByZero target dialect) (fun _ => True) post := by
  intro certificate
  let inputs : Inputs target [.uint] := .cons ⟨0, target.modulus_pos⟩ .nil
  exact certificate.verified.excludesUB inputs trivial .divisionByZero
    (divideByZero_undefined target dialect inputs)

/-- Missing memory semantics cannot be turned into a successful source claim. -/
theorem unsupportedReturn_not_certified (target : Target) (dialect : Dialect)
    (post : Inputs target [] → Value target .uint → Prop) :
    ¬ Certificate (unsupportedReturn target dialect) (fun _ => True) post := by
  intro certificate
  exact unsupportedReturn_not_noUB target dialect certificate.noUB

end EDSL.Source.Examples
