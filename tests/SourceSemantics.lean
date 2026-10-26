/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Certificates
import EDSL.Audit.Owners

set_option autoImplicit false
set_option warningAsError true

#print axioms EDSL.Source.Examples.add_verified
#print axioms EDSL.Source.Examples.add_certificate
#print axioms EDSL.Source.Examples.divideByZero_not_certified
#print axioms EDSL.Source.Examples.overflowingAdd_undefined
#print axioms EDSL.Source.Examples.underflowingAdd_undefined
#print axioms EDSL.Source.Examples.overflowingDiv_undefined
#print axioms EDSL.Source.Examples.negativeDiv_defined
#print axioms EDSL.Source.Examples.unsupportedReturn_not_certified
#print axioms EDSL.Source.no_certificate_for_empty_domain
#audit_edsl_owners
