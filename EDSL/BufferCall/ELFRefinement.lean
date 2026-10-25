/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.BufferCall.ELFCertificate
import EDSL.BufferCall.Refinement

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.BufferCall

/-- Reuse the same complete named-file binding and machine proof under another
independent contract. The target supplies its own useful loaded-resource call;
stronger domain restrictions do not imply useful-domain nonvacuity. The exact
file, requested name, checked input and selected byte bound remain identical.
Trusted grader registration continues to fix the required complete Spec. -/
def ELFCertificate.refine {source target : Spec} {file name : List X86.Byte}
    {maxBytes : Nat} (certificate : ELFCertificate source file name maxBytes)
    (refinement : Refinement source target)
    (call : ELFLoadedCall target file name certificate.input maxBytes)
    (useful : target.useful call.resource.value) : ELFCertificate target file name maxBytes :=
  ELFCertificate.ofLoadedCallWith maxBytes certificate.input certificate.checked
    (refinement.semantics certificate.semantics) call useful

#print axioms ELFCertificate.refine
end EDSL.BufferCall
