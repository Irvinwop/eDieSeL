/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.BufferCall.ELFRefinement
import EDSL.BufferCall.ELFTransport
import EDSL.BufferCall.RegisteredELFCertificate
import EDSL.BinarySearch.LinearRefinement
import EDSL.Audit.Owners

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

#print axioms EDSL.BufferCall.Refinement.semantics
#print axioms EDSL.BufferCall.ELFCertificate.ofRetargetInstalledWith
#print axioms EDSL.BufferCall.ELFCertificate.refine
#print axioms EDSL.BufferCall.ELFCertificate.toRegistered
#print axioms EDSL.BinarySearch.duplicate_second_hit_not_first
#audit_edsl_owners
