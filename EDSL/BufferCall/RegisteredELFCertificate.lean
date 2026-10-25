/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.BufferCall.ELFCertificate
import EDSL.Corpus.BufferCertificate

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

/-! An exact wrapper around the existing fixed Corpus.Buffer.Certificate.
The trusted ID is supplied explicitly and its ENTIRE registered Spec must equal
the neutral certificate's Spec. There is no refinement/coercion from a weaker
candidate result, domain, bindings, snapshots or usefulness. This module changes
no registry: binary search has no TaskID at the pinned revision. -/

namespace EDSL.BufferCall
open X86

/-- Recover the existing fixed certificate only under exact spec equality to
this same trusted ID. Useful witness, complete file/name, bound and bytes stay
identical. The equality is a trusted registration obligation, not a symbol lookup. -/
def ELFCertificate.toRegistered {spec : Spec} {file name : List Byte} {maxBytes : Nat}
    (certificate : ELFCertificate spec file name maxBytes)
    (id : Grading.BufferTask.TaskID)
    (sameSpec : spec = Grading.BufferTask.registeredSpec id) :
    Corpus.Buffer.Certificate id file name maxBytes := by
  subst spec
  refine ⟨certificate.input, certificate.checked,
    ⟨certificate.semantics, certificate.nonvacuous⟩, ?_⟩
  obtain ⟨call, useful⟩ := certificate.inhabited
  exact ⟨⟨call.prior, call.loaded, call.admitted, call.resource, call.initial,
    useful, call.pre, call.entry, call.text, call.retainedImage⟩⟩

/-- Forget only registration packaging, retaining precisely the original fixed
Spec. This does not convert between different task identities or contracts. -/
def ELFCertificate.ofRegistered {id : Grading.BufferTask.TaskID}
    {file name : List Byte} {maxBytes : Nat}
    (certificate : Corpus.Buffer.Certificate id file name maxBytes) :
    ELFCertificate (Grading.BufferTask.registeredSpec id) file name maxBytes := by
  refine ⟨certificate.input, certificate.checked, certificate.claim.1, ?_⟩
  obtain ⟨call⟩ := certificate.inhabited
  exact ⟨⟨call.prior, call.loaded, call.admitted, call.resource, call.initial,
    call.pre, call.entry, call.text, call.retainedImage⟩, call.useful⟩

/-- Conversion preserves the exact checker input, not merely equal code bytes. -/
theorem ELFCertificate.toRegistered_input {id : Grading.BufferTask.TaskID}
    {file name : List Byte} {maxBytes : Nat}
    (certificate : ELFCertificate (Grading.BufferTask.registeredSpec id) file name maxBytes) :
    (certificate.toRegistered id rfl).input = certificate.input := rfl

end EDSL.BufferCall
