/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CountedCertificates.Inputs
import EDSL.Corpus.V1.CountedCertificates.Overlap
import EDSL.Corpus.V1.CountedCertificates.GCCCertificate
import EDSL.Corpus.V1.CountedCertificates.ClangCertificate

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Exact complete-file counted-call certificates for the frozen GCC and Clang
counter workers. The generic contract lives in EDSL.Corpus.CountedCertificate.
Each public constructor uses its own checked image, actual preparation and
same-run overlap/cleanup, reusing the existing instruction and rank proofs.
The compiler-indexed Inputs/Overlap APIs remain compatibility adapters.
-/

namespace EDSL.Corpus.V1.CountedCertificates

/-- Original complete GCC ELF, entire 49-byte symbol and explicit cap64. -/
def gcc : Counted.CountedCertificate GCC.file CounterMixedGraphs.name 64 :=
  GCCCertificate.certificate

/-- Original complete Clang ELF, entire 86-byte symbol and explicit cap128. -/
def clang : Counted.CountedCertificate Clang.file CounterMixedGraphs.name 128 :=
  ClangCertificate.certificate

#print axioms gcc
#print axioms clang
end EDSL.Corpus.V1.CountedCertificates
#audit_edsl
