/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterProofBundle

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Compatibility selection for clients quantified over both frozen compilers.
Canonical per-image certificates pass their compiler-local provider explicitly.
This dispatcher deliberately retains both behavior-proof families. -/
namespace EDSL.Corpus.V1.CounterCommon

/-- Legacy compiler-family selection; explicit-provider clients bypass it. -/
def checkedProofProvider (compiler : Compiler) : ProofProvider compiler := by
  cases compiler with
  | defaultGCC => exact CounterGCC.proofBundle
  | defaultClang => exact CounterClang.proofBundle

#print axioms checkedProofProvider
end EDSL.Corpus.V1.CounterCommon
#audit_edsl
