/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CountedCertificates.PerImage
import EDSL.Corpus.V1.CountedCertificates.GCCPreparation

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Complete counted-call certificate for this original complete named ELF image.
Current resources and both actual attachments use the compiler-local checked
preparation. Existing instruction and rank proofs supply the unrestricted
independent Claim. The useful execution preserves the same own/peer/own prefix,
current cut/ghosts, AF offsets, returned suffix and production logical cleanup.

The imported coherent scalar RAM, protected-resource, stable-translation/no
hidden-alias and represented-CPU/long-mode/CET-off assumptions remain. These
model proofs establish no physical CPU/Linux or compiler correspondence, native
lifetime, fairness, minimum cost, installed grading or corpus credit.
-/

namespace EDSL.Corpus.V1.CountedCertificates.GCCCertificate
open X86 OS OS.TSO64 OS.AddressSpace

private abbrev named := GCCAdmission.named
private abbrev rx := GCCAdmission.rx
private abbrev total := GCCAdmission.total
private abbrev started := GCCPreparation.started
private abbrev present := GCCPreparation.present

/-- The original checked complete extent is the existing behavioral image. -/
theorem image_eq : named.image = CounterCounted.image .defaultGCC := by
  buffer_resource_kernel_rfl

private theorem codeId_eq (old : Word) (slot : Fin 2) :
    CountedResources.Workers.codeId named total old slot = slot.val := by
  rcases slot with ⟨slot, bound⟩
  have alternatives : slot = 0 ∨ slot = 1 := by omega
  rcases alternatives with rfl | rfl <;> buffer_resource_kernel_rfl

private theorem callerId_eq (old : Word) (slot : Fin 2) :
    CountedResources.Workers.callerId named total old slot = slot.val + 2 := by
  rcases slot with ⟨slot, bound⟩
  have alternatives : slot = 0 ∨ slot = 1 := by omega
  rcases alternatives with rfl | rfl <;> buffer_resource_kernel_rfl

private theorem atomicId_eq (old : Word) (slot : Fin 2) :
    CountedResources.Workers.atomicId named total old slot = ⟨slot.val⟩ := by
  rcases slot with ⟨slot, bound⟩
  have alternatives : slot = 0 ∨ slot = 1 := by omega
  rcases alternatives with rfl | rfl <;> buffer_resource_kernel_rfl

/-- Only present resource inequalities and manifests are required here.
Actual retirement success is derived later from the same returned execution. -/
theorem cleanup : Prepared.CleanupPresent named total started where
  codeCallerDistinct := by
    intro old count upper flags slot
    rw [CountedResources.Workers.worker_codeId, CountedResources.Workers.worker_callerId,
      codeId_eq, callerId_eq]
    omega
  separate := by
    intro old count upper flags
    rw [Prepared.workers_list]
    have distinct : Lifecycle.Separate
        (CountedResources.Workers.worker named total started old count upper flags 1).resources
        (CountedResources.Workers.worker named total started old count upper flags 0).resources := by
      simp [Lifecycle.Separate, CountedResources.Workers.worker_codeId,
        CountedResources.Workers.worker_callerId, CountedResources.Workers.worker_atomics,
        codeId_eq, callerId_eq, atomicId_eq]
    simpa using distinct

/-- All supplied old words, upper RSI halves, DF-clear flags and AF streams
retain one actual loaded overlap and its correlated cleanup. -/
abbrev loaded_useful_with_cleanup (old : Word) (upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (clear : ∀ slot, (flags slot).getLsbD 10 = false)
    (choices : Nat → Nat → Bool) :=
  PerImage.loaded_useful_with_cleanup named rx total started present .defaultGCC image_eq cleanup
    old upper flags clear choices

abbrev loaded_useful (old : Word) (upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (clear : ∀ slot, (flags slot).getLsbD 10 = false)
    (choices : Nat → Nat → Bool) :=
  PerImage.loaded_useful named rx total started present .defaultGCC image_eq cleanup
    old upper flags clear choices

abbrev wrapping_useful (choices : Nat → Nat → Bool) :=
  PerImage.wrapping_useful named rx total started present .defaultGCC image_eq cleanup choices

/-- Exact original complete file, requested symbol and explicit byte cap. -/
def certificate : Counted.CountedCertificate GCC.file CounterMixedGraphs.name 64 :=
  PerImage.certificate GCC.file CounterMixedGraphs.name 64
    named rx total started present .defaultGCC image_eq cleanup

#print axioms image_eq
#print axioms codeId_eq
#print axioms callerId_eq
#print axioms atomicId_eq
#print axioms cleanup
#print axioms loaded_useful_with_cleanup
#print axioms loaded_useful
#print axioms wrapping_useful
#print axioms certificate

end EDSL.Corpus.V1.CountedCertificates.GCCCertificate
#audit_edsl
