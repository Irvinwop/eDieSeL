/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.CountedResources.Loaded
import EDSL.Corpus.V1.CountedCertificates.GCCAdmission

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Actual two-worker preparation for this one complete checked image. The old64,
independent requested low32 counts, high32 RSI halves and initial flags remain
arbitrary. Successful setup and both production attachments are proved here;
they are not premises added to the independent counted program contract.

These are present resources and independently admitted loaded batches, not a
useful overlapping execution, a complete certificate or installed grading.
The coherent scalar RAM, protected-resource, stable-translation/no-alias and
represented-CPU/long-mode/CET-off assumptions of the model remain in force.
-/

namespace EDSL.Corpus.V1.CountedCertificates.GCCPreparation
open X86 OS OS.TSO64 OS.AddressSpace

private abbrev named := GCCAdmission.named
private abbrev total := GCCAdmission.total

/-- Both actual attachments succeed for every supplied contextual input. -/
theorem started : CountedResources.Workers.StartTotal named total := by
  intro old count upper flags
  buffer_resource_kernel_rfl

/-- Five current-state obligations for the generic independent entry builder.
Each selection refers to the actual attached worker and actual registered cell. -/
theorem present : CountedResources.Loaded.Present named total started where
  nonempty := by decide +kernel
  baseCanonical := by decide +kernel
  fits := by
    intro old count upper flags slot
    have region : (CountedResources.Workers.worker named total started old count upper flags slot).resources.code.loan.region =
        (⟨named.image.base, named.image.bytes.length⟩ : Region) := by
      rcases slot with ⟨slot, bound⟩
      have alternatives : slot = 0 ∨ slot = 1 := by omega
      rcases alternatives with rfl | rfl <;> buffer_resource_kernel_rfl
    rw [region]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  selected := by
    intro old count upper flags slot
    apply Exists.intro (CountedResources.Workers.atomicId named total old slot)
    apply Exists.intro (show Atomics64.Handle from
      ⟨CountedResources.Workers.actor slot, (CountedResources.Image.resources named total old).target⟩)
    constructor
    · rw [CountedResources.Workers.initial_world]
      unfold atomicFor
      rw [CountedResources.Workers.worker_atomics, CountedResources.Workers.worker_actor]
      rcases slot with ⟨slot, bound⟩
      have alternatives : slot = 0 ∨ slot = 1 := by omega
      rcases alternatives with rfl | rfl <;> buffer_resource_kernel_rfl
    · buffer_resource_kernel_rfl
  codeCallerSeparation := by
    intro old count upper flags slot
    have region := (CountedResources.Workers.worker_resources
      named total started old count upper flags slot).2.2.1
    rw [CountedResources.Workers.worker_callerAddress] at region
    rw [region]
    rcases slot with ⟨slot, bound⟩
    have alternatives : slot = 0 ∨ slot = 1 := by omega
    rcases alternatives with rfl | rfl
    · change Ownership.Disjoint (⟨4207440, 49⟩ : Region) ⟨0x700008, 8⟩
      decide +kernel
    · change Ownership.Disjoint (⟨4207440, 49⟩ : Region) ⟨0x710008, 8⟩
      decide +kernel

/-- The independent Pre, exact file retention and target freshness for every
supplied input, indexed by the actual two-attachment output state. -/
abbrev loadedBatch (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (clear : ∀ slot, (flags slot).getLsbD 10 = false) :
    Counted.LoadedBatch GCCAdmission.named :=
  CountedResources.Loaded.loadedBatch named GCCAdmission.rx total started present
    old count upper flags clear

#print axioms started
#print axioms present
#print axioms loadedBatch

end EDSL.Corpus.V1.CountedCertificates.GCCPreparation
#audit_edsl
