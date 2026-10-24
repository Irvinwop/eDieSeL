/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CountedCertificates.Prepared
import EDSL.Corpus.V1.CountedCertificates.Overlap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 128
set_option maxHeartbeats 300000

/-!
Counted certificates for an explicitly supplied complete named image, using
the actual manager resources and attached workers of CountedResources. Present
preparation constructs the candidate subjects; no future run, desired result
or successful cleanup is a preparation premise. The unrestricted independent
claim is transported only along equality of the selected callable image.

Every supplied old word, upper RSI pair, DF-clear flag pair and AF stream
retains its actual 3/9 own/peer/own overlap, precise cut, current ghosts and
returning suffix. SameOutput supplies the original projections, AF choices,
RET ordering, complete loaded-cell retention and correlated logical cleanup.
The wrapping inhabitant retains both actual current reads of eleven.

The imported coherent scalar RAM, protected resources, stable translation and
no-alias, represented CPU and long-mode/CET-off assumptions remain. These
modeled certificates establish no native join, physical OS/CPU correspondence,
source/compiler refinement, fairness, minimum cost or corpus credit.
-/

namespace EDSL.Corpus.V1.CountedCertificates.PerImage
open X86 OS OS.TSO64

variable {file name : List Byte} {cap : Nat}

/-- One output over the prepared actual subjects and their exact initial
ghosts. The loaded file, current resources and physical worker slots are all
those of the supplied named image; no compiler-indexed file is selected. -/
abbrev Output (named : Counted.NamedImage file name cap)
    (rx : CountedResources.Image.RX named)
    (total : CountedResources.Image.Total named)
    (started : CountedResources.Workers.StartTotal named total)
    (present : CountedResources.Loaded.Present named total started)
    (compiler : CounterCommon.Compiler)
    (imageEq : named.image = CounterCounted.image compiler)
    (old : Word) (upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (choices : Nat → Nat → Bool) :=
  CounterOverlap.Output
    (Prepared.cohort named rx total started present compiler imageEq old
      CounterOverlap.requests upper flags)
    (Prepared.ghosts named rx total started present compiler imageEq old
      CounterOverlap.requests upper flags)
    choices (CountedResources.Image.resources named total old).target
    (CountedResources.Image.resources named total old).cell old

/-- Preserve every independent Claim quantifier. Only the callable image is
transported; no file dispatcher or loaded-resource restriction is introduced. -/
theorem claim (named : Counted.NamedImage file name cap)
    (compiler : CounterCommon.Compiler)
    (imageEq : named.image = CounterCounted.image compiler) :
    Grading.ConcurrentTask.Counted64.Claim named.image := by
  rw [imageEq]
  exact CounterCounted.claim compiler

/-- Construct the production overlap and cleanup for exactly the supplied
actual loaded batch. Cleanup premises concern only current resource identities
and separation; no outcome or future execution is supplied by the caller. -/
theorem loaded_useful_with_cleanup (named : Counted.NamedImage file name cap)
    (rx : CountedResources.Image.RX named)
    (total : CountedResources.Image.Total named)
    (started : CountedResources.Workers.StartTotal named total)
    (present : CountedResources.Loaded.Present named total started)
    (compiler : CounterCommon.Compiler)
    (imageEq : named.image = CounterCounted.image compiler)
    (cleanup : Prepared.CleanupPresent named total started)
    (old : Word) (upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (clear : ∀ slot, (flags slot).getLsbD 10 = false)
    (choices : Nat → Nat → Bool) :
    ∃ output : Output named rx total started present compiler imageEq old upper flags choices,
      Nonempty (SameOutput
        (CountedResources.Loaded.loadedBatch named rx total started present old
          CounterOverlap.requests upper flags clear) output) := by
  let batch : Counted.LoadedBatch named :=
    CountedResources.Loaded.loadedBatch named rx total started present old
      CounterOverlap.requests upper flags clear
  obtain ⟨output⟩ := CounterOverlap.complete_of_subjects
    (Prepared.subjects named rx total started present compiler imageEq old
      CounterOverlap.requests upper flags)
    (Prepared.slots named rx total started present compiler imageEq old
      CounterOverlap.requests upper flags)
    (CountedResources.Workers.wellFormed named total started old
      CounterOverlap.requests upper flags)
    (CountedResources.Workers.workerUniverse2 named total started old
      CounterOverlap.requests upper flags)
    (CountedResources.Workers.quiescent named total started old
      CounterOverlap.requests upper flags)
    (Prepared.cleanupShape named total started present compiler imageEq cleanup old
      CounterOverlap.requests upper flags)
    (cleanup.separate old CounterOverlap.requests upper flags)
    (CountedResources.Image.resources named total old).target
    (CountedResources.Image.resources named total old).cell old
    (Prepared.registered named total started old CounterOverlap.requests upper flags)
    (fun _ => rfl) (fun _ => rfl)
    (Prepared.initial_read named total started old CounterOverlap.requests upper flags)
    (fun slot => CounterOverlap.requests_nat slot) choices
  have population : batch.before.workers.length = 2 :=
    CountedResources.Workers.workerUniverse2 named total started old
      CounterOverlap.requests upper flags
  have amounts : ∀ slot : Fin batch.before.workers.length,
      (batch.requests slot).toNat = if slot.val = 0 then 3 else 9 := by
    intro slot
    exact CounterOverlap.requests_nat
      (CountedResources.Loaded.slot2 named total started old
        CounterOverlap.requests upper flags slot)
  exact ⟨output, useful_of_output batch (claim named compiler imageEq)
    population amounts output⟩

/-- Each input family member has a useful run indexed by its exact new loaded
batch, with both workers still running and unfinished at the real cut. -/
theorem loaded_useful (named : Counted.NamedImage file name cap)
    (rx : CountedResources.Image.RX named)
    (total : CountedResources.Image.Total named)
    (started : CountedResources.Workers.StartTotal named total)
    (present : CountedResources.Loaded.Present named total started)
    (compiler : CounterCommon.Compiler)
    (imageEq : named.image = CounterCounted.image compiler)
    (cleanup : Prepared.CleanupPresent named total started)
    (old : Word) (upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (clear : ∀ slot, (flags slot).getLsbD 10 = false)
    (choices : Nat → Nat → Bool) :
    Nonempty (Counted.UsefulRun
      (CountedResources.Loaded.loadedBatch named rx total started present old
        CounterOverlap.requests upper flags clear)) := by
  obtain ⟨_output, ⟨same⟩⟩ := loaded_useful_with_cleanup named rx total started
    present compiler imageEq cleanup old upper flags clear choices
  exact ⟨same.run⟩

/-- The same output's own and peer slots are the actual physical slots zero
and one. Resource actor identities are not equated with scheduler slots. -/
theorem loaded_useful_slots (named : Counted.NamedImage file name cap)
    (rx : CountedResources.Image.RX named)
    (total : CountedResources.Image.Total named)
    (started : CountedResources.Workers.StartTotal named total)
    (present : CountedResources.Loaded.Present named total started)
    (compiler : CounterCommon.Compiler)
    (imageEq : named.image = CounterCounted.image compiler)
    (old : Word) (upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (clear : ∀ slot, (flags slot).getLsbD 10 = false)
    (choices : Nat → Nat → Bool)
    (output : Output named rx total started present compiler imageEq old upper flags choices)
    (same : SameOutput
      (CountedResources.Loaded.loadedBatch named rx total started present old
        CounterOverlap.requests upper flags clear) output) :
    same.run.own = CountedResources.Loaded.actualSlot named total started old
      CounterOverlap.requests upper flags 0 ∧
    same.run.peer = CountedResources.Loaded.actualSlot named total started old
      CounterOverlap.requests upper flags 1 := by
  constructor
  · apply Fin.ext
    exact same.own
  · apply Fin.ext
    exact same.peer

/-- Specialize only the inhabitant inputs, retaining every AF choice stream.
The full independent Post and this same output's cleanup both read eleven
after the original maximum old word wraps under the supplied 3/9 requests. -/
theorem wrapping_useful (named : Counted.NamedImage file name cap)
    (rx : CountedResources.Image.RX named)
    (total : CountedResources.Image.Total named)
    (started : CountedResources.Workers.StartTotal named total)
    (present : CountedResources.Loaded.Present named total started)
    (compiler : CounterCommon.Compiler)
    (imageEq : named.image = CounterCounted.image compiler)
    (cleanup : Prepared.CleanupPresent named total started)
    (choices : Nat → Nat → Bool) :
    ∃ output : Output named rx total started present compiler imageEq
        wrappingOld wrappingUpper wrappingFlags choices,
      ∃ same : SameOutput
          (CountedResources.Loaded.loadedBatch named rx total started present wrappingOld
            CounterOverlap.requests wrappingUpper wrappingFlags wrappingFlags_clear) output,
        same.run.post.current.toNat = 11 ∧ output.cleanup.value.toNat = 11 := by
  obtain ⟨output, ⟨same⟩⟩ := loaded_useful_with_cleanup named rx total started
    present compiler imageEq cleanup wrappingOld wrappingUpper wrappingFlags
    wrappingFlags_clear choices
  have wrapped : (wrappingOld.toNat + 12) % 2^64 = 11 := by
    change ((0xffffffffffffffff : BitVec 64).toNat + 12) % 2^64 = 11
    decide +kernel
  have cleaned : output.cleanup.value.toNat = 11 := output.cleanup.total.trans wrapped
  have current : same.run.post.current.toNat = 11 := by
    rw [← same.cleanup_current]
    exact cleaned
  exact ⟨output, same, current, cleaned⟩

/-- The caller explicitly supplies the complete external file, exact name,
cap and named image. Universal behavior retains the unrestricted Claim; only
nonvacuity specializes the all-input useful family to the wrapping inputs. -/
def certificate (file name : List Byte) (cap : Nat)
    (named : Counted.NamedImage file name cap)
    (rx : CountedResources.Image.RX named)
    (total : CountedResources.Image.Total named)
    (started : CountedResources.Workers.StartTotal named total)
    (present : CountedResources.Loaded.Present named total started)
    (compiler : CounterCommon.Compiler)
    (imageEq : named.image = CounterCounted.image compiler)
    (cleanup : Prepared.CleanupPresent named total started) :
    Counted.CountedCertificate file name cap where
  named := named
  claim := claim named compiler imageEq
  inhabited := by
    obtain ⟨_output, same, _current, _cleaned⟩ := wrapping_useful named rx total started
      present compiler imageEq cleanup (fun _ _ => false)
    exact ⟨{
      batch := CountedResources.Loaded.loadedBatch named rx total started present wrappingOld
        CounterOverlap.requests wrappingUpper wrappingFlags wrappingFlags_clear
      run := same.run }⟩

#print axioms Output
#print axioms claim
#print axioms loaded_useful_with_cleanup
#print axioms loaded_useful
#print axioms loaded_useful_slots
#print axioms wrapping_useful
#print axioms certificate

end EDSL.Corpus.V1.CountedCertificates.PerImage

#audit_edsl
