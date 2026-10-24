/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.CountedResources.Loaded
import EDSL.Corpus.V1.CounterCounted.Claim
import EDSL.Corpus.V1.CounterCompletion
import EDSL.Corpus.V1.CounterRetirement

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Bridge an explicit named image and its actual successful attachments to the
small shared counter instruction and rank infrastructure. Image equality
transports only the code window: workers, resource identities, protected
caller reads, atomic selection and the world remain the actual operation
outputs. There is no compiler-indexed file, input or loaded-state selection.

Every original count, upper RSI half and modeled flag word is retained.
Cleanup evidence describes only current resource identities and separation;
it assumes no future execution, return, result or successful retirement.
Counts remain a parameter so overlap callers can specialize their requests
without an import cycle.

The imported represented-memory, long-mode/CET-off, coherent scalar RAM,
stable-translation/no-hidden-alias, protected-resource and logical-authority
assumptions remain. This module establishes present admission, population and
initial ghosts, not native execution or physical CPU/OS/compiler refinement.
-/

namespace EDSL.Corpus.V1.CountedCertificates.Prepared
open X86 OS OS.AddressSpace OS.TSO64 OS.TSO64.EffectSimulation
open CountedResources

variable {file name : List Byte} {cap : Nat}
variable (named : Counted.NamedImage file name cap) (rx : Image.RX named)
variable (total : Image.Total named) (started : Workers.StartTotal named total)
variable (present : Loaded.Present named total started)
variable (compiler : CounterCommon.Compiler)
variable (imageEq : named.image = CounterCounted.image compiler)

/-- Current cleanup inputs concern the actual attached workers. No future
behavior or successful resource retirement is a field of this record. -/
structure CleanupPresent : Prop where
  codeCallerDistinct : ∀ (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2),
    (Workers.worker named total started old count upper flags slot).resources.code.identifier ≠
      (Workers.worker named total started old count upper flags slot).resources.caller.identifier
  separate : ∀ (old : Word) (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word),
    (Workers.initial named total started old count upper flags).workers.reverse.Pairwise
      (fun retiring peer => Lifecycle.Separate retiring.resources peer.resources)

/-- Use the actual original worker at its original physical scheduler slot. -/
def site (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) : CounterCommon.Site compiler where
  profile := .ownedOnly
  tid := slot.val
  original := Workers.worker named total started old count upper flags slot
  codeLoan := by
    have fits := present.fits old count upper flags slot
    rw [imageEq] at fits
    exact fits

/-- The call retains the supplied count and the actual resource target. -/
def call (old : Word) (count : Fin 2 → BitVec 32) (slot : Fin 2) : CounterCommon.Call where
  address := (Image.resources named total old).cell.address
  iterations := count slot
  target := (Image.resources named total old).target
  returnAddress := Workers.continuation slot

theorem site_profile (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (site named total started present compiler imageEq old count upper flags slot).profile = .ownedOnly := rfl

theorem site_slot (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (site named total started present compiler imageEq old count upper flags slot).tid = slot.val := rfl

include rx in
/-- Assemble shared Pre from actual present facts and the local code equality.
In particular the ordered selector and caller word use the unchanged world. -/
theorem pre (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    CounterCommon.Pre
      (site named total started present compiler imageEq old count upper flags slot)
      (call named total old count slot)
      (Workers.initial named total started old count upper flags) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact Workers.wellFormed named total started old count upper flags
    · exact Workers.worker_live named total started old count upper flags slot
    · exact Workers.worker_running named total started old count upper flags slot
    · change CodeAt (published (Workers.initial named total started old count upper flags).world)
        (CounterCommon.base compiler) (CounterMixedGraphs.bytes compiler)
      rw [Workers.initial_world]
      have code := Image.code named rx total old
      rw [imageEq] at code
      exact code
    · exact Loaded.caller_read named total started old count upper flags slot
  · change (Workers.worker named total started old count upper flags slot).context.rip =
      CounterCommon.base compiler
    rw [Workers.worker_context]
    change named.image.base = CounterCommon.base compiler
    exact congrArg ScalarCall64.Image.base imageEq
  · change (Workers.worker named total started old count upper flags slot).context.registers .rdi =
      (Image.resources named total old).cell.address
    rw [Workers.worker_context]
    rfl
  · exact Workers.worker_count named total started old count upper flags slot
  · change (Workers.worker named total started old count upper flags slot).context.registers .rsp =
      (Workers.worker named total started old count upper flags slot).resources.callerAddress
    rw [Workers.worker_context, Workers.worker_callerAddress]
    rfl
  · exact Loaded.continuation_canonical slot
  · obtain ⟨identifier, handle, selected, linked⟩ := present.selected old count upper flags slot
    exact ⟨identifier, handle, (Image.resources named total old).cell, selected, linked⟩

/-- Enumerate actual output projections without constructing replacement loans.
This lets image-local providers prove reverse separation using current IDs. -/
theorem workers_list (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :
    (Workers.initial named total started old count upper flags).workers =
      [Workers.worker named total started old count upper flags 0,
       Workers.worker named total started old count upper flags 1] := by
  apply List.ext_getElem
  · simpa only [List.length_cons, List.length_nil] using
      Workers.workerUniverse2 named total started old count upper flags
  · intro index left right
    have bound : index < 2 := by simpa only [List.length_cons, List.length_nil] using right
    have choices : index = 0 ∨ index = 1 := by omega
    rcases choices with rfl | rfl <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> rfl

/-- Singleton atomics come from successful attachment; only the actual current
code/caller identifier inequality is supplied by cleanup evidence. -/
theorem cleanupShape (cleanup : CleanupPresent named total started) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) (slot : Fin 2) :
    CounterCommon.CleanupShape
      (site named total started present compiler imageEq old count upper flags slot) := by
  change ∃ identifier,
    (Workers.worker named total started old count upper flags slot).resources.atomics = [identifier] ∧
    (Workers.worker named total started old count upper flags slot).resources.code.identifier ≠
      (Workers.worker named total started old count upper flags slot).resources.caller.identifier
  exact ⟨Workers.atomicId named total old slot,
    Workers.worker_atomics named total started old count upper flags slot,
    cleanup.codeCallerDistinct old count upper flags slot⟩

/-- Both attachments preserve the actual manager's registered target cell. -/
theorem registered (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :
    (Workers.initial named total started old count upper flags).world.cells
      (Image.resources named total old).target = some (Image.resources named total old).cell := by
  rw [Workers.initial_world]
  exact (Image.resources named total old).live

/-- Read the supplied old word from actual initial RAM at the actual cell. -/
theorem initial_read (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :
    loadQWord (published (Workers.initial named total started old count upper flags).world)
      (Image.resources named total old).cell.address = .ok old :=
  Loaded.initial_read named total started old count upper flags

/-- Subjects preserve each exact site, actual call and derived present Pre. -/
def subjects (old : Word) (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    Fin 2 → CounterCommon.CohortSubject
      (Workers.initial named total started old count upper flags) :=
  fun slot => {
    compiler := compiler
    site := site named total started present compiler imageEq old count upper flags slot
    call := call named total old count slot
    pre := pre named rx total started present compiler imageEq old count upper flags slot
    ownedOnly := rfl }

theorem slots (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (i : Fin 2) :
    (subjects named rx total started present compiler imageEq old count upper flags i).site.tid = i.val := rfl

/-- Keep counts explicit; overlap callers pass their independently fixed requests. -/
abbrev cohort (old : Word) (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :=
  CounterCommon.counterRankedCohort
    (subjects named rx total started present compiler imageEq old count upper flags)
    (slots named rx total started present compiler imageEq old count upper flags)

/-- Initial proof state uses the same actual subjects and physical slots. -/
abbrev ghosts (old : Word) (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :=
  CounterCommon.counterInitialGhosts
    (subjects named rx total started present compiler imageEq old count upper flags)
    (slots named rx total started present compiler imageEq old count upper flags)

#print axioms CleanupPresent
#print axioms site
#print axioms call
#print axioms site_profile
#print axioms site_slot
#print axioms pre
#print axioms workers_list
#print axioms cleanupShape
#print axioms registered
#print axioms initial_read
#print axioms subjects
#print axioms slots
#print axioms cohort
#print axioms ghosts

end EDSL.Corpus.V1.CountedCertificates.Prepared

#audit_edsl
