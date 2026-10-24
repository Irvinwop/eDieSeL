/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.CountedResources.Workers
import EDSL.Corpus.CountedCertificate.Assembly

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Independent counted-call admission over an arbitrary complete named image and
its actual two-attachment output. The remaining image-specific evidence states
five present properties of the actual code and resources, never a future run,
independent Pre, desired result, rank or instruction annotation.

Every physical slot and supplied request is retained. Complete original loaded
cells, including all permissions and inaccessible contents, survive the actual
resource construction and unchanged attachment world. Behavior and progress
still require a separate unrestricted Counted64 Claim for the selected image.
The imported coherent scalar RAM, resource protection, stable translation/no
hidden aliases, represented CPU and long-mode/CET-off assumptions remain.
No native lifetime, physical CPU/OS or source/compiler correspondence follows.
-/

namespace EDSL.Corpus.CountedResources.Loaded
open X86 OS OS.AddressSpace OS.TSO64

namespace Spec
abbrev Entry := Grading.ConcurrentTask.Counted64.Entry
abbrev Pre := Grading.ConcurrentTask.Counted64.Pre
abbrev Post := Grading.ConcurrentTask.Counted64.Post
abbrev Claim := Grading.ConcurrentTask.Counted64.Claim
end Spec

variable {file name : List Byte} {cap : Nat}
variable (named : Counted.NamedImage file name cap) (rx : Image.RX named)
variable (total : Image.Total named) (started : Workers.StartTotal named total)

/-- Image-local obligations about the actual present code and resources.
Success of setup and both attachments is proved separately by their providers;
no future behavior, instruction proof or independent Pre is assumed here. -/
structure Present : Prop where
  nonempty : 0 < named.image.bytes.length
  baseCanonical : canonical named.image.base = true
  fits : ∀ (old : Word) (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (slot : Fin 2),
    Borrowing.Subregion ⟨named.image.base, named.image.bytes.length⟩
      (Workers.worker named total started old count upper flags slot).resources.code.loan.region
  selected : ∀ (old : Word) (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (slot : Fin 2),
    ∃ identifier handle,
      atomicFor (Workers.initial named total started old count upper flags).world
        (Workers.worker named total started old count upper flags slot).resources
        (Image.resources named total old).cell.address =
        some (identifier, handle, (Image.resources named total old).cell) ∧
      handle.cell = (Image.resources named total old).target
  codeCallerSeparation : ∀ (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2),
    Ownership.Disjoint ⟨named.image.base, named.image.bytes.length⟩
      (Workers.worker named total started old count upper flags slot).resources.caller.loan.region

/-- Transport each actual scheduler slot without changing its physical value. -/
def slot2 (old : Word) (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (slot : Fin (Workers.initial named total started old count upper flags).workers.length) : Fin 2 :=
  Fin.cast (Workers.workerUniverse2 named total started old count upper flags) slot

/-- The inverse transport also preserves the physical slot value. -/
def actualSlot (old : Word) (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (slot : Fin 2) :
    Fin (Workers.initial named total started old count upper flags).workers.length :=
  Fin.cast (Workers.workerUniverse2 named total started old count upper flags).symm slot

theorem slot2_val (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word)
    (slot : Fin (Workers.initial named total started old count upper flags).workers.length) :
    (slot2 named total started old count upper flags slot).val = slot.val := rfl

theorem actualSlot_val (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (actualSlot named total started old count upper flags slot).val = slot.val := rfl

theorem slot2_actualSlot (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    slot2 named total started old count upper flags
      (actualSlot named total started old count upper flags slot) = slot := by
  simp only [slot2, actualSlot, Fin.cast_cast, Fin.cast_refl, id_eq]

theorem actualSlot_slot2 (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word)
    (slot : Fin (Workers.initial named total started old count upper flags).workers.length) :
    actualSlot named total started old count upper flags
      (slot2 named total started old count upper flags slot) = slot := by
  simp only [slot2, actualSlot, Fin.cast_cast, Fin.cast_refl, id_eq]

/-- Independent requests use each supplied count at its actual original slot. -/
def requests (old : Word) (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word) :
    Grading.ConcurrentTask.Counted64.Requests
      (Workers.initial named total started old count upper flags) :=
  fun slot => count (slot2 named total started old count upper flags slot)

theorem requests_actualSlot (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    requests named total started old count upper flags
      (actualSlot named total started old count upper flags slot) = count slot :=
  congrArg count (slot2_actualSlot named total started old count upper flags slot)

private theorem stack_facts (slot : Fin 2) :
    ((Workers.stack slot).toNat + 8) % 16 = 0 ∧
    (Workers.stack slot).toNat + 8 < 2^64 ∧
    canonical (Workers.stack slot + 8) = true := by
  rcases slot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl
  · change ((0x700008 : Word).toNat + 8) % 16 = 0 ∧
      (0x700008 : Word).toNat + 8 < 2^64 ∧ canonical ((0x700008 : Word) + 8) = true
    decide +kernel
  · change ((0x710008 : Word).toNat + 8) % 16 = 0 ∧
      (0x710008 : Word).toNat + 8 < 2^64 ∧ canonical ((0x710008 : Word) + 8) = true
    decide +kernel

/-- The independent scalar entry condition uses the actual attached context.
Only DF is constrained; every other modeled flag and high RSI bit remains. -/
theorem worker_scalar (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (clear : ∀ slot, (flags slot).getLsbD 10 = false)
    (slot : Fin 2) :
    ScalarCall64.Entry (Workers.worker named total started old count upper flags slot) := by
  constructor
  · rw [Workers.worker_context]
    exact (stack_facts slot).1
  · rw [Workers.worker_context]
    exact clear slot
  · rw [Workers.worker_context]
    exact (stack_facts slot).2.1
  · rw [Workers.worker_context]
    exact (stack_facts slot).2.2

/-- Actual current caller access follows the retained manager output and the
identities obtained from the actual attachments. -/
theorem caller_read (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    Borrowing.loadWord64
      (Workers.initial named total started old count upper flags).world.legacy.shared
      (Workers.worker named total started old count upper flags slot).resources.actor
      (Workers.worker named total started old count upper flags slot).resources.caller.identifier
      (Workers.worker named total started old count upper flags slot).resources.callerAddress =
      .ok (Workers.continuation slot) := by
  rw [Workers.initial_world, Workers.worker_actor, Workers.worker_callerId,
    Workers.worker_callerAddress]
  rcases slot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl
  · exact (Image.resources named total old).callerReadA
  · exact (Image.resources named total old).callerReadB

theorem continuation_canonical (slot : Fin 2) :
    canonical (Workers.continuation slot) = true := by
  rcases slot with ⟨slot, bound⟩
  have choices : slot = 0 ∨ slot = 1 := by omega
  rcases choices with rfl | rfl
  · change canonical (0x654320 : Word) = true
    decide +kernel
  · change canonical (0x654330 : Word) = true
    decide +kernel

include rx in
/-- Every independent Entry field is established from current setup and actual
worker outputs, with no compiler-indexed annotation contract substituted. -/
theorem worker_entry (present : Present named total started) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (clear : ∀ slot, (flags slot).getLsbD 10 = false) (slot : Fin 2) :
    Spec.Entry named.image (Image.resources named total old).target
      (Image.resources named total old).cell (count slot)
      (Workers.initial named total started old count upper flags)
      (Workers.worker named total started old count upper flags slot) := by
  constructor
  · exact Workers.worker_running named total started old count upper flags slot
  · rw [Workers.worker_context]
    rfl
  · change (Workers.worker named total started old count upper flags slot).context.registers .rdi =
      (Image.resources named total old).cell.address
    rw [Workers.worker_context]
    rfl
  · change ((Workers.worker named total started old count upper flags slot).context.registers .rsi).setWidth 32 =
      count slot
    rw [Workers.worker_context]
    exact BitVec.setWidth_append_eq_right
  · exact Workers.worker_resources named total started old count upper flags slot
  · exact present.nonempty
  · exact present.baseCanonical
  · rw [Workers.initial_world]
    exact Image.code named rx total old
  · exact present.fits old count upper flags slot
  · rw [Workers.worker_context, Workers.worker_callerAddress]
    rfl
  · exact worker_scalar named total started old count upper flags clear slot
  · exact present.selected old count upper flags slot
  · exact ⟨Workers.continuation slot,
      caller_read named total started old count upper flags slot,
      continuation_canonical slot⟩

/-- Caller regions are obtained from current validity and actual addresses,
without requiring a guessed loan descriptor from the provider. -/
theorem caller_region (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (slot : Fin 2) :
    (Workers.worker named total started old count upper flags slot).resources.caller.loan.region =
      qwordRegion (Workers.stack slot) := by
  have region := (Workers.worker_resources named total started old count upper flags slot).2.2.1
  rw [Workers.worker_callerAddress] at region
  exact region

private theorem two_slot_disjoint (regions : Fin 2 → Region)
    (separate : Ownership.Disjoint (regions 0) (regions 1))
    (i j : Fin 2) (different : i ≠ j) :
    Ownership.Disjoint (regions i) (regions j) := by
  rcases i with ⟨i, iBound⟩
  rcases j with ⟨j, jBound⟩
  have iChoices : i = 0 ∨ i = 1 := by omega
  have jChoices : j = 0 ∨ j = 1 := by omega
  rcases iChoices with rfl | rfl <;> rcases jChoices with rfl | rfl
  · exact False.elim (different rfl)
  · exact separate
  · exact Ownership.disjoint_symm (left := regions 0) (right := regions 1) separate
  · exact False.elim (different rfl)

theorem private_slots (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (i j : Fin 2) (different : i ≠ j) :
    Ownership.Disjoint
      (Workers.worker named total started old count upper flags i).resources.caller.loan.region
      (Workers.worker named total started old count upper flags j).resources.caller.loan.region := by
  apply two_slot_disjoint
    (fun slot => (Workers.worker named total started old count upper flags slot).resources.caller.loan.region)
    (i := i) (j := j)
  · rw [caller_region, caller_region]
    change Ownership.Disjoint (⟨0x700008, 8⟩ : Region) ⟨0x710008, 8⟩
    decide +kernel
  · exact different

include rx in
/-- Assemble the unchanged independent Pre from actual present facts. -/
theorem pre (present : Present named total started) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (clear : ∀ slot, (flags slot).getLsbD 10 = false) :
    Spec.Pre named.image (Image.resources named total old).target
      (Image.resources named total old).cell
      (Workers.initial named total started old count upper flags)
      (requests named total started old count upper flags) := by
  refine Counted.pre_of_population named.image
    (Image.resources named total old).target (Image.resources named total old).cell
    (Workers.initial named total started old count upper flags)
    (Workers.workerUniverse2 named total started old count upper flags) count
    (Workers.worker named total started old count upper flags)
    (Workers.wellFormed named total started old count upper flags)
    (Workers.quiescent named total started old count upper flags) ?_ ?_
    (Workers.worker_live named total started old count upper flags)
    (worker_entry named rx total started present old count upper flags clear)
    (private_slots named total started old count upper flags)
    (present.codeCallerSeparation old count upper flags)
  · rw [Workers.initial_world]
    exact (Image.resources named total old).live
  · rw [Workers.initial_world]
    exact ((Image.resources named total old).managed.valid.cells _ _
      (Image.resources named total old).live).2

/-- Actual initial RAM contains the supplied old word at the registered cell. -/
theorem initial_read (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :
    loadQWord (published (Workers.initial named total started old count upper flags).world)
      (Image.resources named total old).cell.address = .ok old := by
  rw [Workers.initial_world, (Image.resources named total old).address]
  exact (Image.resources named total old).initialRead

include rx in
/-- All original optional cells and permission bits survive both attachments. -/
theorem full_image (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) {address : Word} {original : AddressSpace.Cell}
    (live : (Image.installed named).space.cells address = some original) :
    (Workers.initial named total started old count upper flags).world.legacy.shared.resources.space.cells address =
      some original := by
  rw [Workers.initial_world]
  exact Image.full_image named rx total old live

include rx in
/-- Exact complete-file admission and actual present independent Pre. No
completed execution or desired behavioral result is an input to this batch. -/
def loadedBatch (present : Present named total started) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (clear : ∀ slot, (flags slot).getLsbD 10 = false) : Counted.LoadedBatch named where
  priorSpace := empty
  loaded := Image.installed named
  admitted := Image.admitted named
  before := Workers.initial named total started old count upper flags
  target := (Image.resources named total old).target
  cell := (Image.resources named total old).cell
  requests := requests named total started old count upper flags
  pre := pre named rx total started present old count upper flags clear
  text := BufferResources.text_of_retainedWith named.checked rx
    (fun _address _original live => full_image named rx total started old count upper flags live)
  retainedImage := fun _address _original live =>
    full_image named rx total started old count upper flags live
  targetFresh := fun _address _original live => Image.target_fresh named rx total old live

/-- The actual complete slot enumeration projects to the two supplied inputs
in physical order, independently of any observed execution or deltas. -/
private theorem slot2_range (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :
    (List.finRange (Workers.initial named total started old count upper flags).workers.length).map
      (slot2 named total started old count upper flags) = [0, 1] := by
  apply List.ext_getElem
  · simpa only [List.length_map, List.length_finRange, List.length_cons, List.length_nil] using
      Workers.workerUniverse2 named total started old count upper flags
  · intro index left right
    have bound : index < 2 := by simpa only [List.length_cons, List.length_nil] using right
    have choices : index = 0 ∨ index = 1 := by omega
    rw [List.getElem_map, List.getElem_finRange]
    rcases choices with rfl | rfl <;> apply Fin.ext <;> rfl

theorem requested_total (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) :
    Grading.ConcurrentTask.Counted64.requestedTotal
      (requests named total started old count upper flags) =
      (count 0).toNat + (count 1).toNat := by
  calc
    Grading.ConcurrentTask.Counted64.requestedTotal
        (requests named total started old count upper flags) =
        (((List.finRange (Workers.initial named total started old count upper flags).workers.length).map
          (slot2 named total started old count upper flags)).map (fun slot => (count slot).toNat)).sum := by
      rw [List.map_map]
      rfl
    _ = (count 0).toNat + (count 1).toNat := by
      rw [slot2_range]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Supplied inputs determine the modular total of every actual independent
completed Post, rather than an expected value reconstructed from events. -/
theorem loaded_post_total (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) {actions : List Action}
    {actual : TSO64.State × List Observation}
    (post : Spec.Post named.image (Image.resources named total old).target
      (Image.resources named total old).cell
      (Workers.initial named total started old count upper flags)
      (requests named total started old count upper flags) actions actual) :
    post.current.toNat = (old.toNat + (count 0).toNat + (count 1).toNat) % 2^64 := by
  have priorRead := initial_read named total started old count upper flags
  have same : post.old = old := Except.ok.inj (post.oldWord.symm.trans priorRead)
  have supplied := requested_total named total started old count upper flags
  rw [post.total, same, supplied]
  simp only [Nat.add_assoc]

include rx in
/-- A separately proved universal Claim applies to any successful returned
schedule of these actual loaded inputs, preserving the same complete Post. -/
theorem loaded_completed_total (present : Present named total started)
    (claim : Spec.Claim named.image) (old : Word) (count upper : Fin 2 → BitVec 32)
    (flags : Fin 2 → Word) (clear : ∀ slot, (flags slot).getLsbD 10 = false)
    {actions : List Action} {actual : TSO64.State × List Observation}
    (success : schedule (Workers.initial named total started old count upper flags)
      actions .ownedOnly .arithmetic = .ok actual) (returned : Returned actual.1) :
    ∃ post : Spec.Post named.image (Image.resources named total old).target
        (Image.resources named total old).cell
        (Workers.initial named total started old count upper flags)
        (requests named total started old count upper flags) actions actual,
      post.current.toNat = (old.toNat + (count 0).toNat + (count 1).toNat) % 2^64 := by
  obtain ⟨post⟩ := claim.completed
    (Workers.initial named total started old count upper flags)
    (Image.resources named total old).target (Image.resources named total old).cell
    (requests named total started old count upper flags)
    (pre named rx total started present old count upper flags clear)
    actions actual success returned
  exact ⟨post, loaded_post_total named total started old count upper flags
    (actions := actions) (actual := actual) post⟩

end EDSL.Corpus.CountedResources.Loaded

#audit_edsl
