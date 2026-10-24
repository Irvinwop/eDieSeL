/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.CountedCertificate
import EDSL.Corpus.BufferResources
import EDSL.Corpus.PlainResources.Image

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Present resources for an arbitrary checked named image in its complete loaded
ELF space. The provider retains the external file, requested name and explicit
byte cap. Exact RX permissions justify the faster function index without
changing any other loaded cell, including inaccessible contents.

Totality is evidence for the actual checked same-image setup at every initial
word. A concrete provider must prove it before constructing resources; it is
not an additional premise of the independent counted Pre or Claim. Resource
identities and target freshness come from the successful checked operation.

These facts retain the imported modeled memory, translation, protection and
logical-authority assumptions. They establish present resources, not an
execution, progress, native ownership or compiler refinement guarantee.
-/

namespace EDSL.Corpus.CountedResources.Image
open X86 OS OS.AddressSpace

variable {file name : List Byte} {maxBytes : Nat}
variable (named : Counted.NamedImage file name maxBytes)

/-- Executable segments carry exactly the permissions used by the index. -/
abbrev RX : Prop :=
  ∀ segment ∈ named.input.table.image.segments,
    segment.permissions.executable = true → segment.permissions = readExecute

/-- The complete original file installed over an empty prior space. -/
def installed : ELF.Loaded :=
  BufferResources.installed file named.input

/-- A faster selected-function index over the complete installed space. -/
def programSpace : Space :=
  BufferResources.programSpace file named.input

/-- Use the actual manager for two callers of the same checked image. -/
def setup (old : Word) :=
  PlainResources.setup (programSpace named) named.image named.image
    PlainResources.standard old

/-- Proved success of the actual setup for every supplied initial word. -/
abbrev Total : Prop :=
  ∀ old : Word, (setup named old).toOption.isSome = true

def resources (total : Total named) (old : Word) :
    PlainResources.Ready (programSpace named) PlainResources.standard old :=
  (setup named old).toOption.get (total old)

/-- Admission keeps the original external file, name and explicit byte cap. -/
theorem admitted :
    named.input.admitWith maxBytes file name empty = .ok (installed named) :=
  BufferResources.admittedWith named.checked

theorem installed_cell (rx : RX named) (index : Nat)
    (bound : index < named.image.bytes.length) :
    (installed named).space.cells (named.image.base + BitVec.ofNat 64 index) =
      some ⟨named.image.bytes[index], readExecute⟩ :=
  BufferResources.installed_cellWith named.checked rx index bound

/-- Equality of whole spaces preserves every original byte and permission. -/
theorem programSpace_eq (rx : RX named) :
    programSpace named = (installed named).space :=
  BufferResources.programSpace_eqWith named.checked rx

theorem resources_setup (total : Total named) (old : Word) :
    setup named old = .ok (resources named total old) :=
  PlainResources.checked_get _ (total old)

/-- Retain the exact optional cell at every originally mapped address,
including non-code cells and contents hidden by their original permissions. -/
theorem full_image (rx : RX named) (total : Total named) (old : Word)
    {address : Word} {original : AddressSpace.Cell}
    (live : (installed named).space.cells address = some original) :
    (resources named total old).managed.world.legacy.shared.resources.space.cells address =
      some original := by
  apply (resources named total old).managed.retained address original
  rw [programSpace_eq named rx]
  exact live

/-- Current executable bytes follow from admission and exact cell retention. -/
theorem code (rx : RX named) (total : Total named) (old : Word) :
    CodeAt (TSO64.published (resources named total old).managed.world)
      named.image.base named.image.bytes := by
  have text := BufferResources.text_of_retainedWith named.checked rx
    (fun _address _original live => full_image named rx total old live)
  exact ELF.FunctionSymbol.admitted_current_codeWith (admitted named) text

/-- The actual registered target is disjoint from every original loaded cell. -/
theorem target_fresh (rx : RX named) (total : Total named) (old : Word)
    {address : Word} {original : AddressSpace.Cell}
    (live : (installed named).space.cells address = some original) :
    ¬ (qwordRegion (resources named total old).cell.address).Contains address := by
  intro inside
  rw [(resources named total old).address] at inside
  have fresh : allUnmapped (installed named).space
      ⟨PlainResources.standard.target, 8⟩ = true := by
    simpa only [programSpace_eq named rx] using
      (resources named total old).freshTarget
  have missing := allUnmapped_inside (installed named).space
    ⟨PlainResources.standard.target, 8⟩ fresh address inside
  rw [live] at missing
  cases missing

#print axioms RX
#print axioms installed
#print axioms programSpace
#print axioms setup
#print axioms Total
#print axioms resources
#print axioms admitted
#print axioms installed_cell
#print axioms programSpace_eq
#print axioms resources_setup
#print axioms full_image
#print axioms code
#print axioms target_fresh

end EDSL.Corpus.CountedResources.Image
#audit_edsl
