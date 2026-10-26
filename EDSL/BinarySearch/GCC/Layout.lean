import EDSL.BinarySearch.GCC.Window

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

run_cmd do
  let options ← Lean.getOptions
  unless options.getBool `autoImplicit true == false &&
      options.getBool `warningAsError false == true &&
      options.getBool `Elab.async true == false &&
      options.get `maxHeartbeats (0 : Nat) == 300000 &&
      options.get `maxRecDepth (0 : Nat) == 128 do
    throwError "GCC graph stage: effective options differ from the required profile"
  Lean.logInfo "EFFECTIVE_OPTIONS autoImplicit=false warningAsError=true Elab.async=false maxHeartbeats=300000 maxRecDepth=128"

namespace EDSL.BinarySearch.GCC
open X86 X86.Sequential

/-- Retain every production instruction and boundary. Only the cut/depth
annotations change: the low-update block remains inside the loop window. -/
def layout : CFG.Graph := vcgen_cfg_data
  (⟨graph.nodes.mapIdx (fun index node => { node with
    cutpoint := decide (node.offset = 0 ∨ node.offset = 25)
    depth := ([4,3,2,1,0,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,2,1,0][index]?).getD 0 }),
    13⟩ : CFG.Graph)

theorem layout_checked : CFG.checkWith fullWindowProfile bytes layout = true := by
  decide +kernel

theorem layout_valid : CFG.Valid bytes layout fullWindowProfile :=
  CFG.checkWith_sound layout_checked

abbrev entryIx : layout.Index := ⟨0, by decide +kernel⟩
abbrev loopIx : layout.Index := ⟨9, by decide +kernel⟩

theorem cut_classification : ∀ index : layout.Index,
    layout.cutpoint index = true ↔ index = entryIx ∨ index = loopIx := by
  decide +kernel

theorem only_cuts : ∀ index : layout.Index, layout.cutpoint index = true →
    index = entryIx ∨ index = loopIx := fun index => (cut_classification index).mp

theorem cuts_and_fuel :
    (layout.node entryIx).offset = 0 ∧ (layout.node loopIx).offset = 25 ∧
    layout.depth entryIx + 1 = 5 ∧ layout.depth loopIx + 1 = 14 ∧
    layout.maxDepth = 13 := by decide +kernel

theorem instructions_unchanged :
    layout.nodes.map (fun node => (node.offset, node.instruction)) =
      graph.nodes.map (fun node => (node.offset, node.instruction)) := by decide +kernel

/-- Every one of the original 67 byte positions belongs to a checked positive
instruction span. This uses the production partition theorem. -/
theorem full_partition (position : Nat) (inside : position < 67) :
    ∃ index : layout.Index, (layout.node index).offset ≤ position ∧
      position < (layout.node index).offset + (layout.node index).instruction.length :=
  layout_valid.covers position (by simpa only [complete.1] using inside)

#print axioms layout_checked
#print axioms layout_valid
#print axioms cut_classification
#print axioms full_partition
end EDSL.BinarySearch.GCC
#audit_edsl
