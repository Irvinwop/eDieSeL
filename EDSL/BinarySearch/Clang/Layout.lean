import EDSL.BinarySearch.Clang.Window

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.BinarySearch.Clang
open X86 X86.Sequential

/-- Only proof annotations are changed from production discovery. Decoder
results, instruction boundaries and the complete byte partition are retained.
The one loop cut is SUB at +0x21; depths describe acyclic block interiors. -/
def layout : CFG.Graph := vcgen_cfg_data
  (⟨graph.nodes.mapIdx (fun index node => { node with
    cutpoint := decide (node.offset = 0 ∨ node.offset = 0x21)
    depth := ([5,4,3,2,1,9,8,7,6,5,4,3,13,12,11,10,9,6,1,2,1][index]?).getD 0 }), 13⟩ : CFG.Graph)

theorem layout_valid : CFG.Valid bytes layout := CFG.check_sound (by decide +kernel)
abbrev entryIx : layout.Index := ⟨0, by decide +kernel⟩
abbrev loopIx : layout.Index := ⟨12, by decide +kernel⟩
theorem only_cuts : ∀ node : layout.Index, layout.cutpoint node = true →
    node = entryIx ∨ node = loopIx := by decide +kernel
theorem loop_cut : layout.cutpoint loopIx = true ∧ (layout.node loopIx).offset = 0x21 := by
  decide +kernel

#print axioms layout_valid
end EDSL.BinarySearch.Clang
#audit_edsl
