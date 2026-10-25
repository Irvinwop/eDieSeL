import EDSL.X86.VCGen.Proposal

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.BinarySearch.Clang
open X86 X86.Sequential X86.VCGen

/-- The complete unchanged frozen Clang row 33 symbol window, 58 bytes. -/
def bytes : List Byte :=
  [0x48,0x85,0xf6,0x74,0x2d,0x31,0xc9,0x48,0x89,0xf0,0xeb,0x15,
   0x0f,0x1f,0x40,0x00,0x48,0xff,0xc0,0x48,0x89,0xc1,0x48,0x89,
   0xf0,0x48,0x89,0xc6,0x48,0x39,0xc1,0x73,0x11,0x48,0x29,0xc8,
   0x48,0xd1,0xe8,0x48,0x01,0xc8,0x39,0x14,0x87,0x72,0xe1,0x77,
   0xe8,0xc3,0x48,0xc7,0xc0,0xff,0xff,0xff,0xff,0xc3]

/-- Production discovery proposes graph data; Valid rechecks every decoder
result, complete partition, edge, cutpoint and depth in the kernel. -/
def graph : CFG.Graph := vcgen_proposal bytes
theorem valid : CFG.Valid bytes graph := CFG.check_sound (by decide +kernel)
theorem complete : bytes.length = 58 ∧ graph.nodes.length = 21 := by decide +kernel
abbrev entry : graph.Index := ⟨0, by decide +kernel⟩
abbrev loop : graph.Index := ⟨12, by decide +kernel⟩
theorem loop_offset : (graph.node loop).offset = 0x21 := rfl

#print axioms valid
#print axioms complete
end EDSL.BinarySearch.Clang
#audit_edsl
