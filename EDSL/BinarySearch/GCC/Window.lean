import EDSL.X86.VCGen.Proposal
import EDSL.BinarySearch.Contract

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
open X86 X86.Sequential X86.VCGen

/-- The complete original frozen GCC row 33 symbol: no removed prefix,
padding, immediate bytes, or return instruction. -/
def bytes : List Byte :=
  [0xf3,0x0f,0x1e,0xfa,0x48,0x85,0xf6,0x74,0x32,0x31,0xc9,0xeb,
   0x0c,0x0f,0x1f,0x00,0x48,0x8d,0x48,0x01,0x48,0x39,0xf1,0x73,
   0x22,0x48,0x89,0xf0,0x48,0x29,0xc8,0x48,0xd1,0xe8,0x48,0x01,
   0xc8,0x44,0x8b,0x04,0x87,0x41,0x39,0xd0,0x72,0xe2,0x44,0x39,
   0xc2,0x73,0x0f,0x48,0x89,0xc6,0x48,0x39,0xf1,0x72,0xde,0x48,
   0xc7,0xc0,0xff,0xff,0xff,0xff,0xc3]

/-- Only the explicitly selected static byte window exceeds the public default. -/
def fullWindowProfile : CFG.Profile := ⟨128, 32, by decide +kernel⟩

/-- The current shared Proposal helper reifies production discovery as data.
An unsuccessful proposal produces an empty candidate, which cannot pass Valid. -/
def graph : CFG.Graph := vcgen_cfg_data
  ((CFG.discoverWith fullWindowProfile bytes).getD ⟨[], 0⟩)

theorem graph_checked : CFG.checkWith fullWindowProfile bytes graph = true := by
  decide +kernel

theorem valid : CFG.Valid bytes graph fullWindowProfile :=
  CFG.checkWith_sound graph_checked

/-- Independently recorded objdump boundaries of the entire frozen symbol. -/
theorem full_boundaries : bytes.length = 67 ∧
    graph.nodes.map CFG.Node.offset =
      [0,4,7,9,11,13,16,20,23,25,28,31,34,37,41,44,46,49,51,54,57,59,66] := by
  decide +kernel

theorem complete : bytes.length = 67 ∧ graph.nodes.length = 23 := by decide +kernel

#print axioms graph_checked
#print axioms valid
#print axioms full_boundaries
end EDSL.BinarySearch.GCC
#audit_edsl
