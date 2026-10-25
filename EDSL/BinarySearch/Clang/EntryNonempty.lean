import EDSL.BinarySearch.Clang.Invariant
import EDSL.X86.VCGen.BranchTactics

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.BinarySearch.Clang
open X86 X86.Sequential X86.VCGen

theorem entry_nonempty (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec bytes input initial) (nonempty : input.value.values.length ≠ 0) :
    Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read) (Inv input initial) (rank input)
      (input.value.values.length + 1) 6 entryIx initial := by
  have canLoop : canonical (initial.rip + 33#64) = true := by
    simpa [CFG.Graph.node, layout, graph, loopIx] using
      layout_valid.canonical_node pre.code loopIx
  have frame : Frame initial initial := PureCall.ScratchFrame.refl _ _
  have rsi := count_argument pre
  have countNonzero : BitVec.ofNat 64 input.value.values.length ≠ 0#64 := by
    intro zero
    have natural := congrArg BitVec.toNat zero
    rw [count_nat pre] at natural
    exact nonempty natural
  change Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
    (fun _ read => BufferCall.RawRead spec input initial read)
    (Inv input initial) (rank input) (input.value.values.length + 1) 6 entryIx initial
  vcgen_branch_block layout entryIx simp [-BitVec.getLsbD_eq_getElem,
    rsi, countNonzero, Condition.holds, logicalFlags64_zero, canLoop, BitVec.add_assoc]
  dsimp only [Inv, rank]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · vcgen_scratch_frame frame
  · simpa using rsi.symm
  · simpa [rsi, count_nat pre] using
      Math.initial (sequence input.value) input.value.key.toNat input.value.values.length
  · change 0 < (initial.registers .rsi).toNat
    rw [rsi, count_nat pre]
    omega
  · simp [rsi, count_nat pre]

#print axioms entry_nonempty
end EDSL.BinarySearch.Clang
#audit_edsl
