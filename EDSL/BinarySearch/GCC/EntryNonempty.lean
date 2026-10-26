import EDSL.BinarySearch.GCC.Invariant
import EDSL.X86.VCGen.BranchTactics

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
    throwError "GCC entry stage: effective options differ from the required profile"
  Lean.logInfo "EFFECTIVE_OPTIONS autoImplicit=false warningAsError=true Elab.async=false maxHeartbeats=300000 maxRecDepth=128"

namespace EDSL.BinarySearch.GCC
open X86 X86.Sequential X86.VCGen

/-- The real entry initializes only RCX and jumps directly to the checked MOV
cut at +25. The shared interval is [0,n), with strict natural rank n<n+1. -/
theorem entry_nonempty (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec bytes input initial) (nonempty : input.value.values.length ≠ 0) :
    Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read) (Inv input initial) (rank input)
      (input.value.values.length + 1) 5 entryIx initial := by
  have canLoop : canonical (initial.rip + 25#64) = true := by
    simpa [CFG.Graph.node, layout, graph, loopIx] using
      layout_valid.canonical_node pre.code loopIx
  have frame : Frame initial initial := PureCall.ScratchFrame.refl _ _
  have rsi := count_argument pre
  have countNonzero : BitVec.ofNat 64 input.value.values.length ≠ 0#64 := by
    intro zero
    have natural := congrArg BitVec.toNat zero
    rw [count_nat pre] at natural
    exact nonempty natural
  vcgen_block_step layout entryIx simp
  vcgen_block_step layout entryIx simp [-BitVec.getLsbD_eq_getElem, rsi, BitVec.add_assoc]
  vcgen_branch_step simp [-BitVec.getLsbD_eq_getElem,
    countNonzero, Condition.holds, logicalFlags64_zero, BitVec.add_assoc]
  vcgen_block_step layout entryIx simp [BitVec.add_assoc]
  vcgen_branch_step simp [canLoop, BitVec.add_assoc]
  dsimp only [Inv, rank]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · vcgen_scratch_frame frame
  · simpa [rsi, count_nat pre] using
      Math.initial (sequence input.value) input.value.key.toNat input.value.values.length
  · change 0 < (initial.registers .rsi).toNat
    rw [rsi, count_nat pre]
    omega
  · simp [rsi, count_nat pre]

#print axioms entry_nonempty
end EDSL.BinarySearch.GCC
#audit_edsl
