import EDSL.BinarySearch.GCC.Invariant
import EDSL.X86.VCGen.BranchTactics

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

run_cmd do
  let options ← Lean.getOptions
  unless options.getBool `autoImplicit true == false &&
      options.getBool `warningAsError false == true &&
      options.getBool `Elab.async true == false &&
      options.get `maxHeartbeats (0 : Nat) == 300000 &&
      options.get `maxRecDepth (0 : Nat) == 128 do
    throwError "GCC loop stage: effective options differ from the required profile"
  Lean.logInfo "EFFECTIVE_OPTIONS autoImplicit=false warningAsError=true Elab.async=false maxHeartbeats=300000 maxRecDepth=128"

namespace EDSL.BinarySearch.GCC
open X86 X86.Sequential X86.VCGen

local macro "finish_return" frame:ident correct:ident : tactic => `(tactic| (
  vcgen_factor =>
    refine post_of_frame ?_ ?_ rfl rfl
    · vcgen_scratch_frame $frame
    · exact $correct))

theorem loop_hit (input : BufferCall.Invocation spec) (initial state : State)
    (pre : BufferCall.Pre spec bytes input initial)
    (frame : Frame initial state)
    (invariant : Math.Invariant (sequence input.value) input.value.key.toNat input.value.values.length
      (state.registers .rcx).toNat (state.registers .rsi).toNat)
    (active : (state.registers .rcx).toNat < (state.registers .rsi).toNat)
    (pc : state.rip = initial.rip + 25#64)
    (hit : sequence input.value (Math.wordMidpoint (state.registers .rcx)
      (state.registers .rsi)).toNat = input.value.key.toNat) :
    Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read)
      (Inv input initial) (rank input)
      ((state.registers .rsi).toNat - (state.registers .rcx).toNat) 14 loopIx state := by
  have canLoop : canonical (initial.rip + 25#64) = true := by
    simpa [CFG.Graph.node, layout, graph, loopIx] using
      layout_valid.canonical_node pre.code loopIx
  have canLow : canonical (initial.rip + 16#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨6, by decide +kernel⟩ : layout.Index)
  have canHit : canonical (initial.rip + 66#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨22, by decide +kernel⟩ : layout.Index)
  have canAbsent : canonical (initial.rip + 59#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨21, by decide +kernel⟩ : layout.Index)
  have stackAllowed : BufferCall.RawRead spec input initial
      ⟨.stack, initial.registers .rsp, 8⟩ := Or.inl ⟨rfl,rfl,rfl⟩
  have terminalFrame := frame.terminal
  have memory := frame.memory
  have rsp := frame.rsp
  have rdi := frame.rdi.trans (base_argument pre)
  have rdx := (congrArg (BitVec.setWidth 32) frame.rdx).trans (key_argument pre)
  let mid := Math.wordMidpoint (state.registers .rcx) (state.registers .rsi)
  have computed : (((state.registers .rsi - state.registers .rcx) >>> 1) +
      state.registers .rcx) = mid := BitVec.add_comm _ _
  have bounds := Math.wordMidpoint_bounds (state.registers .rcx) (state.registers .rsi) active
  have inside : mid.toNat < input.value.values.length :=
    Nat.lt_of_lt_of_le bounds.2 invariant.high_le_size
  obtain ⟨value, present, loaded, dataAllowed⟩ := snapshot_read pre mid inside
  have observed := sequence_at present
  have progress := Math.wordMidpoint_ranks (state.registers .rcx) (state.registers .rsi) active

  have equal : value.toNat = input.value.key.toNat := by
    rw [← observed]
    exact hit
  have correct := result_hit (count_small pre) (Math.found_word invariant active (by
    rw [observed]
    exact equal))
  have notBelow : ¬value.toNat < input.value.key.toNat := by omega
  have notAbove : ¬input.value.key.toNat < value.toNat := by omega
  change Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
    (fun _ read => BufferCall.RawRead spec input initial read)
    (Inv input initial) (rank input) ((state.registers .rsi).toNat - (state.registers .rcx).toNat)
    14 loopIx state
  vcgen_block_step layout loopIx simp [pc, BitVec.add_assoc]
  vcgen_block_step layout loopIx simp [sub64State, State.writeRegister, BitVec.add_assoc]
  vcgen_block_step layout loopIx simp [BitVec.add_assoc]
  vcgen_block_step layout loopIx simp [computed, BitVec.add_assoc]
  vcgen_block_step layout loopIx simp [memory, rdi, scaled_index, loaded, dataAllowed, BitVec.add_assoc]
  vcgen_block_step layout loopIx simp [rdx, BitVec.add_assoc]
  vcgen_branch_step simp [Condition.cmp32_below, notBelow, BitVec.add_assoc]
  vcgen_block_step layout loopIx simp [rdx, BitVec.add_assoc]
  vcgen_branch_step simp [Condition.cmp32_aboveEqual, equal, canHit, BitVec.add_assoc]
  vcgen_block_step layout loopIx simp [rsp, pre.stack, pre.returnCanonical, stackAllowed]
  finish_return terminalFrame correct

end EDSL.BinarySearch.GCC
