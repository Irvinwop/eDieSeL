import EDSL.BinarySearch.Clang.Invariant
import EDSL.X86.VCGen.BranchTactics

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.BinarySearch.Clang
open X86 X86.Sequential X86.VCGen

local macro "finish_return" frame:ident correct:ident : tactic => `(tactic| (
  vcgen_factor =>
    refine post_of_frame ?_ ?_ rfl rfl
    · vcgen_scratch_frame $frame
    · exact $correct))

theorem loop_lower_continues (input : BufferCall.Invocation spec) (initial state : State)
    (pre : BufferCall.Pre spec bytes input initial)
    (frame : Frame initial state) (raxHigh : state.registers .rax = state.registers .rsi)
    (invariant : Math.Invariant (sequence input.value) input.value.key.toNat input.value.values.length
      (state.registers .rcx).toNat (state.registers .rsi).toNat)
    (active : (state.registers .rcx).toNat < (state.registers .rsi).toNat)
    (pc : state.rip = initial.rip + 33#64)
    (selected : sequence input.value (Math.wordMidpoint (state.registers .rcx) (state.registers .rsi)).toNat < input.value.key.toNat) (continues : (Math.wordMidpoint (state.registers .rcx) (state.registers .rsi) + 1).toNat < (state.registers .rsi).toNat) :
    Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read)
      (Inv input initial) (rank input)
      ((state.registers .rsi).toNat - (state.registers .rcx).toNat) 14 loopIx state := by
  have canLoop : canonical (initial.rip + 33#64) = true := by
    simpa [CFG.Graph.node, layout, graph, loopIx] using
      layout_valid.canonical_node pre.code loopIx
  have canLow : canonical (initial.rip + 16#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨6, by decide +kernel⟩ : layout.Index)
  have canHigh : canonical (initial.rip + 25#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨9, by decide +kernel⟩ : layout.Index)
  have canAbsent : canonical (initial.rip + 50#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨19, by decide +kernel⟩ : layout.Index)
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

  have below : value.toNat < input.value.key.toNat := by
    rw [← observed]; exact selected
  have advanced := Math.advance_low_word (sorted pre) invariant active (by
    rw [observed]; exact below)
  have loopSelect (old : Word) :
      Condition.holds .aboveEqual (cmpFlags64 old (mid + 1#64) (state.registers .rsi)) = false := by
    rw [Condition.cmp_aboveEqual]
    exact decide_eq_false (Nat.not_le_of_lt continues)
  change Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
    (fun _ read => BufferCall.RawRead spec input initial read)
    (Inv input initial) (rank input) ((state.registers .rsi).toNat - (state.registers .rcx).toNat)
    14 loopIx state
  vcgen_branch_block layout loopIx simp [-BitVec.getLsbD_eq_getElem, sub64State,
    State.writeRegister, raxHigh, computed, pc, memory, rdi, rdx, scaled_index,
    loaded, dataAllowed, Condition.cmp32_below, below,
    loopSelect,
    canLow, BitVec.add_assoc]
  dsimp only [Inv, rank]
  exact ⟨⟨by vcgen_scratch_frame frame, rfl, advanced, continues⟩, progress.1⟩

#print axioms loop_lower_continues

theorem loop_lower_exhausted (input : BufferCall.Invocation spec) (initial state : State)
    (pre : BufferCall.Pre spec bytes input initial)
    (frame : Frame initial state) (raxHigh : state.registers .rax = state.registers .rsi)
    (invariant : Math.Invariant (sequence input.value) input.value.key.toNat input.value.values.length
      (state.registers .rcx).toNat (state.registers .rsi).toNat)
    (active : (state.registers .rcx).toNat < (state.registers .rsi).toNat)
    (pc : state.rip = initial.rip + 33#64)
    (selected : sequence input.value (Math.wordMidpoint (state.registers .rcx) (state.registers .rsi)).toNat < input.value.key.toNat) (continues : ¬(Math.wordMidpoint (state.registers .rcx) (state.registers .rsi) + 1).toNat < (state.registers .rsi).toNat) :
    Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read)
      (Inv input initial) (rank input)
      ((state.registers .rsi).toNat - (state.registers .rcx).toNat) 14 loopIx state := by
  have canLoop : canonical (initial.rip + 33#64) = true := by
    simpa [CFG.Graph.node, layout, graph, loopIx] using
      layout_valid.canonical_node pre.code loopIx
  have canLow : canonical (initial.rip + 16#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨6, by decide +kernel⟩ : layout.Index)
  have canHigh : canonical (initial.rip + 25#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨9, by decide +kernel⟩ : layout.Index)
  have canAbsent : canonical (initial.rip + 50#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨19, by decide +kernel⟩ : layout.Index)
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

  have below : value.toNat < input.value.key.toNat := by
    rw [← observed]; exact selected
  have advanced := Math.advance_low_word (sorted pre) invariant active (by
    rw [observed]; exact below)
  have exhausted := Math.exhausted_word advanced (Nat.le_of_not_gt continues)
  have correct := result_absent exhausted
  have loopSelect (old : Word) :
      Condition.holds .aboveEqual (cmpFlags64 old (mid + 1#64) (state.registers .rsi)) = true := by
    rw [Condition.cmp_aboveEqual]
    exact decide_eq_true (Nat.le_of_not_gt continues)
  change Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
    (fun _ read => BufferCall.RawRead spec input initial read)
    (Inv input initial) (rank input) ((state.registers .rsi).toNat - (state.registers .rcx).toNat)
    14 loopIx state
  vcgen_branch_block layout loopIx simp [-BitVec.getLsbD_eq_getElem, sub64State,
    State.writeRegister, raxHigh, computed, pc, memory, rsp, rdi, rdx, scaled_index,
    loaded, dataAllowed, Condition.cmp32_below, below, loopSelect,
     canLow, canAbsent, BitVec.add_assoc,
    pre.stack, pre.returnCanonical, stackAllowed]
  finish_return terminalFrame correct

#print axioms loop_lower_exhausted

theorem loop_upper_continues (input : BufferCall.Invocation spec) (initial state : State)
    (pre : BufferCall.Pre spec bytes input initial)
    (frame : Frame initial state) (raxHigh : state.registers .rax = state.registers .rsi)
    (invariant : Math.Invariant (sequence input.value) input.value.key.toNat input.value.values.length
      (state.registers .rcx).toNat (state.registers .rsi).toNat)
    (active : (state.registers .rcx).toNat < (state.registers .rsi).toNat)
    (pc : state.rip = initial.rip + 33#64)
    (selected : input.value.key.toNat < sequence input.value (Math.wordMidpoint (state.registers .rcx) (state.registers .rsi)).toNat) (continues : (state.registers .rcx).toNat < (Math.wordMidpoint (state.registers .rcx) (state.registers .rsi)).toNat) :
    Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read)
      (Inv input initial) (rank input)
      ((state.registers .rsi).toNat - (state.registers .rcx).toNat) 14 loopIx state := by
  have canLoop : canonical (initial.rip + 33#64) = true := by
    simpa [CFG.Graph.node, layout, graph, loopIx] using
      layout_valid.canonical_node pre.code loopIx
  have canLow : canonical (initial.rip + 16#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨6, by decide +kernel⟩ : layout.Index)
  have canHigh : canonical (initial.rip + 25#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨9, by decide +kernel⟩ : layout.Index)
  have canAbsent : canonical (initial.rip + 50#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨19, by decide +kernel⟩ : layout.Index)
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

  have above : input.value.key.toNat < value.toNat := by
    rw [← observed]; exact selected
  have retreated := Math.retreat_high_word (sorted pre) invariant active (by
    rw [observed]; exact above)
  have notBelow : ¬value.toNat < input.value.key.toNat := by omega
  have loopSelect (old : Word) :
      Condition.holds .aboveEqual (cmpFlags64 old (state.registers .rcx) mid) = false := by
    rw [Condition.cmp_aboveEqual]
    exact decide_eq_false (Nat.not_le_of_lt continues)
  change Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
    (fun _ read => BufferCall.RawRead spec input initial read)
    (Inv input initial) (rank input) ((state.registers .rsi).toNat - (state.registers .rcx).toNat)
    14 loopIx state
  vcgen_branch_block layout loopIx simp [-BitVec.getLsbD_eq_getElem, sub64State,
    State.writeRegister, raxHigh, computed, pc, memory, rdi, rdx, scaled_index,
    loaded, dataAllowed, Condition.cmp32_below, notBelow, Condition.cmp32_above, above,
    loopSelect,
    canHigh, BitVec.add_assoc]
  dsimp only [Inv, rank]
  exact ⟨⟨by vcgen_scratch_frame frame, rfl, retreated, continues⟩, progress.2⟩

#print axioms loop_upper_continues

theorem loop_upper_exhausted (input : BufferCall.Invocation spec) (initial state : State)
    (pre : BufferCall.Pre spec bytes input initial)
    (frame : Frame initial state) (raxHigh : state.registers .rax = state.registers .rsi)
    (invariant : Math.Invariant (sequence input.value) input.value.key.toNat input.value.values.length
      (state.registers .rcx).toNat (state.registers .rsi).toNat)
    (active : (state.registers .rcx).toNat < (state.registers .rsi).toNat)
    (pc : state.rip = initial.rip + 33#64)
    (selected : input.value.key.toNat < sequence input.value (Math.wordMidpoint (state.registers .rcx) (state.registers .rsi)).toNat) (continues : ¬(state.registers .rcx).toNat < (Math.wordMidpoint (state.registers .rcx) (state.registers .rsi)).toNat) :
    Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read)
      (Inv input initial) (rank input)
      ((state.registers .rsi).toNat - (state.registers .rcx).toNat) 14 loopIx state := by
  have canLoop : canonical (initial.rip + 33#64) = true := by
    simpa [CFG.Graph.node, layout, graph, loopIx] using
      layout_valid.canonical_node pre.code loopIx
  have canLow : canonical (initial.rip + 16#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨6, by decide +kernel⟩ : layout.Index)
  have canHigh : canonical (initial.rip + 25#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨9, by decide +kernel⟩ : layout.Index)
  have canAbsent : canonical (initial.rip + 50#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨19, by decide +kernel⟩ : layout.Index)
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

  have above : input.value.key.toNat < value.toNat := by
    rw [← observed]; exact selected
  have retreated := Math.retreat_high_word (sorted pre) invariant active (by
    rw [observed]; exact above)
  have notBelow : ¬value.toNat < input.value.key.toNat := by omega
  have exhausted := Math.exhausted_word retreated (Nat.le_of_not_gt continues)
  have correct := result_absent exhausted
  have loopSelect (old : Word) :
      Condition.holds .aboveEqual (cmpFlags64 old (state.registers .rcx) mid) = true := by
    rw [Condition.cmp_aboveEqual]
    exact decide_eq_true (Nat.le_of_not_gt continues)
  change Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
    (fun _ read => BufferCall.RawRead spec input initial read)
    (Inv input initial) (rank input) ((state.registers .rsi).toNat - (state.registers .rcx).toNat)
    14 loopIx state
  vcgen_branch_block layout loopIx simp [-BitVec.getLsbD_eq_getElem, sub64State,
    State.writeRegister, raxHigh, computed, pc, memory, rsp, rdi, rdx, scaled_index,
    loaded, dataAllowed, Condition.cmp32_below, notBelow, Condition.cmp32_above, above,
    loopSelect,
    canHigh, canAbsent, BitVec.add_assoc, pre.stack, pre.returnCanonical, stackAllowed]
  finish_return terminalFrame correct

#print axioms loop_upper_exhausted

end EDSL.BinarySearch.Clang
#audit_edsl
