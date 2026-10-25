import EDSL.BinarySearch.Support
import EDSL.BinarySearch.Clang.Layout
import EDSL.X86.VCGen.BranchTactics

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.BinarySearch.Clang
open X86 X86.Sequential X86.VCGen

/-- The real frozen entry's empty-input path, using the shared branch-aware
normalizer and the original independent whole-call postcondition. It needs no
DATA loan, data-pointer canonicality, alignment, future run or output premise. -/
theorem entry_empty (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec bytes input initial) (empty : input.value.values.length = 0)
    (Inv : layout.Index → State → Prop) (rank : layout.Index → State → Nat) (budget : Nat) :
    Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read) Inv rank budget
      6 entryIx initial := by
  have canAbsent : canonical (initial.rip + 50#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨19, by decide +kernel⟩ : layout.Index)
  have stackAllowed : BufferCall.RawRead spec input initial
      ⟨.stack, initial.registers .rsp, 8⟩ := Or.inl ⟨rfl, rfl, rfl⟩
  have frame : Frame initial initial := PureCall.ScratchFrame.refl _ _
  have terminalFrame := frame.terminal
  have rsi := count_argument pre
  have correct : Result input.value sizeMax := result_absent (by
    intro index inside
    omega)
  vcgen_branch_block layout entryIx simp [-BitVec.getLsbD_eq_getElem,
    rsi, empty, Condition.holds, logicalFlags64_zero, canAbsent, BitVec.add_assoc,
    pre.stack, pre.returnCanonical, stackAllowed]
  vcgen_factor =>
    refine post_of_frame ?_ ?_ rfl rfl
    · vcgen_scratch_frame terminalFrame
    · exact correct

#print axioms entry_empty
end EDSL.BinarySearch.Clang
#audit_edsl
