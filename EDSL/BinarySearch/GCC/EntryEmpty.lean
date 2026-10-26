import EDSL.BinarySearch.GCC.Support
import EDSL.BinarySearch.GCC.Layout
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

/-- Execute ENDBR64 (CET disabled), TEST, JE, sign-extended sentinel MOV and
the original STACK8 RET in the full checked graph. No DATA operand is read;
the empty buffer's unused base has no canonicality or alignment premise. -/
theorem entry_empty (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec bytes input initial) (empty : input.value.values.length = 0)
    (Inv : layout.Index → State → Prop) (rank : layout.Index → State → Nat) (budget : Nat) :
    Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read) Inv rank budget
      5 entryIx initial := by
  have canAbsent : canonical (initial.rip + 59#64) = true := by
    simpa [CFG.Graph.node, layout, graph] using
      layout_valid.canonical_node pre.code (⟨21, by decide +kernel⟩ : layout.Index)
  have stackAllowed : BufferCall.RawRead spec input initial
      ⟨.stack, initial.registers .rsp, 8⟩ := Or.inl ⟨rfl, rfl, rfl⟩
  have frame : Frame initial initial := PureCall.ScratchFrame.refl _ _
  have terminalFrame := frame.terminal
  have rsi := count_argument pre
  have correct : Result input.value sizeMax := result_absent (by
    intro index inside
    omega)
  -- Compose the shared generic steps directly to keep elaborator nesting
  -- shallow under recursion 128; the complete graph remains unchanged.
  vcgen_block_step layout entryIx simp
  vcgen_block_step layout entryIx simp [-BitVec.getLsbD_eq_getElem, rsi, empty, BitVec.add_assoc]
  vcgen_branch_step simp [Condition.holds, logicalFlags64_zero, canAbsent, BitVec.add_assoc]
  vcgen_block_step layout entryIx simp [BitVec.add_assoc]
  vcgen_block_step layout entryIx simp [pre.stack, pre.returnCanonical, stackAllowed]
  vcgen_factor =>
    refine post_of_frame ?_ ?_ rfl rfl
    · vcgen_scratch_frame terminalFrame
    · exact correct

#print axioms entry_empty
end EDSL.BinarySearch.GCC
#audit_edsl
