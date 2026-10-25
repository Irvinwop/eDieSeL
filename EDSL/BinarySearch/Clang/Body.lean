import EDSL.BinarySearch.Clang.EntryEmpty
import EDSL.BinarySearch.Clang.EntryNonempty
import EDSL.BinarySearch.Clang.LoopBlock

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.BinarySearch.Clang
open X86 X86.Sequential X86.VCGen

/-- The complete frozen function, proved by production generated block VCs.
All loop indices are full64 words. Each independent AF choice is universally
quantified by the shared generator, including entry and SHR/INC choices. -/
def annotations (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec bytes input initial) :
    Cutpoints.Annotations bytes layout initial.rip (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read) where
  Inv := Inv input initial
  rank := rank input
  blocks cut state isCut binding admitted := by
    rcases only_cuts cut isCut with same | same
    · subst cut
      change state = initial at admitted
      subst state
      by_cases empty : input.value.values.length = 0
      · exact entry_empty input initial pre empty _ _ _
      · exact entry_nonempty input initial pre empty
    · subst cut
      change Frame initial state ∧ state.registers .rax = state.registers .rsi ∧
        Math.Invariant (sequence input.value) input.value.key.toNat input.value.values.length
          (state.registers .rcx).toNat (state.registers .rsi).toNat ∧
        (state.registers .rcx).toNat < (state.registers .rsi).toNat at admitted
      obtain ⟨frame, raxHigh, invariant, active⟩ := admitted
      have pc : state.rip = initial.rip + 33#64 := by
        simpa [CFG.Graph.node, layout, graph, loopIx] using binding.2
      exact loop_block input initial state pre frame raxHigh invariant active pc

theorem generated (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec bytes input initial) :
    ∃ evidence : Cutpoints.Annotations bytes layout initial.rip
      (BufferCall.Post spec input initial) (fun _ read => BufferCall.RawRead spec input initial read),
      evidence.Inv layout_valid.entry initial :=
  ⟨annotations input initial pre, rfl⟩

/-- Universal totality and every-prefix original raw authority. No input cap,
future run, decoder premise, correlation of flags or output premise is admitted. -/
theorem raw (input : BufferCall.Invocation spec) (initial : State)
    (pre : BufferCall.Pre spec bytes input initial) :
    AllExecutions initial (fun result => BufferCall.Post spec input initial result.state) ∧
      BufferCall.RawPolicy spec input initial :=
  bufferCall_raw_of_cutpoints spec bytes layout layout_valid generated input initial pre

/-- Universal call/resource contract under sequentialReadOnlyX86CallableV1:
stable ordinary RAM, no asynchronous interference, alignment checks disabled,
four-level canonical addresses, CET disabled. This is a body/resources theorem;
full named-ELF installation, grading admission and corpus credit are separate. -/
theorem semantics : Grading.ReadOnlySemanticClaim (BufferCall.readOnlyTask spec) bytes :=
  bufferCall_semantics_of_cutpoints spec bytes layout layout_valid generated

#print axioms generated
#print axioms raw
#print axioms semantics
end EDSL.BinarySearch.Clang
#audit_edsl
