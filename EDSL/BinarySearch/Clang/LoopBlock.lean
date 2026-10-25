import EDSL.BinarySearch.Clang.LoopHit
import EDSL.BinarySearch.Clang.LoopPaths

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.BinarySearch.Clang
open X86 X86.Sequential X86.VCGen

theorem loop_block (input : BufferCall.Invocation spec) (initial state : State)
    (pre : BufferCall.Pre spec bytes input initial)
    (frame : Frame initial state) (raxHigh : state.registers .rax = state.registers .rsi)
    (invariant : Math.Invariant (sequence input.value) input.value.key.toNat input.value.values.length
      (state.registers .rcx).toNat (state.registers .rsi).toNat)
    (active : (state.registers .rcx).toNat < (state.registers .rsi).toNat)
    (pc : state.rip = initial.rip + 33#64) :
    Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read)
      (Inv input initial) (rank input)
      ((state.registers .rsi).toNat - (state.registers .rcx).toNat) 14 loopIx state := by
  let mid := Math.wordMidpoint (state.registers .rcx) (state.registers .rsi)
  rcases Nat.lt_trichotomy (sequence input.value mid.toNat) input.value.key.toNat with
    below | equal | above
  · by_cases continues : (mid + 1).toNat < (state.registers .rsi).toNat
    · exact loop_lower_continues input initial state pre frame raxHigh invariant active pc below continues
    · exact loop_lower_exhausted input initial state pre frame raxHigh invariant active pc below continues
  · exact loop_hit input initial state pre frame raxHigh invariant active pc equal
  · by_cases continues : (state.registers .rcx).toNat < mid.toNat
    · exact loop_upper_continues input initial state pre frame raxHigh invariant active pc above continues
    · exact loop_upper_exhausted input initial state pre frame raxHigh invariant active pc above continues

#print axioms loop_block
end EDSL.BinarySearch.Clang
#audit_edsl
