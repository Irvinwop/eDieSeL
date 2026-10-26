import EDSL.BinarySearch.GCC.LoopHit
import EDSL.BinarySearch.GCC.LoopLowContinue
import EDSL.BinarySearch.GCC.LoopLowExhausted
import EDSL.BinarySearch.GCC.LoopHighContinue
import EDSL.BinarySearch.GCC.LoopHighExhausted

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

theorem loop_block (input : BufferCall.Invocation spec) (initial state : State)
    (pre : BufferCall.Pre spec bytes input initial)
    (frame : Frame initial state)
    (invariant : Math.Invariant (sequence input.value) input.value.key.toNat input.value.values.length
      (state.registers .rcx).toNat (state.registers .rsi).toNat)
    (active : (state.registers .rcx).toNat < (state.registers .rsi).toNat)
    (pc : state.rip = initial.rip + 25#64) :
    Cutpoints.wp layout initial.rip (BufferCall.Post spec input initial)
      (fun _ read => BufferCall.RawRead spec input initial read)
      (Inv input initial) (rank input)
      ((state.registers .rsi).toNat - (state.registers .rcx).toNat) 14 loopIx state := by
  let mid := Math.wordMidpoint (state.registers .rcx) (state.registers .rsi)
  rcases Nat.lt_trichotomy (sequence input.value mid.toNat) input.value.key.toNat with
    below | equal | above
  · by_cases continues : (mid + 1).toNat < (state.registers .rsi).toNat
    · exact loop_lower_continues input initial state pre frame invariant active pc below continues
    · exact loop_lower_exhausted input initial state pre frame invariant active pc below continues
  · exact loop_hit input initial state pre frame invariant active pc equal
  · by_cases continues : (state.registers .rcx).toNat < mid.toNat
    · exact loop_upper_continues input initial state pre frame invariant active pc above continues
    · exact loop_upper_exhausted input initial state pre frame invariant active pc above continues

#print axioms loop_block
end EDSL.BinarySearch.GCC
#audit_edsl
