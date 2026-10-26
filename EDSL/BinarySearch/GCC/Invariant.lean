import EDSL.BinarySearch.GCC.Support
import EDSL.BinarySearch.GCC.Layout

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

/-- The +25 cut precedes MOV RAX,RSI. Incoming RAX, R8, arithmetic flags, and
RDX's unconstrained upper half need no relation to the active interval. -/
def Inv (input : BufferCall.Invocation spec) (initial : State)
    (node : layout.Index) (state : State) : Prop :=
  if node = entryIx then state = initial else if node = loopIx then
    Frame initial state ∧
    Math.Invariant (sequence input.value) input.value.key.toNat input.value.values.length
      (state.registers .rcx).toNat (state.registers .rsi).toNat ∧
    (state.registers .rcx).toNat < (state.registers .rsi).toNat
  else False

/-- Natural ranks do not truncate n+1 at the maximum representable count. -/
def rank (input : BufferCall.Invocation spec) (node : layout.Index) (state : State) : Nat :=
  if node = entryIx then input.value.values.length + 1
  else if node = loopIx then
    (state.registers .rsi).toNat - (state.registers .rcx).toNat
  else 0

theorem initial_invariant (input : BufferCall.Invocation spec) (initial : State) :
    Inv input initial entryIx initial := by simp [Inv]

#print axioms initial_invariant
end EDSL.BinarySearch.GCC
#audit_edsl
