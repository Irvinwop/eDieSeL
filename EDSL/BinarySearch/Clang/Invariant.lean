import EDSL.BinarySearch.Support
import EDSL.BinarySearch.Clang.Layout

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.BinarySearch.Clang
open X86 X86.Sequential X86.VCGen

def Inv (input : BufferCall.Invocation spec) (initial : State)
    (node : layout.Index) (state : State) : Prop :=
  if node.val = 0 then state = initial else
    Frame initial state ∧ state.registers .rax = state.registers .rsi ∧
    Math.Invariant (sequence input.value) input.value.key.toNat input.value.values.length
      (state.registers .rcx).toNat (state.registers .rsi).toNat ∧
    (state.registers .rcx).toNat < (state.registers .rsi).toNat

def rank (input : BufferCall.Invocation spec) (node : layout.Index) (state : State) : Nat :=
  if node.val = 0 then input.value.values.length + 1
  else (state.registers .rsi).toNat - (state.registers .rcx).toNat

end EDSL.BinarySearch.Clang
