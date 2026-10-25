import EDSL.BinarySearch.Contract
import EDSL.BinarySearch.Clang.Layout

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.BinarySearch.Controls
open X86 X86.Sequential

/-- A 32-bit all-ones return must not be accepted as the ABI's full64 SIZE_MAX.
This catches a result contract that accidentally narrows the return register. -/
theorem rejects_truncated_sentinel (base : Word) (key : BitVec 32) :
    ¬Result ⟨base, [], key⟩ 0xffffffff := by
  have different : (0xffffffff : Word) ≠ sizeMax := by decide +kernel
  simp only [Result, different, ↓reduceIte,
    WordMath.BinarySearch.Correct, List.length_nil]
  omega

/-- An out-of-range index never becomes a hit via the sequence's default
value. This catches loss of the independent range condition on an equal key. -/
theorem rejects_out_of_range (input : Input) (actual : Word)
    (notSentinel : actual ≠ sizeMax) (outside : input.values.length ≤ actual.toNat) :
    ¬Result input actual := by
  simp only [Result, notSentinel, ↓reduceIte, WordMath.BinarySearch.Correct]
  omega

/-- A sentinel cannot represent absence when any equal position exists,
including a nonfirst duplicate. No search path is supplied to this check. -/
theorem rejects_false_absence (input : Input) (index : Nat)
    (inside : index < input.values.length) (matching : input.values[index]? = some input.key) :
    ¬Result input sizeMax := by
  intro result
  have absent := (sentinel_iff_absent result).mp rfl
  exact absent index inside (sequence_at matching)

/-- Empty input admits no positive DATA operand at any address or width.
This checks the authorization contract independently of machine traversal. -/
theorem empty_rejects_data (base : Word) (key : BitVec 32)
    (address : Word) (width : Nat) :
    ¬BufferCall.DataRead (spec.buffers ⟨base, [], key⟩) ⟨.data,address,width⟩ := by
  apply BufferCall.DataRead.no_empty
  intro buffer member
  have same : buffer = ⟨base, []⟩ := by simpa only [spec, BufferCall.Elements.u32Bytes_nil,
    List.mem_singleton] using member
  subst buffer
  rfl

/-- Negative untrusted graph proposals, with the original 58-byte target
unchanged. Omitting unreachable padding must fail complete-window admission. -/
theorem rejects_omitted_padding : CFG.check Clang.bytes
    { Clang.layout with nodes := Clang.layout.nodes.eraseIdx 5 } = false := by
  decide +kernel

/-- Both actual RET sites are part of the complete symbol window. -/
theorem rejects_omitted_final_ret : CFG.check Clang.bytes
    { Clang.layout with nodes := Clang.layout.nodes.take 20 } = false := by
  decide +kernel

#print axioms rejects_truncated_sentinel
#print axioms rejects_out_of_range
#print axioms rejects_false_absence
#print axioms empty_rejects_data
#print axioms rejects_omitted_padding
#print axioms rejects_omitted_final_ret
end EDSL.BinarySearch.Controls
#audit_edsl
