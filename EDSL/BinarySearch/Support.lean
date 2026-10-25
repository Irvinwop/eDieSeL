import EDSL.BinarySearch.Contract
import EDSL.X86.VCGen.BufferCall
import EDSL.X86.VCGen.ScratchFrame
import EDSL.X86.Sequential.ConditionFlags

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.BinarySearch
open X86 X86.Sequential X86.VCGen

def scratch : List Register := [.rax, .rcx, .rsi]
abbrev Frame := PureCall.ScratchFrame scratch

theorem saved_protected : ∀ register ∈ PureCall.calleeSaved,
    register ≠ .rsp ∧ register ∉ scratch := by decide +kernel

theorem Frame.rsp {initial state : State} (frame : Frame initial state) :
    state.registers .rsp = initial.registers .rsp := frame.registers .rsp (by decide +kernel)
theorem Frame.rdi {initial state : State} (frame : Frame initial state) :
    state.registers .rdi = initial.registers .rdi := frame.registers .rdi (by decide +kernel)
theorem Frame.rdx {initial state : State} (frame : Frame initial state) :
    state.registers .rdx = initial.registers .rdx := frame.registers .rdx (by decide +kernel)

theorem Frame.terminal {initial state : State} (frame : Frame initial state) :
    PureCall.ScratchFrame (.rsp :: scratch) initial state :=
  frame.weaken (by intro register member; exact List.mem_cons_of_mem _ member)

theorem post_of_frame {input : BufferCall.Invocation spec} {initial final : State}
    (frame : PureCall.ScratchFrame (.rsp :: scratch) initial final)
    (correct : Result input.value (final.registers .rax))
    (returnAddress : final.rip = input.returnAddress)
    (stackPointer : final.registers .rsp = initial.registers .rsp + 8) :
    BufferCall.Post spec input initial final :=
  frame.post_return saved_protected correct returnAddress stackPointer

variable {bytes : List Byte} {input : BufferCall.Invocation spec} {initial : State}

theorem count_small (pre : BufferCall.Pre spec bytes input initial) :
    input.value.values.length < 2^64 := pre.domain.1
theorem sorted (pre : BufferCall.Pre spec bytes input initial) :
    Math.Sorted (sequence input.value) input.value.values.length := pre.domain.2
theorem count_nat (pre : BufferCall.Pre spec bytes input initial) :
    (BitVec.ofNat 64 input.value.values.length).toNat = input.value.values.length := by
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (count_small pre)]
theorem base_argument (pre : BufferCall.Pre spec bytes input initial) :
    initial.registers .rdi = input.value.base := pre.arguments 0 (.word64 _) rfl
theorem count_argument (pre : BufferCall.Pre spec bytes input initial) :
    initial.registers .rsi = BitVec.ofNat 64 input.value.values.length :=
  pre.arguments 1 (.word64 _) rfl
theorem key_argument (pre : BufferCall.Pre spec bytes input initial) :
    (initial.registers .rdx).setWidth 32 = input.value.key := pre.arguments 2 (.low32 _) rfl

theorem snapshot (pre : BufferCall.Pre spec bytes input initial) :
    BufferAt initial.memory input.value.base (BufferCall.Elements.u32Bytes input.value.values) :=
  pre.buffers ⟨input.value.base, BufferCall.Elements.u32Bytes input.value.values⟩
    (by simp only [spec, List.mem_singleton])

/-- Address scaling only: the full buffer extent independently excludes a
wrapped actual operand and authorizes all four bytes, without alignment. -/
theorem scaled_index (index : Word) : index <<< 2 = BitVec.ofNat 64 (4 * index.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mul_comm index.toNat]

/-- One arbitrary in-range word index reads the stable original full u32
snapshot. This theorem establishes the actual production load and DATA4
authority; it assumes no later execution or result. -/
theorem snapshot_read (pre : BufferCall.Pre spec bytes input initial)
    (index : Word) (inside : index.toNat < input.value.values.length) :
    ∃ value, input.value.values[index.toNat]? = some value ∧
      loadDWord initial.memory (input.value.base + BitVec.ofNat 64 (4 * index.toNat)) = .ok value ∧
      BufferCall.RawRead spec input initial
        ⟨.data, input.value.base + BitVec.ofNat 64 (4 * index.toNat), 4⟩ := by
  have present := List.getElem?_eq_getElem inside
  refine ⟨_, present, BufferCall.Elements.u32_loadDWord (snapshot pre) present, Or.inr ?_⟩
  refine ⟨rfl, ⟨input.value.base, BufferCall.Elements.u32Bytes input.value.values⟩, ?_, ?_⟩
  · simp only [spec, List.mem_singleton]
  · exact BufferCall.Elements.u32_element_span (snapshot pre) inside

#print axioms post_of_frame
#print axioms snapshot_read
end EDSL.BinarySearch
#audit_edsl
