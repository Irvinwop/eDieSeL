import EDSL.BinarySearch.Support

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

/-- GCC permits exactly these four GPR clobbers before RET. The shared frame
preserves the complete memory, permissions, and full nonarithmetic flag mask. -/
def scratch : List Register := [.rax, .rcx, .rsi, .r8]
abbrev Frame := PureCall.ScratchFrame scratch

theorem saved_protected : ∀ register ∈ PureCall.calleeSaved,
    register ≠ .rsp ∧ register ∉ scratch := by decide +kernel

theorem Frame.rsp {initial state : State} (frame : Frame initial state) :
    state.registers .rsp = initial.registers .rsp := frame.registers .rsp (by decide +kernel)
theorem Frame.rdi {initial state : State} (frame : Frame initial state) :
    state.registers .rdi = initial.registers .rdi := frame.registers .rdi (by decide +kernel)
/-- Preserve all 64 bits; the independent call contract binds only EDX. -/
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

#print axioms Frame.rdx
#print axioms post_of_frame
end EDSL.BinarySearch.GCC
#audit_edsl
