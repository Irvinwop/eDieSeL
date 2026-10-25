import EDSL.X86.Sequential.AndImmediate64Resources
import EDSL.X86.Sequential.AndImmediate64Decode
import EDSL.X86.VCGen.ChoiceNext
import EDSL.Audit
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.And64Regression
open X86 Sequential

def registers : List Register := [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,
  .r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]
/-- Distinct banks and upper halves; only code is present. -/
def initial (bytes : List Byte) (destination : Register) (old : Word) (flags : Word := 0xed7) : State :=
  { codeState bytes 0 with
    registers := fun r => if r = destination then old
      else BitVec.ofNat 64 (0xabc0000000000001 + registers.idxOf r * 0x101000001)
    flags := flags }

def view (destination : Register) (af : Bool) (state : State) :
    Option (Word × Word × Bool × Word × List Read) := do
  let observation ← (step af state).toOption
  match observation.result with
  | .next final => return (final.registers destination,final.flags &&& ~~~(0x10 : Word),
      final.flags.getLsbD 4,final.rip,observation.reads)
  | _ => none

/-- The actual production vector step depends only on AF here; no other
current or future component is correlated with it. -/
theorem vector_step {state : State} {destination : Register} {immediate : Byte}
    (decoded : Sequential.decodeAt state = .ok (.andImm64 destination immediate)) (choices : FlagChoices) :
    stepWith choices state = step choices.af state := by
  rw [stepWith_andImm64 decoded, step_andImm64 decoded]
end EDSL.Tests.And64Regression
#audit_edsl
