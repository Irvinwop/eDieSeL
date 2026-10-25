import EDSL.X86.Sequential.Machine
import EDSL.Audit
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.And64Native
open X86
def allRegisters : List Register := [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]
def entry (code : List Byte) (pc : Word) (registers : List Word) (flags : Word) : State where
  registers r := registers.getD (allRegisters.idxOf r) 0
  rip := pc
  flags := flags
  memory := {
    read := fun a => if pc.toNat ≤ a.toNat ∧ a.toNat < pc.toNat + code.length then code[a.toNat - pc.toNat]? else none
    executable := fun a => decide (pc.toNat ≤ a.toNat ∧ a.toNat < pc.toNat + code.length)
    writable := fun _ => false }
def observe (af : Bool) (initial : State) : Option (List Word × Word × Word × List Sequential.Read) := do
  let observation ← (Sequential.step af initial).toOption
  match observation.result with
  | .next final => return (allRegisters.map final.registers,final.flags,final.rip,observation.reads)
  | _ => none
end EDSL.Tests.And64Native
#audit_edsl
