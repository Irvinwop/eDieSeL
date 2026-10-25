import tests.And64TestBase
import EDSL.X86.VCGen.TacticsWith
import EDSL.Logical64.Domain
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.And64VectorContinuation
open X86 Sequential X86.VCGen Logical64
/-- AND RAX,-1; IMUL RAX,RCX; RET: the continuation uses four independent flags. -/
def bytes : List Byte := [0x48,0x83,0xe0,0xff,0x48,0x0f,0xaf,0xc1,0xc3]
def graph : CFG.Graph := ⟨[
  ⟨0,.andImm64 .rax 0xff,true,2⟩,
  ⟨4,.imulReg64 .rax .rcx,false,1⟩,
  ⟨8,.legacy .ret,false,0⟩],2⟩
abbrev entry : graph.Index := ⟨0, by decide⟩
theorem valid : CFG.Valid bytes graph := CFG.check_sound (by decide +kernel)
def initial : State := Logical64.Domain.initial bytes 1 2
  (fun r => if r = .rax then 7 else if r = .rcx then 2 else 0xfedcba9876543210)

theorem pre : Pre bytes ⟨1,2,8192⟩ initial :=
  (Logical64.Domain.resource_pre bytes (by decide) (by decide) 1 2
    (fun r => if r = .rax then 7 else if r = .rcx then 2 else 0xfedcba9876543210)).machine

def Allowed (_before : State) (read : Read) : Prop := read = ⟨.stack,65544,8⟩

theorem all_vectors : wpWith graph initial.rip Allowed 3 entry initial
    (fun result => result.state.registers .rax = 14 ∧
      result.state.flags.getLsbD 0 = false ∧ result.state.flags.getLsbD 11 = false ∧
      result.reads = [⟨.stack,65544,8⟩]) := by
  have stack := pre.stack
  change readWord (OS.AddressSpace.toMemory (Grading.Domain.space bytes)) (65544#64) =
    .ok (8192#64) at stack
  have target : canonical (8192#64) = true := by decide
  have overflow : (7#64).smulOverflow (2#64) = false := by decide
  vcgen_runWith graph entry simp [logical64State, Allowed, initial, Logical64.Domain.initial,
    stack, target, Result.prepend, LogicalOp.eval]
  constructor
  · exact (imulFlags64_bits ..).1.trans overflow
  · exact (imulFlags64_bits ..).2.2.2.2.2.trans overflow

def separate : ChoiceStream FlagChoices := fun index =>
  if index = 1 then ⟨true,true,false,false,true,true⟩ else FlagChoices.uniform false

def observed : Option (Bool × Bool) := do
  let result ← (runWith separate 3 initial).toOption
  return (result.state.flags.getLsbD 2,result.state.flags.getLsbD 6)

theorem independent_future_bits : observed = some (true,false) := by cbv

theorem correlated_future_rejected :
    ¬ wpWith graph initial.rip Allowed 3 entry initial
      (fun result => result.state.flags.getLsbD 2 = result.state.flags.getLsbD 6) := by
  intro vc
  have pc : initial.rip = initial.rip + BitVec.ofNat 64 (graph.node entry).offset := by
    change initial.rip = initial.rip + 0#64
    simp
  obtain ⟨result,actual,wrong,_,_⟩ := run_soundWith valid pre.code pc vc separate
  have measured := independent_future_bits
  unfold observed at measured
  rw [actual] at measured
  change some (result.state.flags.getLsbD 2,result.state.flags.getLsbD 6) = some (true,false) at measured
  have bits : result.state.flags.getLsbD 2 = true ∧ result.state.flags.getLsbD 6 = false := by
    exact Prod.mk.inj (Option.some.inj measured)
  rw [bits.1,bits.2] at wrong
  cases wrong
end EDSL.Tests.And64VectorContinuation
#print axioms EDSL.Tests.And64VectorContinuation.all_vectors
#print axioms EDSL.Tests.And64VectorContinuation.correlated_future_rejected
#audit_edsl
