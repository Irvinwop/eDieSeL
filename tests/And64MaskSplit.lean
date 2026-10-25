import EDSL.X86.VCGen.ChoiceNext
import EDSL.X86.VCGen.Tactics
import EDSL.X86.VCGen.Frame
import EDSL.X86.VCGen.Policy
import EDSL.Logical64.Domain
import EDSL.Audit
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.And64MaskSplit
open X86 Sequential X86.VCGen Logical64
/-- Owned 21-byte seven-instruction candidate for the existing intersection task. -/
def bytes : List Byte :=
  [0x48,0x89,0xf8,0x48,0x21,0xf0,0x49,0x89,0xc0,
   0x49,0x83,0xe0,0xf8,0x48,0x83,0xe0,7,0x4c,9,0xc0,0xc3]
/-- Literal proposal only: the production checker authenticates every node. -/
def graph : CFG.Graph := ⟨[
  ⟨0,.movReg64 .rax .rdi,true,6⟩,
  ⟨3,.logicalReg64 .band .rax .rsi,false,5⟩,
  ⟨6,.movReg64 .r8 .rax,false,4⟩,
  ⟨9,.andImm64 .r8 0xf8,false,3⟩,
  ⟨13,.andImm64 .rax 7,false,2⟩,
  ⟨17,.logicalReg64 .bor .rax .r8,false,1⟩,
  ⟨20,.legacy .ret,false,0⟩],6⟩
abbrev entry : graph.Index := ⟨0, by decide +kernel⟩
theorem valid : CFG.Valid bytes graph := CFG.check_sound (by decide +kernel)
/-- Pure bit partition, valid for every full64 value. -/
theorem mask_split (value : Word) :
    (value &&& (7 : Word)) ||| (value &&& (0xfffffffffffffff8 : Word)) = value := by
  rw [← BitVec.and_or_distrib_left]
  change value &&& BitVec.allOnes 64 = value
  exact BitVec.and_allOnes

set_option pp.all true in
#check EDSL.Tests.And64MaskSplit.mask_split

def Allowed (initial : State) (_before : State) (read : Read) : Prop :=
  read.kind = .stack ∧ read.address = initial.registers .rsp ∧ read.bytes = 8

def Evidence (input : Input) (initial : State) (result : Result) : Prop :=
  Post .intersection input initial result.state ∧ result.instructions = 7 ∧
    result.reads = [⟨.stack,initial.registers .rsp,8⟩] ∧
    (∀ register, register ≠ .rax → register ≠ .r8 → register ≠ .rsp →
      result.state.registers register = initial.registers register)

/-- Production VCG, exact byte-checked CFG, complete independent mathematical
postcondition and literal actual return read, for every admitted argument pair. -/
theorem generated (input : Input) (initial : State) (pre : Pre bytes input initial) :
    wp graph initial.rip (Allowed initial) 7 entry initial (Evidence input initial) := by
  vcgen_run graph entry simp [Allowed, pre.stack, pre.returnCanonical,
    BitVec.add_assoc]
  refine ⟨⟨?_, rfl, rfl, rfl, ?_, ?_⟩, rfl, rfl, ?_⟩
  · simp only [Result.prepend, reduceCtorEq, ite_false, ite_true, LogicalOp.eval, pre.left, pre.right]
    change MathematicalResult .intersection input.left input.right
      (((input.left &&& input.right) &&& (7 : Word)) |||
        ((input.left &&& input.right) &&& (0xfffffffffffffff8 : Word)))
    rw [EDSL.Tests.And64MaskSplit.mask_split]
    exact Logical64.eval_mathematical .intersection input.left input.right
  · intro register member
    have nrax : register ≠ .rax := by intro same; subst register; simp [calleeSaved] at member
    have nr8 : register ≠ .r8 := by intro same; subst register; simp [calleeSaved] at member
    have nrsp : register ≠ .rsp := by intro same; subst register; simp [calleeSaved] at member
    simp only [Result.prepend, ite_eq_right nrax, ite_eq_right nr8, ite_eq_right nrsp]
  · simp only [Result.prepend, logicalFlags64_preserves]
  · intro register nrax nr8 nrsp
    simp only [Result.prepend, ite_eq_right nrax, ite_eq_right nr8, ite_eq_right nrsp]

theorem raw (input : Input) (initial : State) (pre : Pre bytes input initial) :
    AllExecutions initial (fun result => Evidence input initial result) ∧ RawPolicy initial := by
  have pc : initial.rip = initial.rip + BitVec.ofNat 64 (graph.node entry).offset := by
    change initial.rip = initial.rip + 0#64
    simp
  refine ⟨?_, readOnly_policy_memory valid pre.code pc (generated input initial pre)⟩
  intro choices
  obtain ⟨result,execution,evidence,_,_⟩ := sound valid pre.code pc (generated input initial pre) choices
  exact ⟨result,execution,evidence⟩

theorem semantics : Grading.ReadOnlySemanticClaim (readOnlyTask .intersection) bytes := by
  apply readOnly_semantics_of_raw
  intro input initial pre
  obtain ⟨correct,policy⟩ := raw input initial pre
  refine ⟨?_,policy⟩
  intro choices
  obtain ⟨result,execution,post,_,_⟩ := correct choices
  exact ⟨result,execution,post⟩

theorem nonvacuous : Grading.ReadOnlyNonvacuous (readOnlyTask .intersection) bytes :=
  Logical64.Domain.nonvacuous .intersection bytes (by decide) (by decide)

theorem returned_resources {resource : Logical64.Resources} {initial : State}
    (pre : ResourcePre bytes resource initial) (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      Evidence (resourceInput resource) initial result ∧
      OS.CallResources.Current resource.call resource.shared result.state ∧
      result.reads = [⟨.stack,resource.call.stack,8⟩] := by
  obtain ⟨result,actual,evidence⟩ := (raw _ _ pre.machine).1 choices
  exact ⟨result,actual,evidence,pre.current.sameMemory evidence.1.memory,
    by simpa only [pre.stack] using evidence.2.2.1⟩
end EDSL.Tests.And64MaskSplit
#print axioms EDSL.Tests.And64MaskSplit.valid
#print axioms EDSL.Tests.And64MaskSplit.generated
#print axioms EDSL.Tests.And64MaskSplit.semantics
#print axioms EDSL.Tests.And64MaskSplit.nonvacuous
#print axioms EDSL.Tests.And64MaskSplit.returned_resources
#audit_edsl
