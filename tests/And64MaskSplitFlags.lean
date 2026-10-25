import tests.And64MaskSplit
import EDSL.Grading.PolicyRefinement
import EDSL.Grading.ReadOnlyClaimFor
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.And64MaskSplit
open X86 Sequential X86.VCGen Logical64
/-- Genuine all-Bool safety and bounded correctness transport this Bool-safe
program to every independent full-vector stream, retaining actual prefixes. -/
theorem raw_flags (input : Input) (initial : State) (pre : Pre bytes input initial) :
    AllExecutionsWith initial (fun result => Evidence input initial result) ∧
      Grading.ReadOnlyPolicyFor .flags initial (fun before => before.memory = initial.memory)
        (Allowed initial) := by
  obtain ⟨correct,policy⟩ := raw input initial pre
  have bounded : AllExecutions initial
      (fun result => Evidence input initial result ∧ result.instructions ≤ 7) := by
    intro choices
    obtain ⟨result,execution,evidence⟩ := correct choices
    have count := evidence.2.1
    exact ⟨result,execution,evidence,by omega⟩
  refine ⟨?_,policy.flags_of_safe correct.safe⟩
  intro choices
  obtain ⟨result,execution,evidence,_⟩ := allExecutionsWith_of_allExecutions bounded choices
  exact ⟨result,execution,evidence⟩

/-- Explicit infrastructure claim over both unchanged task domains; no new
registry entry or packet/export route is installed by this theorem. -/
theorem semantics_flags :
    Grading.ReadOnlySemanticClaimFor .flags (readOnlyTask .intersection) bytes := by
  constructor
  · intro input initial pre
    obtain ⟨correct,policy⟩ := raw_flags input initial pre
    refine ⟨?_,policy.mono (by intros; trivial) (by intros; trivial)⟩
    intro choices
    obtain ⟨result,execution,evidence⟩ := correct choices
    exact ⟨result,execution,evidence.1⟩
  · intro resource initial pre
    obtain ⟨correct,policy⟩ := raw_flags (resourceInput resource) initial pre.machine
    refine ⟨?_,policy.mono ?_ ?_⟩
    · intro choices
      obtain ⟨result,execution,evidence⟩ := correct choices
      exact ⟨result,execution,evidence.1,pre.current.sameMemory evidence.1.memory⟩
    · intro before memory
      exact pre.current.sameMemory memory
    · intro before read allowed
      exact pre.read_permission allowed
end EDSL.Tests.And64MaskSplit
#print axioms EDSL.Tests.And64MaskSplit.raw_flags
#print axioms EDSL.Tests.And64MaskSplit.semantics_flags
#audit_edsl
