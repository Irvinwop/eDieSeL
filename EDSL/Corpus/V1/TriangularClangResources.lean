/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.TriangularClangBody
import EDSL.X86.VCGen.ChoicesPureCall
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.Corpus.V1.TriangularClangResources
open X86 X86.Sequential X86.VCGen
open TriangularClangBody

/-- Full-vector raw and current-resource semantics for the independent Spec.
The resource adapter retains the same supplied code/caller world at every
actual continuing prefix and return. Authority comes from ResourcePre; the
arithmetic value supplies no memory permission. Stable ordinary RAM, 64-bit
mode, CET/IBT/shadow stacks disabled and no asynchronous interference are the
production sequential target assumptions. -/
theorem semantics :
    Grading.ReadOnlySemanticClaimFor .flags (PureCall.readOnlyTask spec) bytes :=
  pureCall_semantics_of_generatedWith spec bytes graph valid entry entry_offset 12
    Observed (fun _ _ _ evidence => evidence.1) generated_vc

/-- Every prefix retains complete current memory and original-slot-only read
permission, for all independent flag streams. -/
theorem memory_policy (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec bytes input initial) :
    Grading.ReadOnlyPolicyFor .flags initial
      (fun before => before.memory = initial.memory) (PureCallAllowed initial) :=
  readOnly_policy_memoryWith valid pre.code (by simp) (generated_vc input initial pre)

/-- The sole reported stack read has an actual production decoded origin,
succeeds in that pre-state and reads the exact admitted runtime return target.
This is read binding, not a named full-ELF certificate. -/
theorem return_read_binding (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec bytes input initial) (choices : ChoiceStream FlagChoices) :
    ∃ result count before priorReads observation,
      runWith choices 12 initial = .ok result ∧ Observed input initial result ∧
      count < result.instructions ∧ BlockWith choices initial before count priorReads ∧
      stepWith (choices count) before = .ok observation ∧
      stackRead initial ∈ observation.reads ∧ before.memory = initial.memory ∧
      readWord before.memory (stackRead initial).address = .ok input.returnAddress ∧
      canonical input.returnAddress = true ∧ OperandReadSucceeds before (stackRead initial) := by
  obtain ⟨result,actual,observed,trace⟩ := executes input initial pre choices
  have member : stackRead initial ∈ result.reads := by
    rw [observed.2.2.2]
    exact List.mem_singleton_self _
  obtain ⟨count,before,priorReads,observation,bound,block,step,present,_allowed,succeeded⟩ :=
    trace.read_origin member
  obtain ⟨memory,_code,_rest⟩ := block_residualWith valid block pre.code
    (by simp) (generated_vc input initial pre)
  refine ⟨result,count,before,priorReads,observation,actual,observed,bound,block,step,
    present,memory,?_,pre.returnCanonical,succeeded⟩
  change readWord before.memory (initial.registers .rsp) = .ok input.returnAddress
  rw [memory]
  exact pre.stack

#print axioms semantics
#print axioms memory_policy
#print axioms return_read_binding
end EDSL.Corpus.V1.TriangularClangResources
#audit_edsl
