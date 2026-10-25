/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.TriangularGCCSelection
import EDSL.Corpus.V1.TriangularGCCClient
import EDSL.ELF.CallerResources.Stack
import EDSL.PureCall.ELFCertificateFor
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

/-! Neutral certificate for the exact named GCC function in its complete
unchanged ELF. The production sequential profile assumes stable ordinary RAM,
long mode, four-level canonical addresses, alignment checking disabled,
CET/IBT/shadow stacks disabled, and no asynchronous interference or MMIO.
Caller ownership, loans and lifetimes are current supplied logical authority.
Native CPU/OS/loader and compiler/source correspondence remain separate.
This supplies no task registration, grading packet, export or corpus credit. -/

namespace EDSL.Corpus.V1.TriangularGCCArtifact
open X86 X86.Sequential OS ELF.FunctionSymbol

abbrev spec := Arithmetic64.triangularModulo
abbrev bytes := TriangularGCCSelection.bytes
abbrev file := TriangularGCCSelection.file
abbrev name := TriangularGCCSelection.name
abbrev input := TriangularGCCSelection.input

theorem checked : input.check file name = true := TriangularGCCSelection.checked

abbrev caller := ELF.CallerResources.Stack.standard

/-- Every rounded LOAD page is fresh relative to the present return slot. -/
theorem fresh : ELF.fresh input.table.image caller.prior = true :=
  ELF.CallerResources.Stack.check_sound input.table.image 0x700008 0x654321
    (by decide +kernel)

/-- Current text and the original caller stack are disjoint. -/
theorem separate :
    Ownership.Disjoint ⟨input.function.window.base, input.bytes.length⟩ caller.region := by
  decide +kernel

/-- Universal domain True, all low32 inputs, arbitrary upper RDI and incoming
scratch/flags are unchanged. Input 2 only witnesses usefulness. -/
def certificate : PureCall.ELFCertificateFor .flags spec file name :=
  PureCall.ELFCertificateFor.ofCaller .flags spec input checked
    TriangularGCCClient.full_flags_semantics caller fresh ELF.CallerResources.Stack.standard_facts
    separate (2 : BitVec 32) (by change True; exact True.intro)
    (by change 2 ≤ (2 : BitVec 32).toNat; decide +kernel)

theorem binding :
    ELF.FunctionSymbol.CheckedMetadata file input.table.header input.metadata ∧
    input.function.Contract input.metadata name input.bytes.length ∧
    ELF.FunctionWindow.Layout file input.table ∧
    ELF.FunctionWindow.Selection file input.table.image input.function.window input.bytes :=
  certificate.binding

/-- Every admitted current call has the independent natural triangular result
in full64 RAX, the complete ABI/memory/nonarithmetic-flag frames and current
resources, for every independent flag-choice stream. Original read authority
holds at every actual continuing prefix. Admission adds no future success. -/
theorem resource (call : PureCall.ELFLoadedCall spec file name input) :
    Engine.AllExecutions ExecutionModel.flags.transition call.initial (fun result =>
      PureCall.Post spec (PureCall.resourceInput call.resource) call.initial result.state ∧
      CallResources.Current call.resource.call call.resource.shared result.state) ∧
    Grading.ReadOnlyPolicyFor .flags call.initial
      (CallResources.Current call.resource.call call.resource.shared)
      (fun _ read => CallResources.ReadAllowed call.resource.call call.resource.shared read) :=
  certificate.resource call

theorem nonvacuous : Grading.ReadOnlyNonvacuous (PureCall.readOnlyTask spec) bytes :=
  certificate.nonvacuous

/-- A useful installed call starts at the actual selected entry with current
executable text. Its precondition retains the original return stack and
present ownership/loans/lifetimes; it contains no execution/result premise. -/
theorem useful_execution :
    ∃ call : PureCall.ELFLoadedCall spec file name input,
      spec.useful call.resource.value ∧
      call.initial.rip = input.function.window.base ∧
      CodeAt call.initial.memory call.initial.rip input.bytes ∧
      Engine.AllExecutions ExecutionModel.flags.transition call.initial (fun result =>
        PureCall.Post spec (PureCall.resourceInput call.resource) call.initial result.state ∧
        CallResources.Current call.resource.call call.resource.shared result.state) ∧
      Grading.ReadOnlyPolicyFor .flags call.initial
        (CallResources.Current call.resource.call call.resource.shared)
        (fun _ read => CallResources.ReadAllowed call.resource.call call.resource.shared read) := by
  obtain ⟨call, useful, code, execution, policy⟩ := certificate.useful_execution
  exact ⟨call, useful, call.entry, code, execution, policy⟩

#print axioms checked
#print axioms fresh
#print axioms separate
#print axioms certificate
#print axioms binding
#print axioms resource
#print axioms nonvacuous
#print axioms useful_execution
end EDSL.Corpus.V1.TriangularGCCArtifact
#audit_edsl
