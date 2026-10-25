/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionSelection
import EDSL.Corpus.V1.ClangLookup
import EDSL.Corpus.V1.TriangularClangResources
import EDSL.ELF.CallerResources.Stack
import EDSL.PureCall.ELFCertificateFor
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

/-! Neutral full-file/caller certificate for the unchanged Clang triangular
function. This is separate from corpus registration, scoring and export.
The production sequential profile assumes stable ordinary RAM, 64-bit mode,
four-level canonical addresses, alignment checking off, CET/IBT/shadow stacks
off and no asynchronous interference. Caller ownership is supplied logical
authority; native loader/CPU/OS and compiler/source correspondence are separate.
-/

namespace EDSL.Corpus.V1.TriangularClangArtifact
open X86 X86.Sequential OS ELF.FunctionSymbol

abbrev spec := Arithmetic64.triangularModulo
abbrev bytes := TriangularClangBody.bytes
abbrev file := Clang.file

/-- Exact complete ELF byte name, excluding its terminating NUL. -/
def name : List Byte := [99,95,116,114,105,97,110,103,117,108,97,114,95,109,111,100,54,52]

/-- Untrusted static-table selection hint: address 4199440, offset 5136,
complete declared size 37. The production checker authenticates all of these. -/
def symbolIndex : Fin Clang.symbols26.rows.length := ⟨80, by decide +kernel⟩

def function : Function :=
  ELF.FunctionSelection.function Clang.symbols26 Clang.sh13 symbolIndex

def input : ELF.FunctionInput :=
  ELF.FunctionSelection.input Clang.table Clang.metadata Clang.symbols26 Clang.sh13
    symbolIndex bytes

/-- Check the whole original file, unique exact name, complete symbol extent,
section/LOAD mapping and executable bytes under the unchanged default bound.
Only existing full-file proofs and bounded lookup normalization are reused. -/
theorem checked : input.check file name = true := by
  change check Clang.file Clang.table Clang.metadata name function bytes = true
  unfold check
  rw [Clang.metadataAccepted]
  unfold ELF.FunctionWindow.check
  have bounded : function.window.offset ≤ 44240 := by decide +kernel
  rw [Clang.layoutAccepted, Clang.fileDropAt _ bounded]
  simp only [Clang.fileLength, ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
    ELF.install, ELF.segmentCell, ClangLookup.fileByte]
  decide +kernel

abbrev caller := ELF.CallerResources.Stack.standard

/-- Rounded LOAD pages are fresh relative to this present caller slot. -/
theorem fresh : ELF.fresh input.table.image caller.prior = true :=
  ELF.CallerResources.Stack.check_sound input.table.image 0x700008 0x654321
    (by decide +kernel)

/-- Original code/caller separation, independently of future execution. -/
theorem separate :
    Ownership.Disjoint ⟨input.function.window.base, input.bytes.length⟩ caller.region := by
  decide +kernel

/-- Domain is True for every low32 input. Input 2 only witnesses usefulness;
it does not restrict universal callers, upper32 bits or incoming flags. -/
def certificate : PureCall.ELFCertificateFor .flags spec file name :=
  PureCall.ELFCertificateFor.ofCaller .flags spec input checked
    TriangularClangResources.semantics caller fresh ELF.CallerResources.Stack.standard_facts
    separate (2 : BitVec 32) (by change True; exact True.intro)
    (by change 2 ≤ (2 : BitVec 32).toNat; decide +kernel)

/-- Authentication of the same bytes indexing the complete-vector semantics. -/
theorem binding :
    ELF.FunctionSymbol.CheckedMetadata file input.table.header input.metadata ∧
    input.function.Contract input.metadata name input.bytes.length ∧
    ELF.FunctionWindow.Layout file input.table ∧
    ELF.FunctionWindow.Selection file input.table.image input.function.window input.bytes :=
  certificate.binding

/-- Every admitted current call has the independent mathematical/ABI result,
current resources at return and the original read authority at actual prefixes,
for every stream of independent flag choices. -/
theorem resource (call : PureCall.ELFLoadedCall spec file name input) :
    Engine.AllExecutions ExecutionModel.flags.transition call.initial (fun result =>
      PureCall.Post spec (PureCall.resourceInput call.resource) call.initial result.state ∧
      CallResources.Current call.resource.call call.resource.shared result.state) ∧
    Grading.ReadOnlyPolicyFor .flags call.initial
      (CallResources.Current call.resource.call call.resource.shared)
      (fun _ read => CallResources.ReadAllowed call.resource.call call.resource.shared read) :=
  certificate.resource call

/-- Both original useful raw/current-resource domains are actually inhabited. -/
theorem nonvacuous : Grading.ReadOnlyNonvacuous (PureCall.readOnlyTask spec) bytes :=
  certificate.nonvacuous

/-- The certificate API supplies a useful installed call at the actual selected
entry, current executable text and the same universal result/resource policy.
No result, trace or future success is an admission premise. -/
theorem useful_execution :
    ∃ call : PureCall.ELFLoadedCall spec file name input,
      spec.useful call.resource.value ∧
      CodeAt call.initial.memory call.initial.rip input.bytes ∧
      Engine.AllExecutions ExecutionModel.flags.transition call.initial (fun result =>
        PureCall.Post spec (PureCall.resourceInput call.resource) call.initial result.state ∧
        CallResources.Current call.resource.call call.resource.shared result.state) ∧
      Grading.ReadOnlyPolicyFor .flags call.initial
        (CallResources.Current call.resource.call call.resource.shared)
        (fun _ read => CallResources.ReadAllowed call.resource.call call.resource.shared read) :=
  certificate.useful_execution

#print axioms checked
#print axioms fresh
#print axioms separate
#print axioms certificate
#print axioms binding
#print axioms resource
#print axioms nonvacuous
#print axioms useful_execution
end EDSL.Corpus.V1.TriangularClangArtifact
#audit_edsl
