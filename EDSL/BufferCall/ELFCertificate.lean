/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.ELF.FunctionInput
import EDSL.BufferCall.Resources

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

/-!
Neutral, spec-indexed certificates for complete named ELF functions in the
existing sequential read-only execution model. The library client fixes Spec;
this API cannot select a weaker grader contract. Trusted TaskID registration
remains separate. In particular, a generic certificate supplies no registry,
packet-admission or corpus credit.

The target assumes stable ordinary RAM, long mode with four-level canonical
addresses, alignment checking disabled, CET/IBT and shadow stacks disabled,
supplied modeled ownership authority and no asynchronous interference. Native
OS authority, loading/startup, CPU correspondence and source preservation are
separate obligations. These constructors add no future-run, output,
success-policy or candidate-admission premise; the client domain is retained
unchanged. Clients must independently review the domain, result and usefulness
of their Spec. The generic type cannot enforce that independence.
-/

namespace EDSL.BufferCall
open X86 X86.Sequential OS.AddressSpace

/-- A present call in the complete current resource memory. EVERY installed
cell, including unrelated writable segments and every permission bit, is kept.
Text alone is insufficient. The exact caller slot and buffer loan handles are
those in resource, with the existing full ResourcePre and current-memory coupling. -/
structure ELFLoadedCall (spec : Spec) (file name : List Byte)
    (input : ELF.FunctionInput) (maxBytes : Nat := 64) where
  prior : Space
  loaded : ELF.Loaded
  admitted : input.admitWith maxBytes file name prior = .ok loaded
  resource : Resources spec
  initial : X86.State
  pre : ResourcePre spec input.bytes resource initial
  entry : initial.rip = input.function.window.base
  text : ELF.FunctionWindow.TextUnchanged (toMemory loaded.space) initial.memory
    input.function.window input.bytes.length
  retainedImage : ∀ address original, loaded.space.cells address = some original →
    resource.shared.resources.space.cells address = some original

/-- Spec, complete file, exact requested byte name and explicit byte bound index
all evidence. The default stays 64. Universal independent semantics and a useful
present loaded call are separate requirements; neither can substitute for the other. -/
structure ELFCertificate (spec : Spec) (file name : List Byte) (maxBytes : Nat := 64) where
  input : ELF.FunctionInput
  checked : input.checkWith maxBytes file name = true
  semantics : Grading.ReadOnlySemanticClaim (readOnlyTask spec) input.bytes
  inhabited : ∃ call : ELFLoadedCall spec file name input maxBytes,
    spec.useful call.resource.value

theorem ELFLoadedCall.code {spec : Spec} {file name : List Byte}
    {input : ELF.FunctionInput} {maxBytes : Nat}
    (call : ELFLoadedCall spec file name input maxBytes) :
    CodeAt call.initial.memory call.initial.rip input.bytes := by
  rw [call.entry]
  exact ELF.FunctionSymbol.admitted_current_codeWith call.admitted call.text

/-- Compose independent semantics with useful current resources at the actual
checked entry. No new executor, ownership world or successful future run is used. -/
def ELFCertificate.ofLoadedCallWith (maxBytes : Nat) {spec : Spec} {file name : List Byte}
    (input : ELF.FunctionInput) (checked : input.checkWith maxBytes file name = true)
    (semantics : Grading.ReadOnlySemanticClaim (readOnlyTask spec) input.bytes)
    (call : ELFLoadedCall spec file name input maxBytes)
    (useful : spec.useful call.resource.value) : ELFCertificate spec file name maxBytes :=
  ⟨input, checked, semantics, call, useful⟩

/-- Public default-checker entry point; no hidden byte-bound increase. -/
def ELFCertificate.ofLoadedCall {spec : Spec} {file name : List Byte}
    (input : ELF.FunctionInput) (checked : input.check file name = true)
    (semantics : Grading.ReadOnlySemanticClaim (readOnlyTask spec) input.bytes)
    (call : ELFLoadedCall spec file name input)
    (useful : spec.useful call.resource.value) : ELFCertificate spec file name :=
  ofLoadedCallWith 64 input
    ((input.checkWith64_eq_check file name).trans checked) semantics call useful

/-- The unchanged checker authenticates full metadata, the unique exact name,
complete symbol extent, executable LOAD layout and selected file bytes. -/
theorem ELFCertificate.binding {spec : Spec} {file name : List Byte} {maxBytes : Nat}
    (certificate : ELFCertificate spec file name maxBytes) :
    ELF.FunctionSymbol.CheckedMetadata file certificate.input.table.header
      certificate.input.metadata ∧
    certificate.input.function.Contract certificate.input.metadata name
      certificate.input.bytes.length ∧
    ELF.FunctionWindow.Layout file certificate.input.table ∧
    ELF.FunctionWindow.Selection file certificate.input.table.image
      certificate.input.function.window certificate.input.bytes maxBytes :=
  ELF.FunctionSymbol.checked_soundWith certificate.checked

/-- Both raw and resource nonvacuity come from this same useful loaded call. -/
theorem ELFCertificate.nonvacuous {spec : Spec} {file name : List Byte} {maxBytes : Nat}
    (certificate : ELFCertificate spec file name maxBytes) :
    Grading.ReadOnlyNonvacuous (readOnlyTask spec) certificate.input.bytes := by
  obtain ⟨call, useful⟩ := certificate.inhabited
  exact nonvacuous_of_resource call.resource call.initial useful call.pre

/-- Every current call for these checked bytes has the independent mathematical
and ABI postcondition, exact Current resources and original read policy, for all
AF streams. This argument is universal, not restricted to the useful witness. -/
theorem ELFCertificate.resource {spec : Spec} {file name : List Byte} {maxBytes : Nat}
    (certificate : ELFCertificate spec file name maxBytes)
    (call : ELFLoadedCall spec file name certificate.input maxBytes) :
    AllExecutions call.initial (fun result =>
      Post spec (resourceInput call.resource) call.initial result.state ∧
      Current call.resource result.state) ∧
    Grading.ReadOnlyPolicy call.initial (Current call.resource)
      (fun _ read => ReadAllowed call.resource read) :=
  certificate.semantics.resource call.resource call.initial call.pre

/-- Useful execution at the actual selected address, retaining the exact same
whole-memory authority at return and read permission at every continuing prefix. -/
theorem ELFCertificate.useful_execution {spec : Spec} {file name : List Byte} {maxBytes : Nat}
    (certificate : ELFCertificate spec file name maxBytes) :
    ∃ call : ELFLoadedCall spec file name certificate.input maxBytes,
      spec.useful call.resource.value ∧
      CodeAt call.initial.memory call.initial.rip certificate.input.bytes ∧
      AllExecutions call.initial (fun result =>
        Post spec (resourceInput call.resource) call.initial result.state ∧
        Current call.resource result.state) ∧
      Grading.ReadOnlyPolicy call.initial (Current call.resource)
        (fun _ read => ReadAllowed call.resource read) := by
  obtain ⟨call, useful⟩ := certificate.inhabited
  exact ⟨call, useful, call.code, certificate.resource call⟩

end EDSL.BufferCall
