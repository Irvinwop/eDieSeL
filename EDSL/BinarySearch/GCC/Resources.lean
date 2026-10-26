import EDSL.BinarySearch.GCC.Body
import EDSL.Corpus.ReadOnlyCallTransport

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
    throwError "GCC loop stage: effective options differ from the required profile"
  Lean.logInfo "EFFECTIVE_OPTIONS autoImplicit=false warningAsError=true Elab.async=false maxHeartbeats=300000 maxRecDepth=128"

namespace EDSL.BinarySearch.GCC
open X86 X86.Sequential OS BufferCall

/-- Every present admitted resource world receives the universal result,
exact return/frame contract and current original authority at every prefix.
This uses the shared adapter, without installing or executing an ELF. -/
theorem resources (resource : Resources spec) (initial : X86.State)
    (pre : ResourcePre spec bytes resource initial) :
    AllExecutions initial (fun result =>
      Post spec (resourceInput resource) initial result.state ∧ Current resource result.state) ∧
    Grading.ReadOnlyPolicy initial (Current resource) (fun _ read => ReadAllowed resource read) :=
  semantics.resource resource initial pre

/-- Attach the exact body in a preexisting manager using the production
caller/buffer bridge. The original caller slot and full snapshot handles are
retained; admission uses only current code, mathematics and current loans. -/
theorem attached_resources {resource : Resources spec} {before : Corpus.BufferResources.Managed}
    {entry : Word} {oldBytes : List Byte} {initial : X86.State}
    (attached : Corpus.ReadOnlyCalls.Attached before resource.call.worker ⟨entry, bytes.length⟩ [])
    (same : before.shared = resource.shared)
    (pre : ResourcePre spec oldBytes resource initial)
    (code : CodeAt (AddressSpace.toMemory resource.shared.resources.space) entry bytes) :
    let retained := Corpus.ReadOnlyCallTransport.retarget resource bytes attached
    AllExecutions { initial with rip := entry } (fun result =>
      Post spec (resourceInput retained) { initial with rip := entry } result.state ∧
      Current retained result.state) ∧
    Grading.ReadOnlyPolicy { initial with rip := entry } (Current retained)
      (fun _ read => ReadAllowed retained read) := by
  exact resources _ _ (Corpus.ReadOnlyCallTransport.retarget_pre attached same pre code)

#print axioms resources
#print axioms attached_resources
end EDSL.BinarySearch.GCC
#audit_edsl
