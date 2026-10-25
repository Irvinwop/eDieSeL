/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import tests.RexData32Base
import tests.Support.ExceptDecidable
import EDSL.X86.VCGen.Frame
import EDSL.X86.VCGen.Choices
import EDSL.X86.VCGen.Effects.Checked
import EDSL.X86.CallReturn.Machine
namespace EDSL.Tests.RexData32CFG
open X86 X86.Sequential
open scoped EDSL.Tests.Support
private def bytes : List Byte := [0x44,0x8b,4,0x87,0xc3]
private def graph : CFG.Graph := CFG.annotate
  [⟨0,.loadMem32Rex .r8 (.indexed .rdi .rax 2),false,0⟩,
   ⟨4,.legacy .ret,false,0⟩]
private def node : graph.Index := ⟨0,by decide⟩
private def data (a : Word) : Option Byte :=
  if 65544 ≤ a.toNat ∧ a.toNat < 65552 then [0,0x20,0,0,0,0,0,0][a.toNat-65544]?
  else RexData32.bytesAt 0x10000020c [1,0,0,0x80] a
private def initial : State := RexData32.entry bytes RexData32.registers data
private def Allowed (_ : State) (r : Read) : Prop :=
  r = ⟨.data,0x10000020c,4⟩ ∨ r = ⟨.stack,65544,8⟩
private def Post (r : Result) : Prop :=
  RexData32.gprs r.state =
    [3,0x8877665544332211,0x100000021,5,65552,0x100000025,0x100000100,
     0x100000200,0x80000001,0xf000000000000009,0xf00000000000000a,
     0xf00000000000000b,0x100000003,0x100000180,0x100000300,0xf00000000000000f] ∧
  r.state.flags = 0xfedcba9876543210 ∧ r.state.rip = 8192 ∧ r.instructions = 2 ∧
  r.reads = [⟨.data,0x10000020c,4⟩,⟨.stack,65544,8⟩]
private instance (s : State) (r : Read) : Decidable (Allowed s r) :=
  inferInstanceAs (Decidable (_ ∨ _))
private instance (r : Result) : Decidable (Post r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))
private instance : Decidable (VCGen.wp graph 4096 Allowed 2 node initial Post) :=
  VCGen.decidableWP graph 4096 Allowed (fun _ _ => inferInstance) 2 node initial Post
    (fun _ => inferInstance)

theorem actual_discovery : CFG.analyze bytes = .ok graph := by decide +kernel

-- Independent value, all-register/full-flag/read/cost postcondition plus the
-- generic full Memory equality theorem, through real checked executable RAM.
theorem checked_load_return (choices : Choices) :
    ∃ r, Sequential.run choices 2 initial = .ok r ∧ Post r ∧
      r.state.memory = initial.memory ∧ r.instructions ≤ 2 ∧
      VCGen.CheckedTrace Allowed choices initial r := by
  have accepted : VCGen.certify bytes graph 4096 Allowed 2 node initial Post = true := by
    decide +kernel
  exact VCGen.certify_sound_frame accepted choices

private def candidate (i : Sequential.Instruction) (offset : Nat) : CFG.Graph :=
  CFG.annotate [⟨0,i,false,0⟩,⟨offset,.legacy .ret,false,0⟩]
-- Wrong direction, width, bank, constructor and both short/hidden successor
-- offsets are rejected by the production byte/partition checks.
theorem encoding_mutant_graphs :
    [candidate (.loadMem32 .r8 (.indexed .rdi .rax 2)) 3,
     candidate (.loadMem32 .r8 (.indexed .rdi .rax 2)) 4,
     candidate (.loadMem32Rex .rax (.indexed .rdi .rax 2)) 4,
     candidate (.loadMem64 .r8 (.indexed .rdi .rax 2)) 4,
     candidate (.storeMem32 (.indexed .rdi .rax 2) .r8) 4,
     candidate (.loadMem32Rex .r8 (.indexed .rdi .rax 2)) 3].map (CFG.check bytes) =
     [false,false,false,false,false,false] := by decide +kernel

private def Small (_ : State) (r : Read) : Prop :=
  r = ⟨.data,0x10000020c,3⟩ ∨ r = ⟨.stack,65544,8⟩
private instance (s : State) (r : Read) : Decidable (Small s r) :=
  inferInstanceAs (Decidable (_ ∨ _))
private instance : Decidable (VCGen.wp graph 4096 Small 2 node initial Post) :=
  VCGen.decidableWP graph 4096 Small (fun _ _ => inferInstance) 2 node initial Post
    (fun _ => inferInstance)
theorem insufficient_read_extent :
    VCGen.check graph 4096 Small 2 node initial Post = false := by decide +kernel

private def stale : State := RexData32.entry [0x40,0x8b,4,0x87,0xc3]
  RexData32.registers data
private instance : Decidable (VCGen.wp graph 4096 Allowed 2 node stale Post) :=
  VCGen.decidableWP graph 4096 Allowed (fun _ _ => inferInstance) 2 node stale Post
    (fun _ => inferInstance)
-- A formula about the submitted graph is insufficient when actual REX.R differs.
theorem actual_prefix_binding :
    VCGen.check graph 4096 Allowed 2 node stale Post = true ∧
    VCGen.certify bytes graph 4096 Allowed 2 node stale Post = false := by decide +kernel

private def siblingView (af : Bool) : Except Error (List Word × Word × Word × Memory × List Read) := do
  let o ← CallReturn.rawStep af initial
  match o.result with
  | .next f => return (RexData32.gprs f,f.flags,f.rip,f.memory,o.reads)
  | _ => throw .unexpectedReturn
-- The sibling route consumes the exact REX bytes and retains the whole load
-- observation, including full64 addressing and the correct four-byte successor.
theorem callReturn_raw_load (af : Bool) :
    siblingView af = .ok
    ([3,0x8877665544332211,0x100000021,5,65544,0x100000025,0x100000100,
      0x100000200,0x80000001,0xf000000000000009,0xf00000000000000a,
      0xf00000000000000b,0x100000003,0x100000180,0x100000300,0xf00000000000000f],
     0xfedcba9876543210,4100,initial.memory,[⟨.data,0x10000020c,4⟩]) := by rfl

private instance : Decidable (VCGen.wpWith graph 4096 Allowed 2 node initial Post) :=
  VCGen.decidableWPWith graph 4096 Allowed (fun _ _ => inferInstance) 2 node initial Post
    (fun _ => inferInstance)
-- The same independent full-state contract is checked for every flag vector.
theorem checked_vector_load_return (choices : ChoiceStream FlagChoices) :
    ∃ r, runWith choices 2 initial = .ok r ∧ Post r ∧ r.instructions ≤ 2 ∧
      VCGen.CheckedTraceWith Allowed choices initial r := by
  have valid := CFG.analyzeWith_sound (profile := CFG.defaultProfile) actual_discovery
  have code : CodeAt initial.memory 4096 bytes := ELF.checkCode_sound _ _ _ (by decide +kernel)
  have accepted : VCGen.checkChoices graph 4096 Allowed 2 node initial Post = true := by decide +kernel
  exact VCGen.checked_soundWith valid code (by rfl) accepted choices

-- A finite, nontrivial current-state condition for this synthetic sequential
-- certificate. OS ownership/loans are checked separately by the resource tests.
private def Live (s : State) : Prop := s.registers .rdi = 0x100000200
private def EventPost (r : Result) (events : List AtomicEvent) : Prop := Post r ∧ events = []
private def liveDecision (s : State) : Decidable (Live s) := inferInstanceAs (Decidable (_ = _))
private def readDecision (s : State) (r : Read) : Decidable (Allowed s r) := inferInstance
private def eventDecision (r : Result) (events : List AtomicEvent) : Decidable (EventPost r events) :=
  inferInstanceAs (Decidable (_ ∧ _))
-- Actual separated code/CFG/resource-effect checks retain zero atomic events;
-- no submitted local transition or guessed final state is used.
theorem checked_effect_load_return (choices : ChoiceStream FlagChoices) :
    ∃ r events, runWith choices 2 initial = .ok r ∧ EventPost r events ∧
      r.instructions ≤ 2 ∧
      VCGen.Effects.Trace bytes 4096
        (VCGen.Effects.codeSeparatedPolicy bytes 4096 Live Allowed) choices initial r events := by
  have accepted : VCGen.Effects.certifySeparated bytes graph 4096 Live Allowed
      liveDecision readDecision 2 node initial EventPost eventDecision = true := by decide +kernel
  exact VCGen.Effects.certifySeparated_sound bytes graph 4096 Live Allowed
    liveDecision readDecision 2 node initial EventPost eventDecision accepted choices

end EDSL.Tests.RexData32CFG
#audit_edsl
