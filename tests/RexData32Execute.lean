/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import tests.RexData32Base
import tests.Support.ExceptDecidable
namespace EDSL.Tests.RexData32
open X86 X86.Sequential
open scoped EDSL.Tests.Support
-- Full GPRs, full flags, exact RIP, entire Memory (including both permission
-- functions), and exact read trace are observed together after production Sequential.step.
theorem dot_load_full (af : Bool) :
    let s := entry [0x44,0x8b,0x0c,0x86] registers
      (fun a => if a < 0x100000000 then some 0x11 else bytesAt 0x10000010c [0x78,0x56,0x34,0x92] a)
    nextView af s (fun f reads => (gprs f,f.flags,f.rip,f.memory,reads)) =
    .ok ([3,0x8877665544332211,0x100000021,5,65544,0x100000025,0x100000100,
      0x100000200,0xf000000000000008,0x92345678,0xf00000000000000a,
      0xf00000000000000b,0x100000003,0x100000180,0x100000300,0xf00000000000000f],
      0xfedcba9876543210,4100,s.memory,[⟨.data,0x10000010c,4⟩]) := by
  dsimp only
  have decoded : Sequential.decodeAt (entry [0x44,0x8b,0x0c,0x86] registers
      (fun a => if a < 0x100000000 then some 0x11 else bytesAt 0x10000010c [0x78,0x56,0x34,0x92] a)) = .ok (.loadMem32Rex .r9 (.indexed .rsi .rax 2)) := by decide +kernel
  simp only [nextView,Sequential.step,decoded,ok_bind,execute_loadMem32Rex]
  rfl

theorem index_alias_full (af : Bool) :
    let s := entry [0x47,0x8b,0x64,0xa5,0x80] registers
      (bytesAt 0x50000010c [4,3,2,0xf1])
    nextView af s (fun f reads => (gprs f,f.flags,f.rip,f.memory,reads)) =
    .ok ([3,0x8877665544332211,0x100000021,5,65544,0x100000025,0x100000100,
      0x100000200,0xf000000000000008,0xf000000000000009,0xf00000000000000a,
      0xf00000000000000b,0xf1020304,0x100000180,0x100000300,0xf00000000000000f],
      0xfedcba9876543210,4101,s.memory,[⟨.data,0x50000010c,4⟩]) := by
  dsimp only
  have decoded : Sequential.decodeAt (entry [0x47,0x8b,0x64,0xa5,0x80] registers
      (bytesAt 0x50000010c [4,3,2,0xf1])) = .ok (.loadMem32Rex .r12 (.sibDisp8 .r13 (some .r12) 2 0x80)) := by decide +kernel
  simp only [nextView,Sequential.step,decoded,ok_bind,execute_loadMem32Rex]
  rfl

theorem base_alias_full (af : Bool) :
    let s := entry [0x45,0x8b,0x6d,0] registers (bytesAt 0x100000180 [3,2,1,0x80])
    nextView af s (fun f reads => (gprs f,f.flags,f.rip,f.memory,reads)) =
    .ok ([3,0x8877665544332211,0x100000021,5,65544,0x100000025,0x100000100,
      0x100000200,0xf000000000000008,0xf000000000000009,0xf00000000000000a,
      0xf00000000000000b,0x100000003,0x80010203,0x100000300,0xf00000000000000f],
      0xfedcba9876543210,4100,s.memory,[⟨.data,0x100000180,4⟩]) := by
  dsimp only
  have decoded : Sequential.decodeAt (entry [0x45,0x8b,0x6d,0] registers (bytesAt 0x100000180 [3,2,1,0x80])) = .ok (.loadMem32Rex .r13 (.baseDisp8 .r13 0)) := by decide +kernel
  simp only [nextView,Sequential.step,decoded,ok_bind,execute_loadMem32Rex]
  rfl

theorem rsp_full (af : Bool) :
    let s := entry [0x40,0x8b,0x67,0] registers (bytesAt 0x100000200 [0x78,0x56,0x34,0x92])
    nextView af s (fun f reads => (gprs f,f.flags,f.rip,f.memory,reads)) =
    .ok ([3,0x8877665544332211,0x100000021,5,0x92345678,0x100000025,0x100000100,
      0x100000200,0xf000000000000008,0xf000000000000009,0xf00000000000000a,
      0xf00000000000000b,0x100000003,0x100000180,0x100000300,0xf00000000000000f],
      0xfedcba9876543210,4100,s.memory,[⟨.data,0x100000200,4⟩]) := by
  dsimp only
  have decoded : Sequential.decodeAt (entry [0x40,0x8b,0x67,0] registers (bytesAt 0x100000200 [0x78,0x56,0x34,0x92])) = .ok (.loadMem32Rex .rsp (.baseDisp8 .rdi 0)) := by decide +kernel
  simp only [nextView,Sequential.step,decoded,ok_bind,execute_loadMem32Rex]
  rfl

-- Arithmetic expectations are fixed addresses, not Address.eval outputs.
theorem scales_and_signed_offsets (af : Bool) :
    ([([0x40,0x8b,0x44,0x1f,0x80],0x100000185),
      ([0x40,0x8b,0x44,0x5f,0xff],0x100000209),
      ([0x40,0x8b,0x44,0x9f,0],0x100000214),
      ([0x40,0x8b,0x44,0xdf,0x7f],0x1000002a7),
      ([0x45,0x8b,0x64,0xa5,0x80],0x100000100)] : List (List Byte × Word)).map
      (fun (code,p) => nextView af (entry code registers (bytesAt p [0xff,0xff,0xff,0xff]))
        (fun f reads => (f.registers .rax,f.registers .r12,f.rip,reads))) =
    [.ok (0xffffffff,0x100000003,4101,[⟨.data,0x100000185,4⟩]),
     .ok (0xffffffff,0x100000003,4101,[⟨.data,0x100000209,4⟩]),
     .ok (0xffffffff,0x100000003,4101,[⟨.data,0x100000214,4⟩]),
     .ok (0xffffffff,0x100000003,4101,[⟨.data,0x1000002a7,4⟩]),
     .ok (3,0xffffffff,4101,[⟨.data,0x100000100,4⟩])] := by cases af <;> decide +kernel

-- All choices, all states, all aliases: the production vector route has no
-- undefined flags, no vector-only operation and no store/locked effect.
theorem no_choices_or_writes (s : State) (d : Register) (a : Address) (c : FlagChoices) :
    let i := Sequential.Instruction.loadMem32Rex d a
    i.undefinedFlags s = [] ∧ i.boolChoiceProfile = true ∧
    i.storeIntent s = none ∧ i.storeIntent64 s = none ∧ i.isLocked = false ∧
    executeWith s i c = Sequential.execute s i false := by exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem full_prestate_context {s : State} {d : Register} {a : Address} {v : BitVec 32}
    (decoded : Sequential.decodeAt s = .ok (.loadMem32Rex d a))
    (loaded : loadDWord s.memory (a.eval s) = .ok v) (af : Bool) :
    ∃ f, Sequential.step af s = .ok ⟨.next f,[⟨.data,a.eval s,4⟩]⟩ ∧
      f.registers d = v.setWidth 64 ∧
      (∀ r, r ≠ d → f.registers r = s.registers r) ∧
      f.memory = s.memory ∧ f.flags = s.flags ∧
      f.rip = s.rip + BitVec.ofNat 64 (3+a.suffixBytes) := by
  rw [step_eq_execute af decoded]
  exact execute_loadMem32Rex_context af loaded
end EDSL.Tests.RexData32
#audit_edsl
