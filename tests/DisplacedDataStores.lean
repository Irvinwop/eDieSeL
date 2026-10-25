/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import tests.DisplacedDataBase

namespace EDSL.Tests.DisplacedData
open X86

/-- Exact signed-disp8 DWORD store changes just the low four source bytes,
retains every GPR and flag, and preserves complete permission functions. -/
theorem store32_full (af : Bool) :
    let s := entry [0x89,0x4f,0xfc] registers (fun _ => some 0xa5) (fun _ => true)
    nextView af s (fun after reads => (after.registers,after.flags,after.rip,reads,
      after.memory.executable,after.memory.writable,
      ([0x100000004,0x100000005,0x100000006,0x100000007,0x100000008,0x100000009] :
        List Word).map after.memory.read)) =
    .ok (s.registers,0xfedcba9876543210,4099,[],s.memory.executable,s.memory.writable,
      [some 0xa5,some 0x78,some 0x56,some 0x34,some 0x12,some 0xa5]) := by rfl

/-- Qword writes retain the independently specified high half and exact endpoints. -/
theorem store64_full (af : Bool) :
    let s := entry [0x48,0x89,0x4f,0xfc] registers (fun _ => some 0xa5) (fun _ => true)
    nextView af s (fun after reads => (after.registers,after.flags,after.rip,reads,
      after.memory.executable,after.memory.writable,
      (List.range 10).map (fun i => after.memory.read (0x100000004 + BitVec.ofNat 64 i)))) =
    .ok (s.registers,0xfedcba9876543210,4100,[],s.memory.executable,s.memory.writable,
      [some 0xa5,some 0x78,some 0x56,some 0x34,some 0x12,some 0xef,some 0xbe,
        some 0xed,some 0xfe,some 0xa5]) := by rfl

/-- Full outside-frame behavior is inherited from the real checked primitive,
for arbitrary RAM and every query, not a finite sentinel approximation. -/
theorem displaced_store64_outside {before after : State} {base source : Register}
    {d : Byte} {af : Bool} {reads : List Sequential.Read}
    (decoded : Sequential.decodeAt before = .ok (.storeMem64 (.baseDisp8 base d) source))
    (actual : Sequential.step af before = .ok ⟨.next after,reads⟩) :
    after.registers = before.registers ∧ after.flags = before.flags ∧
      (∀ query, 8 ≤ (query-(before.registers base+d.signExtend 64)).toNat →
        after.memory.read query = before.memory.read query) ∧
      after.memory.executable = before.memory.executable ∧
      after.memory.writable = before.memory.writable ∧ reads = [] := by
  have executed := actual
  rw [Sequential.step_eq_execute af decoded] at executed
  have intent : Sequential.Instruction.storeIntent64
      (.storeMem64 (.baseDisp8 base d) source) before =
      some (before.registers base+d.signExtend 64,before.registers source) := rfl
  obtain ⟨registers,flags,_,_,outside,executable,writable,noReads⟩ :=
    Sequential.execute_storeIntent64_frame intent executed rfl
  exact ⟨registers,flags,outside,executable,writable,noReads⟩

end EDSL.Tests.DisplacedData
#audit_edsl
