/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.DisplacedDataBase

namespace EDSL.Tests.DisplacedData
open X86

/-- A DATA4 load uses the old full64 address, zero extends, and preserves every
other GPR, the entire RAM/permission functions, and complete flags. -/
theorem load32_full (af : Bool) :
    let s := entry [0x8b,0x4a,4] registers (bytesAt 0x100000005 [0x78,0x56,0x34,0x92])
    nextView af s (fun after reads =>
      (gprs after, after.memory, after.flags, after.rip, reads)) =
    .ok ([0xffffffffffffffff,0x92345678,0x100000001,3,0x100000009,0x100000005,6,
      0x100000009,8,9,10,11,0x100000003,0x100000180,14,15],
      s.memory,0xfedcba9876543210,4099,[⟨.data,0x100000005,4⟩]) := by rfl

/-- Qword data and full prestate arithmetic cannot be replaced by DATA4. -/
theorem load64_full (af : Bool) :
    let s := entry [0x48,0x8b,0x47,8] registers
      (bytesAt 0x100000011 [1,0x23,0x45,0x67,0x89,0xab,0xcd,0xef])
    nextView af s (fun after reads =>
      (gprs after, after.memory, after.flags, after.rip, reads)) =
    .ok ([0xefcdab8967452301,0xfeedbeef12345678,0x100000001,3,0x100000009,
      0x100000005,6,0x100000009,8,9,10,11,0x100000003,0x100000180,14,15],
      s.memory,0xfedcba9876543210,4100,[⟨.data,0x100000011,8⟩]) := by rfl

/-- R13 aliases its real zero-displacement base; the read uses the old R13. -/
theorem rbp_r13_zero (af : Bool) :
    nextView af (entry [0x4d,0x8b,0x6d,0] registers
      (bytesAt 0x100000180 [1,2,3,4,5,6,7,8]))
      (fun after reads => (gprs after, after.flags, after.rip, reads)) =
    .ok ([0xffffffffffffffff,0xfeedbeef12345678,0x100000001,3,0x100000009,
      0x100000005,6,0x100000009,8,9,10,11,0x100000003,0x0807060504030201,14,15],
      0xfedcba9876543210,4100,[⟨.data,0x100000180,8⟩]) := by rfl

/-- REX.X turns encoded index4 into old R12; the destination aliases that index. -/
theorem rex_x_alias (af : Bool) :
    nextView af (entry [0x4f,0x8b,0x64,0xa5,0x80] registers
      (bytesAt 0x50000010c [1,2,3,4,5,6,7,8]))
      (fun after reads => (gprs after, after.flags, after.rip, reads)) =
    .ok ([0xffffffffffffffff,0xfeedbeef12345678,0x100000001,3,0x100000009,
      0x100000005,6,0x100000009,8,9,10,11,0x0807060504030201,0x100000180,14,15],
      0xfedcba9876543210,4101,[⟨.data,0x50000010c,8⟩]) := by cbv

theorem rex_without_x (af : Bool) :
    nextView af (entry [0x4d,0x8b,0x64,0xa5,0x80] registers
      (bytesAt 0x100000100 [1,2,3,4,5,6,7,8]))
      (fun after reads => (after.registers .r12,after.rip,reads)) =
    .ok (0x0807060504030201,4101,[⟨.data,0x100000100,8⟩]) := by cbv

/-- Absent-index SIB keeps every encoded scale and the signed displacement. -/
theorem scales_and_signs (af : Bool) :
    ([([0x48,0x8b,0x44,0x27,0x80],0xffffff89),
      ([0x48,0x8b,0x44,0x67,0xff],0x100000008),
      ([0x48,0x8b,0x44,0xa7,0],0x100000009),
      ([0x48,0x8b,0x44,0xe7,0x7f],0x100000088)] : List (List Byte × Word)).map
      (fun (code,address) => nextView af (entry code registers
        (bytesAt address [1,2,3,4,5,6,7,8])) (fun after reads =>
          (after.registers .rax,after.rip,reads))) =
    [.ok (0x0807060504030201,4101,[⟨.data,0xffffff89,8⟩]),
      .ok (0x0807060504030201,4101,[⟨.data,0x100000008,8⟩]),
      .ok (0x0807060504030201,4101,[⟨.data,0x100000009,8⟩]),
      .ok (0x0807060504030201,4101,[⟨.data,0x100000088,8⟩])] := by cbv

/-- A nonzero RBX index distinguishes all four scale multipliers independently. -/
theorem indexed_scales (af : Bool) :
    ([([0x48,0x8b,0x44,0x1f,0x80],0xffffff8c),
      ([0x48,0x8b,0x44,0x5f,0xff],0x10000000e),
      ([0x48,0x8b,0x44,0x9f,0],0x100000015),
      ([0x48,0x8b,0x44,0xdf,0x7f],0x1000000a0)] : List (List Byte × Word)).map
      (fun (code,address) => nextView af (entry code registers
        (bytesAt address [1,2,3,4,5,6,7,8])) (fun after reads =>
          (after.registers .rax,after.rip,reads))) =
    [.ok (0x0807060504030201,4101,[⟨.data,0xffffff8c,8⟩]),
      .ok (0x0807060504030201,4101,[⟨.data,0x10000000e,8⟩]),
      .ok (0x0807060504030201,4101,[⟨.data,0x100000015,8⟩]),
      .ok (0x0807060504030201,4101,[⟨.data,0x1000000a0,8⟩])] := by cbv

/-- Longest new form: W=0 REX MOVZX, SIB at4 and signed displacement at5. -/
theorem movzx_long (af : Bool) :
    nextView af (entry [0x47,0x0f,0xb6,0x64,0xa5,0x80] registers
      (bytesAt 0x50000010c [0xe7]))
      (fun after reads => (after.registers .r12,after.flags,after.rip,reads)) =
    .ok (0xe7,0xfedcba9876543210,4102,[⟨.data,0x50000010c,1⟩]) := by rfl

/-- Width8 CMP, whose address wraps only during arithmetic, keeps all context
except exactly the independently specified arithmetic flags and RIP. -/
theorem compare_sib (af : Bool) :
    let s := entry [0x80,0x7c,7,1,0] registers (bytesAt 0x100000009 [0])
    nextView af s (fun after reads =>
      (after.registers,after.memory,after.flags,after.rip,reads)) =
    .ok (s.registers,s.memory,0xfedcba9876543244,4101,[⟨.data,0x100000009,1⟩]) := by cbv

/-- Full64 carry and all six ADD flags, preserving every non-arithmetic bit. -/
theorem add64_carry (af : Bool) :
    nextView af (entry [0x48,3,0x47,0x10] registers
      (bytesAt 0x100000019 [1,0,0,0,0,0,0,0]))
      (fun after reads => (after.registers .rax,after.flags,after.rip,reads)) =
    .ok (0,0xfedcba9876543255,4100,[⟨.data,0x100000019,8⟩]) := by cbv

end EDSL.Tests.DisplacedData
#audit_edsl
