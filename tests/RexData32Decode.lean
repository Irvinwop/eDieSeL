/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import tests.RexData32Base
import tests.Support.ExceptDecidable
namespace EDSL.Tests.RexData32
open X86 X86.Sequential
open scoped EDSL.Tests.Support
-- Frozen corpus witnesses and independently reviewed exact decoded operands.
theorem corpus_loads :
    [[0x44,0x8b,0x0c,0x86],[0x44,0x8b,0x04,0x87],[0x41,0x8b,0x06]].map
      (fun bs => Sequential.decodeAt (codeState bs 0)) =
    [.ok (.loadMem32Rex .r9 (.indexed .rsi .rax 2)),
     .ok (.loadMem32Rex .r8 (.indexed .rdi .rax 2)),
     .ok (.loadMem32Rex .rax (.base .r14))] := by decide +kernel
-- The table is literal: it does not derive expectations from ModRM/REX helpers.
theorem all_prefix_banks :
    [[0x40,0x8b,7],[0x41,0x8b,7],[0x42,0x8b,4,0x27],[0x43,0x8b,4,0x27],
     [0x44,0x8b,7],[0x45,0x8b,7],[0x46,0x8b,4,0x27],[0x47,0x8b,4,0x27],
     [0x42,0x8b,7]].map (fun bs => Sequential.decodeAt (codeState bs 0)) =
    [.ok (.loadMem32Rex .rax (.base .rdi)),.ok (.loadMem32Rex .rax (.base .r15)),
     .ok (.loadMem32Rex .rax (.indexed .rdi .r12 0)),
     .ok (.loadMem32Rex .rax (.indexed .r15 .r12 0)),
     .ok (.loadMem32Rex .r8 (.base .rdi)),.ok (.loadMem32Rex .r8 (.base .r15)),
     .ok (.loadMem32Rex .r8 (.indexed .rdi .r12 0)),
     .ok (.loadMem32Rex .r8 (.indexed .r15 .r12 0)),
     .ok (.loadMem32Rex .rax (.base .rdi))] := by decide +kernel

theorem displaced_forms :
    [[0x45,0x8b,0x6d,0],[0x47,0x8b,0x64,0xa5,0x80],
     [0x45,0x8b,0x64,0xa5,0x80],[0x40,0x8b,0x67,0],
     [0x40,0x8b,0x44,0x1f,0x80],[0x40,0x8b,0x44,0x5f,0xff],
     [0x40,0x8b,0x44,0x9f,0],[0x40,0x8b,0x44,0xdf,0x7f]].map
      (fun bs => Sequential.decodeAt (codeState bs 0)) =
    [.ok (.loadMem32Rex .r13 (.baseDisp8 .r13 0)),
     .ok (.loadMem32Rex .r12 (.sibDisp8 .r13 (some .r12) 2 0x80)),
     .ok (.loadMem32Rex .r12 (.sibDisp8 .r13 none 2 0x80)),
     .ok (.loadMem32Rex .rsp (.baseDisp8 .rdi 0)),
     .ok (.loadMem32Rex .rax (.sibDisp8 .rdi (some .rbx) 0 0x80)),
     .ok (.loadMem32Rex .rax (.sibDisp8 .rdi (some .rbx) 1 0xff)),
     .ok (.loadMem32Rex .rax (.sibDisp8 .rdi (some .rbx) 2 0)),
     .ok (.loadMem32Rex .rax (.sibDisp8 .rdi (some .rbx) 3 0x7f))] := by decide +kernel

theorem width_and_original_api :
    (Sequential.decodeAt (codeState [0x41,0x8b,6] 0),Sequential.decodeAt (codeState [0x49,0x8b,6] 0),
     Sequential.decodeAt (codeState [0x8b,6] 0),Sequential.decodeAt (codeState [0x8b,0xc0] 0)) =
    (.ok (.loadMem32Rex .rax (.base .r14)),.ok (.loadMem64 .rax (.base .r14)),
     .ok (.legacy .loadEaxRsi),.ok (.movReg32 .rax .rax)) := by decide +kernel
end EDSL.Tests.RexData32
#audit_edsl
