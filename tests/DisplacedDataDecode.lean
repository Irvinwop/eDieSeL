/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.DisplacedDataBase
import EDSL.X86.CallReturn.Decode
import tests.Support.ExceptDecidable

open scoped EDSL.Tests.Support

namespace EDSL.Tests.DisplacedData
open X86

/-- Literal encodings independently specify direction, bank and raw displacement. -/
theorem selected_encodings :
    ([[0x80,0x7c,0x07,0x01,0], [0x8b,0x4a,4], [0x89,0x4f,0xfc],
      [0x89,0x57,0xfc], [0x89,0x47,0xfc], [0x48,0x8b,0x47,8],
      [0x48,3,0x47,0x10], [0x48,3,0x47,0x18], [0x8b,0x45,0],
      [0x4d,0x8b,0x6d,0], [0x4f,0x8b,0x64,0xa5,0x80],
      [0x4d,0x8b,0x64,0xa5,0x80], [0x48,0x8b,0x44,0x24,0],
      [0x47,0x0f,0xb6,0x64,0xa5,0x80], [0x3a,0x46,0],
      [0x44,0x3a,0x46,0], [0x38,0x4a,4], [0x39,0x4a,4],
      [3,0x4a,4], [0x0f,0xb6,0x40,0], [0x40,0x8b,0x40,0]] : List (List Byte)).map
      (fun code => Sequential.decodeAt (entry code)) =
    [.ok (.cmpMemImm8 (.sibDisp8 .rdi (some .rax) 0 1) 0),
      .ok (.loadMem32 .rcx (.baseDisp8 .rdx 4)),
      .ok (.storeMem32 (.baseDisp8 .rdi 0xfc) .rcx),
      .ok (.storeMem32 (.baseDisp8 .rdi 0xfc) .rdx),
      .ok (.storeMem32 (.baseDisp8 .rdi 0xfc) .rax),
      .ok (.loadMem64 .rax (.baseDisp8 .rdi 8)),
      .ok (.addMem64 .rax (.baseDisp8 .rdi 0x10)),
      .ok (.addMem64 .rax (.baseDisp8 .rdi 0x18)),
      .ok (.loadMem32 .rax (.baseDisp8 .rbp 0)),
      .ok (.loadMem64 .r13 (.baseDisp8 .r13 0)),
      .ok (.loadMem64 .r12 (.sibDisp8 .r13 (some .r12) 2 0x80)),
      .ok (.loadMem64 .r12 (.sibDisp8 .r13 none 2 0x80)),
      .ok (.loadMem64 .rax (.sibDisp8 .rsp none 0 0)),
      .ok (.movzxMem8 .r12 (.sibDisp8 .r13 (some .r12) 2 0x80) true),
      .ok (.cmpRegMem8 .rax (.baseDisp8 .rsi 0) false),
      .ok (.cmpRegMem8 .r8 (.baseDisp8 .rsi 0) true),
      .ok (.cmpMemReg8 (.baseDisp8 .rdx 4) .rcx),
      .ok (.cmpMemReg32 (.baseDisp8 .rdx 4) .rcx),
      .ok (.addMem32 .rcx (.baseDisp8 .rdx 4)),
      .ok (.movzxMem8 .rax (.baseDisp8 .rax 0) false),
      .ok (.loadMem32Rex .rax (.baseDisp8 .rax 0))] := by decide +kernel

/-- The explicit zero displacement still consumes a byte and is a real RBP base. -/
theorem lengths :
    ([Sequential.Instruction.loadMem32 .rax (.baseDisp8 .rbp 0),
      .loadMem64 .r13 (.baseDisp8 .r13 0),
      .loadMem64 .rax (.sibDisp8 .rsp none 0 0),
      .movzxMem8 .r12 (.sibDisp8 .r13 (some .r12) 2 0x80) true,
      .cmpMemImm8 (.sibDisp8 .rdi (some .rax) 0 1) 0]).map
        Sequential.Instruction.length = [3,4,5,6,5] := by rfl

/-- Unsupported prefixes, high byte registers, mod10 and mod00 absent bases/indices
retain their established rejection behavior. No suffix is read for wrong /group. -/
theorem rejected_forms :
    ([[0x80,0x40], [0x38,0x60], [0x3a,0x60], [0x8b,0x82],
      [0x48,0x8b,0x05], [0x48,0x8b,0x04,0x24], [0x48,0x8b,0x04,0x25],
      [0x40,0x8b,0x80,0,0,0,0], [0x67,0x8b,0x40,0]] : List (List Byte)).map
      (fun code => Sequential.decodeAt (entry code)) =
    [.error .unsupportedEncoding,.error .unsupportedEncoding,.error .unsupportedEncoding,
      .error .unsupportedEncoding,.error .unsupportedEncoding,.error .unsupportedEncoding,
      .error .unsupportedEncoding,.error .unsupportedEncoding,
      .error (.unsupportedOpcode 0x67)] := by decide +kernel

/-- Ordinary DATA accessed through RSP never becomes the original STACK8 read. -/
theorem rsp_is_data : ¬Sequential.CallerOnly
    (.loadMem64 .rax (.sibDisp8 .rsp none 0 0)) := by exact id

end EDSL.Tests.DisplacedData
#audit_edsl
