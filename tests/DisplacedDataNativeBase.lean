/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import tests.DisplacedDataBase
namespace EDSL.Tests.DisplacedDataNative
open X86
open DisplacedData
def initial (code : List Byte) (pre : List Word) (flags address : Word) (before : List Byte) : State :=
  { entry code (fun r => if r = .rax then pre[0]! else if r = .rcx then pre[1]! else if r = .rdx then pre[2]! else if r = .rbx then pre[3]! else if r = .rsp then pre[4]! else if r = .rbp then pre[5]! else if r = .rsi then pre[6]! else if r = .rdi then pre[7]! else if r = .r8 then pre[8]! else if r = .r9 then pre[9]! else if r = .r10 then pre[10]! else if r = .r11 then pre[11]! else if r = .r12 then pre[12]! else if r = .r13 then pre[13]! else if r = .r14 then pre[14]! else if r = .r15 then pre[15]! else 0)
    (bytesAt (address-8) before) (fun a => decide (address ≤ a ∧ a < address + BitVec.ofNat 64 (before.length-8))) with flags := flags }
def view (af : Bool) (s : State) (address : Word) (width : Nat) :=
  nextView af s (fun after reads => (gprs after,after.flags,after.rip,reads,
    (List.range (width+8)).map (fun i => after.memory.read (address-8 + BitVec.ofNat 64 i))))
end EDSL.Tests.DisplacedDataNative
