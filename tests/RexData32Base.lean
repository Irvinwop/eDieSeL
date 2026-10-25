/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.X86.Sequential.MachineChoices
import EDSL.X86.Sequential.DecodeTransport
import EDSL.X86.Sequential.Code
import EDSL.Audit
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.RexData32
open X86
-- This is a memory/input fixture only; every transition uses production step.
def entry (code : List Byte) (registers : Register → Word)
    (data : Word → Option Byte := fun _ => none) : State where
  registers := registers
  flags := 0xfedcba9876543210
  rip := 4096
  memory := {
    read := fun a => if 4096 ≤ a.toNat ∧ a.toNat < 4096 + code.length
      then code[a.toNat - 4096]? else data a
    executable := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + code.length)
    writable := fun _ => false }
def bytesAt (base : Word) (bytes : List Byte) (a : Word) : Option Byte := bytes[(a-base).toNat]?
def registers : Register → Word
  | .rax => 3 | .rcx => 0x8877665544332211 | .rdx => 0x100000021 | .rbx => 5
  | .rsp => 65544 | .rbp => 0x100000025 | .rsi => 0x100000100 | .rdi => 0x100000200
  | .r8 => 0xf000000000000008 | .r9 => 0xf000000000000009 | .r10 => 0xf00000000000000a
  | .r11 => 0xf00000000000000b | .r12 => 0x100000003 | .r13 => 0x100000180
  | .r14 => 0x100000300 | .r15 => 0xf00000000000000f
-- All modeled GPRs, in architectural code order.
def gprs (s : State) : List Word := [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,
  .r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15].map s.registers
-- Observation projection only: no instruction semantics or expected-value generation.
def nextView {α : Type} (choice : Bool) (state : State)
    (view : State → List Sequential.Read → α) : Except Error α := do
  let observed ← Sequential.step choice state
  match observed.result with
  | .next after => return view after observed.reads
  | _ => throw .unexpectedReturn
end EDSL.Tests.RexData32
