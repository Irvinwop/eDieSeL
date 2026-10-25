/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Address32
import EDSL.X86.Sequential.DecodeTransport
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.DisplacedData
open X86

/-- Executable code is separate from the ordinary operand mapping. -/
def entry (code : List Byte) (registers : Register → Word := fun _ => 0)
    (data : Word → Option Byte := fun _ => none)
    (writable : Word → Bool := fun _ => false) : State where
  registers := registers
  flags := 0xfedcba9876543210
  rip := 4096
  memory := {
    read := fun a => if 4096 ≤ a.toNat ∧ a.toNat < 4096 + code.length
      then code[a.toNat - 4096]? else data a
    executable := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + code.length)
    writable := writable }

def registers : Register → Word
  | .rax => 0xffffffffffffffff | .rcx => 0xfeedbeef12345678
  | .rdx => 0x100000001 | .rbx => 3 | .rsp => 0x100000009 | .rbp => 0x100000005
  | .rsi => 6 | .rdi => 0x100000009 | .r8 => 8 | .r9 => 9 | .r10 => 10
  | .r11 => 11 | .r12 => 0x100000003 | .r13 => 0x100000180 | .r14 => 14 | .r15 => 15

def gprs (s : State) : List Word := [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,
    .r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15].map s.registers

def bytesAt (base : Word) (bytes : List Byte) (a : Word) : Option Byte :=
  bytes[(a-base).toNat]?

def nextView {α : Type} (choice : Bool) (state : State) (view : State → List Sequential.Read → α) :
    Except Error α := do
  let observed ← Sequential.step choice state
  match observed.result with
  | .next after => return view after observed.reads
  | _ => throw .unexpectedReturn

end EDSL.Tests.DisplacedData
