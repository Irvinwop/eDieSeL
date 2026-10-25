/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.NopPadding
import EDSL.X86.Sequential.Literals
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.ExactNopPadding
open X86 X86.Sequential

deriving instance DecidableEq for Except

/-- Independent target byte windows: do not construct tests from the encoder. -/
def seven : List Byte := [0x0f, 0x1f, 0x80, 0, 0, 0, 0]
def eight : List Byte := [0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0]

private def entry (bytes : List Byte) : State where
  registers := fun _ => 0x800000000000
  rip := 4096
  flags := 0xdeadbeef00000ed7
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length
      then bytes[address.toNat - 4096]? else none
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length)
    writable := fun address => address == 0x9000 }

private def denyExecute (before : State) (offset : Nat) : State :=
  { before with
    memory := { before.memory with
      executable := fun address =>
        before.memory.executable address && address != 4096 + BitVec.ofNat 64 offset } }

private def removeByte (before : State) (offset : Nat) : State :=
  { before with
    memory := { before.memory with
      read := fun address =>
        if address = 4096 + BitVec.ofNat 64 offset then none else before.memory.read address } }

private def faultsAt (before : State) (expected : Word) : Bool :=
  match Sequential.decodeAt before with
  | .error (.inaccessibleInstruction address) => address == expected
  | _ => false

private def unsupported (before : State) : Bool :=
  match Sequential.decodeAt before with
  | .error .unsupportedEncoding => true
  | _ => false

theorem exact_production_decode :
    Sequential.decodeAt (entry seven) = .ok (.nop .seven) ∧
    Sequential.decodeAt (entry eight) = .ok (.nop .eight) := by decide +kernel

/-- All registers (including arbitrary apparent operand values), flags, RAM
and permission maps survive. Expected advances are literal 7/8, not encoder
length projections; both actual entry points and all flag vectors are covered. -/
theorem full_state_seven (before : State)
    (code : CodeAt before.memory before.rip seven) (choice : Bool) (choices : FlagChoices) :
    Sequential.step choice before = .ok ⟨.next { before with rip := before.rip + 7 }, []⟩ ∧
    stepWith choices before = .ok ⟨.next { before with rip := before.rip + 7 }, []⟩ := by
  exact ⟨step_nop_context before .seven code choice, stepWith_nop_context before .seven code choices⟩

theorem full_state_eight (before : State)
    (code : CodeAt before.memory before.rip eight) (choice : Bool) (choices : FlagChoices) :
    Sequential.step choice before = .ok ⟨.next { before with rip := before.rip + 8 }, []⟩ ∧
    stepWith choices before = .ok ⟨.next { before with rip := before.rip + 8 }, []⟩ := by
  exact ⟨step_nop_context before .eight code choice, stepWith_nop_context before .eight code choices⟩

/-- The finite windows contain no operand RAM or following byte. The apparent
RAX and RAX+RAX addresses are noncanonical; the actual step still succeeds. -/
theorem no_operand_or_following_fetch (choice : Bool) :
    Sequential.step choice (entry seven) = .ok ⟨.next { entry seven with rip := 4103 }, []⟩ ∧
    Sequential.step choice (entry eight) = .ok ⟨.next { entry eight with rip := 4104 }, []⟩ := by
  exact ⟨(step_eq_execute choice exact_production_decode.1).trans (execute_nop _ .seven choice),
    (step_eq_execute choice exact_production_decode.2).trans (execute_nop _ .eight choice)⟩

/-- Check all cuts and all independent read/execute failures, including the
last displacement byte. Present bytes with execute permission removed must
fail just like missing bytes whose execute permission is retained. -/
theorem every_seven_byte_required :
    (List.range 7).all (fun offset =>
      faultsAt (entry (seven.take offset)) (4096 + BitVec.ofNat 64 offset) &&
      faultsAt (denyExecute (entry seven) offset) (4096 + BitVec.ofNat 64 offset) &&
      faultsAt (removeByte (entry seven) offset) (4096 + BitVec.ofNat 64 offset)) = true := by
  decide +kernel

theorem every_eight_byte_required :
    (List.range 8).all (fun offset =>
      faultsAt (entry (eight.take offset)) (4096 + BitVec.ofNat 64 offset) &&
      faultsAt (denyExecute (entry eight) offset) (4096 + BitVec.ofNat 64 offset) &&
      faultsAt (removeByte (entry eight) offset) (4096 + BitVec.ofNat 64 offset)) = true := by
  decide +kernel

/-- Every displacement position matters, including the high/sign byte. These
are nonzero architectural displacements, not alternate accepted NOP forms. -/
theorem reject_nonzero_displacements :
    (List.range 4).all (fun byte => ([1, 0x80, 0xff] : List Byte).all (fun value =>
      unsupported (entry (seven.set (3 + byte) value)) &&
      unsupported (entry (eight.set (4 + byte) value)))) = true := by decide +kernel

/-- Zero is the only admitted SIB. /1 through /7 and other apparent operands
cannot be accepted by replacing exact bytes with a general 0F1F grammar. -/
theorem reject_sib_group_and_operands :
    ([1, 4, 0x20, 0x24, 0x40, 0xff] : List Byte).all
      (fun sib => unsupported (entry (eight.set 3 sib))) = true ∧
    ([0x88,0x90,0x98,0xa0,0xa8,0xb0,0xb8] : List Byte).all
      (fun modrm => unsupported (entry (seven.set 2 modrm))) = true ∧
    ([0x8c,0x94,0x9c,0xa4,0xac,0xb4,0xbc] : List Byte).all
      (fun modrm => unsupported (entry (eight.set 2 modrm))) = true ∧
    ([0x81,0x82,0x83,0x85,0x86,0x87,0xc0] : List Byte).all
      (fun modrm => unsupported (entry (seven.set 2 modrm))) = true := by decide +kernel

/-- Extra operand/address/segment/REX/lock/repeat prefixes do not strip into
the new cases. 66 + NOP8 remains the existing, separately admitted NOP9. -/
theorem reject_prefix_aliases :
    ([0x67,0x2e,0x40,0x41,0x48,0x4f,0xf0,0xf2,0xf3] : List Byte).all
      (fun lead => !(Sequential.decodeAt (entry (lead :: seven))).isOk &&
        !(Sequential.decodeAt (entry (lead :: eight))).isOk) = true ∧
    unsupported (entry (0x66 :: seven)) = true ∧
    unsupported (entry (0x66 :: 0x66 :: eight)) = true ∧
    Sequential.decodeAt (entry (0x66 :: eight)) = .ok (.nop .nine) := by decide +kernel

/-- Fetched mismatches precede later absent bytes; access denial precedes
comparison of that same bad byte. This observes the public decoder's order. -/
theorem exact_suffix_fault_order :
    (List.range 4).all (fun suffix =>
      let offset := 3 + suffix
      unsupported (entry ((seven.set offset 1).take (offset + 1))) &&
      faultsAt (denyExecute (entry (seven.set offset 1)) offset)
        (4096 + BitVec.ofNat 64 offset)) = true ∧
    (List.range 5).all (fun suffix =>
      let offset := 3 + suffix
      unsupported (entry ((eight.set offset 1).take (offset + 1))) &&
      faultsAt (denyExecute (entry (eight.set offset 1)) offset)
        (4096 + BitVec.ofNat 64 offset)) = true := by decide +kernel

/-- Literal emission round-trips the actual decoded constructors. -/
theorem decoded_literals :
    (Sequential.decodeAt (entry seven)).map Literals.instruction = .ok "(.nop .seven)" ∧
    (Sequential.decodeAt (entry eight)).map Literals.instruction = .ok "(.nop .eight)" := by
  rw [exact_production_decode.1, exact_production_decode.2]
  exact ⟨rfl, rfl⟩

end EDSL.Tests.ExactNopPadding

#audit_edsl
