/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Sub64
import EDSL.X86.Sequential.Code
import EDSL.Audit
import tests.Support.ExceptDecidable

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.SequentialSub64
open X86 Sequential
open scoped EDSL.Tests.Support

private def entry (bytes : List Byte) (registers : Register → Word) : State :=
  { codeState bytes 0 with registers := registers, flags := 0xffffffffffffffff }

private def operands (left right : Word) : Register → Word
  | .rax => left | .rcx => right | _ => 0xfeedface12345678

private def nextView (choice : Bool) (bytes : List Byte) (registers : Register → Word)
    (destination : Register := .rax) : Except Error (Word × Word × Word × List Read) := do
  let observation ← step choice (entry bytes registers)
  match observation.result with
  | .next final => return (final.registers destination, final.flags &&& 0x8d5,
      final.rip, observation.reads)
  | _ => throw .unexpectedReturn

/-- Literal result/status vectors come from unsigned borrow, nibble borrow,
signed64 overflow and low-byte parity. Actual production decoding/execution is
exercised; the expected side contains no SUB or flag-transformer implementation. -/
theorem full64_result_and_status_boundaries (choice : Bool) :
    ([ (0, 0), (0, 1), (0x10, 1), (0x11, 1),
       (0x8000000000000000, 1), (0x7fffffffffffffff, 0xffffffffffffffff),
       (0x100000000, 1) ] : List (Word × Word)).map (fun (left,right) =>
      nextView choice [0x48,0x29,0xc8] (operands left right)) =
    [.ok (0,0x044,3,[]), .ok (0xffffffffffffffff,0x095,3,[]),
     .ok (0x0f,0x014,3,[]), .ok (0x10,0x000,3,[]),
     .ok (0x7fffffffffffffff,0x814,3,[]), .ok (0x8000000000000000,0x885,3,[]),
     .ok (0xffffffff,0x014,3,[])] := by
  cases choice <;> decide +kernel

/-- Negative-byte cases distinguish true SUB flags from ADD(left,-right).
In particular 0-SX64(FF)=1 sets CF and AF, whereas ADD(0,1) would clear them. -/
theorem immediate_sign_extension_and_borrow (choice : Bool) :
    ([0xff,0x80,0x7f,0x00] : List Byte).map (fun immediate =>
      nextView choice [0x48,0x83,0xe8,immediate] (operands 0 37)) =
    [.ok (1,0x011,4,[]), .ok (0x80,0x001,4,[]),
     .ok (0xffffffffffffff81,0x095,4,[]), .ok (0,0x044,4,[])] := by
  cases choice <;> decide +kernel

private def banks : Register → Word
  | .rax => 0x400000020 | .rcx => 0x100000001
  | .r8 => 0x300000040 | .r9 => 0x200000002
  | _ => 0xfeedface12345678

/-- Unequal high64 operands detect direction, R/B selection and ignored X.
The immediate case separately exercises REX.B on the opcode-group destination. -/
theorem register_direction_and_extended_banks (choice : Bool) :
    ([([0x48,0x29,0xc8],.rax), ([0x48,0x2b,0xc1],.rax),
      ([0x4d,0x29,0xc8],.r8), ([0x4d,0x2b,0xc1],.r8),
      ([0x4c,0x29,0xc8],.rax), ([0x49,0x29,0xc8],.r8),
      ([0x4a,0x29,0xc8],.rax), ([0x49,0x83,0xe8,0xff],.r8)] :
      List (List Byte × Register)).map (fun (bytes,destination) =>
        nextView choice bytes banks destination) =
    [.ok (0x30000001f,0x010,3,[]), .ok (0x30000001f,0x010,3,[]),
     .ok (0x10000003e,0x010,3,[]), .ok (0x10000003e,0x010,3,[]),
     .ok (0x20000001e,0x014,3,[]), .ok (0x20000003f,0x014,3,[]),
     .ok (0x30000001f,0x010,3,[]), .ok (0x300000041,0x015,4,[])] := by
  cases choice <;> decide +kernel

/-- Self aliases read both operands before writing, including RSP. Stale flags
must be replaced by the defined zero-result status, independently of choice. -/
theorem aliases_include_stack_register (choice : Bool) :
    nextView choice [0x48,0x29,0xc0] banks .rax = .ok (0,0x044,3,[]) ∧
    nextView choice [0x48,0x29,0xe4] banks .rsp = .ok (0,0x044,3,[]) := by
  cases choice <;> decide +kernel

/-- Full64 arithmetic must retain the high half where the preexisting SUB32
encoding clears it. This catches accidentally routing the new leaf through32. -/
theorem distinct_full64_and_low32_widths (choice : Bool) :
    nextView choice [0x48,0x83,0xe8,0x01] (operands 0x100000001 0) =
      .ok (0x100000000,0x004,4,[]) ∧
    nextView choice [0x83,0xe8,0x01] (operands 0x100000001 0) =
      .ok (0,0x044,3,[]) := by
  cases choice <;> decide +kernel

private def failureView (choice : Bool) (bytes : List Byte) : Option Error :=
  match step choice (entry bytes banks) with
  | .error error => some error
  | .ok _ => none

/-- Each required fetch fails at the independently specified missing byte.
The projection observes the real production step without comparing states. -/
theorem required_fetches_and_truncation (choice : Bool) :
    failureView choice [] = some (.inaccessibleInstruction 0) ∧
    failureView choice [0x48] = some (.inaccessibleInstruction 1) ∧
    failureView choice [0x48,0x29] = some (.inaccessibleInstruction 2) ∧
    failureView choice [0x48,0x83,0xe8] = some (.inaccessibleInstruction 3) := by
  cases choice <;> decide +kernel

theorem immediate_fetch_requires_execute_permission (choice : Bool) :
    let before := entry [0x48,0x83,0xe8,0x01] banks
    let denied := { before with memory := { before.memory with
      executable := fun address => address != 3 && before.memory.executable address } }
    step choice denied = .error (.inaccessibleInstruction 3) := by
  rfl

/-- Public decoding rejects unsupported width/prefix/group/address aliases.
Neither memory SUB nor a REX.R/X group alias is silently weakened. -/
theorem conservative_decode_rejections :
    ([ [0x48,0x29,0x08], [0x48,0x2b,0x08], [0x48,0x83,0x28,0x01],
       [0x4c,0x83,0xe8,0x01], [0x4a,0x83,0xe8,0x01],
       [0x48,0x48,0x29,0xc8], [0x48,0x81,0xe8,1,0,0,0],
       [0x48,0x83,0xd8,1], [0x49,0x83,0xc0,1] ] :
      List (List Byte)).map (fun bytes => Sequential.decodeAt (codeState bytes 0)) =
    List.replicate 9 (.error .unsupportedEncoding) := by decide +kernel

/-- Refactoring the immediate group must retain old ADD/CMP identities and
restrictions. In particular no accidental new 49 /0 ADD is admitted above. -/
theorem existing_group1_forms_retain_identity :
    Sequential.decodeAt (codeState [0x48,0x83,0xc0,1] 0) = .ok (.addImm64 .rax 1) ∧
    Sequential.decodeAt (codeState [0x48,0x83,0xf8,1] 0) = .ok (.cmpImm64 .rax 1) ∧
    Sequential.decodeAt (codeState [0x49,0x83,0xf8,1] 0) = .ok (.cmpImm64 .r8 1) := by
  decide +kernel

end EDSL.Tests.SequentialSub64
#audit_edsl
