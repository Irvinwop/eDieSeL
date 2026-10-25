/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import tests.RexData32Base
import tests.Support.ExceptDecidable
namespace EDSL.Tests.RexData32
open X86 X86.Sequential
open scoped EDSL.Tests.Support
private def fetchCodes : List (List Byte) :=
  [[0x41,0x8b,6],[0x44,0x8b,0x0c,0x86],[0x45,0x8b,0x6d,0],
   [0x47,0x8b,0x64,0xa5,0x80]]
private def missingFetch (code : List Byte) (i : Nat) (missing canExecute : Bool) : State :=
  let s := entry code registers
  {s with memory := {s.memory with
    read := fun a => if missing && a == 4096 + BitVec.ofNat 64 i then none else s.memory.read a
    executable := fun a => s.memory.executable a && (canExecute || a != 4096 + BitVec.ofNat 64 i)}}
-- A readable byte denied execute and an executable byte missing from read
-- mapping are separate gates, including every SIB/explicit zero displacement.
theorem all_fetch_permissions : fetchCodes.all (fun code => (List.range code.length).all
    (fun i => decide (Sequential.decodeAt (missingFetch code i false false) =
      .error (.inaccessibleInstruction (4096+BitVec.ofNat 64 i)))) ) = true := by decide +kernel

theorem all_fetch_readability : fetchCodes.all (fun code => (List.range code.length).all
    (fun i => decide (Sequential.decodeAt (missingFetch code i true true) =
      .error (.inaccessibleInstruction (4096+BitVec.ofNat 64 i)))) ) = true := by decide +kernel

theorem all_truncated_prefixes : fetchCodes.all (fun code => (List.range code.length).all
    (fun n => decide (Sequential.decodeAt (entry (code.take n) registers) =
      .error (.inaccessibleInstruction (4096+BitVec.ofNat 64 n)))) ) = true := by decide +kernel

theorem ordered_sib_then_disp :
    (Sequential.decodeAt (entry [0x47,0x8b,0x64] registers),
     Sequential.decodeAt (entry [0x47,0x8b,0x64,0xa5] registers)) =
    (.error (.inaccessibleInstruction 4099),.error (.inaccessibleInstruction 4100)) := by decide +kernel

private def refused (bs : List Byte) : Bool := match Sequential.decodeAt (entry bs registers) with
  | .ok _ => false | .error _ => true
-- Unsupported directions/families do not silently become an ordinary load.
theorem encoding_refusals :
    [[0x44,0x89,0x0c,0x86],[0x44,3,7],[0x40,0x8b,0xc0],
     [0x41,0x8b,5,0,0,0,0],[0x41,0x8b,0x86,0,0,0,0],
     [0x40,0x8b,4,0x24],[0x43,0x8b,4,0x25],
     [0x67,0x41,0x8b,6],[0x66,0x41,0x8b,6],[0xf0,0x41,0x8b,6],
     [0xf2,0x41,0x8b,6],[0xf3,0x41,0x8b,6],[0x2e,0x41,0x8b,6],
     [0x40,0x41,0x8b,6],[0x41,0x48,0x8b,6]].all refused = true := by decide +kernel
-- No unused displacement fetch is fabricated after a refused mod00 base.
theorem refused_before_unused_suffix :
    (Sequential.decodeAt (entry [0x41,0x8b,5] registers),
     Sequential.decodeAt (entry [0x40,0x8b,4,0x24] registers)) =
    (.error .unsupportedEncoding,.error .unsupportedEncoding) := by decide +kernel

private def missingOperand (i : Nat) : State := entry [0x41,0x8b,6] registers
  (fun a => if a == 0x100000300+BitVec.ofNat 64 i then none
    else bytesAt 0x100000300 [0x98,0xba,0xdc,0xfe] a)
theorem every_required_data_byte (af : Bool) :
    (List.range 4).all (fun i => decide (nextView af (missingOperand i) (fun _ _ => true) =
      .error (.inaccessibleData (0x100000300+BitVec.ofNat 64 i)))) = true := by
  cases af <;> decide +kernel

-- Only four mapped read bytes, no write or Sequential.execute permission on DATA, and
-- no mapped/executable byte after the last instruction byte.
theorem exact_four_and_final_fetch (af : Bool) :
    let s := entry [0x41,0x8b,6] registers (bytesAt 0x100000300 [0x98,0xba,0xdc,0xfe])
    nextView af s (fun f reads => (f.registers .rax,f.flags,f.memory,f.rip,reads)) =
    .ok (0xfedcba98,0xfedcba9876543210,s.memory,4099,[⟨.data,0x100000300,4⟩]) := by
  dsimp only
  have decoded : Sequential.decodeAt (entry [0x41,0x8b,6] registers (bytesAt 0x100000300 [0x98,0xba,0xdc,0xfe])) = .ok (.loadMem32Rex .rax (.base .r14)) := by decide +kernel
  simp only [nextView,Sequential.step,decoded,ok_bind,execute_loadMem32Rex]
  rfl

theorem rex_w_requires_eight (af : Bool) :
    nextView af (entry [0x49,0x8b,6] registers (bytesAt 0x100000300 [0x98,0xba,0xdc,0xfe]))
      (fun _ _ => true) = .error (.inaccessibleData 0x100000304) := by cases af <;> decide +kernel

theorem bad_data_boundaries (af : Bool) :
    ([0x800000000000,0x7ffffffffffe,0xfffffffffffffffe] : List Word).map
      (fun p => nextView af (entry [0x41,0x8b,6] (fun _ => p) (fun _ => some 0))
        (fun _ _ => true)) =
    [.error (.inaccessibleData 0x800000000000),
     .error (.inaccessibleData 0x800000000000),
     .error (.inaccessibleData 0xfffffffffffffffe)] := by cases af <;> decide +kernel

theorem arithmetic_wrap_precedes_access (af : Bool) :
    nextView af (entry [0x41,0x8b,0x46,0x20]
      (fun r => if r = .r14 then 0xfffffffffffffff0 else registers r)
      (bytesAt 16 [1,0,0,0x80])) (fun f reads => (f.registers .rax,f.rip,reads)) =
    .ok (0x80000001,4100,[⟨.data,16,4⟩]) := by cases af <;> decide +kernel

theorem noncanonical_modrm_fetch :
    let s := entry [0x41,0x8b,6] registers
    Sequential.decodeAt {s with rip := 0x7ffffffffffe, memory := {
      read := fun a => if a == 0x7ffffffffffe then some 0x41
        else if a == 0x7fffffffffff then some 0x8b else some 6
      executable := fun _ => true, writable := fun _ => false}} =
      .error (.inaccessibleInstruction 0x800000000000) := by decide +kernel
end EDSL.Tests.RexData32
#audit_edsl
