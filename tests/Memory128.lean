/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory128

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

namespace EDSL.Tests.Memory128
open X86

private def payload : List Byte :=
  [0x10,0x32,0x54,0x76,0x98,0xba,0xdc,0xfe,
   0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef]

private def bytesAt : Memory where
  read := fun address => payload[(address - 0x1003).toNat]?
  executable := fun _ => false
  writable := fun _ => true

/-- Independent byte-vector and integer representations exercise lane order,
unaligned access and all high bits, rather than merely round-tripping a writer. -/
theorem load_little_endian_unaligned :
    loadOWord bytesAt 0x1003 = .ok 0xefcdab8967452301fedcba9876543210#128 := by cbv

private def missingLast : Memory :=
  { bytesAt with read := fun address =>
    if address = 0x1012 then none else bytesAt.read address }

theorem absent_sixteenth_byte_faults :
    loadOWord missingLast 0x1003 = .error (.inaccessibleData 0x1012) := by cbv

private def deniedLast : Memory :=
  { bytesAt with writable := fun address => address != 0x1012 }

theorem denied_sixteenth_byte_refuses_store :
    storeOWord deniedLast 0x1003 0x0123456789abcdeffedcba9876543210#128 =
      .error (.writeDenied 0x1003) := by cbv

/-- A complete mapping makes these boundary controls distinguish address
validation from a coincidental missing-byte failure. -/
private def allMapped : Memory where
  read := fun _ => some 0x5a
  executable := fun _ => false
  writable := fun _ => true

theorem wrapping_load_refused :
    loadOWord allMapped 0xfffffffffffffff8 =
      .error (.inaccessibleData 0xfffffffffffffff8) := by cbv

theorem wrapping_store_refused :
    storeOWord allMapped 0xfffffffffffffff8 0 =
      .error (.writeDenied 0xfffffffffffffff8) := by cbv

theorem canonical_hole_load_fault :
    loadOWord allMapped 0x7ffffffffff8 =
      .error (.inaccessibleData 0x800000000000) := by cbv

theorem canonical_hole_store_refused :
    storeOWord allMapped 0x7ffffffffff8 0 =
      .error (.writeDenied 0x7ffffffffff8) := by cbv

/-- Exact stored bytes are specified independently of the lane split/extract
implementation. This catches high/low swaps and byte-order mistakes. -/
theorem stored_byte_image :
    (storeOWord bytesAt 0x1003 0x0123456789abcdeffedcba9876543210#128).map
      (fun memory => (List.range 16).map fun offset =>
        memory.read (0x1003 + BitVec.ofNat 64 offset)) =
    .ok [some 0x10,some 0x32,some 0x54,some 0x76,
      some 0x98,some 0xba,some 0xdc,some 0xfe,
      some 0xef,some 0xcd,some 0xab,some 0x89,
      some 0x67,some 0x45,some 0x23,some 0x01] := by cbv

end EDSL.Tests.Memory128
#audit_edsl
