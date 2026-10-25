/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.DisplacedDataBase
import tests.Support.ExceptDecidable

namespace EDSL.Tests.DisplacedData
open X86
open scoped EDSL.Tests.Support

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : BEq (Except ε α) :=
  ⟨fun a b => decide (a = b)⟩

/-- Every suffix offset is a required executable readable byte, even zero disp8. -/
def fetchCases : List (List Byte) := [[0x80,0x7c,7,1,0], [0x8b,0x4a,4],
  [0x89,0x4f,0xfc], [0x48,0x8b,0x47,8], [0x48,0x89,0x47,8],
  [0x48,3,0x47,0x10], [3,0x4a,4], [0x38,0x4a,4], [0x39,0x4a,4],
  [0x3a,0x46,0], [0x44,0x3a,0x46,0], [0x0f,0xb6,0x40,0],
  [0x47,0x0f,0xb6,0x64,0xa5,0x80]]

def blockedFetch (code : List Byte) (index : Nat) (missing : Bool) : State :=
  let s := entry code
  { s with memory := {
    read := fun a => if missing && a == 4096 + BitVec.ofNat 64 index then none else s.memory.read a
    executable := fun a => s.memory.executable a && a != 4096 + BitVec.ofNat 64 index
    writable := fun _ => false } }

theorem all_required_fetches : fetchCases.all (fun code => (List.range code.length).all
    (fun i => [false,true].all (fun missing =>
      Sequential.decodeAt (blockedFetch code i missing) ==
        .error (.inaccessibleInstruction (4096 + BitVec.ofNat 64 i))))) = true := by decide +kernel

/-- Missing bytes and denied execute permissions are independent gates. -/
def missingFetch (code : List Byte) (index : Nat) : State :=
  let s := entry code
  { s with
    memory := { s.memory with
      read := fun a =>
        if a == (4096 + BitVec.ofNat 64 index) then none else s.memory.read a } }

theorem all_missing_fetches : fetchCases.all (fun code => (List.range code.length).all
    (fun i => Sequential.decodeAt (missingFetch code i) ==
      .error (.inaccessibleInstruction (4096 + BitVec.ofNat 64 i)))) = true := by decide +kernel

/-- The SIB displacement and trailing immediate have different failure addresses. -/
theorem ordered_suffix : (Sequential.decodeAt (entry [0x80,0x7c,7]),
    Sequential.decodeAt (entry [0x80,0x7c,7,1])) =
    (.error (.inaccessibleInstruction 4099),.error (.inaccessibleInstruction 4100)) := by rfl

/-- Decoder success grants no operand mapping. Read failures identify every byte
of DATA1/4/8 independently of executable code permissions. -/
def missingData (code : List Byte) (width index : Nat) : State :=
  entry code registers (fun a => if a == 0x100000005 + BitVec.ofNat 64 index then none
    else bytesAt 0x100000005 (List.replicate width 0x78) a)

theorem data_denials (af : Bool) :
    ([([0x3a,0x45,0],1),([0x8b,0x45,0],4),([0x48,0x8b,0x45,0],8)] :
        List (List Byte × Nat)).all (fun (code,width) =>
      (List.range width).all (fun index =>
        nextView af (missingData code width index) (fun _ _ => true) ==
          .error (.inaccessibleData (0x100000005 + BitVec.ofNat 64 index)))) = true := by
  cases af <;> decide +kernel

/-- Canonical hole and full-width wrap retain existing checked primitive errors. -/
theorem bad_effective_addresses (af : Bool) :
    ([0x800000000000,0x7ffffffffffc,0xfffffffffffffffc] : List Word).map
      (fun p => nextView af (entry [0x48,0x8b,0x45,0]
        (fun _ => p) (fun _ => some 0)) (fun _ _ => true)) =
    [.error (.inaccessibleData 0x800000000000),
      .error (.inaccessibleData 0x800000000000),
      .error (.inaccessibleData 0xfffffffffffffffc)] := by cbv

/-- A suffix fetch crossing the canonical boundary faults at its real byte. -/
theorem noncanonical_fetch :
    let s := entry [0x8b,0x45,0]
    Sequential.decodeAt {s with rip := 0x7ffffffffffe, memory := {
      read := fun a => if a == 0x7ffffffffffe then some 0x8b
        else if a == 0x7fffffffffff then some 0x45 else some 0
      executable := fun _ => true
      writable := fun _ => false }} = .error (.inaccessibleInstruction 0x800000000000) := by cbv

/-- Every store byte is preflighted; same-value writes still require permission. -/
theorem denied_store (af : Bool) :
    ([([0x89,0x4f,0xfc],4),([0x48,0x89,0x4f,0xfc],8)] :
      List (List Byte × Nat)).all (fun (code,width) => (List.range width).all (fun index =>
        nextView af (entry code registers (fun _ => some 0x78)
          (fun a => a != 0x100000005 + BitVec.ofNat 64 index)) (fun _ _ => true) ==
        .error (.writeDenied 0x100000005))) = true := by
  cases af <;> decide +kernel

/-- Writing exactly the existing four zero bytes still requires every write permission. -/
theorem same_value_denied (af : Bool) :
    nextView af (entry [0x89,0x4f,0xfc]
      (fun r => if r = .rdi then 0x100000009 else 0) (fun _ => some 0)
      (fun a => a != 0x100000008)) (fun _ _ => true) =
      .error (.writeDenied 0x100000005) := by rfl

end EDSL.Tests.DisplacedData
#audit_edsl
