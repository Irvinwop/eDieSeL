import tests.And64TestBase
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
namespace EDSL.Tests.And64Regression
open X86 Sequential
/-- Required bytes, including the actual immediate, fail at their own address. -/
theorem required_fetches :
    Sequential.decodeAt (codeState [] 0) = .error (.inaccessibleInstruction 0) ∧
    Sequential.decodeAt (codeState [0x48] 0) = .error (.inaccessibleInstruction 1) ∧
    Sequential.decodeAt (codeState [0x48,0x83] 0) = .error (.inaccessibleInstruction 2) ∧
    Sequential.decodeAt (codeState [0x48,0x83,0xe0] 0) = .error (.inaccessibleInstruction 3) := by
  refine ⟨?_,?_,?_,?_⟩ <;> cbv

def deniedImmediate : State :=
  let state := codeState [0x48,0x83,0xe0,0xf8] 0
  { state with memory := {state.memory with executable := fun a => a != 3} }
theorem denied_immediate : Sequential.decodeAt deniedImmediate = .error (.inaccessibleInstruction 3) := by cbv

def deniedByte (offset : Nat) : State :=
  let state := codeState [0x48,0x83,0xe0,0xf8] 0
  { state with memory := {state.memory with executable := fun a => a != BitVec.ofNat 64 offset} }
theorem every_byte_requires_execute :
    Sequential.decodeAt (deniedByte 0) = .error (.inaccessibleInstruction 0) ∧
    Sequential.decodeAt (deniedByte 1) = .error (.inaccessibleInstruction 1) ∧
    Sequential.decodeAt (deniedByte 2) = .error (.inaccessibleInstruction 2) ∧
    Sequential.decodeAt (deniedByte 3) = .error (.inaccessibleInstruction 3) := by
  refine ⟨?_,?_,?_,?_⟩ <;> cbv

theorem rejected_leading_prefixes :
    Sequential.decodeAt (codeState [0x66,0x48,0x83,0xe0,0xf8] 0) = .error .unsupportedEncoding ∧
    Sequential.decodeAt (codeState [0x67,0x48,0x83,0xe0,0xf8] 0) = .error (.unsupportedOpcode 0x67) ∧
    Sequential.decodeAt (codeState [0xf0,0x48,0x83,0xe0,0xf8] 0) = .error .unsupportedEncoding := by
  refine ⟨?_,?_,?_⟩ <;> cbv

def boundary : State where
  registers := fun _ => 0
  rip := 0x7ffffffffffd
  flags := 0
  memory := {
    read := fun a => if a = 0x7ffffffffffd then some 0x48
      else if a = 0x7ffffffffffe then some 0x83
      else if a = 0x7fffffffffff then some 0xe0 else some 0xf8
    executable := fun _ => true }
theorem noncanonical_immediate : Sequential.decodeAt boundary =
    .error (.inaccessibleInstruction 0x800000000000) := by cbv

def boundaryAt (start : Word) : State where
  registers := fun _ => 0
  rip := start
  flags := 0
  memory := {
    read := fun a => if a = start then some 0x48
      else if a = start + 1 then some 0x83
      else if a = start + 2 then some 0xe0 else some 0xf8
    executable := fun _ => true }
/-- The first noncanonical required byte is rejected at every fetch position,
although all bytes are present and marked executable. -/
theorem every_byte_requires_canonical :
    Sequential.decodeAt (boundaryAt 0x800000000000) = .error (.inaccessibleInstruction 0x800000000000) ∧
    Sequential.decodeAt (boundaryAt 0x7fffffffffff) = .error (.inaccessibleInstruction 0x800000000000) ∧
    Sequential.decodeAt (boundaryAt 0x7ffffffffffe) = .error (.inaccessibleInstruction 0x800000000000) ∧
    Sequential.decodeAt (boundaryAt 0x7ffffffffffd) = .error (.inaccessibleInstruction 0x800000000000) := by
  refine ⟨?_,?_,?_,?_⟩ <;> cbv

/-- No byte4 exists: the first step succeeds; the real successor fetch fails. -/
theorem no_overfetch (af : Bool) :
    let state := initial [0x48,0x83,0xe0,0xf8] .rax 0x800000010000000f
    ∃ after, step af state = .ok ⟨.next after,[]⟩ ∧
      step false after = .error (.inaccessibleInstruction 4) := by
  refine ⟨logical64State (initial [0x48,0x83,0xe0,0xf8] .rax 0x800000010000000f)
    .band .rax ((0xf8 : Byte).signExtend 64) 4 af, ?_, ?_⟩ <;> cases af <;> cbv

/-- A complete instruction ending at the canonical boundary retires normally;
only the next actual fetch rejects the noncanonical successor. -/
theorem no_eager_successor_check (af : Bool) :
    let before := boundaryAt 0x7ffffffffffc
    ∃ after, step af before = .ok ⟨.next after,[]⟩ ∧
      after.rip = 0x800000000000 ∧
      step false after = .error (.inaccessibleInstruction 0x800000000000) := by
  refine ⟨logical64State (boundaryAt 0x7ffffffffffc) .band .rax
    ((0xf8 : Byte).signExtend 64) 4 af, ?_, ?_, ?_⟩ <;> cases af <;> cbv

/-- Unsupported forms reject before fetching unavailable operands. -/
theorem unsupported_modrm :
    ([[0x48,0x83,0x20],[0x48,0x83,0x24],[0x48,0x83,0x60],[0x48,0x83,0xa0],
      [0x48,0x83,0xc8],[0x48,0x83,0xd0],[0x48,0x83,0xd8],[0x48,0x83,0xf0],
      [0x4a,0x83],[0x4b,0x83],[0x4c,0x83],[0x4d,0x83],[0x4e,0x83],[0x4f,0x83]] :
      List (List Byte)).all (fun b => match Sequential.decodeAt (codeState b 0) with
        | .error .unsupportedEncoding => true | _ => false) = true := by cbv

theorem rejected_full_immediates_and_prefixes :
    ([[0x48,0x81],[0x49,0x81],[0x48,0x25],[0x49,0x25],
      [0x48,0x48],[0x48,0x66]] : List (List Byte)).all
      (fun b => match Sequential.decodeAt (codeState b 0) with
        | .error .unsupportedEncoding => true | _ => false) = true := by cbv

/-- Identical masks distinguish low32 from full64, including the high bank. -/
theorem width_contrast (af : Bool) :
    view .rax af (initial [0x83,0xe0,0xf8] .rax 0x800000010000000f) = some (8,0x602,af,3,[]) ∧
    view .r8 af (initial [0x41,0x83,0xe0,0xf8] .r8 0x800000010000000f) = some (8,0x602,af,4,[]) ∧
    view .rax af (initial [0x48,0x83,0xe0,0xf8] .rax 0x800000010000000f) = some (0x8000000100000008,0x682,af,4,[]) ∧
    view .r8 af (initial [0x49,0x83,0xe0,0xf8] .r8 0x800000010000000f) = some (0x8000000100000008,0x682,af,4,[]) := by
  cases af <;> refine ⟨?_,?_,?_,?_⟩ <;> cbv
end EDSL.Tests.And64Regression
#print axioms EDSL.Tests.And64Regression.required_fetches
#print axioms EDSL.Tests.And64Regression.no_overfetch
#print axioms EDSL.Tests.And64Regression.unsupported_modrm
#print axioms EDSL.Tests.And64Regression.width_contrast
#audit_edsl
