/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Decode

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential.DecodeTransportSupport

variable {α β : Type}

def SuccessRefines (source destination : Except Error α) : Prop :=
  ∀ value, source = .ok value → destination = .ok value

theorem SuccessRefines.refl (result : Except Error α) : SuccessRefines result result :=
  fun _ success => success

theorem SuccessRefines.bind {source destination : Except Error α}
    {left right : α → Except Error β} (first : SuccessRefines source destination)
    (rest : ∀ value, SuccessRefines (left value) (right value)) :
    SuccessRefines (source >>= left) (destination >>= right) := by
  intro value success
  cases fetched : source with
  | error fault => simp only [fetched, error_bind, reduceCtorEq] at success
  | ok byte =>
    rw [first byte fetched, ok_bind]
    exact rest byte value (by simpa only [fetched, ok_bind] using success)

theorem SuccessRefines.ite (condition : Prop) [Decidable condition]
    {a b c d : Except Error α} (yes : SuccessRefines a b) (no : SuccessRefines c d) :
    SuccessRefines (if condition then a else c) (if condition then b else d) := by
  split <;> assumption

/-- Local transport of the unmodified legacy decoder. Only successful fetches
are transported; an inaccessible byte after the decoded instruction is irrelevant. -/
theorem legacy_decodeAt_transport_short {source destination : State} {instruction : X86.Instruction}
    (transport : SuccessfulFetchTransportWithin 9 source destination)
    (decoded : X86.decodeAt source = .ok instruction) :
    X86.decodeAt destination = .ok instruction := by
  have t0 := transport 0 (by decide)
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  simp only [BitVec.add_zero] at t0
  have refinement : SuccessRefines (X86.decodeAt source) (X86.decodeAt destination) := by
    unfold X86.decodeAt
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t0
      | exact t1
      | exact t2
      | exact t3
      | exact t4
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value
  exact refinement instruction decoded

theorem legacy_decodeAt_transport {source destination : State} {instruction : X86.Instruction}
    (transport : SuccessfulFetchTransport source destination)
    (decoded : X86.decodeAt source = .ok instruction) :
    X86.decodeAt destination = .ok instruction :=
  legacy_decodeAt_transport_short (transport.restrict (by decide : 9 ≤ 15)) decoded

/-- Successful fetch transport for the shared mod01 suffix. -/
theorem decodeDisp8AddressSuffixAt_refines {source destination : State}
    (rex modrm : Byte) (offset : Nat) (bound : offset + 2 ≤ 15)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeDisp8AddressSuffixAt source rex modrm offset)
      (decodeDisp8AddressSuffixAt destination rex modrm offset) := by
  have first := transport offset (by omega)
  have second := transport (offset + 1) (by omega)
  unfold decodeDisp8AddressSuffixAt
  apply SuccessRefines.ite
  · exact SuccessRefines.refl _
  · apply SuccessRefines.ite
    · apply SuccessRefines.bind first
      intro sib
      apply SuccessRefines.bind second
      intro displacement
      exact SuccessRefines.refl _
    · apply SuccessRefines.bind first
      intro displacement
      exact SuccessRefines.refl _

/-- Successful suffix transport remains within the unchanged15-byte fetch window. -/
theorem decodeDisp8AddressSuffixAt_transport {source destination : State}
    {address : Address} (rex modrm : Byte) (offset : Nat) (bound : offset + 2 ≤ 15)
    (transport : SuccessfulFetchTransport source destination)
    (decoded : decodeDisp8AddressSuffixAt source rex modrm offset = .ok address) :
    decodeDisp8AddressSuffixAt destination rex modrm offset = .ok address :=
  decodeDisp8AddressSuffixAt_refines rex modrm offset bound transport address decoded

theorem decodeAddressAt_refines {source destination : State} (modrm : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeAddressAt source modrm) (decodeAddressAt destination modrm) := by
  have t2 := transport 2 (by decide)
  unfold decodeAddressAt
  apply SuccessRefines.ite
  · exact decodeDisp8AddressSuffixAt_refines 0 modrm 2 (by decide) transport
  · repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t2
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeQWordAddressAt_refines {source destination : State} (rex modrm : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeQWordAddressAt source rex modrm) (decodeQWordAddressAt destination rex modrm) := by
  have t3 := transport 3 (by decide)
  unfold decodeQWordAddressAt
  apply SuccessRefines.ite
  · exact decodeDisp8AddressSuffixAt_refines rex modrm 3 (by decide) transport
  · repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t3
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeCmpMemImm8At_refines {source destination : State}
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeCmpMemImm8At source) (decodeCmpMemImm8At destination) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  unfold decodeCmpMemImm8At
  apply SuccessRefines.bind t1
  intro modrm
  apply SuccessRefines.ite
  · exact SuccessRefines.refl _
  · apply SuccessRefines.bind (decodeAddressAt_refines _ transport)
    intro address
    cases address <;> simp only [Address.suffixBytes] <;>
      apply SuccessRefines.bind (by assumption) <;>
      intro immediate <;> exact SuccessRefines.refl _

theorem decodeCmpRegMem8At_refines {source destination : State} (rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeCmpRegMem8At source rex prefixed)
      (decodeCmpRegMem8At destination rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  cases prefixed <;> unfold decodeCmpRegMem8At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | with_reducible exact decodeAddressAt_refines _ transport
      | with_reducible exact decodeQWordAddressAt_refines _ _ transport
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeMovImm32At_refines {source destination : State} (opcode : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeMovImm32At source opcode) (decodeMovImm32At destination opcode) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  unfold decodeMovImm32At
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t1
    | exact t2
    | exact t3
    | exact t4
    | apply SuccessRefines.bind
    | intro value

theorem decodeCmpMemRegAt_refines {source destination : State} (byteWidth : Bool)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeCmpMemRegAt source byteWidth) (decodeCmpMemRegAt destination byteWidth) := by
  have t1 := transport 1 (by decide)
  unfold decodeCmpMemRegAt
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t1
    | exact decodeAddressAt_refines _ transport
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

theorem decodeMovSignImm32At_refines {source destination : State} (rex : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeMovSignImm32At source rex) (decodeMovSignImm32At destination rex) := by
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  have t5 := transport 5 (by decide)
  have t6 := transport 6 (by decide)
  unfold decodeMovSignImm32At
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t2
    | exact t3
    | exact t4
    | exact t5
    | exact t6
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

theorem decodeDisp8AddressAt_refines {source destination : State} (rex modrm : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeDisp8AddressAt source rex modrm)
      (decodeDisp8AddressAt destination rex modrm) := by
  exact decodeDisp8AddressSuffixAt_refines rex modrm 3 (by decide) transport

theorem decodeLogicalReg32At_refines {source destination : State} (opcode rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeLogicalReg32At source opcode rex prefixed)
      (decodeLogicalReg32At destination opcode rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  cases prefixed <;> unfold decodeLogicalReg32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeShiftRightImm32At_refines {source destination : State} (rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeShiftRightImm32At source rex prefixed)
      (decodeShiftRightImm32At destination rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  cases prefixed <;> unfold decodeShiftRightImm32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | exact t3
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeCounter32At_refines {source destination : State} (opcode rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeCounter32At source opcode rex prefixed)
      (decodeCounter32At destination opcode rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  cases prefixed <;> unfold decodeCounter32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | exact t3
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeSubReg64At_refines {source destination : State} (operation rex : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeSubReg64At source operation rex)
      (decodeSubReg64At destination operation rex) := by
  have t2 := transport 2 (by decide)
  unfold decodeSubReg64At
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t2
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

theorem decodeGroup1Imm64At_refines {source destination : State} (rex : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeGroup1Imm64At source rex)
      (decodeGroup1Imm64At destination rex) := by
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  unfold decodeGroup1Imm64At
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t2
    | exact t3
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

theorem decodeREXWAt_refines {source destination : State} (rex : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeREXWAt source rex) (decodeREXWAt destination rex) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  unfold decodeREXWAt
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t1
    | exact t2
    | exact t3
    | exact decodeMovSignImm32At_refines _ transport
    | exact decodeSubReg64At_refines _ _ transport
    | exact decodeGroup1Imm64At_refines _ transport
    | exact decodeQWordAddressAt_refines _ _ transport
    | exact decodeDisp8AddressAt_refines _ _ transport
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

theorem decodeCompare32At_refines {source destination : State} (opcode rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeCompare32At source opcode rex prefixed)
      (decodeCompare32At destination opcode rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  cases prefixed <;> unfold decodeCompare32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeCmov32At_refines {source destination : State} (rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeCmov32At source rex prefixed)
      (decodeCmov32At destination rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  cases prefixed <;> unfold decodeCmov32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | exact t3
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeSetccAt_refines {source destination : State} (rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeSetccAt source rex prefixed)
      (decodeSetccAt destination rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  cases prefixed <;> unfold decodeSetccAt <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | exact t3
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeMovImm8At_refines {source destination : State} (opcode rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeMovImm8At source opcode rex prefixed)
      (decodeMovImm8At destination opcode rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  cases prefixed <;> unfold decodeMovImm8At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeCmpReg8At_refines {source destination : State} (opcode rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeCmpReg8At source opcode rex prefixed)
      (decodeCmpReg8At destination opcode rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  cases prefixed <;> unfold decodeCmpReg8At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeSubReg32At_refines {source destination : State} (opcode rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeSubReg32At source opcode rex prefixed)
      (decodeSubReg32At destination opcode rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  cases prefixed <;> unfold decodeSubReg32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeNegReg32At_refines {source destination : State} (rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeNegReg32At source rex prefixed)
      (decodeNegReg32At destination rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  cases prefixed <;> unfold decodeNegReg32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeMovzxAddressAt_refines {source destination : State} (rex modrm : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeMovzxAddressAt source rex modrm prefixed)
      (decodeMovzxAddressAt destination rex modrm prefixed) := by
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  unfold decodeMovzxAddressAt
  apply SuccessRefines.ite
  · exact decodeDisp8AddressSuffixAt_refines rex modrm
      (if prefixed then 4 else 3) (by cases prefixed <;> decide) transport
  · cases prefixed <;>
      repeat first
        | with_reducible exact SuccessRefines.refl _
        | exact t3
        | exact t4
        | apply SuccessRefines.ite
        | apply SuccessRefines.bind
        | intro value

theorem decodeMovzx8At_refines {source destination : State} (rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeMovzx8At source rex prefixed)
      (decodeMovzx8At destination rex prefixed) := by
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  cases prefixed <;> unfold decodeMovzx8At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t2
      | exact t3
      | with_reducible exact decodeMovzxAddressAt_refines _ _ _ transport
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decode0FREX32At_refines {source destination : State} (rex : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decode0FREX32At source rex) (decode0FREX32At destination rex) := by
  have t2 := transport 2 (by decide)
  unfold decode0FREX32At
  apply SuccessRefines.bind t2
  intro second
  apply SuccessRefines.ite
  · exact decodeMovzx8At_refines rex true transport
  · apply SuccessRefines.ite
    · exact decodeSetccAt_refines rex true transport
    · exact decodeCmov32At_refines rex true transport

theorem decodeTestImm8At_refines {source destination : State} (rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeTestImm8At source rex prefixed)
      (decodeTestImm8At destination rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  cases prefixed <;> unfold decodeTestImm8At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | exact t3
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeLea32At_refines {source destination : State} (rex : Byte)
    (prefixed : Bool) (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeLea32At source rex prefixed)
      (decodeLea32At destination rex prefixed) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  cases prefixed <;> unfold decodeLea32At <;>
    repeat first
      | with_reducible exact SuccessRefines.refl _
      | exact t1
      | exact t2
      | exact t3
      | with_reducible exact decodeDisp8AddressAt_refines _ _ transport
      | with_reducible exact decodeQWordAddressAt_refines _ _ transport
      | with_reducible exact decodeAddressAt_refines _ transport
      | apply SuccessRefines.ite
      | apply SuccessRefines.bind
      | intro value

theorem decodeREX32At_refines {source destination : State} (rex : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeREX32At source rex) (decodeREX32At destination rex) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  unfold decodeREX32At
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t1
    | exact t2
    | with_reducible exact decodeQWordAddressAt_refines _ _ transport
    | with_reducible exact decodeMovImm8At_refines _ _ _ transport
    | with_reducible exact decode0FREX32At_refines _ transport
    | with_reducible exact decodeCmpRegMem8At_refines _ _ transport
    | with_reducible exact decodeCmpReg8At_refines _ _ _ transport
    | with_reducible exact decodeSubReg32At_refines _ _ _ transport
    | with_reducible exact decodeLogicalReg32At_refines _ _ _ transport
    | with_reducible exact decodeShiftRightImm32At_refines _ _ transport
    | with_reducible exact decodeTestImm8At_refines _ _ transport
    | with_reducible exact decodeLea32At_refines _ _ transport
    | with_reducible exact decodeNegReg32At_refines _ _ transport
    | with_reducible exact decodeCounter32At_refines _ _ _ transport
    | with_reducible exact decodeCompare32At_refines _ _ _ transport
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

theorem fetchExactAt_refines {source destination : State} (bytes : List Byte)
    (transport : SuccessfulFetchTransport source destination) (offset : Nat)
    (bound : offset + bytes.length ≤ 15) :
    SuccessRefines (fetchExactAt source offset bytes) (fetchExactAt destination offset bytes) := by
  induction bytes generalizing offset with
  | nil => exact SuccessRefines.refl _
  | cons expected rest ih =>
    unfold fetchExactAt
    apply SuccessRefines.bind (transport offset (by simp only [List.length_cons] at bound; omega))
    intro actual
    apply SuccessRefines.ite
    · exact ih (offset + 1) (by simp only [List.length_cons] at bound; omega)
    · exact SuccessRefines.refl _

theorem decodePaddingAt_refines {source destination : State} (opcode : Byte)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodePaddingAt source opcode) (decodePaddingAt destination opcode) := by
  have t1 := transport 1 (by decide)
  have t2 := transport 2 (by decide)
  have t3 := transport 3 (by decide)
  have t4 := transport 4 (by decide)
  have exactSeven := fetchExactAt_refines [0, 0, 0, 0] transport 3 (by decide)
  have exactEight := fetchExactAt_refines [0, 0, 0, 0, 0] transport 3 (by decide)
  have exactSix := fetchExactAt_refines [0, 0] transport 4 (by decide)
  have exactNine := fetchExactAt_refines [0, 0, 0, 0, 0] transport 4 (by decide)
  have repeatedLead := fetchExactAt_refines [0x66, 0x66] transport 2 (by decide)
  have exactThirteen := fetchExactAt_refines
    [0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0] transport 5 (by decide)
  have exactFifteen := fetchExactAt_refines
    [0x66, 0x2e, 0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0] transport 5 (by decide)
  unfold decodePaddingAt
  apply SuccessRefines.ite
  · exact SuccessRefines.refl _
  · apply SuccessRefines.bind t1
    intro second
    apply SuccessRefines.ite
    · apply SuccessRefines.ite
      · exact SuccessRefines.refl _
      · apply SuccessRefines.ite
        · apply SuccessRefines.bind repeatedLead
          intro authenticated
          apply SuccessRefines.bind t4
          intro fifth
          apply SuccessRefines.ite
          · apply SuccessRefines.bind exactThirteen
            intro completed
            exact SuccessRefines.refl _
          · apply SuccessRefines.ite
            · apply SuccessRefines.bind exactFifteen
              intro completed
              exact SuccessRefines.refl _
            · exact SuccessRefines.refl _
        · repeat first
            | exact t2
            | exact t3
            | exact exactSix
            | exact exactNine
            | with_reducible exact SuccessRefines.refl _
            | apply SuccessRefines.ite
            | apply SuccessRefines.bind
            | intro value
    · repeat first
        | exact t2
        | exact t3
        | exact t4
        | exact exactSeven
        | exact exactEight
        | with_reducible exact SuccessRefines.refl _
        | apply SuccessRefines.ite
        | apply SuccessRefines.bind
        | intro value

theorem decode0F32At_refines {source destination : State}
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decode0F32At source) (decode0F32At destination) := by
  have t1 := transport 1 (by decide)
  unfold decode0F32At
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t1
    | with_reducible exact decodeCmov32At_refines _ _ transport
    | with_reducible exact decodeSetccAt_refines _ _ transport
    | with_reducible exact decodeMovzx8At_refines _ _ transport
    | with_reducible exact decodePaddingAt_refines _ transport
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value

theorem decodeTailAt_refines {source destination : State} (opcode : Byte) (fault : Error)
    (transport : SuccessfulFetchTransport source destination) :
    SuccessRefines (decodeTailAt source opcode fault) (decodeTailAt destination opcode fault) := by
  have t1 := transport 1 (by decide)
  unfold decodeTailAt
  repeat first
    | with_reducible exact SuccessRefines.refl _
    | exact t1
    | with_reducible exact decodeAddressAt_refines _ transport
    | with_reducible exact (show SuccessRefines (decodeJccAt source _) (decodeJccAt destination _) from by
        unfold decodeJccAt
        apply SuccessRefines.bind t1
        intro displacement
        exact SuccessRefines.refl _)
    | apply SuccessRefines.ite
    | apply SuccessRefines.bind
    | intro value


end EDSL.X86.Sequential.DecodeTransportSupport
