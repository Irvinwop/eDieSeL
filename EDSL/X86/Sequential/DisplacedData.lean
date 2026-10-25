/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.DecodeTransport
import EDSL.X86.Sequential.Address32

namespace EDSL.X86.Sequential

/-- CallReturn and LEA retain the same offset3 entry point. -/
theorem decodeDisp8AddressAt_eq_suffix (s : State) (rex modrm : Byte) :
    decodeDisp8AddressAt s rex modrm = decodeDisp8AddressSuffixAt s rex modrm 3 := rfl

/-- Original plain mod00 decoding is unaffected by admitting mod01. -/
theorem decodeAddressAt_mod00_plain (s : State) (modrm : Byte)
    (mode : modrm.toNat / 64 = 0) (plain : modrm.toNat % 8 ≠ 4)
    (realBase : modrm.toNat % 8 ≠ 5) :
    decodeAddressAt s modrm = .ok (.base (modRMRM modrm)) := by
  simp [decodeAddressAt,mode,plain,realBase]

/-- A signed displacement is kept raw; RBP/R13 are real bases in mod01. This
helper contract assumes authenticated enclosing opcode/ModRM separately. -/
theorem decodeDisp8AddressSuffixAt_plain (s : State) (rex modrm d : Byte) (offset : Nat)
    (mode : modrm.toNat / 64 = 1) (plain : modrm.toNat % 8 ≠ 4)
    (fetched : fetchByte s.memory (s.rip + BitVec.ofNat 64 offset) = .ok d) :
    decodeDisp8AddressSuffixAt s rex modrm offset = .ok (.baseDisp8 (rexModRMRM rex modrm) d) := by
  simp [decodeDisp8AddressSuffixAt,mode,plain,fetched]

/-- The second suffix fetch follows the SIB, with no-index retained as an
explicit SIB and X extending only the encoded index. -/
theorem decodeDisp8AddressSuffixAt_sib (s : State) (rex modrm sib d : Byte) (offset : Nat)
    (mode : modrm.toNat / 64 = 1) (isSib : modrm.toNat % 8 = 4)
    (fetchedSib : fetchByte s.memory (s.rip + BitVec.ofNat 64 offset) = .ok sib)
    (fetchedDisp : fetchByte s.memory (s.rip + BitVec.ofNat 64 (offset+1)) = .ok d) :
    decodeDisp8AddressSuffixAt s rex modrm offset = .ok
      (.sibDisp8 (rexModRMRM rex sib)
        (if sib.toNat / 8 % 8 = 4 ∧ rex.getLsbD 1 = false then none
          else some (rexSIBIndex rex sib))
        ⟨sib.toNat / 64, by have := sib.isLt; omega⟩ d) := by
  simp [decodeDisp8AddressSuffixAt,mode,isSib,fetchedSib,fetchedDisp]

/-- Absent-index scale bits do not affect arithmetic, but remain encoded in the
Address and hence in length/accounting. Neither arithmetic law grants DATA. -/
theorem Address.eval_sibDisp8_none_signed (s : State) (base : Register) (scale : Fin 4) (d : Byte) :
    ((Address.sibDisp8 base none scale d).eval s).toInt =
      ((s.registers base).toInt + d.toInt).bmod (2^64) := by
  simp only [Address.eval, BitVec.toInt_add,
    BitVec.toInt_signExtend_of_le (by decide : 8 ≤ 64)]

end EDSL.X86.Sequential
