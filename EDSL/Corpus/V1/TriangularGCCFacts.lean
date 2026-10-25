/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.TriangularGCCBase

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.Corpus.V1.TriangularGCCBase
open X86 X86.Sequential X86.VCGen
open TriangularGCCGraph

theorem minusOne64 : (0xff : Byte).signExtend 64 = 18446744073709551615#64 := by decide +kernel

theorem two64 : (2 : Byte).signExtend 64 = 2#64 := by decide +kernel

theorem saved_protected :
    ∀ register ∈ PureCall.calleeSaved, register ≠ .rsp ∧ register ∉ scratch := by
  decide +kernel

theorem test32_zero_bit (old : Word) (value : BitVec 32) (af : Bool) :
    (logicalFlags32 old value af)[6] = (value == 0) :=
  logicalFlags32_zero ..

theorem test64_zero_bit (old value : Word) (af : Bool) :
    (logicalFlags64 old value af)[6] = (value == 0) :=
  logicalFlags64_zero ..

theorem test8_zero_bit (old : Word) (value : Byte) (af : Bool) :
    (logicalFlags8 old value af)[6] = decide (value.toNat = 0) := by
  change (logicalFlags8 old value af).getLsbD 6 = decide (value.toNat = 0)
  have zero : (0 : Byte).toNat = 0 := rfl
  simpa only [Bool.beq_eq_decide_eq, ← BitVec.toNat_inj, zero] using
    (logicalFlags8_bits old value af).2.2.2.1

theorem low8_and_one (value : Word) :
    (value.setWidth 8 &&& (1 : Byte)).toNat = value.toNat % 2 := by
  rw [BitVec.toNat_and, BitVec.toNat_setWidth]
  change (value.toNat % 256) &&& 1 = value.toNat % 2
  rw [Nat.and_one_is_mod, Nat.mod_mod_of_dvd value.toNat (by decide : 2 ∣ 256)]

theorem predecessor_toNat (value : BitVec 32) (positive : 0 < value.toNat) :
    (value.setWidth 64 + (0xff : Byte).signExtend 64).toNat = value.toNat - 1 := by
  have negative : (0xff : Byte).signExtend 64 = -(1 : Word) := by decide +kernel
  rw [negative, BitVec.add_neg_eq_sub, BitVec.toNat_sub_of_le]
  · exact congrArg (fun n => n - 1) (BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64))
  · change (1 : Nat) ≤ (value.setWidth 64).toNat
    rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
    omega

theorem result_of_nat (input : BitVec 32) (output : Word)
    (correct : output.toNat = WordMath.triangular input.toNat) :
    Arithmetic64.triangularModulo.result input output := by
  change output.toNat = WordMath.triangular input.toNat % 2^64
  have bound := WordMath.triangular_u32_lt63 input.isLt
  rw [Nat.mod_eq_of_lt (show WordMath.triangular input.toNat < 2^64 by omega)]
  exact correct

end EDSL.Corpus.V1.TriangularGCCBase

#print axioms EDSL.Corpus.V1.TriangularGCCBase.low8_and_one
#print axioms EDSL.Corpus.V1.TriangularGCCBase.result_of_nat
