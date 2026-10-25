/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.TriangularGCCFacts

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.Corpus.V1.TriangularGCCBase
open X86 X86.Sequential X86.VCGen
open TriangularGCCGraph

/-- Internal exhaustive arithmetic case of the universal original entry VC. -/
theorem entryEven (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec bytes input initial)
    (zero : (initial.registers .rdi).setWidth 32 ≠ 0#32)
    (even : input.value.toNat % 2 = 0) :
    Cutpoints.wp graph initial.rip (PureCall.Post spec input initial)
      (fun _ read => PureCall.RawRead initial read)
      (invariant input initial) (rank input) (rank input entry initial) 13 entry initial := by
  have argument := (Arithmetic64.triangularModulo_bound_iff input.value initial).mp pre.arguments
  have stack := pre.stack
  have target := pre.returnCanonical
  have canonicalZero : canonical (initial.rip + 56#64) = true :=
    code_canonical_offset pre.code 56 (by decide +kernel)
  have canonicalHead : canonical (initial.rip + 40#64) = true :=
    code_canonical_offset pre.code 40 (by decide +kernel)
  have canonicalOne : canonical (initial.rip + 59#64) = true :=
    code_canonical_offset pre.code 59 (by decide +kernel)
  have lowNat : ((initial.registers .rdi).setWidth 32).toNat = input.value.toNat := congrArg BitVec.toNat argument
  have wideNat : (((initial.registers .rdi).setWidth 32).setWidth 64).toNat = input.value.toNat :=
    (BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)).trans lowNat
  have parity : (initial.registers .rdi).toNat % 2 = input.value.toNat % 2 := by
    have observed := congrArg (fun n : Nat => n % 2) lowNat
    simpa only [BitVec.toNat_setWidth,
      Nat.mod_mod_of_dvd (initial.registers .rdi).toNat (by decide : 2 ∣ 2^32)] using observed
  have rawPositive : 0 < ((initial.registers .rdi).setWidth 32).toNat := by
    have nonzero : ((initial.registers .rdi).setWidth 32).toNat ≠ 0 := by
      intro eq
      apply zero
      exact BitVec.eq_of_toNat_eq eq
    omega
  have positive : 0 < input.value.toNat := by rw [← lowNat]; exact rawPositive
  have predecessor : ((((initial.registers .rdi).setWidth 32).setWidth 64) + (0xff : Byte).signExtend 64).toNat = input.value.toNat - 1 :=
    (predecessor_toNat ((initial.registers .rdi).setWidth 32) rawPositive).trans (congrArg (fun n => n - 1) lowNat)
  have predNat : ((((initial.registers .rdi).setWidth 32).setWidth 64) + 18446744073709551615#64).toNat = input.value.toNat - 1 := by
    simpa only [minusOne64] using predecessor
  have start := WordMath.TriangularCountdown.start_even input.value.toNat even
  have smaller := WordMath.TriangularCountdown.entry_rank (Nat.le_refl input.value.toNat)
  vcgen_block_step graph entry simp
  vcgen_block_step graph entry simp [BitVec.add_assoc]
  vcgen_block_step graph entry simp [test32_zero_bit, zero, BitVec.add_assoc]
  vcgen_block_step graph entry simp [BitVec.add_assoc]
  vcgen_block_step graph entry simp [BitVec.add_assoc]
  vcgen_block_step graph entry simp [BitVec.add_assoc]
  vcgen_block_step graph entry simp [BitVec.add_assoc]
  vcgen_block_step graph entry simp [test8_zero_bit, parity, even, BitVec.add_assoc, canonicalHead]
  vcgen_factor =>
    change LoopInvariant input initial _ ∧ _
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · vcgen_scratch_frame (PureCall.ScratchFrame.refl scratch initial) with
        simp only [State.writeRegister, logicalFlags8_preserves, logicalFlags32_preserves]
    · change WordMath.TriangularCountdown input.value.toNat (0#64).toNat (((initial.registers .rdi).setWidth 32).setWidth 64).toNat
      rw [wideNat]
      exact start
    · change 0 < (((initial.registers .rdi).setWidth 32).setWidth 64).toNat
      rw [wideNat]
      exact positive
    · change (((initial.registers .rdi).setWidth 32).setWidth 64).toNat / 2 < input.value.toNat / 2 + 1
      rw [wideNat]
      exact smaller

end EDSL.Corpus.V1.TriangularGCCBase

#print axioms EDSL.Corpus.V1.TriangularGCCBase.entryEven
