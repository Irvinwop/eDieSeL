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

abbrev oddStart : graph.Index := ⟨8, by decide +kernel⟩

/-- Five actual instructions after the odd parity edge. These are internal
state facts established by the entry prefix, not invocation admission. -/
theorem preparedOdd (input : PureCall.Invocation spec) (initial current : State)
    (frame : PureCall.ScratchFrame scratch initial current)
    (pc : current.rip = initial.rip + 22#64)
    (argument : (current.registers .rdi).toNat = input.value.toNat)
    (predecessor : (current.registers .rdx).toNat = input.value.toNat - 1)
    (odd : input.value.toNat % 2 = 1) (positive : 0 < input.value.toNat - 1) :
    Cutpoints.wp graph initial.rip (PureCall.Post spec input initial)
      (fun _ read => PureCall.RawRead initial read)
      (invariant input initial) (rank input) (rank input entry initial) 5 oddStart current := by
  have nonzero : current.registers .rdx ≠ 0#64 := by
    intro eq
    have bad := congrArg BitVec.toNat eq
    change (current.registers .rdx).toNat = 0 at bad
    omega
  have start : WordMath.TriangularCountdown input.value.toNat
      (current.registers .rdi).toNat (current.registers .rdx).toNat := by
    rw [argument, predecessor]
    exact WordMath.TriangularCountdown.start_odd input.value.toNat odd
  have smaller : (current.registers .rdx).toNat / 2 < input.value.toNat / 2 + 1 :=
    WordMath.TriangularCountdown.entry_rank (by omega)
  vcgen_block_step graph oddStart simp [pc, BitVec.add_assoc]
  vcgen_block_step graph oddStart simp [BitVec.add_assoc]
  vcgen_block_step graph oddStart simp [BitVec.add_assoc]
  vcgen_block_step graph oddStart simp [test64_zero_bit, nonzero, BitVec.add_assoc]
  vcgen_block_step graph oddStart simp [BitVec.add_assoc]
  vcgen_factor =>
    change LoopInvariant input initial _ ∧ _
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · vcgen_scratch_frame frame
    · change WordMath.TriangularCountdown input.value.toNat
        (current.registers .rdi).toNat (current.registers .rdx).toNat
      exact start
    · change 0 < (current.registers .rdx).toNat
      omega
    · change (current.registers .rdx).toNat / 2 < input.value.toNat / 2 + 1
      exact smaller

end EDSL.Corpus.V1.TriangularGCCBase

#print axioms EDSL.Corpus.V1.TriangularGCCBase.preparedOdd
