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

/-- Universal loop block with actual SUB flags, branch and terminal RET. -/
theorem loopBlock : LoopBlockVC := by
  intro input initial pre current binding admitted
  obtain ⟨frame, budget, positive⟩ := admitted
  have enough := budget.enough positive
  have updated := budget.word_step (current.registers .rax) (current.registers .rdi)
    input.value.isLt enough
  have decrement := subImm64_two_nat (current.registers .rdi) _ rfl enough
  have rsp : current.registers .rsp = initial.registers .rsp := frame.registers .rsp (by decide)
  have stack : readWord current.memory (current.registers .rsp) = .ok input.returnAddress := by
    rw [frame.memory, rsp]
    exact pre.stack
  have target := pre.returnCanonical
  have pc : current.rip = initial.rip + 40#64 := binding.2
  have canonicalHead : canonical (initial.rip + 40#64) = true :=
    code_canonical_offset pre.code 40 (by decide +kernel)
  by_cases last : (current.registers .rdi).toNat = 2
  · have equalTwo : current.registers .rdi = (2 : Word) := BitVec.eq_of_toNat_eq last
    have done : (current.registers .rdi - (2 : Byte).signExtend 64).toNat = 0 := by
      rw [decrement, last]
    have result := result_of_nat input.value
      (current.registers .rax + (current.registers .rdi <<< 1) + (0xff : Byte).signExtend 64)
      (updated.1.finish done)
    have branchFlag : (cmpFlags64 current.flags (current.registers .rdi) 2#64)[6] = true := by
      change (cmpFlags64 current.flags (current.registers .rdi) ((2 : Byte).signExtend 64)).getLsbD 6 = true
      simp only [cmpFlags64_zero, equalTwo]; decide +kernel
    vcgen_block_step graph loopHead simp [pc, BitVec.add_assoc]
    vcgen_block_step graph loopHead simp [sub64State, BitVec.add_assoc]
    vcgen_block_step graph loopHead simp [branchFlag, BitVec.add_assoc]
    vcgen_block_step graph loopHead simp [frame.memory, pre.stack, target, PureCall.RawRead, rsp]
    vcgen_factor =>
      refine PureCall.ScratchFrame.post_return (scratch := scratch) ?_ saved_protected ?_ rfl ?_
      · vcgen_scratch_frame (frame.weaken (show scratch ⊆ .rsp :: scratch from fun _ h => List.mem_cons_of_mem _ h))
      · change spec.result input.value (current.registers .rax + ((current.registers .rdi <<< 1) + 18446744073709551615#64))
        simpa only [BitVec.add_assoc, minusOne64] using result
      · rfl
  · have unequalTwo : current.registers .rdi ≠ (2 : Word) := by
      intro eq
      apply last
      exact congrArg BitVec.toNat eq
    have nextPositive : 0 < (current.registers .rdi - (2 : Byte).signExtend 64).toNat := by
      rw [decrement]
      omega
    have branchFlag : (cmpFlags64 current.flags (current.registers .rdi) 2#64)[6] = false := by
      change (cmpFlags64 current.flags (current.registers .rdi) ((2 : Byte).signExtend 64)).getLsbD 6 = false
      simp only [cmpFlags64_zero, Bool.beq_eq_decide_eq]
      exact decide_eq_false unequalTwo
    vcgen_block_step graph loopHead simp [pc, BitVec.add_assoc]
    vcgen_block_step graph loopHead simp [sub64State, BitVec.add_assoc]
    vcgen_block_step graph loopHead simp [branchFlag, BitVec.add_assoc, canonicalHead]
    vcgen_factor =>
      change LoopInvariant input initial _ ∧ _
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · vcgen_scratch_frame frame
      · simpa only [BitVec.add_assoc, minusOne64, two64, reduceCtorEq, ↓reduceIte] using updated.1
      · exact nextPositive
      · change (current.registers .rdi - 2#64).toNat / 2 < (current.registers .rdi).toNat / 2
        simpa only [two64] using updated.2

end EDSL.Corpus.V1.TriangularGCCBase

#print axioms EDSL.Corpus.V1.TriangularGCCBase.loopBlock
