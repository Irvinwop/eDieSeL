/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.BufferCall.Refinement
import EDSL.Grading.IndexSearch
import EDSL.BinarySearch.Contract

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.BinarySearch
open X86 X86.Sequential

/-- The inputs describe the same snapshot and key; first-match search permits
unsorted inputs while the binary-search contract requires nondecreasing order. -/
def linearInput (input : Input) : Grading.IndexSearch.U32Input :=
  ⟨input.base, input.values, input.key⟩

/-- The earliest-match specification implies any-match/complete-absence.
The converse fails on duplicates. This is mathematics over independent result
relations, with no code, instruction shape, execution or resource premise. -/
theorem result_of_first_match (input : Input) (actual : Word)
    (small : input.values.length < 2^64)
    (correct : Grading.IndexSearch.Result input.values input.key actual) :
    Result input actual := by
  by_cases absent : actual = sizeMax
  · subst actual
    apply result_absent
    have allAbsent := (correct.sentinel_iff small).mp (by rfl)
    intro index inside equal
    apply allAbsent input.values[index] (List.getElem_mem inside)
    apply BitVec.eq_of_toNat_eq
    simpa only [sequence, List.getElem?_eq_getElem inside, Option.getD_some] using equal
  · obtain ⟨inside, present, _⟩ := correct.present small (by exact absent)
    apply result_hit small
    exact ⟨inside, sequence_at present⟩

/-- A verified first-u32-match implementation can serve the any-match task on
its sorted domain. Full64 count/sentinel, arbitrary upper key bits, every byte
of the input snapshot, and all original resources are preserved. -/
def fromFirstMatch : BufferCall.Refinement Grading.IndexSearch.u32Spec spec where
  translate := linearInput
  arguments _ := rfl
  buffers _ := rfl
  domain _ admitted := admitted.1
  result input actual admitted correct := result_of_first_match input actual admitted.1 correct

/-- Reuse an existing complete machine/resource proof without another set of
program VCs. This theorem does not claim that a particular binary is a verified
first-match implementation, or establish useful target-domain nonvacuity. -/
theorem semantics_of_first_match {bytes : List Byte}
    (verified : Grading.ReadOnlySemanticClaim
      (BufferCall.readOnlyTask Grading.IndexSearch.u32Spec) bytes) :
    Grading.ReadOnlySemanticClaim (BufferCall.readOnlyTask spec) bytes :=
  fromFirstMatch.semantics verified

/-- Independent duplicate behavior prevents accidentally reversing the
refinement or strengthening an any-match contract to earliest-match. -/
theorem duplicate_second_hit_not_first :
    Result ⟨0, [7, 7], 7⟩ 1 ∧
      ¬Grading.IndexSearch.Result ([7, 7] : List (BitVec 32)) 7 1 := by
  constructor
  · apply result_hit (by decide +kernel)
    constructor
    · decide +kernel
    · decide +kernel
  · intro first
    obtain ⟨_, _, earlier⟩ := first.present (by decide +kernel) (by decide +kernel)
    exact earlier 0 (by decide +kernel) rfl

#print axioms result_of_first_match
#print axioms semantics_of_first_match
#print axioms duplicate_second_hit_not_first
end EDSL.BinarySearch
