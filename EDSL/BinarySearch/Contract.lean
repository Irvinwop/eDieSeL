import EDSL.BufferCall.Elements
import EDSL.WordMath.BinarySearch.Transitions

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.BinarySearch
open X86 X86.Sequential
namespace Math
export WordMath.BinarySearch (Sorted Invariant Correct initial wordMidpoint wordMidpoint_toNat
  wordMidpoint_bounds wordMidpoint_successor_toNat wordMidpoint_ranks
  advance_low_word retreat_high_word found_word exhausted_word)
end Math

structure Input where
  base : Word
  values : List (BitVec 32)
  key : BitVec 32

def sequence (input : Input) (index : Nat) : Nat := (input.values[index]?.getD 0).toNat
def sizeMax : Word := 0xffffffffffffffff

/-- Any in-range equal position is permitted, including duplicates. The
full-width all-ones sentinel is returned precisely for complete absence. -/
def Result (input : Input) (actual : Word) : Prop :=
  if actual = sizeMax then
    WordMath.BinarySearch.Correct (sequence input) input.key.toNat input.values.length none
  else WordMath.BinarySearch.Correct (sequence input) input.key.toNat input.values.length
    (some actual.toNat)

/-- Only representability and nondecreasing mathematical order. Current full
byte extent/readability and OS loans are supplied by the generic call bridge. -/
abbrev spec : BufferCall.Spec where
  Input := Input
  arguments input index := match index.val with
    | 0 => some (.word64 input.base)
    | 1 => some (.word64 (BitVec.ofNat 64 input.values.length))
    | 2 => some (.low32 input.key)
    | _ => none
  buffers input := [⟨input.base, BufferCall.Elements.u32Bytes input.values⟩]
  domain input := input.values.length < 2^64 ∧
    WordMath.BinarySearch.Sorted (sequence input) input.values.length
  result := Result
  useful input := input.values ≠ []

theorem sequence_at {input : Input} {index : Nat} {value : BitVec 32}
    (present : input.values[index]? = some value) : sequence input index = value.toNat := by
  simp only [sequence, present, Option.getD_some]

theorem result_hit {input : Input} {actual : Word}
    (small : input.values.length < 2^64)
    (correct : WordMath.BinarySearch.Correct (sequence input) input.key.toNat
      input.values.length (some actual.toNat)) : Result input actual := by
  have different : actual ≠ sizeMax := by
    intro same
    have bound := correct.1
    rw [same] at bound
    change 18446744073709551615 < input.values.length at bound
    omega
  simpa only [Result, different, ↓reduceIte] using correct

theorem result_absent {input : Input}
    (correct : WordMath.BinarySearch.Correct (sequence input) input.key.toNat
      input.values.length none) : Result input sizeMax := by
  simpa only [Result, ↓reduceIte] using correct

theorem sentinel_iff_absent {input : Input} {actual : Word} (result : Result input actual) :
    actual = sizeMax ↔ ∀ index, index < input.values.length →
      sequence input index ≠ input.key.toNat := by
  by_cases sentinel : actual = sizeMax
  · simp only [Result, sentinel, ↓reduceIte] at result
    exact ⟨fun _ => result, fun _ => sentinel⟩
  · simp only [Result, sentinel, ↓reduceIte, WordMath.BinarySearch.Correct] at result
    constructor
    · exact False.elim ∘ sentinel
    · intro absent
      exact False.elim (absent actual.toNat result.1 result.2)

#print axioms result_hit
#print axioms result_absent
#print axioms sentinel_iff_absent
end EDSL.BinarySearch
#audit_edsl
