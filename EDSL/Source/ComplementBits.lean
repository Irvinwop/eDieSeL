/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Syntax
import Init.Data.BitVec.Lemmas

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Source.ComplementBits

/-- Mathematical value bits only: every retained bit of the unsigned word is
flipped. No subtraction, source evaluator, object layout or native run occurs in
this specification. -/
def NatBits (width input result : Nat) : Prop :=
  ∀ index, index < width → result.testBit index = !input.testBit index

/-- Integer values are observed through their width-bounded mathematical
residues. This says nothing about object padding or memory representation. -/
def IntBits (width : Nat) (input result : Int) : Prop :=
  ∀ index, index < width →
    (BitVec.ofInt width result).getLsbD index =
      !(BitVec.ofInt width input).getLsbD index

/-- The all-ones conservation equation is exactly bitwise complementation for
bounded naturals. The library supplies the width-general bit-vector bridge. -/
theorem nat_sum_iff_word_not {width input result : Nat}
    (input_bound : input < 2 ^ width) (result_bound : result < 2 ^ width) :
    input + result = 2 ^ width - 1 ↔
      BitVec.ofNat width result = ~~~BitVec.ofNat width input := by
  constructor
  · intro equation
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_not, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt input_bound, Nat.mod_eq_of_lt result_bound]
    omega
  · intro words
    have equation := congrArg BitVec.toNat words
    simp only [BitVec.toNat_not, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt input_bound, Nat.mod_eq_of_lt result_bound] at equation
    have positive := Nat.two_pow_pos width
    omega

/-- This equivalence connects an arithmetic contract to independently specified
per-bit behavior for every width, including the empty width. -/
theorem nat_sum_iff_bits {width input result : Nat}
    (input_bound : input < 2 ^ width) (result_bound : result < 2 ^ width) :
    input + result = 2 ^ width - 1 ↔ NatBits width input result := by
  constructor
  · intro equation index below
    have words := (nat_sum_iff_word_not input_bound result_bound).mp equation
    have bit := congrArg (fun word : BitVec width => word.getLsbD index) words
    simpa only [BitVec.getLsbD_not, BitVec.getLsbD_ofNat, below, decide_true, Bool.true_and] using bit
  · intro bits
    apply (nat_sum_iff_word_not input_bound result_bound).mpr
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro index below
    simpa only [BitVec.getLsbD_not, BitVec.getLsbD_ofNat, below, decide_true, Bool.true_and] using bits index below

theorem nat_bits_unique {width input first second : Nat}
    (input_bound : input < 2 ^ width) (first_bound : first < 2 ^ width)
    (second_bound : second < 2 ^ width)
    (first_bits : NatBits width input first) (second_bits : NatBits width input second) :
    first = second := by
  have first_sum := (nat_sum_iff_bits input_bound first_bound).mpr first_bits
  have second_sum := (nat_sum_iff_bits input_bound second_bound).mpr second_bits
  omega

/-- The signed complement equation implies complement of the width residues.
No signed-range premise is required in this direction. -/
theorem int_sum_word_not {width : Nat} {input result : Int}
    (equation : input + result = -1) :
    BitVec.ofInt width result = ~~~BitVec.ofInt width input := by
  cases input with
  | ofNat value =>
      have result_eq : result = Int.negSucc value := by
        simp only [Int.negSucc_eq, Int.ofNat_eq_natCast] at equation ⊢
        omega
      simp only [result_eq, Int.ofNat_eq_natCast,
        BitVec.ofInt_negSucc_eq_not_ofNat, BitVec.ofInt_natCast]
  | negSucc value =>
      have result_eq : result = (value : Int) := by
        simp only [Int.negSucc_eq] at equation
        omega
      simp only [result_eq, BitVec.ofInt_negSucc_eq_not_ofNat, BitVec.not_not,
        BitVec.ofInt_natCast]

theorem int_sum_bits {width : Nat} {input result : Int}
    (equation : input + result = -1) : IntBits width input result := by
  intro index below
  have bit := congrArg (fun word : BitVec width => word.getLsbD index)
    (int_sum_word_not (width := width) equation)
  simpa [below] using bit

/-- Signed-range observations are injective. Consequently the independent
bit specification determines a unique representable signed result. -/
theorem int_bits_unique {width : Nat} (positive : 0 < width)
    {input first second : Int}
    (first_lower : -(2 : Int) ^ (width - 1) ≤ first)
    (first_upper : first < (2 : Int) ^ (width - 1))
    (second_lower : -(2 : Int) ^ (width - 1) ≤ second)
    (second_upper : second < (2 : Int) ^ (width - 1))
    (first_bits : IntBits width input first) (second_bits : IntBits width input second) :
    first = second := by
  have words : BitVec.ofInt width first = BitVec.ofInt width second := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro index below
    exact (first_bits index below).trans (second_bits index below).symm
  have observation := congrArg BitVec.toInt words
  simpa only [BitVec.toInt_ofInt_eq_self positive first_lower first_upper,
    BitVec.toInt_ofInt_eq_self positive second_lower second_upper] using observation

/-- At a signed value range, the sum equation and all retained value-bit flips
are equivalent. This closes both soundness and uniqueness of the arithmetic
complement law without assigning bit meanings by that arithmetic law. -/
theorem int_sum_iff_bits {width : Nat} (positive : 0 < width)
    {input result : Int}
    (input_lower : -(2 : Int) ^ (width - 1) ≤ input)
    (input_upper : input < (2 : Int) ^ (width - 1))
    (result_lower : -(2 : Int) ^ (width - 1) ≤ result)
    (result_upper : result < (2 : Int) ^ (width - 1)) :
    input + result = -1 ↔ IntBits width input result := by
  constructor
  · exact int_sum_bits
  · intro bits
    have candidate_lower : -(2 : Int) ^ (width - 1) ≤ -1 - input := by omega
    have candidate_upper : -1 - input < (2 : Int) ^ (width - 1) := by omega
    have candidate_bits : IntBits width input (-1 - input) := int_sum_bits (by omega)
    have same := int_bits_unique positive result_lower result_upper
      candidate_lower candidate_upper bits candidate_bits
    omega

/-- Direct bridge from the existing unsigned complement relation's arithmetic
field to the independent bits of the source integer's full value width. -/
theorem unsigned_value_bits (target : Target) (input result : Value target .uint)
    (equation : input.val + result.val = target.modulus - 1) :
    NatBits target.intBits input.val result.val :=
  (nat_sum_iff_bits input.isLt result.isLt).mp equation

/-- Direct bridge from the existing signed complement relation; this sound
bitwise consequence needs neither a source evaluator nor a safety assumption. -/
theorem signed_value_bits (target : Target) (input result : Value target .sint)
    (equation : input.val + result.val = -1) :
    IntBits target.intBits input.val result.val := int_sum_bits equation


end EDSL.Source.ComplementBits
