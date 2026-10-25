/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.MachineChoices
import EDSL.X86.Sequential.ConditionFlags
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

/-!
Full64 register and sign-extended imm8 subtraction under the existing sequential
CET-off target. Both leaves reuse one state transformer and cmpFlags64. Operands
come from the original state, including aliases and RSP. All six arithmetic
flags are defined; there is no undefined-choice, DATA, store, locked or syscall
effect. Updating RSP supplies no new return-stack permission or ownership.

These are local machine-model contracts, not physical CPU/OS correspondence,
source/compiler preservation, program termination or corpus certification.
-/

/-- Independent arithmetic and full-state frame shared by both SUB64 leaves.
The unsigned RHS is its complete Word representation; a negative imm8 therefore
has a large unsigned representative for CF. It is not an ADD carry contract. -/
structure Sub64Contract (initial final : State) (destination : Register)
    (right : Word) (length : Nat) : Prop where
  unsignedResult : (final.registers destination).toNat =
    (2^64 - right.toNat + (initial.registers destination).toNat) % 2^64
  signedResult : (final.registers destination).toInt =
    ((initial.registers destination).toInt - right.toInt).bmod (2^64)
  registerFrame : ∀ register, register ≠ destination →
    final.registers register = initial.registers register
  memory : final.memory = initial.memory
  flagsFrame : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask
  nextPC : final.rip = initial.rip + BitVec.ofNat 64 length
  carry : final.flags.getLsbD 0 = true ↔ (initial.registers destination).toNat < right.toNat
  parity : final.flags.getLsbD 2 =
    evenParity (((initial.registers destination) - right).setWidth 8)
  auxiliary : final.flags.getLsbD 4 = true ↔
    (initial.registers destination).toNat % 16 < right.toNat % 16
  zero : final.flags.getLsbD 6 = (initial.registers destination == right)
  sign : final.flags.getLsbD 7 = (initial.registers destination - right).msb
  overflow : final.flags.getLsbD 11 = true ↔
    (initial.registers destination).toInt - right.toInt < -(2^63 : Int) ∨
      2^63 ≤ (initial.registers destination).toInt - right.toInt

/-- Shared contract over arbitrary full64 operands and every GPR. No memory
accessibility, canonicality or special stack precondition is hidden here. -/
theorem sub64State_contract (state : State) (destination : Register) (right : Word)
    (length : Nat) : Sub64Contract state (sub64State state destination right length)
      destination right length := by
  refine {
    unsignedResult := ?_
    signedResult := ?_
    registerFrame := ?_
    memory := rfl
    flagsFrame := cmpFlags64_preserves ..
    nextPC := rfl
    carry := cmpFlags64_borrow ..
    parity := (cmpFlags64_bits ..).2.1
    auxiliary := cmpFlags64_auxiliary ..
    zero := cmpFlags64_zero ..
    sign := (cmpFlags64_bits ..).2.2.2.2.1
    overflow := cmpFlags64_overflow .. }
  · simp only [sub64State, State.writeRegister, ↓reduceIte, BitVec.toNat_sub]
  · simp only [sub64State, State.writeRegister, ↓reduceIte, BitVec.toInt_sub]
  · intro register different
    simp [sub64State, State.writeRegister, different]

/-- The unsigned full64 representation of a signed byte, without a bitvector
extension on the right side. Negative-byte CF uses this representation. -/
theorem signExtend8_toNat64 (immediate : Byte) :
    (immediate.signExtend 64).toNat =
      if immediate.toNat < 128 then immediate.toNat else 2^64 - 256 + immediate.toNat := by
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
  by_cases nonnegative : immediate.toNat < 128
  · have notHigh : ¬128 ≤ immediate.toNat := by omega
    simp [BitVec.msb_eq_decide, nonnegative, notHigh]
  · have high : 128 ≤ immediate.toNat := by omega
    simp [BitVec.msb_eq_decide, nonnegative, high, Nat.add_comm]

theorem execute_subReg64 (state : State) (destination source : Register) (choice : Bool) :
    execute state (.subReg64 destination source) choice =
      .ok ⟨.next (sub64State state destination (state.registers source) 3), []⟩ := rfl

theorem execute_subImm64 (state : State) (destination : Register) (immediate : Byte)
    (choice : Bool) :
    execute state (.subImm64 destination immediate) choice =
      .ok ⟨.next (sub64State state destination (immediate.signExtend 64) 4), []⟩ := rfl

theorem step_subReg64 {state : State} {destination source : Register}
    (decoded : decodeAt state = .ok (.subReg64 destination source)) (choice : Bool) :
    step choice state =
      .ok ⟨.next (sub64State state destination (state.registers source) 3), []⟩ := by
  rw [step_eq_execute choice decoded, execute_subReg64]

theorem step_subImm64 {state : State} {destination : Register} {immediate : Byte}
    (decoded : decodeAt state = .ok (.subImm64 destination immediate)) (choice : Bool) :
    step choice state =
      .ok ⟨.next (sub64State state destination (immediate.signExtend 64) 4), []⟩ := by
  rw [step_eq_execute choice decoded, execute_subImm64]

/-- A decoded register SUB always has the independent arithmetic/frame
contract, with the source captured before the destination write. -/
theorem execute_subReg64_contract (state : State) (destination source : Register)
    (choice : Bool) :
    ∃ final, execute state (.subReg64 destination source) choice = .ok ⟨.next final, []⟩ ∧
      Sub64Contract state final destination (state.registers source) 3 :=
  ⟨_, rfl, sub64State_contract ..⟩

theorem execute_subImm64_contract (state : State) (destination : Register) (immediate : Byte)
    (choice : Bool) :
    ∃ final, execute state (.subImm64 destination immediate) choice = .ok ⟨.next final, []⟩ ∧
      Sub64Contract state final destination (immediate.signExtend 64) 4 :=
  ⟨_, rfl, sub64State_contract ..⟩

/-- Success inversion exposes the independent contract and the actual empty
read trace; a caller cannot supply a separate operand-read observation. -/
theorem execute_subReg64_success {state final : State} {destination source : Register}
    {choice : Bool} {reads : List Read}
    (actual : execute state (.subReg64 destination source) choice = .ok ⟨.next final, reads⟩) :
    Sub64Contract state final destination (state.registers source) 3 ∧ reads = [] := by
  cases actual
  exact ⟨sub64State_contract .., rfl⟩

theorem execute_subImm64_success {state final : State} {destination : Register}
    {immediate : Byte} {choice : Bool} {reads : List Read}
    (actual : execute state (.subImm64 destination immediate) choice = .ok ⟨.next final, reads⟩) :
    Sub64Contract state final destination (immediate.signExtend 64) 4 ∧ reads = [] := by
  cases actual
  exact ⟨sub64State_contract .., rfl⟩

/-- All status flags are defined. The vector API delegates to the same
production transformer and ignores every flag-choice component. -/
theorem executeWith_subReg64 (state : State) (destination source : Register)
    (choices : FlagChoices) :
    executeWith state (.subReg64 destination source) choices =
      .ok ⟨.next (sub64State state destination (state.registers source) 3), []⟩ := rfl

theorem executeWith_subImm64 (state : State) (destination : Register) (immediate : Byte)
    (choices : FlagChoices) :
    executeWith state (.subImm64 destination immediate) choices =
      .ok ⟨.next (sub64State state destination (immediate.signExtend 64) 4), []⟩ := rfl

/-- Full64 interval distance is natural subtraction when no borrow is
possible. The architectural flags remain SUB flags, not DEC or ADD flags. -/
theorem subReg64_distance_nat (left right : Word) (ordered : right.toNat ≤ left.toNat) :
    (left - right).toNat = left.toNat - right.toNat := by
  exact BitVec.toNat_sub_of_le (show right ≤ left from ordered)

/-- Generic nonnegative-byte decrement; negative imm8 values deliberately
remain outside this Nat-decrement corollary. -/
theorem subImm64_decrement_nat (value : Word) (immediate : Byte)
    (nonnegative : immediate.toNat < 128) (enough : immediate.toNat ≤ value.toNat) :
    (value - immediate.signExtend 64).toNat = value.toNat - immediate.toNat := by
  have rhs : (immediate.signExtend 64).toNat = immediate.toNat := by
    rw [signExtend8_toNat64, ite_eq_left nonnegative]
  rw [subReg64_distance_nat value (immediate.signExtend 64) (by omega), rhs]

/-- The counted-by-two arithmetic needed by a future triangular loop proof.
No loop invariant, progress or function certification is assumed or supplied. -/
theorem subImm64_two_nat (value : Word) (remaining : Nat)
    (matching : value.toNat = remaining) (enough : 2 ≤ remaining) :
    (value - (2 : Byte).signExtend 64).toNat = remaining - 2 := by
  simpa [matching] using subImm64_decrement_nat value 2 (by decide) (by simpa [matching] using enough)

end EDSL.X86.Sequential

#print axioms EDSL.X86.Sequential.sub64State_contract
#print axioms EDSL.X86.Sequential.signExtend8_toNat64
#print axioms EDSL.X86.Sequential.execute_subReg64_success
#print axioms EDSL.X86.Sequential.execute_subImm64_success
#print axioms EDSL.X86.Sequential.executeWith_subReg64
#print axioms EDSL.X86.Sequential.executeWith_subImm64
#print axioms EDSL.X86.Sequential.subReg64_distance_nat
#print axioms EDSL.X86.Sequential.subImm64_decrement_nat
#print axioms EDSL.X86.Sequential.subImm64_two_nat
#audit_edsl
