/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Sub64
import EDSL.Logical64.Algebra
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

/-- Unsigned representation of the signed byte, independently of extension. -/
def signedByteMaskNat (immediate : Byte) : Nat :=
  if immediate.toNat < 128 then immediate.toNat else 2^64 - 256 + immediate.toNat

/-- Even population of precisely the eight low result positions. -/
def lowByteEven (result : Word) : Bool :=
  decide (((List.range 8).filter (fun bit => result.toNat.testBit bit)).length % 2 = 0)

private theorem cpop_count {width : Nat} (value : BitVec width) (n acc : Nat) :
    value.cpopNatRec n acc = acc +
      ((List.range n).filter (fun bit => value.toNat.testBit bit)).length := by
  induction n generalizing acc with
  | zero => simp [BitVec.cpopNatRec]
  | succ n ih =>
    rw [BitVec.cpopNatRec, ih, List.range_succ, List.filter_append, List.length_append]
    cases bit : value.toNat.testBit n <;>
      simp [BitVec.getLsbD, bit] <;> omega

/-- Bridges the existing flag implementation to the independent population spec. -/
theorem evenParity_lowByte (result : Word) :
    evenParity (result.setWidth 8) = lowByteEven result := by
  have same : ((List.range 8).filter
      (fun bit => (result.setWidth 8).toNat.testBit bit)) =
      (List.range 8).filter (fun bit => result.toNat.testBit bit) := by
    apply List.filter_congr
    intro bit member
    have bound : bit < 8 := List.mem_range.mp member
    change (result.toNat % 2^8).testBit bit = result.toNat.testBit bit
    rw [Nat.testBit_mod_two_pow]
    simp only [bound, decide_true, Bool.true_and]
  have count : (result.setWidth 8).cpop.toNat =
      ((List.range 8).filter (fun bit => result.toNat.testBit bit)).length := by
    rw [BitVec.toNat_cpop, cpop_count, Nat.zero_add, same]
  unfold evenParity lowByteEven
  rw [BitVec.getLsbD, count, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one
      ((List.range 8).filter (fun bit => result.toNat.testBit bit)).length with h | h <;> simp [h]

structure AndImmediate64Contract (initial final : State)
    (destination : Register) (immediate : Byte) (af : Bool) : Prop where
  mathematical : EDSL.Logical64.MathematicalResult .intersection
    (initial.registers destination) (BitVec.ofNat 64 (signedByteMaskNat immediate))
    (final.registers destination)
  registerFrame : ∀ register, register ≠ destination →
    final.registers register = initial.registers register
  memory : final.memory = initial.memory
  flagsFrame : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask
  nextPC : final.rip = initial.rip + 4
  carry : final.flags.getLsbD 0 = false
  parity : final.flags.getLsbD 2 = lowByteEven (final.registers destination)
  auxiliary : final.flags.getLsbD 4 = af
  zero : final.flags.getLsbD 6 = decide ((final.registers destination).toNat = 0)
  sign : final.flags.getLsbD 7 = (final.registers destination).toNat.testBit 63
  overflow : final.flags.getLsbD 11 = false

/-- All 16 destinations, all 256 signed imm8s, arbitrary complete machine states
and both independent AF values. No operand-memory or stack premise. -/
theorem andImm64_contract (state : State) (destination : Register)
    (immediate : Byte) (af : Bool) :
    AndImmediate64Contract state
      (logical64State state .band destination (immediate.signExtend 64) 4 af)
      destination immediate af := by
  have mask : BitVec.ofNat 64 (signedByteMaskNat immediate) = immediate.signExtend 64 := by
    rw [signedByteMaskNat, ← signExtend8_toNat64, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have bits := logicalFlags64_bits state.flags
    (LogicalOp.band.eval (state.registers destination) (immediate.signExtend 64)) af
  refine ⟨?_, ?_, rfl, logicalFlags64_preserves .., rfl, bits.1, ?_, bits.2.2.1,
    ?_, ?_, bits.2.2.2.2.2⟩
  · simpa [logical64State, State.writeRegister, mask, EDSL.Logical64.Operation.toLogicalOp]
      using EDSL.Logical64.eval_mathematical .intersection
        (state.registers destination) (immediate.signExtend 64)
  · intro register different
    simp [logical64State, State.writeRegister, different]
  · simpa [logical64State, State.writeRegister, evenParity_lowByte] using bits.2.1
  · have zero (value : Word) : (value == 0) = decide (value.toNat = 0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq, BitVec.toNat_eq]
      rfl
    simpa only [logical64State, State.writeRegister, ite_true, zero] using bits.2.2.2.1
  · simpa [logical64State, State.writeRegister, BitVec.msb_eq_getLsbD_last,
      BitVec.testBit_toNat] using bits.2.2.2.2.1

theorem execute_andImm64 (state : State) (destination : Register)
    (immediate : Byte) (af : Bool) :
    execute state (.andImm64 destination immediate) af =
      .ok ⟨.next (logical64State state .band destination (immediate.signExtend 64) 4 af), []⟩ := rfl

theorem executeWith_andImm64 (state : State) (destination : Register)
    (immediate : Byte) (choices : FlagChoices) :
    executeWith state (.andImm64 destination immediate) choices =
      .ok ⟨.next (logical64State state .band destination (immediate.signExtend 64) 4 choices.af), []⟩ := rfl

theorem execute_andImm64_success {state final : State} {destination : Register}
    {immediate : Byte} {af : Bool} {reads : List Read}
    (actual : execute state (.andImm64 destination immediate) af = .ok ⟨.next final, reads⟩) :
    AndImmediate64Contract state final destination immediate af ∧ reads = [] := by
  cases actual
  exact ⟨andImm64_contract .., rfl⟩

theorem executeWith_andImm64_success {state final : State} {destination : Register}
    {immediate : Byte} {choices : FlagChoices} {reads : List Read}
    (actual : executeWith state (.andImm64 destination immediate) choices = .ok ⟨.next final, reads⟩) :
    AndImmediate64Contract state final destination immediate choices.af ∧ reads = [] := by
  cases actual
  exact ⟨andImm64_contract .., rfl⟩

/-- Success cannot hide a return, store, syscall or locked observation. -/
theorem execute_andImm64_observation {state : State} {destination : Register}
    {immediate : Byte} {af : Bool} {observation : Observation}
    (actual : execute state (.andImm64 destination immediate) af = .ok observation) :
    ∃ final, observation = ⟨.next final, []⟩ ∧
      AndImmediate64Contract state final destination immediate af := by
  cases actual
  exact ⟨_, rfl, andImm64_contract ..⟩

theorem executeWith_andImm64_observation {state : State} {destination : Register}
    {immediate : Byte} {choices : FlagChoices} {observation : Observation}
    (actual : executeWith state (.andImm64 destination immediate) choices = .ok observation) :
    ∃ final, observation = ⟨.next final, []⟩ ∧
      AndImmediate64Contract state final destination immediate choices.af := by
  cases actual
  exact ⟨_, rfl, andImm64_contract ..⟩

/-- These classifiers expose the actual pure family to existing policy APIs.
WP rules above this layer still require the ordinary checked executor equation. -/
theorem andImm64_classifiers (state : State) (destination : Register) (immediate : Byte) :
    let instruction := Instruction.andImm64 destination immediate
    instruction.operandReads state = [] ∧ instruction.storeIntent state = none ∧
      instruction.storeIntent64 state = none ∧ instruction.isLocked = false ∧
      instruction.boolChoiceProfile = true ∧ instruction.choiceFlag state = some .af ∧
      instruction.undefinedFlags state = [.af] := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Actual successful decoding composes with the existing ordered, canonical,
executable fetch implementation; no following-byte premise is introduced. -/
theorem step_andImm64 {state : State} {destination : Register} {immediate : Byte}
    (decoded : decodeAt state = .ok (.andImm64 destination immediate)) (af : Bool) :
    step af state =
      .ok ⟨.next (logical64State state .band destination (immediate.signExtend 64) 4 af), []⟩ :=
  (step_eq_execute af decoded).trans (execute_andImm64 ..)

theorem stepWith_andImm64 {state : State} {destination : Register} {immediate : Byte}
    (decoded : decodeAt state = .ok (.andImm64 destination immediate)) (choices : FlagChoices) :
    stepWith choices state =
      .ok ⟨.next (logical64State state .band destination (immediate.signExtend 64) 4 choices.af), []⟩ :=
  (stepWith_eq_executeWith choices decoded).trans (executeWith_andImm64 ..)

end EDSL.X86.Sequential
#print axioms EDSL.X86.Sequential.evenParity_lowByte
#print axioms EDSL.X86.Sequential.andImm64_contract
#print axioms EDSL.X86.Sequential.execute_andImm64_success
#print axioms EDSL.X86.Sequential.executeWith_andImm64_success
#audit_edsl
