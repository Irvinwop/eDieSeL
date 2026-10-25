/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.WordMath.TriangularCountdown
import EDSL.X86.Sequential.Sub64
import EDSL.PureCall.Frame

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential

/-- The actual SIB expression; scale=1 means multiplication by two.
The fit premise concerns arithmetic, and grants no RAM/operand permission. -/
theorem Address.sib_scale_one_minus_one_toNat (before : State) (base index : Register)
    (positive : 0 < (before.registers index).toNat)
    (fit : (before.registers base).toNat + 2 * (before.registers index).toNat < 2^64) :
    ((Address.sibDisp8 base (some index) 1 0xff).eval before).toNat =
      (before.registers base).toNat + (2 * (before.registers index).toNat - 1) := by
  exact WordMath.add_twice_minus_one_toNat _ _ positive fit

/-- This is the legacy JNZ decision after actual SUB, not ADD/DEC flags. -/
theorem subImm64_two_jnz (before : State) (destination : Register) :
    (!(sub64State before destination ((2 : Byte).signExtend 64) 4).flags.getLsbD 6) =
      decide ((before.registers destination).toNat ≠ 2) := by
  change Condition.holds .notEqual
    (cmpFlags64 before.flags (before.registers destination) ((2 : Byte).signExtend 64)) = _
  exact Condition.cmp_notEqual_nat before.flags (before.registers destination) 2

end EDSL.X86.Sequential

namespace EDSL.PureCall
open X86 X86.Sequential

/-- Shared full frame for production SUB64, including an explicit scratch
membership requirement even for RSP. No execution or read authority is inferred. -/
theorem ScratchFrame.sub64State {scratch : List Register} {initial current : State}
    (frame : ScratchFrame scratch initial current) (destination : Register)
    (right : Word) (length : Nat) (member : destination ∈ scratch) :
    ScratchFrame scratch initial (sub64State current destination right length) := by
  refine ⟨frame.memory, (cmpFlags64_preserves current.flags (current.registers destination) right).trans
    frame.flags, ?_⟩
  intro register outside
  have different : register ≠ destination := fun same => outside (same.symm ▸ member)
  exact ((Sequential.sub64State_contract current destination right length).registerFrame
    register different).trans (frame.registers register outside)

end EDSL.PureCall

#print axioms EDSL.X86.Sequential.Address.sib_scale_one_minus_one_toNat
#print axioms EDSL.X86.Sequential.subImm64_two_jnz
#print axioms EDSL.PureCall.ScratchFrame.sub64State
