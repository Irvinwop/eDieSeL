import EDSL.X86.VCGen.Branch
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.X86.VCGen.BranchControls
open Sequential Cutpoints

/-- Deliberately tiny WP inputs, without any claim of CFG validity. -/
def two (instruction : Sequential.Instruction) (cut : Bool) (destination : Nat) : CFG.Graph :=
  ⟨[⟨0, instruction, false, 1⟩, ⟨destination, .legacy .ret, cut, 0⟩], 1⟩

abbrev first (instruction : Sequential.Instruction) (cut : Bool) (destination : Nat) :
    (two instruction cut destination).Index := ⟨0, by change 0 < 2; decide⟩

/-- An unused target must not reject fallthrough. No operand reads are authorized. The invariant checks
all registers, flags and the complete RAM/permission map. -/
theorem untaken_preserves_context (state : State)
    (notEqual : Condition.holds .equal state.flags = false) :
    wp (two (.je 1) true 2) state.rip (fun _ => False) (fun _ _ => False)
      (fun _ final => final.registers = state.registers ∧ final.flags = state.flags ∧
        final.memory = state.memory) (fun _ _ => 0) 1 1 (first _ _ _) state := by
  apply (wp_je_iff _ _ _ _ _ _ _ _ _ _ 1 false rfl notEqual (by simp)).2
  refine ⟨⟨1, by change 1 < 2; decide⟩, ?_, ?_⟩
  · rfl
  · exact ⟨⟨rfl, rfl, rfl⟩, by change 0 < 1; decide⟩

theorem boundary_taken_je_rejected (state : State)
    (pc : state.rip = 0x00007ffffffffffd#64)
    (equal : Condition.holds .equal state.flags = true) :
    ¬wp (two (.je 1) true 3) state.rip (fun _ => True) (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => 0) 1 1 (first _ _ _) state := by
  intro admitted
  have bad : canonical (state.rip + 2 + (1 : Byte).signExtend 64) = false := by
    rw [pc]; decide +kernel
  have effect := execute_shortBranch_noncanonical state (.equal 1) equal bad false
  have one := admitted false
  change (match execute state (.je 1) false with
    | .error _ => False | .ok _ => _) at one
  simp only [effect] at one

theorem boundary_taken_jcc_rejected (state : State)
    (pc : state.rip = 0x00007ffffffffffd#64)
    (below : Condition.holds .below state.flags = true) :
    ¬wp (two (.jcc .below 1) true 3) state.rip (fun _ => True) (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => 0) 1 1 (first _ _ _) state := by
  intro admitted
  have bad : canonical (state.rip + 2 + (1 : Byte).signExtend 64) = false := by
    rw [pc]; decide +kernel
  have effect := execute_shortBranch_noncanonical state (.generic .below 1) below bad false
  have one := admitted false
  change (match execute state (.jcc .below 1) false with
    | .error _ => False | .ok _ => _) at one
  simp only [effect] at one

/-- A branch cannot manufacture progress in a rank read from the unchanged
RCX register. This guards the strict dynamic-rank test. -/
theorem unchanged_dynamic_rank_rejected (state : State)
    (notEqual : Condition.holds .equal state.flags = false) :
    ¬wp (two (.je 1) true 2) state.rip (fun _ => True) (fun _ _ => True)
      (fun _ _ => True) (fun _ final => (final.registers .rcx).toNat)
      (state.registers .rcx).toNat 1 (first _ _ _) state := by
  rw [wp_je_iff _ _ _ _ _ _ _ _ _ _ 1 false rfl notEqual (by simp)]
  simp [Next, two, CFG.Graph.node, CFG.Graph.cutpoint, wp]

/-- Reaching an interior node consumes fuel and cannot use its invariant as
though it were a cutpoint. -/
theorem interior_zero_fuel_rejected (state : State)
    (notEqual : Condition.holds .equal state.flags = false) :
    ¬wp (two (.je 1) false 2) state.rip (fun _ => True) (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => 0) 1 1 (first _ _ _) state := by
  rw [wp_je_iff _ _ _ _ _ _ _ _ _ _ 1 false rfl notEqual (by simp)]
  intro admitted
  obtain ⟨destination, _, continuation⟩ := admitted
  have bounds : destination.val < 2 := destination.isLt
  have cases : destination.val = 0 ∨ destination.val = 1 := by omega
  rcases cases with zero | one
  · simp [two, CFG.Graph.cutpoint, CFG.Graph.node, zero, wp] at continuation
  · simp [two, CFG.Graph.cutpoint, CFG.Graph.node, one, wp] at continuation

/-- Even a permissive invariant cannot supply a missing destination. -/
theorem missing_destination_rejected (state : State)
    (notEqual : Condition.holds .equal state.flags = false) :
    ¬wp (two (.je 1) true 7) state.rip (fun _ => True) (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => 0) 1 1 (first _ _ _) state := by
  rw [wp_je_iff _ _ _ _ _ _ _ _ _ _ 1 false rfl notEqual (by simp)]
  intro admitted
  obtain ⟨destination, pc, _⟩ := admitted
  have bounds : destination.val < 2 := destination.isLt
  have cases : destination.val = 0 ∨ destination.val = 1 := by omega
  rcases cases with zero | one
  · simp [two, CFG.Graph.node, zero] at pc
  · simp [two, CFG.Graph.node, one] at pc

#print axioms untaken_preserves_context
#print axioms boundary_taken_je_rejected
#print axioms boundary_taken_jcc_rejected
#print axioms unchanged_dynamic_rank_rejected
#print axioms interior_zero_fuel_rejected
#print axioms missing_destination_rejected
end EDSL.X86.VCGen.BranchControls
#audit_edsl
