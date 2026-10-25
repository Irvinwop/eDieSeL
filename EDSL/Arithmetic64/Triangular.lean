/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0

-/
import EDSL.PureCall.Contract
import EDSL.WordMath.Triangular

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Arithmetic64
open X86

/-- Independent row-15 contract. Only the unsigned low32 argument is bound;
RAX is the full64 residue of the natural triangular number. -/
def triangularModulo : PureCall.Spec where
  Input := BitVec 32
  arguments input index := if index.val = 0 then some (.low32 input) else none
  domain _ := True
  result input output := WordMath.TriangularModulo input.toNat output
  useful input := 2 ≤ input.toNat

theorem triangularModulo_bound_iff (input : BitVec 32) (state : State) :
    PureCall.Bound triangularModulo input state ↔ (state.registers .rdi).setWidth 32 = input := by
  constructor
  · intro bound
    exact bound 0 (.low32 input) rfl
  · intro value index argument binding
    simp only [triangularModulo] at binding
    split at binding
    · have zero : index = 0 := Fin.ext (by assumption)
      subst index
      cases binding
      exact value
    · contradiction

theorem triangularModulo_result_exists_unique (input : BitVec 32) :
    ∃ output, triangularModulo.result input output ∧
      ∀ other, triangularModulo.result input other → other = output :=
  WordMath.triangularModulo_exists_unique input.toNat

end EDSL.Arithmetic64

#print axioms EDSL.Arithmetic64.triangularModulo_bound_iff
#print axioms EDSL.Arithmetic64.triangularModulo_result_exists_unique
