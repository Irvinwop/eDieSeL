/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export.Core

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Synthetic source metadata, loaded separately from the trusted snapshot.
The test imports this module for its build dependency only. -/
namespace GeneratedRefinementFixture
universe u

inductive Token where
  | unit

def throughToken (_token : Token) (input : Nat) : Nat := input

theorem oldProof (oldInput : Nat) : oldInput + 0 = oldInput := rfl
theorem aux (auxInput : Nat) : auxInput + 0 = auxInput := oldProof auxInput
theorem later (laterInput : Nat) : laterInput + 0 = laterInput := aux laterInput
theorem root (rootInput : Nat) : rootInput + 0 = rootInput :=
  later (throughToken Token.unit rootInput)

-- This recursive source group stays outside root's original closure. Generated
-- data can require it without granting singleton self-reference permission.
inductive FreshTree where
  | leaf
  | branch (left right : FreshTree)

-- Genuinely fresh polymorphic source support: root has no dependency on it.
-- Generated branches instantiate it at both Nat and Bool.
theorem keepWitness {α : Sort u} (_witness : α) {P : Prop} (h : P) : P := h

-- These valid source helpers isolate forbidden old-suffix dependencies in a
-- type or a body. A generated bridge reaches them transitively.
def proofIndexed (_proof : ∀ n : Nat, n + 0 = n) : Prop := ∀ n : Nat, n + 0 = n
theorem typeForward : proofIndexed later := oldProof
theorem typeForwardBridge : proofIndexed later := typeForward
theorem bodyForward : ∀ n : Nat, n + 0 = n := later
theorem bodyForwardBridge : ∀ n : Nat, n + 0 = n := bodyForward

theorem unrelated : True := True.intro

end GeneratedRefinementFixture
