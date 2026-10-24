/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export.ByteLength

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Synthetic client metadata, imported separately from the replay snapshot.
Compile this module before either certificate integration test. -/
namespace PreparedRefinementFixture
open EDSL
universe u

def original : List X86.Byte :=
  [41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,
   58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73]

def file : List X86.Byte := original
def expectedCount : Nat := 33

-- Keep this named proof in the old closure even after aux stops referring to it.
theorem oldLengthProof : file.length = expectedCount := by decide +kernel
theorem aux : file.length = expectedCount := oldLengthProof
theorem later : file.length = expectedCount := aux

theorem poly {α : Sort u} (value : α) : value = value := rfl
theorem root : file.length = expectedCount := Eq.trans (poly file.length) later

-- Fresh helpers are intentionally outside root's original closure. The valid
-- chain reaches only the prefix proof; the two invalid helpers reach later
-- through different declaration fields. Fixed numerals keep these cases
-- separate from the expectedCount inline-preparation test.
theorem freshLengthProof : file.length = 33 := oldLengthProof
theorem freshLengthBridge : file.length = 33 := freshLengthProof
theorem bodyForward : file.length = 33 := later
def indexedLength (_ : file.length = 33) : Prop := file.length = 33
theorem typeForward : indexedLength later := oldLengthProof

-- A monomorphic export root discovers the polymorphic generic helper through
-- its actual client body. Tests use its declarations, never its type as a goal.
theorem helperCarrier (xs ys : List X86.Byte) :
    (xs ++ ys).length = xs.length + ys.length :=
  EDSLGrader.Export.ByteLength.appendLength xs ys xs.length ys.length
    (xs.length + ys.length) rfl rfl rfl

theorem unrelated : True := True.intro

end PreparedRefinementFixture
