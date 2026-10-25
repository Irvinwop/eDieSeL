/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export.PackedBytes.Encoding
import EDSL.Grading.Export.ByteLength

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Generic paired length and numeric-encoding composition.

Both child lengths remain hypotheses: numeric equality alone does not
distinguish trailing zero bytes. The result certifies the exact combined count
and the adjacent numeric range, including zero counts and arbitrary words.
There are no environmental assumptions or performance/admission claims.
-/
namespace EDSLGrader.Export.PackedBytes.EncodingFacts

/-- Compose adjacent regions using one conjunction per child. All parameters
are explicit, monomorphic, and in the fixed producer-facing order below. -/
theorem appendFacts (word offset leftCount rightCount : Nat)
    (left right : List (BitVec 8))
    (leftFacts : left.length = leftCount ∧
      PackedBytes.natOfBytes left = Encoding.rangeValue word offset leftCount)
    (rightFacts : right.length = rightCount ∧
      PackedBytes.natOfBytes right =
        Encoding.rangeValue word (offset + leftCount) rightCount) :
    (List.append left right).length = leftCount + rightCount ∧
      PackedBytes.natOfBytes (List.append left right) =
        Encoding.rangeValue word offset (leftCount + rightCount) :=
  And.intro
    (ByteLength.appendLength (α := BitVec 8) left right leftCount rightCount
      (leftCount + rightCount) (And.left leftFacts) (And.left rightFacts)
      (Eq.refl (leftCount + rightCount)))
    (Encoding.encodeAppend word offset leftCount rightCount left right
      (And.left leftFacts) (And.right leftFacts) (And.right rightFacts))

#print axioms appendFacts

end EDSLGrader.Export.PackedBytes.EncodingFacts
