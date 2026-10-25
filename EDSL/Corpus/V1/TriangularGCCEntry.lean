/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.TriangularGCCEntryZero
import EDSL.Corpus.V1.TriangularGCCEntryEven
import EDSL.Corpus.V1.TriangularGCCEntryOne
import EDSL.Corpus.V1.TriangularGCCEntryOdd

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.Corpus.V1.TriangularGCCBase
open X86 X86.Sequential X86.VCGen
open TriangularGCCGraph

/-- Constructed universal EntryBlockVC; no new input admission premises. -/
theorem entryBlock : EntryBlockVC := by
  intro input initial pre
  by_cases zero : (initial.registers .rdi).setWidth 32 = 0#32
  · exact entryZero input initial pre zero
  · by_cases even : input.value.toNat % 2 = 0
    · exact entryEven input initial pre zero even
    · have odd : input.value.toNat % 2 = 1 := by omega
      by_cases one : input.value.toNat = 1
      · exact entryOne input initial pre zero odd one
      · exact entryOdd input initial pre zero odd one

end EDSL.Corpus.V1.TriangularGCCBase

#print axioms EDSL.Corpus.V1.TriangularGCCBase.entryBlock
