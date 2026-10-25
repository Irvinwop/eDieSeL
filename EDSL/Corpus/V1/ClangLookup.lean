/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.Clang

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

namespace EDSL.Corpus.V1.ClangLookup
open X86

/-- Shared bounded lookup in the complete original Clang file, including
absence outside the file. This normalizes reads without importing arithmetic
clients or establishing acceptance of any selected function. -/
theorem fileByte (offset : Nat) :
    Clang.file[offset]? = if offset < 44240 then
      (((Clang.chunks.drop (offset / 128)).flatten).drop (offset % 128))[0]? else none := by
  by_cases inside : offset < 44240
  · rw [ite_eq_left inside]
    have dropped := congrArg (fun source : List Byte => source[0]?)
      (Clang.fileDropAt offset (by omega))
    simpa only [List.getElem?_drop, Nat.add_zero] using dropped
  · rw [ite_eq_right inside]
    exact List.getElem?_eq_none (by rw [Clang.fileLength]; omega)

end EDSL.Corpus.V1.ClangLookup
