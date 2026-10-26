/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.BinarySearch.Clang.NamedELFProperties

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.BinarySearch.Clang.NamedELF
open X86 ELF.FunctionSymbol

/-- Every proper prefix is rejected with the actual original symbol/table/file.
The independent production contract requires the complete declared extent. -/
theorem rejects_truncation (length : Nat) (short : length < input.bytes.length) :
    ({ input with bytes := input.bytes.take length } : ELF.FunctionInput).check file name = false := by
  cases accepted : ({ input with bytes := input.bytes.take length } : ELF.FunctionInput).check
      file name with
  | false => rfl
  | true =>
    rw [ELF.FunctionInput.check_eq_symbol] at accepted
    have size := (checked_mapping accepted).2.1
    change input.function.occurrence.symbol.size = (input.bytes.take length).length at size
    rw [mapping.2.1, List.length_take] at size
    omega

/-- Moving the entry while keeping the original symbol is independently
rejected by the symbol/entry association, before any execution is considered. -/
theorem rejects_displaced_entry (address : Nat)
    (different : address ≠ input.function.window.address) :
    ({ input with function := { input.function with
      window := { input.function.window with address := address } } } : ELF.FunctionInput).check
      file name = false := by
  cases accepted : ({ input with function := { input.function with
      window := { input.function.window with address := address } } } : ELF.FunctionInput).check
      file name with
  | false => rfl
  | true =>
    rw [ELF.FunctionInput.check_eq_symbol] at accepted
    have entry := (checked_mapping accepted).1
    change address = input.function.occurrence.symbol.value at entry
    exact (different (entry.trans mapping.1.symm)).elim

/-- An authentic different static function name cannot select binary search. -/
theorem rejects_linear_search_name :
    input.check file [99,95,108,105,110,101,97,114,95,115,101,97,114,99,104,95,117,51,50] =
      false := by
  cases accepted : input.check file
      [99,95,108,105,110,101,97,114,95,115,101,97,114,99,104,95,117,51,50] with
  | false => rfl
  | true =>
    rw [ELF.FunctionInput.check_eq_symbol] at accepted
    have wrong : input.metadata.matches
        [99,95,108,105,110,101,97,114,95,115,101,97,114,99,104,95,117,51,50] ≠
        [input.function.occurrence] := by decide +kernel
    exact (wrong (checked_sound accepted).2.1.2.2.1).elim

end EDSL.BinarySearch.Clang.NamedELF
