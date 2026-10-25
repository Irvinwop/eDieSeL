/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionInput

set_option autoImplicit false
set_option warningAsError true

/-! Data-only selection from arbitrary ELF hints. Neither a bounded row nor
this packaging authenticates a symbol, its name, extent, mapping or bytes.
The complete file and requested name remain inputs to `FunctionInput.check`.
-/

namespace EDSL.ELF.FunctionSelection
open X86 FunctionSymbol

/-- Select a row and suggest its section-relative window. Subtraction is the
same natural subtraction used by the production contract; invalid hints still
have to pass every independent checker obligation. -/
def function (symbols : Symbols) (textSection : Section)
    (index : Fin symbols.rows.length) : Function :=
  let symbol := symbols.rows[index]
  { occurrence := ⟨symbols.sectionIndex, index.val, symbol⟩
    sh := textSection
    window := ⟨symbol.value, textSection.offset + (symbol.value - textSection.address)⟩ }

/-- Package untrusted table, metadata, row, section and byte hints. -/
def input (table : FunctionWindow.Table) (metadata : Metadata)
    (symbols : Symbols) (textSection : Section) (index : Fin symbols.rows.length)
    (bytes : List Byte) : FunctionInput :=
  { table := table
    metadata := metadata
    function := function symbols textSection index
    bytes := bytes }

end EDSL.ELF.FunctionSelection
