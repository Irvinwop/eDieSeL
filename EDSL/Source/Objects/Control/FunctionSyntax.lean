/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.Syntax
import EDSL.Source.Objects.Declarations

set_option autoImplicit false
namespace EDSL.Source.Objects.Control
open StateSyntax

/-! Functions specialize the neutral declaration prefix to internal control.
This does not add nested declarations or establish the source standard's loop
mapping or forward-progress requirements. -/

abbrev FunctionDeclarations (target : Target) := DeclarationSpine target (Code target)

/-- An internal function with one finite declaration prefix and a control body.
Its Code.loop nodes need a separate source-standard mapping/progress proof. -/
structure Function (target : Target) (parameters : List ArithmeticType) (result : IntType) where
  dialect : Dialect
  conversions : IntegerConversionPolicy
  body : FunctionDeclarations target parameters result

namespace Function
variable {target : Target} {parameters : List ArithmeticType} {result : IntType}

def firstUnsupported (function : Function target parameters result) : Option UnsupportedFeature :=
  function.body.firstUnsupported Code.firstUnsupported

def Supported (function : Function target parameters result) : Prop :=
  function.body.Supported Code.Supported

theorem firstUnsupported_none_iff (function : Function target parameters result) :
    function.firstUnsupported = none ↔ function.Supported :=
  function.body.firstUnsupported_none_iff Code.firstUnsupported Code.Supported
    Code.firstUnsupported_none_iff

/-- Declaration types and initializers are kept exactly; only finite statements
are embedded into internal control. No frontend/native correspondence is claimed. -/
def ofProgram (program : StateSyntax.Program target parameters result) :
    Function target parameters result :=
  ⟨program.dialect, program.conversions, DeclarationSpine.ofDecls Code.ofStmt program.body⟩

@[simp] theorem ofProgram_localKinds (program : StateSyntax.Program target parameters result) :
    (ofProgram program).body.localKinds = program.body.localKinds :=
  DeclarationSpine.ofDecls_localKinds Code.ofStmt program.body

end Function
end EDSL.Source.Objects.Control
