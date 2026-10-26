/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.Syntax

set_option autoImplicit false
namespace EDSL.Source.Objects.Control
open StateSyntax

/-! A declaration spine parameterized by its terminal body language. Its typed
initializers and reservation plan are shared by finite statements and internal
loop control. This does not add nested declarations or establish the source
standard's loop mapping or forward-progress requirements. -/

inductive DeclarationSpine (target : Target)
    (Body : List ArithmeticType → IntType → Type) : List ArithmeticType → IntType → Type where
  | declare {context : List ArithmeticType} {result : IntType} (kind : ArithmeticType)
      (initial : Option (RHS target context kind.asIntType))
      (rest : DeclarationSpine target Body (kind :: context) result) :
      DeclarationSpine target Body context result
  | body {context : List ArithmeticType} {result : IntType} (code : Body context result) :
      DeclarationSpine target Body context result

namespace DeclarationSpine
variable {target : Target} {Body : List ArithmeticType → IntType → Type}

@[simp] def localKinds {context : List ArithmeticType} {result : IntType} :
    DeclarationSpine target Body context result → List ArithmeticType
  | .declare kind _ rest => kind :: rest.localKinds
  | .body _ => []

@[simp] def finalContext {context : List ArithmeticType} {result : IntType} :
    DeclarationSpine target Body context result → List ArithmeticType
  | .declare _ _ rest => rest.finalContext
  | .body (context := context) _ => context

theorem finalContext_eq {context : List ArithmeticType} {result : IntType}
    (declarations : DeclarationSpine target Body context result) :
    declarations.finalContext = declarations.localKinds.reverse ++ context := by
  induction declarations <;> simp_all [List.reverse_cons, List.append_assoc]

private def firstSome (first second : Option UnsupportedFeature) : Option UnsupportedFeature :=
  match first with | some feature => some feature | none => second

private theorem firstSome_none (first second : Option UnsupportedFeature) :
    firstSome first second = none ↔ first = none ∧ second = none := by
  cases first <;> simp [firstSome]

@[simp] def firstUnsupported
    (scan : ∀ {context result}, Body context result → Option UnsupportedFeature)
    {context : List ArithmeticType} {result : IntType} :
    DeclarationSpine target Body context result → Option UnsupportedFeature
  | .declare _ initial rest =>
      firstSome (initial.bind Expr.firstUnsupported) (rest.firstUnsupported scan)
  | .body code => scan code

@[simp] def Supported (covered : ∀ {context result}, Body context result → Prop)
    {context : List ArithmeticType} {result : IntType} :
    DeclarationSpine target Body context result → Prop
  | .declare _ initial rest =>
      (match initial with | none => True | some expression => expression.Supported) ∧
        rest.Supported covered
  | .body code => covered code

theorem firstUnsupported_none_iff
    (scan : ∀ {context result}, Body context result → Option UnsupportedFeature)
    (covered : ∀ {context result}, Body context result → Prop)
    (correct : ∀ {context result} (body : Body context result), scan body = none ↔ covered body)
    {context : List ArithmeticType} {result : IntType}
    (declarations : DeclarationSpine target Body context result) :
    declarations.firstUnsupported scan = none ↔ declarations.Supported covered := by
  induction declarations with
  | body code => exact correct code
  | declare kind initial rest ih =>
      cases initial <;> simp_all [firstSome_none, Expr.Supported]

/-- Embed the existing finite declaration syntax, translating only its body. -/
def ofDecls (translate : ∀ {context result}, Stmt target context result → Body context result)
    {context : List ArithmeticType} {result : IntType} :
    Decls target context result → DeclarationSpine target Body context result
  | .declare kind initial rest => .declare kind initial (ofDecls translate rest)
  | .body statement => .body (translate statement)

@[simp] theorem ofDecls_localKinds
    (translate : ∀ {context result}, Stmt target context result → Body context result)
    {context : List ArithmeticType} {result : IntType} (declarations : Decls target context result) :
    (ofDecls translate declarations).localKinds = declarations.localKinds := by
  induction declarations <;> simp_all [ofDecls]

end DeclarationSpine

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
