/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.StateSyntax

set_option autoImplicit false
namespace EDSL.Source.Objects.Control
open StateSyntax

/-- Control over already-bound full-int objects. Loops carry no execution fuel,
rank or invariant. Return exits all enclosing control; skip permits fallthrough.
Declarations/scopes, break/continue, calls and native sequencing are separate. -/
inductive Code (target : Target) (context : List ArithmeticType) (result : IntType) where
  | skip
  | assign {kind : ArithmeticType} (index : Vars context kind)
      (value : RHS target context kind.asIntType)
  | seq (first next : Code target context result)
  | branch (condition : RHS target context (.small .boolean))
      (yes no : Code target context result)
  | loop (condition : RHS target context (.small .boolean))
      (body : Code target context result)
  | ret (value : RHS target context result)
  | unsupported (feature : UnsupportedFeature)

namespace Code
private def firstSome (first second : Option UnsupportedFeature) : Option UnsupportedFeature :=
  match first with | some feature => some feature | none => second

private theorem firstSome_none (first second : Option UnsupportedFeature) :
    firstSome first second = none ↔ first = none ∧ second = none := by
  cases first <;> simp [firstSome]

/-- Static coverage visits both branches and the loop body even if execution
would skip them. Only the first diagnostic in syntax order is returned. -/
@[simp] def firstUnsupported {target : Target} {context : List ArithmeticType} {result : IntType} :
    Code target context result → Option UnsupportedFeature
  | .skip => none
  | .assign _ value => value.firstUnsupported
  | .seq first next => firstSome first.firstUnsupported next.firstUnsupported
  | .branch condition yes no =>
      firstSome condition.firstUnsupported (firstSome yes.firstUnsupported no.firstUnsupported)
  | .loop condition body => firstSome condition.firstUnsupported body.firstUnsupported
  | .ret value => value.firstUnsupported
  | .unsupported feature => some feature

@[simp] def Supported {target : Target} {context : List ArithmeticType} {result : IntType} :
    Code target context result → Prop
  | .skip => True
  | .assign _ value => value.Supported
  | .seq first next => first.Supported ∧ next.Supported
  | .branch condition yes no => condition.Supported ∧ yes.Supported ∧ no.Supported
  | .loop condition body => condition.Supported ∧ body.Supported
  | .ret value => value.Supported
  | .unsupported _ => False

theorem firstUnsupported_none_iff {target : Target} {context : List ArithmeticType}
    {result : IntType} (code : Code target context result) :
    code.firstUnsupported = none ↔ code.Supported := by
  induction code <;> simp_all [firstSome_none, Expr.Supported]

/-- Embed the existing finite source syntax without inventing variables,
allocations, values or a second expression evaluator. -/
def ofStmt {target : Target} {context : List ArithmeticType} {result : IntType} :
    Stmt target context result → Code target context result
  | .set index value next => .seq (.assign index value) (ofStmt next)
  | .branch condition yes no => .branch condition (ofStmt yes) (ofStmt no)
  | .ret value => .ret value
  | .unsupported feature => .unsupported feature

theorem ofStmt_supported {target : Target} {context : List ArithmeticType}
    {result : IntType} (statement : Stmt target context result) :
    (ofStmt statement).Supported ↔ statement.Supported := by
  induction statement <;> simp_all [ofStmt]

end Code
end EDSL.Source.Objects.Control
