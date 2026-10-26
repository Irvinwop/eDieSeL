/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Syntax

set_option autoImplicit false

namespace EDSL.Source
open Memory

namespace Expr

/-- Pure proof induction with the old integer and Param indices. This is an
explicit compatibility eliminator, not the old generated Expr.rec/recOn API. -/
@[elab_as_elim] theorem inductionOn {target : Target} {parameters : List IntType}
    {motive : {ty : IntType} → Expr target parameters ty → Prop}
    {ty : IntType} (expression : Expr target parameters ty)
    (literal : ∀ {ty : IntType} (value : Value target ty), motive (Expr.literal value))
    (param : ∀ {ty : IntType} (index : Param parameters ty), motive (Expr.param index))
    (convert : ∀ (destination : IntType) {source : IntType}
      (operand : Expr target parameters source), motive operand → motive (Expr.convert destination operand))
    (promote : ∀ {source : IntType} (operand : Expr target parameters source),
      motive operand → motive (Expr.promote operand))
    (uadd : ∀ (left right : Expr target parameters .uint),
      motive left → motive right → motive (Expr.uadd left right))
    (sadd : ∀ (left right : Expr target parameters .sint),
      motive left → motive right → motive (Expr.sadd left right))
    (usub : ∀ (left right : Expr target parameters .uint),
      motive left → motive right → motive (Expr.usub left right))
    (ssub : ∀ (left right : Expr target parameters .sint),
      motive left → motive right → motive (Expr.ssub left right))
    (umul : ∀ (left right : Expr target parameters .uint),
      motive left → motive right → motive (Expr.umul left right))
    (smul : ∀ (left right : Expr target parameters .sint),
      motive left → motive right → motive (Expr.smul left right))
    (udiv : ∀ (left right : Expr target parameters .uint),
      motive left → motive right → motive (Expr.udiv left right))
    (sdiv : ∀ (left right : Expr target parameters .sint),
      motive left → motive right → motive (Expr.sdiv left right))
    (urem : ∀ (left right : Expr target parameters .uint),
      motive left → motive right → motive (Expr.urem left right))
    (srem : ∀ (left right : Expr target parameters .sint),
      motive left → motive right → motive (Expr.srem left right))
    (compare : ∀ (operation : ComparisonOp) (kind : ArithmeticType)
      (left right : Expr target parameters kind.asIntType),
      motive left → motive right → motive (Expr.compare operation kind left right))
    (select : ∀ {ty : IntType} (condition : Expr target parameters (.small .boolean))
      (onTrue onFalse : Expr target parameters ty),
      motive condition → motive onTrue → motive onFalse → motive (Expr.select condition onTrue onFalse))
    (unsupported : ∀ {ty : IntType} (feature : UnsupportedFeature),
      motive (Expr.unsupported (ty := ty) feature)) : motive expression :=
  match expression with
  | Engine.Expr.literal value => literal value
  | Engine.Expr.param index => by
      simpa only [Expr.param, Param.toIndex_ofIndex] using param (Param.ofIndex index)
  | Engine.Expr.convert destination operand => convert destination operand (inductionOn operand literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported)
  | Engine.Expr.promote operand => promote operand (inductionOn operand literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported)
  | Engine.Expr.uadd left right => uadd left right (inductionOn left literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported) (inductionOn right literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported)
  | Engine.Expr.sadd left right => sadd left right (inductionOn left literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported) (inductionOn right literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported)
  | Engine.Expr.usub left right => usub left right (inductionOn left literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported) (inductionOn right literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported)
  | Engine.Expr.ssub left right => ssub left right (inductionOn left literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported) (inductionOn right literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported)
  | Engine.Expr.umul left right => umul left right (inductionOn left literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported) (inductionOn right literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported)
  | Engine.Expr.smul left right => smul left right (inductionOn left literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported) (inductionOn right literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported)
  | Engine.Expr.udiv left right => udiv left right (inductionOn left literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported) (inductionOn right literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported)
  | Engine.Expr.sdiv left right => sdiv left right (inductionOn left literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported) (inductionOn right literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported)
  | Engine.Expr.urem left right => urem left right (inductionOn left literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported) (inductionOn right literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported)
  | Engine.Expr.srem left right => srem left right (inductionOn left literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported) (inductionOn right literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported)
  | Engine.Expr.compare operation kind left right =>
      compare operation kind left right (inductionOn left literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported) (inductionOn right literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported)
  | Engine.Expr.select condition onTrue onFalse =>
      select condition onTrue onFalse (inductionOn condition literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported) (inductionOn onTrue literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported) (inductionOn onFalse literal param convert promote uadd sadd usub ssub umul smul udiv sdiv urem srem compare select unsupported)
  | Engine.Expr.unsupported feature => unsupported feature

end Expr

namespace Engine

/-- Constructor-preserving embedding; no inputs are evaluated or object loads
inserted. A mutable-variable embedding must instead build load(variable ...). -/
def Expr.embedPure {target : Target} {inputs : List ScalarType}
    {sourceObjects destinationObjects : List ObjectType} :
    {ty : ScalarType} → Expr target inputs sourceObjects .pureInteger ty →
      Expr target inputs destinationObjects .object ty
  | _, .literal value => .literal value
  | _, .param index => .param index
  | _, .convert destination operand => .convert destination (embedPure operand)
  | _, .promote operand => .promote (embedPure operand)
  | _, .uadd left right => .uadd (embedPure left) (embedPure right)
  | _, .sadd left right => .sadd (embedPure left) (embedPure right)
  | _, .usub left right => .usub (embedPure left) (embedPure right)
  | _, .ssub left right => .ssub (embedPure left) (embedPure right)
  | _, .umul left right => .umul (embedPure left) (embedPure right)
  | _, .smul left right => .smul (embedPure left) (embedPure right)
  | _, .udiv left right => .udiv (embedPure left) (embedPure right)
  | _, .sdiv left right => .sdiv (embedPure left) (embedPure right)
  | _, .urem left right => .urem (embedPure left) (embedPure right)
  | _, .srem left right => .srem (embedPure left) (embedPure right)
  | _, .compare operation kind left right => .compare operation kind (embedPure left) (embedPure right)
  | _, .select condition onTrue onFalse => .select (embedPure condition) (embedPure onTrue) (embedPure onFalse)
  | _, .unsupported feature => .unsupported feature

theorem Expr.embedPure_firstUnsupported {target : Target} {dialect : Dialect}
    {inputs : List ScalarType} {sourceObjects destinationObjects : List ObjectType}
    (profile : SyntaxProfile target dialect) {ty : ScalarType}
    (expression : Expr target inputs sourceObjects .pureInteger ty) :
    (Expr.embedPure (destinationObjects := destinationObjects) expression).firstUnsupported profile =
      expression.firstUnsupported profile :=
  match expression with
  | .literal _ => by simp only [embedPure, firstUnsupported]
  | .param _ => by simp only [embedPure, firstUnsupported]
  | .convert _ operand => by
      simp only [embedPure, firstUnsupported, embedPure_firstUnsupported profile operand]
  | .promote operand => by
      simp only [embedPure, firstUnsupported, embedPure_firstUnsupported profile operand]
  | .uadd left right => by
      simp only [embedPure, firstUnsupported, embedPure_firstUnsupported profile left,
        embedPure_firstUnsupported profile right]
  | .sadd left right => by
      simp only [embedPure, firstUnsupported, embedPure_firstUnsupported profile left,
        embedPure_firstUnsupported profile right]
  | .usub left right => by
      simp only [embedPure, firstUnsupported, embedPure_firstUnsupported profile left,
        embedPure_firstUnsupported profile right]
  | .ssub left right => by
      simp only [embedPure, firstUnsupported, embedPure_firstUnsupported profile left,
        embedPure_firstUnsupported profile right]
  | .umul left right => by
      simp only [embedPure, firstUnsupported, embedPure_firstUnsupported profile left,
        embedPure_firstUnsupported profile right]
  | .smul left right => by
      simp only [embedPure, firstUnsupported, embedPure_firstUnsupported profile left,
        embedPure_firstUnsupported profile right]
  | .udiv left right => by
      simp only [embedPure, firstUnsupported, embedPure_firstUnsupported profile left,
        embedPure_firstUnsupported profile right]
  | .sdiv left right => by
      simp only [embedPure, firstUnsupported, embedPure_firstUnsupported profile left,
        embedPure_firstUnsupported profile right]
  | .urem left right => by
      simp only [embedPure, firstUnsupported, embedPure_firstUnsupported profile left,
        embedPure_firstUnsupported profile right]
  | .srem left right => by
      simp only [embedPure, firstUnsupported, embedPure_firstUnsupported profile left,
        embedPure_firstUnsupported profile right]
  | .compare _ _ left right => by
      simp only [embedPure, firstUnsupported, embedPure_firstUnsupported profile left,
        embedPure_firstUnsupported profile right]
  | .select condition onTrue onFalse => by
      simp only [embedPure, firstUnsupported, embedPure_firstUnsupported profile condition,
        embedPure_firstUnsupported profile onTrue, embedPure_firstUnsupported profile onFalse]
  | .unsupported _ => by simp only [embedPure, firstUnsupported]

end Engine

def Expr.toObject {target : Target} {parameters : List IntType} {objects : List ObjectType}
    {ty : IntType} (expression : Expr target parameters ty) :
    Engine.Expr target (parameters.map ScalarType.integer) objects .object (.integer ty) :=
  Engine.Expr.embedPure expression

end EDSL.Source
