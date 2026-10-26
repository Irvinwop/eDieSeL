/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Declarations
import EDSL.Source.Objects.StateEval

set_option autoImplicit false
namespace EDSL.Source.Objects.Control
open StateSyntax

/-! One initializer traversal shared by finite statements and function control.
The caller reserves the complete local plan before invoking this fold. Only the
terminal body interpreter varies; expression evaluation and initialization use
the existing object operations, retaining their exact errors, state and events. -/

namespace DeclarationSpine
variable {target : Target} {Body : List ArithmeticType → IntType → Type}
variable {parameters : List IntType} {Environment α : Type}

/-- A generic initializer traversal for a terminal body language/interpreter.
Its plan contains the complete already reserved declaration prefix; the active
bindings grow only after actual initialization of the next object. -/
def fold (dialect : Dialect) (policy : IntegerConversionPolicy) {result : IntType}
    (onBody : ∀ {context}, Body context result → Env context →
      Op target parameters Environment α) :
    {context : List ArithmeticType} →
    (declarations : DeclarationSpine target Body context result) → Env context →
    Env declarations.localKinds → Op target parameters Environment α
  | _, .body code, bindings, _ => onBody code bindings
  | _, .declare _ initial rest, bindings, plan =>
    match plan with
    | .cons reference tail =>
      let initialValue := match initial with
        | none => Op.pure none
        | some expression => Op.bind (StateEval.evalExpr dialect policy bindings expression)
            fun value => Op.pure (some value)
      Op.bind initialValue fun value =>
      Op.bind («initialize» dialect reference value) fun _ =>
        fold dialect policy onBody rest (bindings.extend reference) tail

end DeclarationSpine
end EDSL.Source.Objects.Control
