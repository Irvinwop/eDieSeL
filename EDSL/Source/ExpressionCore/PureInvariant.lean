/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.ExpressionCore
import EDSL.Source.Syntax.Properties

set_option autoImplicit false
namespace EDSL.Source.ExpressionCore

/-- A relation on complete computations transports through exactly the guarded
legacy integer fragment. The bind obligation compares continuations at the same
returned value. No Monad laws or successful-run/coverage premises are assumed.
This is proof induction over the shared evaluator, not another interpreter. -/
theorem evalCore_rel {M N : Type → Type} [Monad M] [Monad N]
    {target : Target} {parameters : List IntType} {ty : IntType}
    (relation : {α : Type} → M α → N α → Prop)
    (pure_relation : ∀ {α : Type} (value : α), relation (pure value) (pure value))
    (bind_relation : ∀ {α β : Type} (firstM : M α) (firstN : N α)
      (nextM : α → M β) (nextN : α → N β),
      relation firstM firstN → (∀ value, relation (nextM value) (nextN value)) →
      relation (firstM >>= nextM) (firstN >>= nextN))
    (policy : IntegerConversionPolicy)
    (liftM : {α : Type} → Outcome α → M α)
    (liftN : {α : Type} → Outcome α → N α)
    (getM : {kind : IntType} → Param parameters kind → M (Value target kind))
    (getN : {kind : IntType} → Param parameters kind → N (Value target kind))
    (lift_relation : ∀ {α : Type} (outcome : Outcome α), relation (liftM outcome) (liftN outcome))
    (get_relation : ∀ {kind : IntType} (index : Param parameters kind),
      relation (getM index) (getN index))
    (expression : Expr target parameters ty) :
    relation (evalCore policy liftM getM expression) (evalCore policy liftN getN expression) := by
  induction expression using Expr.inductionOn <;>
    simp only [evalCore, evalEngine, integerResolver_index, Param.ofIndex_toIndex]
  all_goals repeat' first
    | assumption
    | apply pure_relation
    | apply lift_relation
    | apply get_relation
    | apply bind_relation
    | split
    | intro value

/-- Properties observe the full computation, including errors, state and events.
The supplied closure obligations cover all raw outcomes and resolver calls. -/
theorem evalCore_property {M : Type → Type} [Monad M]
    {target : Target} {parameters : List IntType} {ty : IntType}
    (property : {α : Type} → M α → Prop)
    (pure_property : ∀ {α : Type} (value : α), property (pure value))
    (bind_property : ∀ {α β : Type} (first : M α) (next : α → M β),
      property first → (∀ value, property (next value)) → property (first >>= next))
    (policy : IntegerConversionPolicy)
    (lift : {α : Type} → Outcome α → M α)
    (get : {kind : IntType} → Param parameters kind → M (Value target kind))
    (lift_property : ∀ {α : Type} (outcome : Outcome α), property (lift outcome))
    (get_property : ∀ {kind : IntType} (index : Param parameters kind), property (get index))
    (expression : Expr target parameters ty) :
    property (evalCore policy lift get expression) := by
  exact evalCore_rel (N := M) (fun first _ => property first) pure_property
    (fun firstM _ nextM _ firstProof nextProof => bind_property firstM nextM firstProof nextProof)
    policy lift lift get get lift_property get_property expression

end EDSL.Source.ExpressionCore
