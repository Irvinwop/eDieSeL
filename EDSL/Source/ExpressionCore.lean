/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Operations

set_option autoImplicit false
namespace EDSL.Source.ExpressionCore

/-- Traverse the current Expr grammar with an explicit effect carrier, typed
parameter resolver and scalar Outcome adapter. There are no state, environment,
purity, interference or Monad-law premises. The supplied effects determine
those properties; this definition does not establish them.

Only arithmetic/conversion outcomes and explicit unsupported markers use lift.
Literals, promotions and comparisons use pure, just as evalExpr constructs
defined values. The resolver may itself fail or perform effects. A branch is
traversed only inside the condition's bind continuation, and only when selected.

Binary binds retain the current evaluator's left-first diagnostic priority.
This order is not a C/C++ operand sequencing claim. Static unsupported coverage
must still scan the original expression separately, before public execution. -/
def evalCore {M : Type → Type} [Monad M]
    {target : Target} {parameters : List IntType}
    (policy : IntegerConversionPolicy)
    (lift : {α : Type} → Outcome α → M α)
    (get : {ty : IntType} → Param parameters ty → M (Value target ty)) :
    {ty : IntType} → Expr target parameters ty → M (Value target ty)
  | _, .literal value => pure value
  | _, .param index => get index
  | _, .promote operand => do
      let value ← evalCore policy lift get operand
      pure (IntegerPromotions.promoteValue value)
  | _, .convert destination operand => do
      let value ← evalCore policy lift get operand
      lift (convertValue policy target _ destination value)
  | _, .uadd left right => do
      let x ← evalCore policy lift get left
      let y ← evalCore policy lift get right
      lift (unsignedAdd target x y)
  | _, .sadd left right => do
      let x ← evalCore policy lift get left
      let y ← evalCore policy lift get right
      lift (signedAdd target x y)
  | _, .usub left right => do
      let x ← evalCore policy lift get left
      let y ← evalCore policy lift get right
      lift (unsignedSub target x y)
  | _, .ssub left right => do
      let x ← evalCore policy lift get left
      let y ← evalCore policy lift get right
      lift (signedSub target x y)
  | _, .umul left right => do
      let x ← evalCore policy lift get left
      let y ← evalCore policy lift get right
      lift (unsignedMul target x y)
  | _, .smul left right => do
      let x ← evalCore policy lift get left
      let y ← evalCore policy lift get right
      lift (signedMul target x y)
  | _, .udiv left right => do
      let x ← evalCore policy lift get left
      let y ← evalCore policy lift get right
      lift (unsignedDiv target x y)
  | _, .sdiv left right => do
      let x ← evalCore policy lift get left
      let y ← evalCore policy lift get right
      lift (signedDiv target x y)
  | _, .urem left right => do
      let x ← evalCore policy lift get left
      let y ← evalCore policy lift get right
      lift (unsignedRem target x y)
  | _, .srem left right => do
      let x ← evalCore policy lift get left
      let y ← evalCore policy lift get right
      lift (signedRem target x y)
  | _, .compare operation _ left right => do
      let x ← evalCore policy lift get left
      let y ← evalCore policy lift get right
      pure (compareValues operation x y)
  | _, .select condition onTrue onFalse => do
      let value ← evalCore policy lift get condition
      if value.toInt = 0 then evalCore policy lift get onFalse
      else evalCore policy lift get onTrue
  | _, .unsupported feature => lift (.unsupported feature)

/-- Resolver replacement requires equality of the entire effectful computation,
not just equality of returned values. In a future state carrier this premise
also constrains failures, state updates and events. -/
theorem evalCore_congr_get {M : Type → Type} [Monad M]
    {target : Target} {parameters : List IntType} {ty : IntType}
    (policy : IntegerConversionPolicy)
    (lift : {α : Type} → Outcome α → M α)
    (first second : {kind : IntType} → Param parameters kind → M (Value target kind))
    (same : ∀ {kind : IntType} (index : Param parameters kind), first index = second index)
    (expression : Expr target parameters ty) :
    evalCore policy lift first expression = evalCore policy lift second expression := by
  have resolvers : @first = @second := by
    funext kind index
    exact same index
  cases resolvers
  rfl


/-- The shared traversal commutes with a supplied map preserving pure, bind,
scalar lifting and typed lookup. These are explicit equations on computations;
neither carrier is assumed lawful, state preserving or event free. -/
theorem evalCore_map {M N : Type → Type} [Monad M] [Monad N]
    {target : Target} {parameters : List IntType} {ty : IntType}
    (policy : IntegerConversionPolicy)
    (map : {α : Type} → M α → N α)
    (map_pure : ∀ {α : Type} (value : α), map (pure value) = pure value)
    (map_bind : ∀ {α β : Type} (first : M α) (next : α → M β),
      map (first >>= next) = (map first >>= fun value => map (next value)))
    (liftM : {α : Type} → Outcome α → M α)
    (liftN : {α : Type} → Outcome α → N α)
    (getM : {kind : IntType} → Param parameters kind → M (Value target kind))
    (getN : {kind : IntType} → Param parameters kind → N (Value target kind))
    (map_lift : ∀ {α : Type} (outcome : Outcome α), map (liftM outcome) = liftN outcome)
    (map_get : ∀ {kind : IntType} (index : Param parameters kind),
      map (getM index) = getN index)
    (expression : Expr target parameters ty) :
    map (evalCore policy liftM getM expression) = evalCore policy liftN getN expression := by
  induction expression <;>
    simp_all only [evalCore, apply_ite]



@[instance_reducible] private def outcomeMonad : Monad Outcome where
  pure := Outcome.defined
  bind := Outcome.andThen

attribute [local instance] outcomeMonad

/-- The scalar specialization. Its Monad instance is local to this file and
uses exactly Outcome.andThen, with no assumed Monad laws. -/
def evalOutcome {target : Target} {parameters : List IntType} {ty : IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (expression : Expr target parameters ty) : Outcome (Value target ty) :=
  evalCore policy (fun outcome => outcome) (fun index => .defined (inputs.get index)) expression


end EDSL.Source.ExpressionCore
