/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Operations

set_option autoImplicit false
namespace EDSL.Source.ExpressionCore
open Memory

/-- Supplied computation leaves, not a memory model or a validity proof. The
actual object adapter fixes these to registry operations; the core has no heap.
In particular variable designation is distinct from loading its old contents. -/
structure MemoryOps (target : Target) (M : Type → Type)
    (Handle : ObjectType → Type) (objects : List ObjectType) where
  «variable» : {object : ObjectType} → Index objects object → M (Handle object)
  usePointer : {object : ObjectType} → PointerValue object → M (PointerValue object)
  indirect : {object : ObjectType} → PointerValue object → M (Handle object)
  load : {kind : ScalarType} → Handle (.scalar kind) → M (ScalarValue target kind)
  address : {object : ObjectType} → Handle object → M (PointerValue object)
  decay : {object : ObjectType} → {length : Nat} →
    Handle (.array object length) → M (PointerValue object)
  offset : {object : ObjectType} → {index : IntType} → OffsetOp →
    PointerValue object → Value target index → M (PointerValue object)

/-- The pure fragment needs no invented memory callbacks. -/
def MemoryInterface (target : Target) (M : Type → Type)
    (Handle : ObjectType → Type) (objects : List ObjectType) : Fragment → Type
  | .pureInteger => Unit
  | .object => MemoryOps target M Handle objects

mutual
  /-- One scalar/place traversal. Arithmetic uses the original primitives and
  left-first diagnostic order. Static coverage remains a separate preflight.
  No purity, validity, native operand sequencing or Monad laws are assumed. -/
  def evalEngine {M : Type → Type} [Monad M]
      {target : Target} {inputs : List ScalarType} {objects : List ObjectType}
      {Handle : ObjectType → Type} (policy : IntegerConversionPolicy)
      (lift : {α : Type} → Outcome α → M α)
      (get : {kind : ScalarType} → Index inputs kind → M (ScalarValue target kind)) :
      {fragment : Fragment} → MemoryInterface target M Handle objects fragment →
      {kind : ScalarType} → Engine.Expr target inputs objects fragment kind →
      M (ScalarValue target kind)
    | _, _, _, .literal value => pure value
    | _, _, _, .param index => get index
    | _, memory, _, .promote operand => do
        let value ← evalEngine policy lift get memory operand
        pure (IntegerPromotions.promoteValue value)
    | _, memory, _, .convert destination operand => do
        let value ← evalEngine policy lift get memory operand
        lift (convertValue policy target _ destination value)
    | _, memory, _, .uadd left right => do
        let x ← evalEngine policy lift get memory left
        let y ← evalEngine policy lift get memory right
        lift (unsignedAdd target x y)
    | _, memory, _, .sadd left right => do
        let x ← evalEngine policy lift get memory left
        let y ← evalEngine policy lift get memory right
        lift (signedAdd target x y)
    | _, memory, _, .usub left right => do
        let x ← evalEngine policy lift get memory left
        let y ← evalEngine policy lift get memory right
        lift (unsignedSub target x y)
    | _, memory, _, .ssub left right => do
        let x ← evalEngine policy lift get memory left
        let y ← evalEngine policy lift get memory right
        lift (signedSub target x y)
    | _, memory, _, .umul left right => do
        let x ← evalEngine policy lift get memory left
        let y ← evalEngine policy lift get memory right
        lift (unsignedMul target x y)
    | _, memory, _, .smul left right => do
        let x ← evalEngine policy lift get memory left
        let y ← evalEngine policy lift get memory right
        lift (signedMul target x y)
    | _, memory, _, .udiv left right => do
        let x ← evalEngine policy lift get memory left
        let y ← evalEngine policy lift get memory right
        lift (unsignedDiv target x y)
    | _, memory, _, .sdiv left right => do
        let x ← evalEngine policy lift get memory left
        let y ← evalEngine policy lift get memory right
        lift (signedDiv target x y)
    | _, memory, _, .urem left right => do
        let x ← evalEngine policy lift get memory left
        let y ← evalEngine policy lift get memory right
        lift (unsignedRem target x y)
    | _, memory, _, .srem left right => do
        let x ← evalEngine policy lift get memory left
        let y ← evalEngine policy lift get memory right
        lift (signedRem target x y)
    | _, memory, _, .compare operation _ left right => do
        let x ← evalEngine policy lift get memory left
        let y ← evalEngine policy lift get memory right
        pure (compareValues operation x y)
    | _, memory, _, .select condition onTrue onFalse => do
        let value ← evalEngine policy lift get memory condition
        if Value.toInt (target := target) (ty := .small .boolean) value = 0 then evalEngine policy lift get memory onFalse
        else evalEngine policy lift get memory onTrue
    | _, _, _, .unsupported feature => lift (.unsupported feature)
    | .object, _, _, .null => pure .null
    | .object, memory, _, .load place => do
        let handle ← evalPlace policy lift get memory .designate place
        memory.load handle
    | .object, memory, _, .address place =>
        evalPlace policy lift get memory .address place
    | .object, memory, _, .decay place => do
        let handle ← evalPlace policy lift get memory .designate place
        memory.decay handle
    | .object, memory, _, .offset operation base displacement => do
        let pointer ← evalEngine policy lift get memory base
        let distance ← evalEngine policy lift get memory displacement
        memory.offset operation pointer distance

  /-- Address intent cancels explicit indirection BEFORE designation. It still
  evaluates and interprets the supplied pointer once through usePointer. -/
  def evalPlace {M : Type → Type} [Monad M]
      {target : Target} {inputs : List ScalarType} {objects : List ObjectType}
      {Handle : ObjectType → Type} (policy : IntegerConversionPolicy)
      (lift : {α : Type} → Outcome α → M α)
      (get : {kind : ScalarType} → Index inputs kind → M (ScalarValue target kind))
      (memory : MemoryOps target M Handle objects) :
      (intent : Engine.PlaceIntent) → {object : ObjectType} →
      Engine.Place target inputs objects object → M (Engine.PlaceResult Handle intent object)
    | .designate, _, .variable index => memory.variable index
    | .address, _, .variable index => do
        let handle ← memory.variable index
        memory.address handle
    | .designate, _, .indirect expression => do
        let pointer ← evalEngine (fragment := .object) policy lift get memory expression
        memory.indirect pointer
    | .address, _, .indirect expression => do
        let pointer ← evalEngine (fragment := .object) policy lift get memory expression
        memory.usePointer pointer
    | .designate, _, .unsupported feature => lift (.unsupported feature)
    | .address, _, .unsupported feature => lift (.unsupported feature)
end

/-- Lift old typed integer lookup into the mapped scalar-input family. -/
def integerResolver {M : Type → Type} {target : Target} :
    {parameters : List IntType} →
    ({kind : IntType} → Param parameters kind → M (Value target kind)) →
    {kind : ScalarType} → Index (parameters.map ScalarType.integer) kind →
    M (ScalarValue target kind)
  | [], _, _, index => nomatch index
  | _ :: _, get, _, .here => get .here
  | _ :: _, get, _, .there index => integerResolver (fun index => get (.there index)) index

@[simp] theorem integerResolver_index {M : Type → Type} {target : Target}
    {parameters : List IntType} {kind : IntType}
    (get : {kind : IntType} → Param parameters kind → M (Value target kind))
    (index : Index (parameters.map ScalarType.integer) (.integer kind)) :
    integerResolver get index = get (Param.ofIndex index) := by
  induction parameters with
  | nil => cases index
  | cons head tail ih =>
      cases index with
      | here => rfl
      | there index => exact ih (fun index => get (.there index)) index

/-- Compatibility wrapper: pure expressions use Unit, never memory callbacks. -/
def evalCore {M : Type → Type} [Monad M]
    {target : Target} {parameters : List IntType}
    (policy : IntegerConversionPolicy)
    (lift : {α : Type} → Outcome α → M α)
    (get : {ty : IntType} → Param parameters ty → M (Value target ty))
    {ty : IntType} (expression : Expr target parameters ty) : M (Value target ty) :=
  evalEngine (Handle := fun _ => Unit) (objects := []) (fragment := .pureInteger) policy lift (integerResolver get) () expression

@[instance_reducible] private def outcomeMonad : Monad Outcome where
  pure := Outcome.defined
  bind := Outcome.andThen

attribute [local instance] outcomeMonad

def evalOutcome {target : Target} {parameters : List IntType} {ty : IntType}
    (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
    (expression : Expr target parameters ty) : Outcome (Value target ty) :=
  evalCore policy (fun outcome => outcome) (fun index => .defined (inputs.get index)) expression


/-- Map every supplied memory computation, retaining the same typed handles. -/
def MemoryOps.map {target : Target} {M N : Type → Type}
    {Handle : ObjectType → Type} {objects : List ObjectType}
    (map : {α : Type} → M α → N α) (memory : MemoryOps target M Handle objects) :
    MemoryOps target N Handle objects where
  «variable» := fun index => map (memory.variable index)
  usePointer := fun pointer => map (memory.usePointer pointer)
  indirect := fun pointer => map (memory.indirect pointer)
  load := fun handle => map (memory.load handle)
  address := fun handle => map (memory.address handle)
  decay := fun handle => map (memory.decay handle)
  offset := fun operation pointer distance => map (memory.offset operation pointer distance)

def mapMemory {target : Target} {M N : Type → Type}
    {Handle : ObjectType → Type} {objects : List ObjectType}
    (map : {α : Type} → M α → N α) :
    {fragment : Fragment} → MemoryInterface target M Handle objects fragment →
      MemoryInterface target N Handle objects fragment
  | .pureInteger, _ => ()
  | .object, memory => memory.map map

private theorem map_bind_congr {M N : Type → Type} [Monad M] [Monad N]
    (map : {α : Type} → M α → N α)
    (map_bind : ∀ {α β : Type} (first : M α) (next : α → M β),
      map (first >>= next) = (map first >>= fun value => map (next value)))
    {α β : Type} {firstM : M α} {firstN : N α}
    {nextM : α → M β} {nextN : α → N β}
    (first_eq : map firstM = firstN)
    (next_eq : ∀ value, map (nextM value) = nextN value) :
    map (firstM >>= nextM) = (firstN >>= nextN) := by
  rw [map_bind, first_eq]
  exact congrArg (fun next => firstN >>= next) (funext next_eq)

/-- Computation equality for the complete mutual traversal. The place induction
motive quantifies over intent, so address cancellation is preserved as well as
ordinary designation. Map laws constrain full computations, not returned values. -/
theorem evalEngine_map {M N : Type → Type} [Monad M] [Monad N]
    {target : Target} {inputs : List ScalarType} {objects : List ObjectType}
    {Handle : ObjectType → Type} {fragment : Fragment} {kind : ScalarType}
    (policy : IntegerConversionPolicy)
    (map : {α : Type} → M α → N α)
    (map_pure : ∀ {α : Type} (value : α), map (pure value) = pure value)
    (map_bind : ∀ {α β : Type} (first : M α) (next : α → M β),
      map (first >>= next) = (map first >>= fun value => map (next value)))
    (liftM : {α : Type} → Outcome α → M α)
    (liftN : {α : Type} → Outcome α → N α)
    (getM : {kind : ScalarType} → Index inputs kind → M (ScalarValue target kind))
    (getN : {kind : ScalarType} → Index inputs kind → N (ScalarValue target kind))
    (map_lift : ∀ {α : Type} (outcome : Outcome α), map (liftM outcome) = liftN outcome)
    (map_get : ∀ {kind : ScalarType} (index : Index inputs kind), map (getM index) = getN index)
    (expression : Engine.Expr target inputs objects fragment kind)
    (memory : MemoryInterface target M Handle objects fragment) :
    map (evalEngine policy liftM getM memory expression) =
      evalEngine policy liftN getN (mapMemory map memory) expression := by
  induction expression using Engine.Expr.rec
      (motive_2 := fun object place => ∀ (intent : Engine.PlaceIntent)
        (memory : MemoryOps target M Handle objects),
        map (evalPlace policy liftM getM memory intent place) =
          evalPlace policy liftN getN (memory.map map) intent place)
  all_goals (intros)
  case «variable» =>
    rename_i intent memory
    cases intent
    · rfl
    · exact map_bind _ _
  case indirect =>
    rename_i expression ih intent memory
    cases intent <;>
      exact map_bind_congr map map_bind (ih memory) (fun _ => rfl)
  case unsupported => exact map_lift _
  case unsupported =>
    rename_i intent memory
    cases intent <;> exact map_lift _
  all_goals (
    simp only [evalEngine]
    repeat' first
    | exact map_pure _
    | exact map_lift _
    | exact map_get _
    | rfl
    | assumption
    | apply_assumption
    | apply map_bind_congr map map_bind
    | funext value
    | intro value
    | split)


/-- Export the place half of the joint computation transport. -/
theorem evalPlace_map {M N : Type → Type} [Monad M] [Monad N]
    {target : Target} {inputs : List ScalarType} {objects : List ObjectType}
    {Handle : ObjectType → Type} {object : ObjectType}
    (policy : IntegerConversionPolicy)
    (map : {α : Type} → M α → N α)
    (map_pure : ∀ {α : Type} (value : α), map (pure value) = pure value)
    (map_bind : ∀ {α β : Type} (first : M α) (next : α → M β),
      map (first >>= next) = (map first >>= fun value => map (next value)))
    (liftM : {α : Type} → Outcome α → M α)
    (liftN : {α : Type} → Outcome α → N α)
    (getM : {kind : ScalarType} → Index inputs kind → M (ScalarValue target kind))
    (getN : {kind : ScalarType} → Index inputs kind → N (ScalarValue target kind))
    (map_lift : ∀ {α : Type} (outcome : Outcome α), map (liftM outcome) = liftN outcome)
    (map_get : ∀ {kind : ScalarType} (index : Index inputs kind), map (getM index) = getN index)
    (place : Engine.Place target inputs objects object)
    (intent : Engine.PlaceIntent) (memory : MemoryOps target M Handle objects) :
    map (evalPlace policy liftM getM memory intent place) =
      evalPlace policy liftN getN (memory.map map) intent place := by
  cases place with
  | «variable» index =>
      cases intent
      · rfl
      · exact map_bind _ _
  | indirect expression =>
      cases intent <;> exact map_bind_congr map map_bind
        (evalEngine_map policy map map_pure map_bind liftM liftN getM getN
          map_lift map_get expression memory) (fun _ => rfl)
  | unsupported feature =>
      cases intent <;> exact map_lift _

/-- Resolver replacement constrains complete computations, as before. -/
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

private theorem integerResolver_map {M N : Type → Type} {target : Target}
    {parameters : List IntType}
    (map : {α : Type} → M α → N α)
    (getM : {kind : IntType} → Param parameters kind → M (Value target kind))
    (getN : {kind : IntType} → Param parameters kind → N (Value target kind))
    (map_get : ∀ {kind : IntType} (index : Param parameters kind), map (getM index) = getN index)
    {kind : ScalarType} (index : Index (parameters.map ScalarType.integer) kind) :
    map (integerResolver getM index) = integerResolver getN index := by
  induction parameters with
  | nil => cases index
  | cons head tail ih =>
      cases index with
      | here => exact map_get .here
      | there index =>
          exact ih (fun index => getM (.there index)) (fun index => getN (.there index))
            (fun index => map_get (.there index)) index

/-- Original pure carrier-map API, now a specialization of the joint theorem.
There is no independent arithmetic induction or second evaluator. -/
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
    (map_get : ∀ {kind : IntType} (index : Param parameters kind), map (getM index) = getN index)
    (expression : Expr target parameters ty) :
    map (evalCore policy liftM getM expression) = evalCore policy liftN getN expression := by
  exact evalEngine_map (Handle := fun _ => Unit) policy (@map) map_pure map_bind
    (@liftM) (@liftN) (@integerResolver M target parameters (@getM))
    (@integerResolver N target parameters (@getN)) (@map_lift)
    (fun {kind} index =>
      @integerResolver_map M N target parameters (@map) (@getM) (@getN) (@map_get) kind index)
    expression ()

end EDSL.Source.ExpressionCore
