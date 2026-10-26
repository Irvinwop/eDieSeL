/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Model

set_option autoImplicit false

namespace EDSL.Source.Objects.StateSyntax

/-! Typed syntax and binding infrastructure. Execution and certificates are
defined separately. Every variable, including a formal parameter, denotes an
object; the shared Expr grammar supplies all scalar RHS types and operations.
An executor must resolve Expr.param through object loads, never State.inputs.

The block has a declaration prefix followed by finite set/branch/return syntax.
There are no self/forward initializers, nested scopes, loops, assignment
expressions, qualifiers, bytes, pointers, frontend or OS correspondence.
All declarations must be reserved before evaluating any initializer. This file
describes bindings and syntax, without prescribing allocation at a declaration.
-/

abbrev VariableTypes (context : List ArithmeticType) : List IntType :=
  context.map ArithmeticType.asIntType

abbrev Vars (context : List ArithmeticType) (kind : ArithmeticType) :=
  Param (VariableTypes context) kind.asIntType

abbrev RHS (target : Target) (context : List ArithmeticType) (type : IntType) :=
  Expr target (VariableTypes context) type

/-- External call values, distinct from the mutable formal parameter objects. -/
abbrev CallInputs (target : Target) (parameters : List ArithmeticType) :=
  Inputs target (VariableTypes parameters)

private def position {types : List IntType} {type : IntType} : Param types type → Nat
  | .here => 0
  | .there index => position index + 1

private theorem position_lt {types : List IntType} {type : IntType}
    (index : Param types type) : position index < types.length := by
  induction index with
  | here => simp [position]
  | there index ih => simpa only [position, List.length_cons] using Nat.succ_lt_succ ih

private theorem position_injective {types : List IntType} {type : IntType}
    (first second : Param types type) (same : position first = position second) :
    first = second := by
  induction first with
  | here => cases second <;> simp_all [position]
  | there first ih =>
      cases second with
      | here => simp [position] at same
      | there second => exact congrArg Param.there (ih second (Nat.succ.inj same))

namespace Vars

/-- De Bruijn position; newer locals precede all earlier locals and parameters. -/
abbrev slot {context : List ArithmeticType} {kind : ArithmeticType}
    (index : Vars context kind) : Nat := position index

theorem slot_lt {context : List ArithmeticType} {kind : ArithmeticType}
    (index : Vars context kind) : slot index < context.length := by
  simpa only [List.length_map] using position_lt index

theorem slot_injective {context : List ArithmeticType} {kind : ArithmeticType}
    (first second : Vars context kind) (same : slot first = slot second) : first = second :=
  position_injective first second same

end Vars

/-- Every possible Expr.param in an object context has a full object kind.
In particular no small-type immutable input can be smuggled into the resolver. -/
theorem variable_kind {context : List ArithmeticType} {type : IntType}
    (index : Param (VariableTypes context) type) : ∃ kind : ArithmeticType, type = kind.asIntType := by
  induction context with
  | nil => cases index
  | cons kind context ih =>
      cases index with
      | here => exact ⟨kind, rfl⟩
      | there index => exact ih index

/-- Bindings carry only typed object identities, with no cached input values.
Registry membership, lifetime, initialization and authority are executor duties. -/
inductive Env : List ArithmeticType → Type where
  | nil : Env []
  | cons {kind : ArithmeticType} {context : List ArithmeticType} :
      LValue kind → Env context → Env (kind :: context)

namespace Env

def get {context : List ArithmeticType} {kind : ArithmeticType}
    (environment : Env context) (index : Vars context kind) : LValue kind :=
  match environment with
  | .nil => nomatch index
  | .cons (kind := .sint) reference tail =>
      match kind with
      | .sint =>
          match index with
          | .here => reference
          | .there index => get tail index
      | .uint =>
          match index with
          | .there index => get tail index
  | .cons (kind := .uint) reference tail =>
      match kind with
      | .sint =>
          match index with
          | .there index => get tail index
      | .uint =>
          match index with
          | .here => reference
          | .there index => get tail index

abbrev extend {context : List ArithmeticType} {kind : ArithmeticType}
    (environment : Env context) (reference : LValue kind) : Env (kind :: context) :=
  .cons reference environment

@[simp] theorem get_here {context : List ArithmeticType} {kind : ArithmeticType}
    (environment : Env context) (reference : LValue kind) :
    (environment.extend reference).get (.here : Vars (kind :: context) kind) = reference := by
  cases kind <;> rfl

@[simp] theorem get_there {context : List ArithmeticType} {kind other : ArithmeticType}
    (environment : Env context) (reference : LValue other) (index : Vars context kind) :
    (environment.extend reference).get (.there index) = environment.get index := by
  cases kind <;> cases other <;> rfl

def ids {context : List ArithmeticType} : Env context → List Nat
  | .nil => []
  | .cons reference tail => reference.id :: tail.ids

@[simp] theorem ids_length {context : List ArithmeticType} (environment : Env context) :
    environment.ids.length = context.length := by
  induction environment <;> simp_all [ids]

/-- Identity uniqueness across all kinds, independent of execution or admission. -/
def Unique {context : List ArithmeticType} (environment : Env context) : Prop :=
  environment.ids.Nodup

/-- Freshness is disjointness from every parameter/local, regardless of kind. -/
def Fresh {context : List ArithmeticType} {kind : ArithmeticType}
    (environment : Env context) (reference : LValue kind) : Prop :=
  reference.id ∉ environment.ids

@[simp] theorem unique_nil : (Env.nil : Env []).Unique := by simp [Unique, ids]

theorem unique_extend_iff {context : List ArithmeticType} {kind : ArithmeticType}
    (environment : Env context) (reference : LValue kind) :
    (environment.extend reference).Unique ↔ environment.Fresh reference ∧ environment.Unique := by
  simp only [Unique, Fresh, ids, List.nodup_cons]

theorem get_id_at {context : List ArithmeticType} {kind : ArithmeticType}
    (environment : Env context) (index : Vars context kind) :
    environment.ids[Vars.slot index]? = some (environment.get index).id := by
  induction environment with
  | nil => cases index
  | @cons head context reference tail ih =>
      cases head <;> cases kind <;> cases index <;>
        simp_all [ids, Vars.slot, position]

theorem get_id_mem {context : List ArithmeticType} {kind : ArithmeticType}
    (environment : Env context) (index : Vars context kind) :
    (environment.get index).id ∈ environment.ids :=
  List.mem_of_getElem? (environment.get_id_at index)

/-- Equal identities in a unique environment imply the same source slot,
even when the variables were presented at different object kinds. -/
theorem slot_eq_of_id_eq {context : List ArithmeticType} {left right : ArithmeticType}
    (environment : Env context) (unique : environment.Unique)
    (first : Vars context left) (second : Vars context right)
    (same : (environment.get first).id = (environment.get second).id) :
    Vars.slot first = Vars.slot second := by
  have bound : Vars.slot first < environment.ids.length := by
    simpa only [ids_length] using Vars.slot_lt first
  apply (List.Nodup.getElem?_inj bound unique).mp
  rw [get_id_at, get_id_at, same]

theorem get_injective {context : List ArithmeticType} {kind : ArithmeticType}
    (environment : Env context) (unique : environment.Unique)
    (first second : Vars context kind)
    (same : (environment.get first).id = (environment.get second).id) : first = second :=
  Vars.slot_injective first second (environment.slot_eq_of_id_eq unique first second same)

theorem fresh_get_ne {context : List ArithmeticType} {kind other : ArithmeticType}
    (environment : Env context) (reference : LValue other)
    (fresh : environment.Fresh reference) (index : Vars context kind) :
    (environment.get index).id ≠ reference.id := by
  intro same
  exact fresh (same ▸ environment.get_id_mem index)

end Env

/-- A finite statement tree. Assignment is a sequenced full expression; both
branches retain the identical context/result type. Every leaf returns or marks
unsupported syntax. Declarations cannot occur within statements. -/
inductive Stmt (target : Target) (context : List ArithmeticType) (result : IntType) where
  | set {kind : ArithmeticType} (index : Vars context kind)
      (value : RHS target context kind.asIntType) (next : Stmt target context result)
  | branch (condition : RHS target context (.small .boolean))
      (yes no : Stmt target context result)
  | ret (value : RHS target context result)
  | unsupported (feature : UnsupportedFeature)

private def firstSome (first second : Option UnsupportedFeature) : Option UnsupportedFeature :=
  match first with
  | some feature => some feature
  | none => second

private theorem firstSome_eq_none (first second : Option UnsupportedFeature) :
    firstSome first second = none ↔ first = none ∧ second = none := by
  cases first <;> simp [firstSome]

namespace Stmt

def setConverted {target : Target} {context : List ArithmeticType} {result source : IntType}
    {kind : ArithmeticType} (index : Vars context kind) (value : RHS target context source)
    (next : Stmt target context result) : Stmt target context result :=
  .set index (.convert kind.asIntType value) next

def retConverted {target : Target} {context : List ArithmeticType} {source : IntType}
    (result : IntType) (value : RHS target context source) : Stmt target context result :=
  .ret (.convert result value)

def branchTruth {target : Target} {context : List ArithmeticType} {result source : IntType}
    (condition : RHS target context source) (yes no : Stmt target context result) :
    Stmt target context result :=
  .branch (.convert (.small .boolean) condition) yes no

/-- Whole-tree coverage, including every RHS and both branches. This is not
lazy execution; an unsupported marker in skipped syntax still fails coverage. -/
@[simp] def firstUnsupported {target : Target} {context : List ArithmeticType} {result : IntType} :
    Stmt target context result → Option UnsupportedFeature
  | .set _ value next => firstSome value.firstUnsupported next.firstUnsupported
  | .branch condition yes no =>
      firstSome condition.firstUnsupported (firstSome yes.firstUnsupported no.firstUnsupported)
  | .ret value => value.firstUnsupported
  | .unsupported feature => some feature

/-- Structural coverage specified independently of the diagnostic scan. -/
@[simp] def Supported {target : Target} {context : List ArithmeticType} {result : IntType} :
    Stmt target context result → Prop
  | .set _ value next => value.Supported ∧ next.Supported
  | .branch condition yes no => condition.Supported ∧ yes.Supported ∧ no.Supported
  | .ret value => value.Supported
  | .unsupported _ => False

theorem firstUnsupported_eq_none_iff {target : Target} {context : List ArithmeticType}
    {result : IntType} (statement : Stmt target context result) :
    statement.firstUnsupported = none ↔ statement.Supported := by
  induction statement <;> simp_all [firstSome_eq_none, Expr.Supported]

@[simp] theorem firstUnsupported_setConverted {target : Target} {context : List ArithmeticType}
    {result source : IntType} {kind : ArithmeticType} (index : Vars context kind)
    (value : RHS target context source) (next : Stmt target context result) :
    (setConverted index value next).firstUnsupported =
      firstSome value.firstUnsupported next.firstUnsupported := rfl

@[simp] theorem firstUnsupported_retConverted {target : Target} {context : List ArithmeticType}
    {source : IntType} (result : IntType) (value : RHS target context source) :
    (retConverted result value).firstUnsupported = value.firstUnsupported := rfl

@[simp] theorem firstUnsupported_branchTruth {target : Target} {context : List ArithmeticType}
    {result source : IntType} (condition : RHS target context source)
    (yes no : Stmt target context result) :
    (branchTruth condition yes no).firstUnsupported =
      firstSome condition.firstUnsupported (firstSome yes.firstUnsupported no.firstUnsupported) := rfl

/-- Statement constructors only; shared Expr already has a finite inductive AST. -/
@[simp] def measure {target : Target} {context : List ArithmeticType} {result : IntType} :
    Stmt target context result → Nat
  | .set _ _ next => next.measure + 1
  | .branch _ yes no => yes.measure + no.measure + 1
  | .ret _ | .unsupported _ => 1

theorem measure_pos {target : Target} {context : List ArithmeticType} {result : IntType}
    (statement : Stmt target context result) : 0 < statement.measure := by
  cases statement <;> simp only [measure] <;> omega

theorem measure_set_next {target : Target} {context : List ArithmeticType} {result : IntType}
    {kind : ArithmeticType} (index : Vars context kind) (value : RHS target context kind.asIntType)
    (next : Stmt target context result) : next.measure < (Stmt.set index value next).measure := by
  simp only [measure]; omega

theorem measure_branch_children {target : Target} {context : List ArithmeticType} {result : IntType}
    (condition : RHS target context (.small .boolean)) (yes no : Stmt target context result) :
    yes.measure < (Stmt.branch condition yes no).measure ∧
      no.measure < (Stmt.branch condition yes no).measure := by
  simp only [measure]; omega

end Stmt

/-- A declaration's initializer sees only the old context; its continuation
keeps all old bindings and adds exactly its new full-int object. `none` is
vacuous initialization, not an implicit zero or an omitted reservation. -/
inductive Decls (target : Target) : List ArithmeticType → IntType → Type where
  | declare {context : List ArithmeticType} {result : IntType} (kind : ArithmeticType)
      (initial : Option (RHS target context kind.asIntType))
      (rest : Decls target (kind :: context) result) : Decls target context result
  | body {context : List ArithmeticType} {result : IntType}
      (statement : Stmt target context result) : Decls target context result

namespace Decls

def declareConverted {target : Target} {context : List ArithmeticType} {result source : IntType}
    (kind : ArithmeticType) (initial : RHS target context source)
    (rest : Decls target (kind :: context) result) : Decls target context result :=
  .declare kind (some (.convert kind.asIntType initial)) rest

/-- In declaration order, available before any initializer is evaluated. -/
@[simp] def localKinds {target : Target} {context : List ArithmeticType} {result : IntType} :
    Decls target context result → List ArithmeticType
  | .declare kind _ rest => kind :: rest.localKinds
  | .body _ => []

@[simp] def localCount {target : Target} {context : List ArithmeticType} {result : IntType} :
    Decls target context result → Nat
  | .declare _ _ rest => rest.localCount + 1
  | .body _ => 0

theorem localKinds_length {target : Target} {context : List ArithmeticType} {result : IntType}
    (declarations : Decls target context result) :
    declarations.localKinds.length = declarations.localCount := by
  induction declarations <;> simp_all

@[simp] def finalContext {target : Target} {context : List ArithmeticType} {result : IntType} :
    Decls target context result → List ArithmeticType
  | .declare _ _ rest => rest.finalContext
  | .body (context := context) _ => context

theorem finalContext_eq {target : Target} {context : List ArithmeticType} {result : IntType}
    (declarations : Decls target context result) :
    declarations.finalContext = declarations.localKinds.reverse ++ context := by
  induction declarations <;> simp_all [List.reverse_cons, List.append_assoc]

@[simp] def firstUnsupported {target : Target} {context : List ArithmeticType} {result : IntType} :
    Decls target context result → Option UnsupportedFeature
  | .declare _ initial rest =>
      firstSome (initial.bind Expr.firstUnsupported) rest.firstUnsupported
  | .body statement => statement.firstUnsupported

@[simp] def Supported {target : Target} {context : List ArithmeticType} {result : IntType} :
    Decls target context result → Prop
  | .declare _ initial rest =>
      (match initial with | none => True | some expression => expression.Supported) ∧ rest.Supported
  | .body statement => statement.Supported

theorem firstUnsupported_eq_none_iff {target : Target} {context : List ArithmeticType}
    {result : IntType} (declarations : Decls target context result) :
    declarations.firstUnsupported = none ↔ declarations.Supported := by
  induction declarations with
  | body statement => exact statement.firstUnsupported_eq_none_iff
  | declare kind initial rest ih =>
      cases initial <;> simp_all [firstSome_eq_none, Expr.Supported]

@[simp] theorem firstUnsupported_declareConverted {target : Target} {context : List ArithmeticType}
    {result source : IntType} (kind : ArithmeticType) (initial : RHS target context source)
    (rest : Decls target (kind :: context) result) :
    (declareConverted kind initial rest).firstUnsupported =
      firstSome initial.firstUnsupported rest.firstUnsupported := rfl

/-- Declaration and statement constructors, with strict descent to either child. -/
@[simp] def measure {target : Target} {context : List ArithmeticType} {result : IntType} :
    Decls target context result → Nat
  | .declare _ _ rest => rest.measure + 1
  | .body statement => statement.measure + 1

theorem measure_pos {target : Target} {context : List ArithmeticType} {result : IntType}
    (declarations : Decls target context result) : 0 < declarations.measure := by
  cases declarations <;> simp only [measure] <;> omega

theorem localCount_lt_measure {target : Target} {context : List ArithmeticType} {result : IntType}
    (declarations : Decls target context result) : declarations.localCount < declarations.measure := by
  induction declarations <;> simp_all only [localCount, measure] <;> omega

theorem measure_declare_rest {target : Target} {context : List ArithmeticType} {result : IntType}
    (kind : ArithmeticType) (initial : Option (RHS target context kind.asIntType))
    (rest : Decls target (kind :: context) result) :
    rest.measure < (Decls.declare kind initial rest).measure := by
  simp only [measure]; omega

theorem measure_body_statement {target : Target} {context : List ArithmeticType} {result : IntType}
    (statement : Stmt target context result) : statement.measure < (Decls.body statement).measure := by
  simp only [measure]; omega

end Decls

/-- All local identities at once, typed in declaration order. This is binding
data, not evidence of actual reservation. The executor must construct/validate
the complete plan before evaluating initializers; parameter objects are bound
and initialized separately. Unique plan IDs must also be fresh against Env P.
C lifetime begins at entry; C++ initialization precedes beginLifetime. -/
abbrev ReservationPlan {target : Target} {context : List ArithmeticType} {result : IntType}
    (declarations : Decls target context result) := Env declarations.localKinds

theorem reservationPlan_count {target : Target} {context : List ArithmeticType} {result : IntType}
    (declarations : Decls target context result) (plan : ReservationPlan declarations) :
    plan.ids.length = declarations.localCount := by
  rw [Env.ids_length, Decls.localKinds_length]

/-- One dialect and conversion policy for the entire block. Return values must
be computed before cleanup; BlockEval supplies the separate runner. -/
structure Program (target : Target) (parameters : List ArithmeticType) (result : IntType) where
  dialect : Dialect
  conversions : IntegerConversionPolicy
  body : Decls target parameters result

namespace Program

def firstUnsupported {target : Target} {parameters : List ArithmeticType} {result : IntType}
    (program : Program target parameters result) : Option UnsupportedFeature :=
  program.body.firstUnsupported

def Supported {target : Target} {parameters : List ArithmeticType} {result : IntType}
    (program : Program target parameters result) : Prop := program.body.Supported

theorem firstUnsupported_eq_none_iff {target : Target} {parameters : List ArithmeticType}
    {result : IntType} (program : Program target parameters result) :
    program.firstUnsupported = none ↔ program.Supported :=
  program.body.firstUnsupported_eq_none_iff

end Program
end EDSL.Source.Objects.StateSyntax
