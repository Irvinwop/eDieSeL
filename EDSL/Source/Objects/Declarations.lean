/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.StateSyntax

set_option autoImplicit false
namespace EDSL.Source.Objects.Control
open StateSyntax

/-! A declaration prefix parameterized by its terminal body language. Typed
initializers see only the preceding source context. The reservation plan lists
the complete prefix in source order, independently of the terminal language.
This module has no dependency on control syntax or execution. -/

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

/-- Transport an already reserved plan through body translation. Constructor
reduction keeps the finite driver's public declaration equations definitional;
this only transports identities and never evaluates an initializer. -/
def planOfDecls (translate : ∀ {context result}, Stmt target context result → Body context result) :
    {context : List ArithmeticType} → {result : IntType} →
    (declarations : Decls target context result) → ReservationPlan declarations →
    Env (ofDecls translate declarations).localKinds
  | _, _, .body _, _ => .nil
  | _, _, .declare _ _ rest, plan =>
    match plan with
    | .cons reference tail => .cons reference (planOfDecls translate rest tail)

private theorem cast_cons {first second : List ArithmeticType} {kind : ArithmeticType}
    (same : first = second) (reference : LValue kind) (tail : Env first) :
    cast (congrArg Env (congrArg (List.cons kind) same)) (.cons reference tail) =
      .cons reference (cast (congrArg Env same) tail) := by
  cases same
  rfl

/-- Plan transport preserves every reserved identity and its source order. -/
theorem planOfDecls_eq_cast
    (translate : ∀ {context result}, Stmt target context result → Body context result)
    {context : List ArithmeticType} {result : IntType} (declarations : Decls target context result)
    (plan : ReservationPlan declarations) :
    planOfDecls translate declarations plan =
      cast (congrArg Env (ofDecls_localKinds translate declarations).symm) plan := by
  induction declarations with
  | body statement => cases plan; rfl
  | declare kind initial rest ih =>
      cases plan with
      | cons reference tail =>
          change Env.cons reference (planOfDecls translate rest tail) = _
          rw [ih]
          exact (cast_cons (ofDecls_localKinds translate rest).symm reference tail).symm

end DeclarationSpine
end EDSL.Source.Objects.Control
