/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Syntax.Properties

set_option autoImplicit false

namespace EDSL.Source
open Memory

namespace Engine

/- Independent structural coverage judgment: every child, including both
conditional arms and places under address-of, must meet its syntax rule. -/
mutual
  def Expr.Covered {target : Target} {dialect : Dialect}
      {inputs : List ScalarType} {objects : List ObjectType}
      (profile : SyntaxProfile target dialect) :
      {f : Fragment} → {ty : ScalarType} → Expr target inputs objects f ty → Prop
    | _, _, .literal _ => True
    | _, ty, .param _ => profile.scalarCovered ty = true
    | _, _, .convert _ operand => operand.Covered profile
    | _, _, .promote operand => operand.Covered profile
    | _, _, .uadd left right => left.Covered profile ∧ right.Covered profile
    | _, _, .sadd left right => left.Covered profile ∧ right.Covered profile
    | _, _, .usub left right => left.Covered profile ∧ right.Covered profile
    | _, _, .ssub left right => left.Covered profile ∧ right.Covered profile
    | _, _, .umul left right => left.Covered profile ∧ right.Covered profile
    | _, _, .smul left right => left.Covered profile ∧ right.Covered profile
    | _, _, .udiv left right => left.Covered profile ∧ right.Covered profile
    | _, _, .sdiv left right => left.Covered profile ∧ right.Covered profile
    | _, _, .urem left right => left.Covered profile ∧ right.Covered profile
    | _, _, .srem left right => left.Covered profile ∧ right.Covered profile
    | _, _, .compare _ _ left right => left.Covered profile ∧ right.Covered profile
    | _, ty, .select condition onTrue onFalse =>
        profile.scalarCovered ty = true ∧ condition.Covered profile ∧
          onTrue.Covered profile ∧ onFalse.Covered profile
    | _, _, .unsupported _ => False
    | _, _, .null (object := object) => profile.pointerDiagnostic object = none
    | _, _, .load place => Expr.loadDiagnostic profile place = none ∧ place.Covered profile
    | _, _, .address (object := object) place =>
        profile.pointerDiagnostic object = none ∧ place.Covered profile
    | _, _, .decay (element := element) (length := length) place =>
        profile.objectCovered (.array element length) = true ∧
          profile.pointerDiagnostic element = none ∧ place.Covered profile
    | _, _, .offset (object := object) _ base displacement =>
        profile.offsetDiagnostic object = none ∧ base.Covered profile ∧ displacement.Covered profile

  def Place.Covered {target : Target} {dialect : Dialect}
      {inputs : List ScalarType} {objects : List ObjectType}
      (profile : SyntaxProfile target dialect) :
      {object : ObjectType} → Place target inputs objects object → Prop
    | object, .variable _ => profile.objectCovered object = true
    | object, .indirect pointer =>
        profile.pointerDiagnostic object = none ∧ pointer.Covered profile
    | _, .unsupported _ => False
end

@[simp] theorem typeDiagnostic_eq_none_iff (covered : Bool) :
    typeDiagnostic covered = none ↔ covered = true := by
  cases covered <;> simp only [typeDiagnostic, Bool.false_eq_true, ↓reduceIte, reduceCtorEq]

mutual
  theorem Expr.firstUnsupported_none_iff {target : Target} {dialect : Dialect}
      {inputs : List ScalarType} {objects : List ObjectType}
      (profile : SyntaxProfile target dialect) {f : Fragment} {ty : ScalarType}
      (expression : Expr target inputs objects f ty) :
      expression.firstUnsupported profile = none ↔ expression.Covered profile :=
    match expression with
    | .literal _ => by simp only [Expr.firstUnsupported, Expr.Covered]
    | .param _ => typeDiagnostic_eq_none_iff _
    | .convert _ operand => Expr.firstUnsupported_none_iff profile operand
    | .promote operand => Expr.firstUnsupported_none_iff profile operand
    | .uadd left right => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff,
          Expr.firstUnsupported_none_iff profile left, Expr.firstUnsupported_none_iff profile right]
    | .sadd left right => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff,
          Expr.firstUnsupported_none_iff profile left, Expr.firstUnsupported_none_iff profile right]
    | .usub left right => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff,
          Expr.firstUnsupported_none_iff profile left, Expr.firstUnsupported_none_iff profile right]
    | .ssub left right => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff,
          Expr.firstUnsupported_none_iff profile left, Expr.firstUnsupported_none_iff profile right]
    | .umul left right => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff,
          Expr.firstUnsupported_none_iff profile left, Expr.firstUnsupported_none_iff profile right]
    | .smul left right => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff,
          Expr.firstUnsupported_none_iff profile left, Expr.firstUnsupported_none_iff profile right]
    | .udiv left right => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff,
          Expr.firstUnsupported_none_iff profile left, Expr.firstUnsupported_none_iff profile right]
    | .sdiv left right => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff,
          Expr.firstUnsupported_none_iff profile left, Expr.firstUnsupported_none_iff profile right]
    | .urem left right => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff,
          Expr.firstUnsupported_none_iff profile left, Expr.firstUnsupported_none_iff profile right]
    | .srem left right => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff,
          Expr.firstUnsupported_none_iff profile left, Expr.firstUnsupported_none_iff profile right]
    | .compare _ _ left right => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff,
          Expr.firstUnsupported_none_iff profile left, Expr.firstUnsupported_none_iff profile right]
    | .select condition onTrue onFalse => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff, typeDiagnostic_eq_none_iff,
          Expr.firstUnsupported_none_iff profile condition, Expr.firstUnsupported_none_iff profile onTrue,
          Expr.firstUnsupported_none_iff profile onFalse]
    | .unsupported _ => by simp only [Expr.firstUnsupported, Expr.Covered, reduceCtorEq]
    | .null => Iff.rfl
    | .load place => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff,
          Place.firstUnsupported_none_iff profile place]
    | .address place => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff,
          Place.firstUnsupported_none_iff profile place]
    | .decay place => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff, typeDiagnostic_eq_none_iff,
          Place.firstUnsupported_none_iff profile place]
    | .offset _ base displacement => by
        simp only [Expr.firstUnsupported, Expr.Covered, firstSome_eq_none_iff,
          Expr.firstUnsupported_none_iff profile base, Expr.firstUnsupported_none_iff profile displacement]
  theorem Place.firstUnsupported_none_iff {target : Target} {dialect : Dialect}
      {inputs : List ScalarType} {objects : List ObjectType}
      (profile : SyntaxProfile target dialect) {object : ObjectType}
      (place : Place target inputs objects object) :
      place.firstUnsupported profile = none ↔ place.Covered profile :=
    match place with
    | .variable _ => typeDiagnostic_eq_none_iff _
    | .indirect pointer => by
        simp only [Place.firstUnsupported, Place.Covered, firstSome_eq_none_iff,
          Expr.firstUnsupported_none_iff profile pointer]
    | .unsupported _ => by simp only [Place.firstUnsupported, Place.Covered, reduceCtorEq]
end

theorem firstUnsupportedTypes_none_iff {α : Type} (covered : α → Bool) (types : List α) :
    firstUnsupportedTypes covered types = none ↔ ∀ ty ∈ types, covered ty = true := by
  induction types with
  | nil => simp [firstUnsupportedTypes]
  | cons head tail ih =>
      simp only [firstUnsupportedTypes, firstSome_eq_none_iff, typeDiagnostic_eq_none_iff, ih,
        List.mem_cons, forall_eq_or_imp]

theorem Expr.preflight_none_iff {target : Target} {dialect : Dialect}
    {inputs : List ScalarType} {objects : List ObjectType} {f : Fragment} {ty : ScalarType}
    (profile : SyntaxProfile target dialect) (expression : Expr target inputs objects f ty) :
    expression.preflight profile = none ↔
      (∀ input ∈ inputs, profile.scalarCovered input = true) ∧
      profile.scalarCovered ty = true ∧
      (∀ object ∈ objects, profile.objectCovered object = true) ∧ expression.Covered profile := by
  simp only [Expr.preflight, firstSome_eq_none_iff, firstUnsupportedTypes_none_iff,
    typeDiagnostic_eq_none_iff, Expr.firstUnsupported_none_iff]

/-- Common full-int object types stay admitted in each dialect. This gate
deliberately does not call the new C23-only Memory.typeCovered. -/
@[simp] theorem common_fullInt {target : Target} (dialect : Dialect) (kind : ArithmeticType) :
    (SyntaxProfile.common (target := target) (dialect := dialect)).objectCovered
      (.scalar (.integer kind.asIntType)) = true := by
  cases kind <;> rfl

@[simp] theorem common_pointer {target : Target} (dialect : Dialect) (object : ObjectType) :
    (SyntaxProfile.common (target := target) (dialect := dialect)).scalarCovered
      (.pointer object) = false := rfl

/-- The C23 constructor cannot be reindexed as a C++ syntax profile. -/
theorem cpp_profile_is_common {target : Target} (profile : SyntaxProfile target .gnuCpp26) :
    profile = .common := by cases profile; rfl

end Engine

namespace Expr

theorem preflight_eq_firstUnsupported {target : Target} {parameters : List IntType} {ty : IntType}
    (dialect : Dialect) (expression : Expr target parameters ty) :
    expression.preflight (Engine.SyntaxProfile.common (dialect := dialect)) =
      expression.firstUnsupported := by
  have inputs : Engine.firstUnsupportedTypes
      (Engine.SyntaxProfile.common (target := target) (dialect := dialect)).scalarCovered
      (parameters.map ScalarType.integer) = none := by
    apply (Engine.firstUnsupportedTypes_none_iff _ _).mpr
    intro input member
    obtain ⟨kind, _, rfl⟩ := List.mem_map.mp member
    rfl
  simp only [Engine.Expr.preflight, inputs, Engine.firstSome, Engine.typeDiagnostic,
    Engine.SyntaxProfile.scalarCovered, ↓reduceIte, Engine.firstUnsupportedTypes]
  induction expression using Expr.inductionOn <;>
    simp_all only [Expr.firstUnsupported, Engine.Expr.firstUnsupported, Engine.typeDiagnostic,
      Engine.SyntaxProfile.scalarCovered, Engine.firstSome, ↓reduceIte]

end Expr
end EDSL.Source
