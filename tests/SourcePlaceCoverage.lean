import EDSL.Source.Syntax.Coverage

set_option autoImplicit false
namespace EDSL.Tests.SourcePlaceCoverage
open EDSL.Source EDSL.Source.Memory EDSL.Source.Engine

/-- Supporting real load syntax never turns an old diagnostic marker into support. -/
theorem explicit_marker {target : Target} {dialect : Dialect}
    {inputs : List ScalarType} {objects : List ObjectType} {ty : ScalarType}
    (profile : SyntaxProfile target dialect) (feature : UnsupportedFeature) :
    (Engine.Expr.unsupported feature : Engine.Expr target inputs objects .object ty).firstUnsupported
      profile = some feature := rfl

/-- Regression boundary: the C23-only data gate must not disable old C++ loads. -/
theorem common_integer_load {target : Target} (dialect : Dialect) (kind : ArithmeticType) :
    (Engine.Expr.load (.variable .here) :
      Engine.RHS target [.scalar (.integer kind.asIntType)] (.integer kind.asIntType)).preflight
        (.common (dialect := dialect)) = none := by
  cases kind <;> rfl

theorem cpp_address_rejected {target : Target} {inputs : List ScalarType}
    {objects : List ObjectType} {object : ObjectType}
    (profile : SyntaxProfile target .gnuCpp26) (place : Engine.Place target inputs objects object) :
    (Engine.Expr.address place).firstUnsupported profile = some .memoryAccess := by
  cases profile
  rfl

/-- Covered pointer-to-array data does not admit whole-array offset operations. -/
theorem whole_array_offset_rejected {target : Target} {dialect : Dialect}
    {inputs : List ScalarType} {objects : List ObjectType}
    {element : ObjectType} {length : Nat} {index : IntType}
    (profile : SyntaxProfile target dialect) (operation : OffsetOp)
    (base : Engine.Expr target inputs objects .object (.pointer (.array element length)))
    (displacement : Engine.Expr target inputs objects .object (.integer index)) :
    (Engine.Expr.offset operation base displacement).firstUnsupported profile = some .memoryAccess := rfl

/-- Cancellation is a later dynamic rule; static coverage still sees the operand. -/
theorem address_indirect_scans_operand {target : Target} {dialect : Dialect}
    {inputs : List ScalarType} {objects : List ObjectType} {object : ObjectType}
    (profile : SyntaxProfile target dialect)
    (pointer : Engine.Expr target inputs objects .object (.pointer object))
    (covered : (Engine.Expr.address (.indirect pointer)).firstUnsupported profile = none) :
    pointer.firstUnsupported profile = none := by
  have all := (Engine.Expr.firstUnsupported_none_iff profile _).mp covered
  exact (Engine.Expr.firstUnsupported_none_iff profile pointer).mpr all.2.2

theorem subscript_scans_index {target : Target} {dialect : Dialect}
    {inputs : List ScalarType} {objects : List ObjectType} {object : ObjectType} {index : IntType}
    (profile : SyntaxProfile target dialect)
    (base : Engine.Expr target inputs objects .object (.pointer object))
    (displacement : Engine.Expr target inputs objects .object (.integer index))
    (covered : (Engine.Place.subscript base displacement).firstUnsupported profile = none) :
    displacement.firstUnsupported profile = none := by
  have all := (Engine.Place.firstUnsupported_none_iff profile _).mp covered
  exact (Engine.Expr.firstUnsupported_none_iff profile displacement).mpr all.2.2.2

/-- An unused zero-bound binding is rejected before the body is considered. -/
theorem unused_zero_array_rejected {target : Target} (layout : StorageLayout target)
    {element : ObjectType} {objects : List ObjectType}
    (expression : Engine.Expr target [] (.array element 0 :: objects) .object (.integer .sint)) :
    expression.preflight (.c23Data layout) = some .memoryAccess := by
  cases gate : (SyntaxProfile.c23Data layout).scalarCovered (.integer .sint) <;>
    simp only [Engine.Expr.preflight, firstUnsupportedTypes, firstSome, gate, typeDiagnostic,
      Bool.false_eq_true, ↓reduceIte, SyntaxProfile.objectCovered, Memory.typeCovered,
      ObjectType.zeroArray_not_inC23Profile, Bool.and_false, Bool.false_and]

/- A mutable RHS cannot contain an immutable input leaf, even when a same-typed
object binding exists. This checks the actual alias rather than empty indices. -/
/--
Index [] (ScalarType.integer IntType.uint)
-/
#guard_msgs (error, drop info, substring := true) in
#check (fun (target : Target) =>
  (Engine.Expr.param .here :
    Engine.RHS target [.scalar (.integer .uint)] (.integer .uint)))

end EDSL.Tests.SourcePlaceCoverage
