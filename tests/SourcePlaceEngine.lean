/- Synthetic supplied-algebra regressions; not an object-memory model. -/
import EDSL.Source.ExpressionCore

-- Tests of traversal demand/effects with a supplied algebra, not C pointer validity.
set_option autoImplicit false
namespace EDSL.Tests.SourcePlaceEngine
open EDSL.Source EDSL.Source.Memory EDSL.Source.ExpressionCore
inductive Fault where
  | lift | indirect | load
  deriving DecidableEq
abbrev Trace (α : Type) := Except Fault α × List Nat
instance : Monad Trace where
  pure value := (.ok value, [])
  bind first next :=
    match first.1 with
    | .error failure => (.error failure, first.2)
    | .ok value =>
        let second := next value
        (second.1, first.2 ++ second.2)
def primitive {α : Type} (value : Except Fault α) (tag : Nat) : Trace α :=
  (value, [tag])
def handlers (target : Target) : MemoryOps target Trace (fun _ => Nat) [] where
  «variable» := fun index => nomatch index
  usePointer := fun pointer => primitive (.ok pointer) 2
  indirect := fun _ => primitive (.error .indirect) 3
  load := fun _ => primitive (.error .load) 4
  address := fun _ => primitive (.ok .null) 5
  decay := fun _ => primitive (.ok .null) 6
  offset := fun _ pointer _ => primitive (.ok pointer) 7
def resolve {target : Target} {object : ObjectType} (pointer : PointerValue object) :
    {kind : ScalarType} → Index [.pointer object] kind → Trace (ScalarValue target kind)
  | _, .here => primitive (.ok pointer) 1
  | _, .there index => nomatch index
def lift {α : Type} (_ : Outcome α) : Trace α := primitive (.error .lift) 8
/-- Cancellation evaluates a failing-indirection operand exactly once, while
preserving the explicitly supplied pointer interpretation observation. -/
theorem address_null_evaluates_once (target : Target) (object : ObjectType)
    (policy : IntegerConversionPolicy) :
    evalEngine (fragment := .object) (objects := []) (Handle := fun _ => Nat) policy lift (resolve (target := target) (PointerValue.null : PointerValue object))
      (handlers target) (Engine.Expr.address (.indirect (.param .here))) =
        ((.ok PointerValue.null, [1, 2]) : Trace (PointerValue object)) := by
  rfl
/-- Ordinary indirection fails, retaining the input observation; its load is
never executed. The same null input is used as in the cancellation theorem. -/
theorem load_null_retains_failure (target : Target) (kind : ScalarType)
    (policy : IntegerConversionPolicy) :
    evalEngine (fragment := .object) (objects := []) (Handle := fun _ => Nat) policy lift
      (resolve (target := target) (PointerValue.null : PointerValue (.scalar kind)))
      (handlers target) (Engine.Expr.load (.indirect (.param .here))) =
        ((.error .indirect, [1, 3]) : Trace (ScalarValue target kind)) := by
  rfl
def boolTrue (target : Target) : Value target (.small .boolean) :=
  ⟨1, by simp [SmallType.lowerBound, SmallType.upperBound, SmallType.isSigned, SmallType.rangeBits]⟩
/-- Dynamic selection must not evaluate the unselected rejecting pointer arm.
Static coverage remains separate and would reject unsupported source markers. -/
theorem selected_address_skips_other_arm (target : Target) (object : ObjectType)
    (policy : IntegerConversionPolicy) :
    evalEngine (fragment := .object) (objects := []) (Handle := fun _ => Nat) policy lift (resolve (target := target) (PointerValue.null : PointerValue object))
      (handlers target)
      (Engine.Expr.select (.literal (boolTrue target))
        (.address (.indirect (.param .here))) (.unsupported .memoryAccess)) =
      ((.ok PointerValue.null, [1, 2]) : Trace (PointerValue object)) := by
  rfl
end EDSL.Tests.SourcePlaceEngine
