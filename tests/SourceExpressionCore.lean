/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.ExpressionCore

set_option autoImplicit false
set_option warningAsError true
namespace EDSL.Tests.SourceExpressionCore
open EDSL.Source

/- These probes observe demand through the real generic traversal and standard
StateT/Except carrier. The recording resolver supplies explicit effects/errors;
it is not a source/OS memory model or a replacement expression interpreter.
Only query traces and selected failures are specified, not fixture values. -/
private inductive ProbeError where
  | forbiddenRead
  | scalarUB (reason : UBReason)
  | unmodeled (feature : UnsupportedFeature)
  deriving DecidableEq

private abbrev ProbeM := StateT (List Nat) (Except ProbeError)
private abbrev Parameters : List IntType := [.small .boolean, .uint, .uint]

private def liftPrimitive {α : Type} (outcome : Outcome α) : ProbeM α :=
  fun trace => match outcome with
    | .defined value => .ok (value, trace)
    | .undefined reason => .error (.scalarUB reason)
    | .unsupported feature => .error (.unmodeled feature)

private def lookup (condition denied : Bool) {ty : IntType} :
    Param Parameters ty → ProbeM (Value Target.int32 ty)
  | .here => fun trace => .ok (booleanValue condition, trace ++ [0])
  | .there .here => fun trace => .ok (⟨7, by decide +kernel⟩, trace ++ [1])
  | .there (.there .here) => fun trace =>
      if denied then .error .forbiddenRead
      else .ok (⟨11, by decide +kernel⟩, trace ++ [2])

private inductive Observation where
  | ok (trace : List Nat)
  | error (reason : ProbeError)
  deriving DecidableEq

private def observeTrace {α : Type} :
    Except ProbeError (α × List Nat) → Observation
  | .ok (_, trace) => .ok trace
  | .error reason => .error reason

private def queries {ty : IntType} (condition denied : Bool)
    (expression : Expr Target.int32 Parameters ty) : Observation :=
  observeTrace ((ExpressionCore.evalCore .gnuModulo liftPrimitive
    (lookup condition denied) expression).run [])

private def branch : Expr Target.int32 Parameters .uint :=
  .select (.param .here) (.param (.there (.there .here))) (.param (.there .here))

/-- An allowed unselected lookup must still have no recording effect. -/
example : queries false false branch = .ok [0, 1] := by decide +kernel

/-- An unselected denied lookup must not poison the selected execution. -/
example : queries false true branch = .ok [0, 1] := by decide +kernel

/-- Selecting that same lookup exposes the actual supplied failure. -/
example : queries true true branch = .error .forbiddenRead := by decide +kernel

/-- Reversing selection queries only the other arm. -/
example : queries true false branch = .ok [0, 2] := by decide +kernel

/-- Both operands are demanded, in the core's internal diagnostic order.
This is not a C/C++ native operand-sequencing claim. -/
example : queries false false
    (.uadd (.param (.there .here)) (.param (.there (.there .here)))) = .ok [1, 2] := by
  decide +kernel

/-- Swapping operands swaps actual query effects, without preloading parameters. -/
example : queries false false
    (.uadd (.param (.there (.there .here))) (.param (.there .here))) = .ok [2, 1] := by
  decide +kernel

end EDSL.Tests.SourceExpressionCore
