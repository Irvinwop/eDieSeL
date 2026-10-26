/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.BlockEquations

set_option autoImplicit false
namespace EDSL.Source.Objects.Checks
open StateSyntax
attribute [local implicit_reducible] Value Target.modulus Decls.localKinds

/-- A read of an uninitialized local must preserve accepted allocation and
initialization effects on terminal failure; no rollback or normal cleanup. -/
def uninitialized (target : Target) (dialect : Dialect) :
    StateSyntax.Program target [] .uint :=
  ⟨dialect, .gnuModulo, .declare .uint none (.body (.ret (.param .here)))⟩

theorem uninitialized_retains_effects {Environment : Type} (target : Target)
    (dialect : Dialect) (environment : Environment) (actor : Nat) :
    let initial := State.empty (target := target) .nil environment actor 1
    let execution := BlockEval.runProgram (uninitialized target dialect) initial
    execution.1 = .error (uninitializedRead dialect) ∧
    execution.2.1.next = 1 ∧ execution.2.1.automaticSlots = 0 ∧
    execution.2.2 = (match dialect with
      | .gnuC23 => [.reserve 0 .uint actor, .beginLifetime 0 .uint,
          .initialize 0 .uint none]
      | .gnuCpp26 => [.reserve 0 .uint actor, .initialize 0 .uint none,
          .beginLifetime 0 .uint]) := by
  have covered : (uninitialized target dialect).Supported :=
    ((uninitialized target dialect).firstUnsupported_eq_none_iff).mp rfl
  dsimp only
  rw [BlockEval.runProgram_supported _ _ covered]
  cases dialect <;> with_unfolding_all
    simp [uninitialized, BlockEval.execute, BlockEval.enterParameters_nil,
      BlockEval.reserveAll_cons, BlockEval.reserveAll_nil,
      BlockEval.evalDecls_declare, BlockEval.evalDecls_body,
      StateEval.evalStmt_ret, StateEval.evalExpr_var,
      Decls.localKinds, Env.extend,
      Op.bind, Op.pure, Op.reject, reserve, «initialize», load,
      State.empty, State.putObject, reservationLife, uninitializedRead]

/-- Static coverage in a skipped arm must win before resource exhaustion.
Without complete-body preflight this program could allocate or accept the
selected supported branch. -/
def skippedUnsupported (target : Target) (dialect : Dialect) :
    StateSyntax.Program target [] .uint :=
  ⟨dialect, .gnuModulo, .declare .uint none (.body
    (.branch (.literal ⟨1, by change (0 : Int) ≤ 1 ∧ 1 < 2; omega⟩)
      (.ret (.literal ⟨0, target.modulus_pos⟩)) (.unsupported .memoryAccess)))⟩

theorem skipped_unsupported_precedes_allocation {Environment : Type} (target : Target)
    (dialect : Dialect) (initial : State target [] Environment) :
    BlockEval.runProgram (skippedUnsupported target dialect) initial =
      (.error (.unsupported .memoryAccess), initial, []) := by
  apply BlockEval.unsupported_unchanged
  rfl

/-- The second initializer reads the first local before it has a value. Both
locals must already have storage when the first declaration is initialized. -/
def earlyInitializerFailure (target : Target) (dialect : Dialect) :
    StateSyntax.Program target [] .uint :=
  ⟨dialect, .gnuModulo, .declare .uint none
    (.declare .uint (some (.param .here)) (.body (.ret (.param .here))))⟩

theorem early_initializer_failure_retains_reservations {Environment : Type}
    (target : Target) (dialect : Dialect) (environment : Environment) (actor : Nat) :
    let initial := State.empty (target := target) .nil environment actor 2
    let execution := BlockEval.runProgram (earlyInitializerFailure target dialect) initial
    execution.1 = .error (uninitializedRead dialect) ∧
    execution.2.1.next = 2 ∧ execution.2.1.automaticSlots = 0 ∧
    execution.2.1.objects 0 = some {
      kind := .uint, life := .live, reached := true, value := none,
      owner := actor, permissions := ⟨true, true⟩ } ∧
    execution.2.1.objects 1 = some {
      kind := .uint,
      life := match dialect with | .gnuC23 => .live | .gnuCpp26 => .reserved,
      reached := false, value := none, owner := actor, permissions := ⟨true, true⟩ } ∧
    execution.2.2 = (match dialect with
      | .gnuC23 => [.reserve 0 .uint actor, .beginLifetime 0 .uint,
          .reserve 1 .uint actor, .beginLifetime 1 .uint, .initialize 0 .uint none]
      | .gnuCpp26 => [.reserve 0 .uint actor, .reserve 1 .uint actor,
          .initialize 0 .uint none, .beginLifetime 0 .uint]) := by
  have covered : (earlyInitializerFailure target dialect).Supported :=
    ((earlyInitializerFailure target dialect).firstUnsupported_eq_none_iff).mp rfl
  dsimp only
  rw [BlockEval.runProgram_supported _ _ covered]
  cases dialect <;> with_unfolding_all
    simp [earlyInitializerFailure, BlockEval.execute, BlockEval.enterParameters_nil,
      BlockEval.reserveAll_cons, BlockEval.reserveAll_nil,
      BlockEval.evalDecls_declare, StateEval.evalExpr_var,
      Decls.localKinds, Env.extend,
      Op.bind, Op.pure, Op.reject, reserve, «initialize», load,
      State.empty, State.putObject, reservationLife, uninitializedRead]

end EDSL.Source.Objects.Checks
