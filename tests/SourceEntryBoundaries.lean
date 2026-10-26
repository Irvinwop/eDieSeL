/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.EntryContracts

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.EntryBoundaryValidation
open StateSyntax LifecycleContracts BlockContracts ParameterContracts EntryContracts

variable {target : Target} {stateParameters : List IntType} {Environment : Type}
variable (dialect : Dialect) (policy : IntegerConversionPolicy)

/- This body is intentionally unsupported. Unchecked entry must prepare its
mixed prefix, while public start must reject before any reservation. No Code
execution, observer normalization or success admission is used. -/
private def mixed (value : Value target .uint) : Function target [.sint, .uint] .uint :=
  ⟨dialect, policy,
    .declare .sint none
      (.declare .uint (some (.literal value)) (.body (.unsupported .memoryAccess)))⟩

private def mixedLiteral (value : Value target .uint) :
    LiteralInitializers (mixed dialect policy value).body :=
  .declare .sint none (.declare .uint (some value)
    (.body (Code.unsupported .memoryAccess : Code target [.uint, .sint, .sint, .uint] .uint)))

/-- Both dialects: a genuinely uninitialized signed local can be written and
then read. Its unsigned neighbor and mixed formal parameters remain usable;
all four objects can actually be cleaned in reverse local/parameter order. -/
theorem mixed_entry_and_cleanup (value : Value target .uint)
    (signed : Value target .sint) (unsigned : Value target .uint)
    (replacement : Value target .sint) (initial : State target stateParameters Environment)
    (metadata : initial.WellFormed) (capacity : 4 ≤ initial.automaticSlots) :
    let function := mixed dialect policy value
    let literal := mixedLiteral dialect policy value
    let values : CallInputs target [.sint, .uint] := .cons signed (.cons unsigned .nil)
    ∃ middle final,
      FunctionEval.enterUnchecked function values initial =
        (.ok (entryFor function initial.next), middle,
          entryEvents function literal values initial.actor initial.next) ∧
      load dialect (⟨initial.next⟩ : LValue .sint) middle =
        (.ok signed, middle, [.read initial.next .sint signed.toInt]) ∧
      load dialect (⟨initial.next + 1⟩ : LValue .uint) middle =
        (.ok unsigned, middle, [.read (initial.next + 1) .uint unsigned.toInt]) ∧
      load dialect (⟨initial.next + 3⟩ : LValue .uint) middle =
        (.ok value, middle, [.read (initial.next + 3) .uint value.toInt]) ∧
      load dialect (⟨initial.next + 2⟩ : LValue .sint) middle =
        (.error (uninitializedRead dialect), middle, []) ∧
      (∃ updated, Op.bind (store (⟨initial.next + 2⟩ : LValue .sint) replacement)
          (fun _ => load dialect (⟨initial.next + 2⟩ : LValue .sint)) middle =
        (.ok replacement, updated,
          [.write (initial.next + 2) .sint replacement.toInt,
           .read (initial.next + 2) .sint replacement.toInt])) ∧
      FunctionEval.cleanup (entryFor function initial.next) value middle =
        (.ok value, final,
          [.endLifetime (initial.next + 3) .uint, .endLifetime (initial.next + 2) .sint,
           .endLifetime (initial.next + 1) .uint, .endLifetime initial.next .sint]) ∧
      Frozen initial final ∧ final.WellFormed ∧ final.next = initial.next + 4 ∧
      final.automaticSlots = initial.automaticSlots ∧
      (∀ id object, initial.objects id = some object → final.objects id = some object) := by
  let function := mixed dialect policy value
  let literal := mixedLiteral dialect policy value
  let values : CallInputs target [.sint, .uint] := .cons signed (.cons unsigned .nil)
  obtain ⟨middle, entered, facts⟩ := enter_contract function literal values initial metadata capacity
  have signedRead := facts.parameter_access (kind := .sint) .here
  have unsignedRead := facts.parameter_access (kind := .uint) (.there .here)
  have localAccess := localRecords_access _ literal.values middle facts.localRecords
    (kind := .uint) (.there .here)
  have localRead := localAccess.2 value rfl
  have absent := localRecords_absent dialect _ literal.values middle facts.localRecords
    (kind := .sint) .here rfl
  have uninitialized := localRecords_get _ literal.values middle.actor middle facts.localRecords
    (kind := .sint) .here
  obtain ⟨updated, _, _, written⟩ := store_load_uninitialized dialect middle
    (⟨initial.next + 2⟩ : LValue .sint) replacement ⟨true, true⟩ uninitialized rfl rfl
  obtain ⟨localsLive, parametersLive⟩ := facts.cleanup
  obtain ⟨final, closed, frozen, next, slots, finalMeta, _, _, frame⟩ :=
    FunctionVC.cleanup_contract (entryFor function initial.next) value middle facts.metadata
      facts.localUnique facts.parameterUnique facts.disjoint localsLive parametersLive
  refine ⟨middle, final, entered,
    load_contract dialect middle (⟨initial.next⟩ : LValue .sint) signed signedRead.1,
    load_contract dialect middle (⟨initial.next + 1⟩ : LValue .uint) unsigned unsignedRead.1,
    load_contract dialect middle (⟨initial.next + 3⟩ : LValue .uint) value localRead,
    absent, ⟨updated, written⟩, closed,
    ⟨frozen.1.trans facts.frozen.1, frozen.2.1.trans facts.frozen.2.1,
      frozen.2.2.trans facts.frozen.2.2⟩, finalMeta, next.trans facts.next, ?_, ?_⟩
  · have entrySlots := facts.slots
    change final.automaticSlots = middle.automaticSlots + 2 + 2 at slots
    change middle.automaticSlots + 4 = initial.automaticSlots at entrySlots
    omega
  · intro id object registered
    have old := (metadata id object registered).1
    apply (frame id ?_ ?_).trans (facts.caller id object registered)
    · have bounds := reservationEnv_bounds (initial.next + 2) [.sint, .uint] id
      intro member
      have lower := (bounds member).1
      omega
    · have bounds := reservationEnv_bounds initial.next [.sint, .uint] id
      intro member
      have lower := (bounds member).1
      omega

/-- Full-tree support stays a public preflight, even though unchecked entry of
the identical function succeeds under the metadata/capacity admissions above. -/
theorem public_start_rejects (value : Value target .uint)
    (initial : State target [.sint, .uint] Environment) :
    FunctionEval.start (mixed dialect policy value) initial =
      .stopped (.unsupported .memoryAccess) initial [] :=
  FunctionEval.start_unsupported (mixed dialect policy value) initial .memoryAccess rfl

/-- The empty prefix is covered too, with no assumed body behavior. -/
theorem empty_prefix (code : Code target [] .uint)
    (initial : State target stateParameters Environment) (metadata : initial.WellFormed) :
    let function : Function target [] .uint := ⟨dialect, policy, .body code⟩
    FunctionEval.enterUnchecked function .nil initial =
      (.ok ⟨⟨[], .nil, code⟩, .nil, [], .nil⟩, initial, []) := by
  let function : Function target [] .uint := ⟨dialect, policy, .body code⟩
  obtain ⟨final, entered, facts⟩ := enter_contract function (.body code) .nil initial metadata (by simp [function])
  have same : final = initial := by
    have registry : final.objects = initial.objects := by
      funext id
      exact facts.outside id (by simp only [function, DeclarationSpine.localKinds, List.length_nil, Nat.add_zero]; omega)
    have world := facts.frozen
    have counter : final.next = initial.next := by simpa only [function,
      DeclarationSpine.localKinds, List.length_nil, Nat.add_zero] using facts.next
    have slots : final.automaticSlots = initial.automaticSlots := by simpa only [function,
      DeclarationSpine.localKinds, List.length_nil, Nat.add_zero] using facts.slots
    cases initial
    cases final
    simp only [Registry.State.mk.injEq]
    exact ⟨world.1, world.2.1, world.2.2, counter, slots, registry⟩
  simpa only [same, function, entryFor, prepared, reservationEnv, List.length_nil,
    Nat.add_zero, entryEvents, parameterEvents, DeclarationSpine.localKinds,
    reservationEvents, initializationEvents, LiteralInitializers.values, List.nil_append] using entered

end EDSL.Source.Objects.Control.EntryBoundaryValidation
