/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.Division

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.Division.Checks
open StateSyntax
attribute [local implicit_reducible] Value Target.modulus

/- Internal object-control regressions. No source-standard loop progress,
function cleanup, native binary, scheduling or OS refinement is asserted. -/

private def one : Value Target.int32 .uint := ⟨1, by decide +kernel⟩
private def two : Value Target.int32 .uint := ⟨2, by decide +kernel⟩
private def three : Value Target.int32 .uint := ⟨3, by decide +kernel⟩
private def seven : Value Target.int32 .uint := ⟨7, by decide +kernel⟩
private def q : LValue .uint := ⟨0⟩
private def r : LValue .uint := ⟨1⟩
private def dRef : LValue .uint := ⟨2⟩

private def aliasedInitial : State Target.int32 [] Unit :=
  put (put { State.empty .nil () 0 5 with next := 3 } q (zero _)) dRef two

/-- Resource authorization alone does not replace nonaliasing. With q and r
sharing an actual object, this loop returns 1 for 2/2 but leaves remainder 1:
the independently specified Euclidean post is false. This catches weakening
the q/r distinction even when all reads and writes still succeed. -/
theorem alias_changes_numeric_contract :
    let final := run .gnuC23 .gnuModulo (bindings q q dRef) 11
      (start (code two) aliasedInitial)
    final.status = .returned one ∧
      ¬ Post two two q q dRef aliasedInitial one final.state final.events := by
  dsimp only
  constructor
  · rfl
  · intro post
    obtain ⟨remainder, reconstruction, _, _, held, _, _⟩ := post
    have observed : Holds
        (run .gnuC23 .gnuModulo (bindings q q dRef) 11
          (start (code two) aliasedInitial)).state q one := by
      rfl
    have sameObject := Option.some.inj (held.symm.trans observed)
    have sameValue := congrArg (fun object : Object Target.int32 =>
      object.value.map (fun value => value.toInt)) sameObject
    change some (remainder.val : Int) = some (one.val : Int) at sameValue
    have numeric : remainder.val = one.val := Int.ofNat.inj (Option.some.inj sameValue)
    have same : remainder = one := Fin.ext numeric
    subst remainder
    change 2 = 2 * 1 + 1 at reconstruction
    omega

private def sentinel : Object Target.int32 :=
  ⟨.uint, .ended, true, some seven, 29, ⟨false, false⟩⟩

/-- Both work cells are genuinely uninitialized; d is readable but not
writable; a foreign ended object exercises preservation of arbitrary metadata.
The fresh identity, world and remaining automatic capacity are also nonzero. -/
private def readonlyInitial : State Target.int32 [] Nat where
  inputs := .nil
  environment := 41
  actor := 7
  next := 10
  automaticSlots := 4
  objects := fun id =>
    if id = 0 then some (cell _ 7 none)
    else if id = 1 then some (cell _ 7 none)
    else if id = 2 then some {
      kind := .uint, life := .live, reached := true, value := some three,
      owner := 7, permissions := ⟨true, false⟩ }
    else if id = 3 then some sentinel else none

private theorem readonly_admitted : Admission q r dRef three readonlyInitial := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨none, rfl⟩, ⟨none, rfl⟩, ⟨⟨true, false⟩, rfl, rfl⟩, by decide +kernel⟩

/-- A useful consumer of the universal certificate: both dialects/policies
finish 7/3 with independently determined quotient 2 and remainder 1 despite
uninitialized old work cells and a read-only denominator. All prefixes exclude
every stop, and a foreign tombstone plus the complete caller world survive. -/
theorem readonly_division_preserves_caller
    (dialect : Dialect) (policy : IntegerConversionPolicy) :
    NoFailure dialect policy (bindings q r dRef) (start (code seven) readonlyInitial) ∧
    ∃ steps result,
      (run dialect policy (bindings q r dRef) steps (start (code seven) readonlyInitial)).status =
        .returned result ∧ result.val = 2 ∧
      Holds (run dialect policy (bindings q r dRef) steps (start (code seven) readonlyInitial)).state r one ∧
      (run dialect policy (bindings q r dRef) steps (start (code seven) readonlyInitial)).state.objects 3 =
        some sentinel ∧
      WorldFrame readonlyInitial
        (run dialect policy (bindings q r dRef) steps (start (code seven) readonlyInitial)).state := by
  have correct := verified (parameters := []) (Environment := Nat)
    dialect policy seven three q r dRef
  refine ⟨correct.noFailure readonlyInitial readonly_admitted, ?_⟩
  obtain ⟨steps, result, returned, remainder, reconstruction, bounded, hq, hr, hd, frame⟩ :=
    correct readonlyInitial readonly_admitted
  have arithmetic : result.val = 2 ∧ remainder.val = 1 := by
    change 7 = 3 * result.val + remainder.val at reconstruction
    change remainder.val < 3 at bounded
    omega
  have remainderIsOne : remainder = one := Fin.ext arithmetic.2
  refine ⟨steps, result, returned, arithmetic.1, ?_, ?_, frame.world⟩
  · simpa only [remainderIsOne] using hr
  · exact (frame.outside 3 (by decide +kernel) (by decide +kernel)).trans rfl

end EDSL.Source.Objects.Control.Division.Checks
