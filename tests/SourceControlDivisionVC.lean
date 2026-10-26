/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Objects.Control.StructuredVC
import EDSL.Source.Objects.Control.Division

set_option autoImplicit false
namespace EDSL.Source.Objects.Control.StructuredVC.DivisionValidation
open StateSyntax Protocol
attribute [local implicit_reducible] Value Target.modulus

variable {target : Target} {parameters : List IntType} {Environment : Type}
variable (dialect : Dialect) (policy : IntegerConversionPolicy)

/- Reuse the old client's *local* arithmetic, expression and object lemmas.
No old control-run, progress, return or certificate theorem is used here.
The mathematical postcondition and caller frame are the existing independent
division specification. There is no tick/perform/run unfolding in this client.
-/
private def invariant (n d : Value target .uint) (q r dRef : LValue .uint)
    (original : State target parameters Environment) : Assertion target parameters Environment :=
  fun state _ => ∃ qv rv, Division.Frame q r original state ∧ Division.Holds state q qv ∧ Division.Holds state r rv ∧
    CanLoad state dRef d ∧ Division.Invariant n d qv rv

private def annotation (n d : Value target .uint) (q r dRef : LValue .uint)
    (original : State target parameters Environment) : Annotation (parameters := parameters)
      (Environment := Environment) (.seq (Division.loop target) (.ret (.param Division.qVar))) :=
  .seq (.loop (invariant n d q r dRef original)
    (fun state events => Division.rank r (Division.header state events)) (.seq .assign .assign)) .ret

theorem loop_segment (n d : Value target .uint) (q r dRef : LValue .uint)
    (qr : q.id ≠ r.id) (qd : q.id ≠ dRef.id) (rd : r.id ≠ dRef.id) (positive : 0 < d.val)
    (original state : State target parameters Environment) (earlier : List Event)
    (qv rv : Value target .uint) (frame : Division.Frame q r original state)
    (hq : Division.Holds state q qv) (hr : Division.Holds state r rv) (hd : CanLoad state dRef d)
    (reconstruction : Division.Invariant n d qv rv) :
    Segment dialect policy (Division.bindings q r dRef) (.seq (Division.loop target) (.ret (.param Division.qVar)))
      (fun _ _ => False) (fun value final events => Division.Post n d q r dRef original value final events)
      state earlier := by
  apply vc_sound dialect policy (Division.bindings q r dRef) (annotation n d q r dRef original)
  change invariant n d q r dRef original state earlier ∧ _
  refine ⟨⟨qv, rv, frame, hq, hr, hd, reconstruction⟩, ?_⟩
  intro current history member
  obtain ⟨qNow, rNow, callerFrame, heldQ, heldR, readD, numeric⟩ := member
  apply (expression_iff dialect policy (Division.bindings q r dRef) (Division.condition target) _ current history).mpr
  refine ⟨compareValues .ge rNow d, current,
    [.read r.id .uint rNow.toInt, .read dRef.id .uint d.toInt],
    Division.eval_condition dialect policy q r dRef current rNow d heldR readD, ?_⟩
  by_cases guard : d.val ≤ rNow.val
  · have nonzero : (compareValues .ge rNow d).toInt ≠ 0 :=
      (compareValues_nonzero_iff .ge rNow d).mpr (Int.ofNat_le.mpr guard)
    simp only [nonzero, ↓reduceIte]
    obtain ⟨fits, decreases, preserved⟩ := Division.iteration_arithmetic n d qNow rNow positive numeric guard
    let rNext := Division.subValue rNow d
    let qNext := Division.succValue qNow fits
    let middle := Division.put current r rNext
    let final := Division.put middle q qNext
    have middleQ : Division.Holds middle q qNow := Division.put_holds_other current r q rNext qNow qr heldQ
    have finalQ : Division.Holds final q qNext := Division.put_holds middle q qNext
    have finalR : Division.Holds final r rNext :=
      Division.put_holds_other middle q r qNext rNext (Ne.symm qr) (Division.put_holds current r rNext)
    have finalD : CanLoad final dRef d :=
      Division.put_canLoad_other middle q dRef qNext d (Ne.symm qd)
        (Division.put_canLoad_other current r dRef rNext d (Ne.symm rd) readD)
    have finalFrame : Division.Frame q r original final :=
      callerFrame.trans ((Division.put_frame q r r current rNext (Or.inr rfl)).trans
        (Division.put_frame q r q middle qNext (Or.inl rfl)))
    change expression policy (Division.bindings q r dRef) (.usub (.param Division.rVar) (.param Division.dVar)) _ current _
    apply (expression_iff dialect policy (Division.bindings q r dRef) _ _ current _).mpr
    refine ⟨rNext, current, [.read r.id .uint rNow.toInt, .read dRef.id .uint d.toInt],
      Division.eval_subtract dialect policy q r dRef current rNow d heldR readD guard, ?_⟩
    apply (write_iff r rNext _ current _).mpr
    apply (wp_iff _ _ _).mpr
    refine ⟨(), middle, [.write r.id .uint rNext.toInt],
      Division.store_ready current r rNext (Division.holds_ready current r rNow heldR), ?_⟩
    change expression policy (Division.bindings q r dRef)
      (.uadd (.param Division.qVar) (.literal (Division.one target))) _ middle _
    apply (expression_iff dialect policy (Division.bindings q r dRef) _ _ middle _).mpr
    refine ⟨qNext, middle, [.read q.id .uint qNow.toInt],
      Division.eval_increment dialect policy q r dRef middle qNow middleQ fits, ?_⟩
    apply (write_iff q qNext _ middle _).mpr
    apply (wp_iff _ _ _).mpr
    refine ⟨(), final, [.write q.id .uint qNext.toInt],
      Division.store_ready middle q qNext (Division.holds_ready middle q qNow middleQ), ?_⟩
    refine ⟨⟨qNext, rNext, finalFrame, finalQ, finalR, finalD, preserved⟩, ?_⟩
    rw [Division.rank_header r final _ rNext finalR, Division.rank_header r current _ rNow heldR]
    exact decreases
  · have zero : (compareValues .ge rNow d).toInt = 0 := by
      apply (compareValues_zero_iff .ge rNow d).mpr
      change ¬(d.val : Int) ≤ (rNow.val : Int)
      omega
    simp only [zero, ↓reduceIte]
    change expression policy (Division.bindings q r dRef) (.param Division.qVar) _ current _
    apply (expression_iff dialect policy (Division.bindings q r dRef) _ _ current _).mpr
    refine ⟨qNow, current, [.read q.id .uint qNow.toInt],
      Division.eval_var dialect policy q r dRef Division.qVar current qNow (Division.holds_load current q qNow heldQ), ?_⟩
    exact ⟨rNow, numeric, by omega, heldQ, heldR, readD, callerFrame⟩

end EDSL.Source.Objects.Control.StructuredVC.DivisionValidation
