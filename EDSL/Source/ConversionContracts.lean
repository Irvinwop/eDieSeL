/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.ArithmeticConversions
import EDSL.Source.VCGen
import EDSL.Source.Examples
import EDSL.Source.Division

set_option autoImplicit false

namespace EDSL.Source.ConversionContracts

/-- An independent same-width representative equation. Both typed values
already carry their respective range bounds; no remainder operation occurs. -/
def UnsignedRepresentative {target : Target}
    (signed : Value target .sint) (unsigned : Value target .uint) : Prop :=
  ∃ carry : Nat, carry ≤ 1 ∧
    (unsigned.val : Int) = signed.val + (carry : Int) * (target.modulus : Int)

theorem signed_representative {target : Target} (value : Value target .sint) :
    UnsignedRepresentative value (IntegerConversions.signedToUnsigned value) := by
  by_cases nonnegative : 0 ≤ value.val
  · refine ⟨0, by omega, ?_⟩
    simpa using IntegerConversions.signedToUnsigned_of_nonnegative value nonnegative
  · refine ⟨1, by omega, ?_⟩
    simpa using IntegerConversions.signedToUnsigned_of_negative value (by omega)

theorem unsigned_representative {target : Target} (value : Value target .uint) :
    UnsignedRepresentative (IntegerConversions.unsignedToSigned value) value := by
  have representative := signed_representative (IntegerConversions.unsignedToSigned value)
  rwa [IntegerConversions.signedToUnsigned_unsignedToSigned] at representative

def signedZero (target : Target) : Value target .sint :=
  ⟨0, by have positive := target.signedBound_pos; omega⟩

def toUnsigned (target : Target) (dialect : Dialect) : Program target [.sint] .uint :=
  ⟨dialect, .gnuModulo, .convert .uint (.param .here)⟩

def toSigned (target : Target) (dialect : Dialect) : Program target [.uint] .sint :=
  ⟨dialect, .gnuModulo, .convert .sint (.param .here)⟩

/-- The client supplies arithmetic conditions to the reusable VC generator,
without proving another execution-soundness theorem. -/
theorem toUnsigned_certificate (target : Target) (dialect : Dialect) :
    Certificate (toUnsigned target dialect) (fun _ => True)
      (fun inputs result => UnsignedRepresentative (inputs.get .here) result) := by
  refine certificate_of_vc ⟨.cons (signedZero target) .nil, trivial⟩ ?_
  intro inputs _
  change UnsignedRepresentative (inputs.get .here)
    (IntegerConversions.signedToUnsigned (inputs.get .here))
  exact signed_representative _

theorem toSigned_certificate (target : Target) (dialect : Dialect) :
    Certificate (toSigned target dialect) (fun _ => True)
      (fun inputs result => UnsignedRepresentative result (inputs.get .here)) := by
  refine certificate_of_vc ⟨.cons (Division.zero target) .nil, trivial⟩ ?_
  intro inputs _
  change UnsignedRepresentative (IntegerConversions.unsignedToSigned (inputs.get .here))
    (inputs.get .here)
  exact unsigned_representative _

def roundTrip (target : Target) (dialect : Dialect) : Program target [.sint] .sint :=
  ⟨dialect, .gnuModulo, .convert .sint (.convert .uint (.param .here))⟩

theorem roundTrip_certificate (target : Target) (dialect : Dialect) :
    Certificate (roundTrip target dialect) (fun _ => True)
      (fun inputs result => result = inputs.get .here) := by
  refine certificate_of_vc ⟨.cons (signedZero target) .nil, trivial⟩ ?_
  intro inputs _
  change IntegerConversions.unsignedToSigned
    (IntegerConversions.signedToUnsigned (inputs.get .here)) = inputs.get .here
  exact IntegerConversions.unsignedToSigned_signedToUnsigned _

/-- Independent carry equations on the original mathematical operands. Neither
conversion helpers nor the evaluator appear in the result specification. -/
def MixedSum {target : Target} (left : Value target .sint)
    (right result : Value target .uint) : Prop :=
  ∃ representativeCarry sumCarry : Nat,
    representativeCarry ≤ 1 ∧ sumCarry ≤ 1 ∧
    (result.val : Int) + (sumCarry : Int) * (target.modulus : Int) =
      left.val + (right.val : Int) + (representativeCarry : Int) * (target.modulus : Int)

def mixedAdd (target : Target) (dialect : Dialect) : Program target [.sint, .uint] .uint :=
  ⟨dialect, .gnuModulo, Expr.usualAdd (.param .here) (.param (.there .here))⟩

theorem mixedAdd_verified (target : Target) (dialect : Dialect) :
    Verifies (mixedAdd target dialect) (fun _ => True)
      (fun inputs result => MixedSum (inputs.get .here) (inputs.get (.there .here)) result) := by
  intro inputs _
  let left := inputs.get .here
  let right := inputs.get (.there .here)
  let representative := IntegerConversions.signedToUnsigned left
  let converted : Inputs target [.uint, .uint] := .cons representative (.cons right .nil)
  obtain ⟨result, execution, sumCarry, sumBound, sumEquation⟩ :=
    Examples.add_verified target dialect converted trivial
  obtain ⟨representativeCarry, representativeBound, representativeEquation⟩ :=
    signed_representative left
  refine ⟨result, execution, representativeCarry, sumCarry,
    representativeBound, sumBound, ?_⟩
  have integerSum := congrArg (fun n : Nat => (n : Int)) sumEquation
  simp only [Int.natCast_add, Int.natCast_mul] at integerSum
  change (result.val : Int) + (sumCarry : Int) * (target.modulus : Int) =
    (representative.val : Int) + (right.val : Int) at integerSum
  change (representative.val : Int) =
    left.val + (representativeCarry : Int) * (target.modulus : Int) at representativeEquation
  change (result.val : Int) + (sumCarry : Int) * (target.modulus : Int) =
    left.val + (right.val : Int) + (representativeCarry : Int) * (target.modulus : Int)
  omega

theorem mixedAdd_certificate (target : Target) (dialect : Dialect) :
    Certificate (mixedAdd target dialect) (fun _ => True)
      (fun inputs result => MixedSum (inputs.get .here) (inputs.get (.there .here)) result) where
  useful := ⟨.cons (signedZero target) (.cons (Division.zero target) .nil), trivial⟩
  verified := mixedAdd_verified target dialect

/-- Division is specified using a bounded representative satisfying an
independent carry equation, then a quotient interval without division. -/
def MixedQuotient {target : Target} (left : Value target .sint)
    (right result : Value target .uint) : Prop :=
  ∃ representative : Value target .uint,
    UnsignedRepresentative left representative ∧
      Division.QuotientInterval target representative right result

def NonzeroDenominator {target : Target} (inputs : Inputs target [.sint, .uint]) : Prop :=
  (inputs.get (.there .here)).val ≠ 0

def mixedDiv (target : Target) (dialect : Dialect) : Program target [.sint, .uint] .uint :=
  ⟨dialect, .gnuModulo, Expr.usualDiv (.param .here) (.param (.there .here))⟩

theorem mixedDiv_verified (target : Target) (dialect : Dialect) :
    Verifies (mixedDiv target dialect) NonzeroDenominator
      (fun inputs result => MixedQuotient (inputs.get .here) (inputs.get (.there .here)) result) := by
  intro inputs permitted
  let left := inputs.get .here
  let right := inputs.get (.there .here)
  let representative := IntegerConversions.signedToUnsigned left
  let converted : Inputs target [.uint, .uint] := .cons representative (.cons right .nil)
  obtain ⟨result, execution, interval⟩ :=
    Division.quotient_verified target dialect converted permitted
  exact ⟨result, execution, representative, signed_representative left, interval⟩

theorem mixedDiv_certificate (target : Target) (dialect : Dialect) :
    Certificate (mixedDiv target dialect) NonzeroDenominator
      (fun inputs result => MixedQuotient (inputs.get .here) (inputs.get (.there .here)) result) where
  useful := ⟨.cons (signedZero target) (.cons (Division.one target) .nil), by
    change (1 : Nat) ≠ 0
    omega⟩
  verified := mixedDiv_verified target dialect

/- Definedness is derived from the actual source contract proofs. -/
theorem toUnsigned_noUB (target : Target) (dialect : Dialect) :
    NoUB (toUnsigned target dialect) (fun _ => True) :=
  (toUnsigned_certificate target dialect).noUB

theorem toSigned_noUB (target : Target) (dialect : Dialect) :
    NoUB (toSigned target dialect) (fun _ => True) :=
  (toSigned_certificate target dialect).noUB

theorem roundTrip_noUB (target : Target) (dialect : Dialect) :
    NoUB (roundTrip target dialect) (fun _ => True) :=
  (roundTrip_certificate target dialect).noUB

theorem mixedAdd_noUB (target : Target) (dialect : Dialect) :
    NoUB (mixedAdd target dialect) (fun _ => True) :=
  (mixedAdd_certificate target dialect).noUB

theorem mixedDiv_noUB (target : Target) (dialect : Dialect) :
    NoUB (mixedDiv target dialect) NonzeroDenominator :=
  (mixedDiv_certificate target dialect).noUB

end EDSL.Source.ConversionContracts
