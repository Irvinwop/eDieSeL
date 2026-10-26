/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.IntegerArithmetic
import EDSL.Source.ArithmeticConversions
import EDSL.Source.Division
import EDSL.Source.PromotionContracts

set_option autoImplicit false

namespace EDSL.Source.ArithmeticContracts

/-- One client syntax constructor for every unsigned arithmetic operation. -/
def unsignedReturn (target : Target) (dialect : Dialect) (operation : ArithmeticOp) :
    Program target [.uint, .uint] .uint :=
  ⟨dialect, .gnuModulo, Expr.usualBinary operation (.param .here) (.param (.there .here))⟩

def UnsignedAdmission {target : Target} (operation : ArithmeticOp)
    (inputs : Inputs target [.uint, .uint]) : Prop :=
  match operation with
  | .div | .rem => (inputs.get (.there .here)).val ≠ 0
  | _ => True

/-- The result laws use independent arithmetic equations and intervals. -/
def UnsignedResult {target : Target} (operation : ArithmeticOp)
    (inputs : Inputs target [.uint, .uint]) (result : Value target .uint) : Prop :=
  match operation with
  | .add => ∃ carry : Nat, carry ≤ 1 ∧
      result.val + carry * target.modulus =
        (inputs.get .here).val + (inputs.get (.there .here)).val
  | .sub => IntegerArithmetic.UnsignedSubtraction target
      (inputs.get .here) (inputs.get (.there .here)) result
  | .mul => IntegerArithmetic.UnsignedMultiplication target
      (inputs.get .here) (inputs.get (.there .here)) result
  | .div => Division.QuotientInterval target
      (inputs.get .here) (inputs.get (.there .here)) result
  | .rem => IntegerArithmetic.UnsignedRemainder target
      (inputs.get .here) (inputs.get (.there .here)) result

theorem unsignedReturn_verified (target : Target) (dialect : Dialect)
    (operation : ArithmeticOp) :
    Verifies (unsignedReturn target dialect operation) (UnsignedAdmission operation)
      (UnsignedResult operation) := by
  intro inputs admitted
  cases operation with
  | add => exact Examples.add_verified target dialect inputs admitted
  | sub =>
      exact IntegerArithmetic.unsignedSub_spec target
        (inputs.get .here) (inputs.get (.there .here))
  | mul =>
      exact IntegerArithmetic.unsignedMul_spec target
        (inputs.get .here) (inputs.get (.there .here))
  | div => exact Division.quotient_verified target dialect inputs admitted
  | rem =>
      exact IntegerArithmetic.unsignedRem_spec target
        (inputs.get .here) (inputs.get (.there .here)) admitted

theorem unsignedReturn_certificate (target : Target) (dialect : Dialect)
    (operation : ArithmeticOp) :
    Certificate (unsignedReturn target dialect operation) (UnsignedAdmission operation)
      (UnsignedResult operation) where
  useful := ⟨.cons (Division.zero target) (.cons (Division.one target) .nil), by
    cases operation <;> first | trivial | (change (1 : Nat) ≠ 0; omega)⟩
  verified := unsignedReturn_verified target dialect operation

theorem unsignedReturn_noUB (target : Target) (dialect : Dialect)
    (operation : ArithmeticOp) :
    NoUB (unsignedReturn target dialect operation) (UnsignedAdmission operation) :=
  (unsignedReturn_certificate target dialect operation).noUB

/-- Signed arithmetic retains the same promoted construction and evaluator. -/
def signedReturn (target : Target) (dialect : Dialect) (operation : ArithmeticOp) :
    Program target [.sint, .sint] .sint :=
  ⟨dialect, .gnuModulo, Expr.usualBinary operation (.param .here) (.param (.there .here))⟩

/-- Numeric preconditions are separate from source execution and NoUB. Clients
must discharge them on their intended input domain; they are not compiler flags. -/
def SignedAdmission {target : Target} (operation : ArithmeticOp)
    (inputs : Inputs target [.sint, .sint]) : Prop :=
  let x := (inputs.get .here).val
  let y := (inputs.get (.there .here)).val
  match operation with
  | .add => IntegerArithmetic.SignedRange target (x + y)
  | .sub => IntegerArithmetic.SignedRange target (x - y)
  | .mul => IntegerArithmetic.SignedRange target (x * y)
  | .div | .rem => y ≠ 0 ∧ ¬ IntegerArithmetic.DivisionOverflowPair
      (inputs.get .here) (inputs.get (.there .here))

def SignedResult {target : Target} (operation : ArithmeticOp)
    (inputs : Inputs target [.sint, .sint]) (result : Value target .sint) : Prop :=
  match operation with
  | .add => result.val = (inputs.get .here).val + (inputs.get (.there .here)).val
  | .sub => IntegerArithmetic.SignedSubtraction
      (inputs.get .here) (inputs.get (.there .here)) result
  | .mul => IntegerArithmetic.SignedMultiplication
      (inputs.get .here) (inputs.get (.there .here)) result
  | .div => ∃ remainder : Int, IntegerArithmetic.TruncatingDivision
      (inputs.get .here).val (inputs.get (.there .here)).val result.val remainder
  | .rem => IntegerArithmetic.SignedRemainder
      (inputs.get .here) (inputs.get (.there .here)) result

theorem signedReturn_verified (target : Target) (dialect : Dialect)
    (operation : ArithmeticOp) :
    Verifies (signedReturn target dialect operation) (SignedAdmission operation)
      (SignedResult operation) := by
  intro inputs admitted
  cases operation with
  | add =>
      refine ⟨⟨(inputs.get .here).val + (inputs.get (.there .here)).val, admitted⟩, ?_, rfl⟩
      exact dite_eq_left admitted
  | sub =>
      exact IntegerArithmetic.signedSub_spec target
        (inputs.get .here) (inputs.get (.there .here)) admitted
  | mul =>
      exact IntegerArithmetic.signedMul_spec target
        (inputs.get .here) (inputs.get (.there .here)) admitted
  | div =>
      exact IntegerArithmetic.signedDiv_spec target
        (inputs.get .here) (inputs.get (.there .here)) admitted.1 admitted.2
  | rem =>
      exact IntegerArithmetic.signedRem_spec target
        (inputs.get .here) (inputs.get (.there .here)) admitted.1 admitted.2

private def signedOne (target : Target) : Value target .sint :=
  ⟨1, by have minimum := IntegerArithmetic.signedBound_atLeast32768 target; omega⟩

theorem signedReturn_certificate (target : Target) (dialect : Dialect)
    (operation : ArithmeticOp) :
    Certificate (signedReturn target dialect operation) (SignedAdmission operation)
      (SignedResult operation) where
  useful := ⟨.cons (PromotionContracts.zeroValue target .sint) (.cons (signedOne target) .nil), by
    have minimum := IntegerArithmetic.signedBound_atLeast32768 target
    cases operation with
    | add => change -target.signedBound ≤ (0 : Int) + 1 ∧ 0 + 1 < target.signedBound; omega
    | sub => change -target.signedBound ≤ (0 : Int) - 1 ∧ 0 - 1 < target.signedBound; omega
    | mul => change -target.signedBound ≤ (0 : Int) * 1 ∧ 0 * 1 < target.signedBound; omega
    | div => change (1 : Int) ≠ 0 ∧ ¬ ((0 : Int) = -target.signedBound ∧ (1 : Int) = -1); omega
    | rem => change (1 : Int) ≠ 0 ∧ ¬ ((0 : Int) = -target.signedBound ∧ (1 : Int) = -1); omega⟩
  verified := signedReturn_verified target dialect operation

theorem signedReturn_noUB (target : Target) (dialect : Dialect)
    (operation : ArithmeticOp) :
    NoUB (signedReturn target dialect operation) (SignedAdmission operation) :=
  (signedReturn_certificate target dialect operation).noUB

/-- Nonzero alone is insufficient for a source remainder certificate: the
minimum / -1 pair still fails, for every admitted target and every postcondition. -/
theorem signedRem_nonzero_not_verified (target : Target) (dialect : Dialect)
    (post : Inputs target [.sint, .sint] → Value target .sint → Prop) :
    ¬ Verifies (signedReturn target dialect .rem)
      (fun inputs => (inputs.get (.there .here)).val ≠ 0) post := by
  intro verified
  have minimumBound := IntegerArithmetic.signedBound_atLeast32768 target
  let minimum : Value target .sint := ⟨-target.signedBound, by omega⟩
  let negativeOne : Value target .sint := ⟨-1, by omega⟩
  let inputs : Inputs target [.sint, .sint] := .cons minimum (.cons negativeOne .nil)
  obtain ⟨result, execution, _⟩ := verified inputs (by change (-1 : Int) ≠ 0; decide +kernel)
  change signedRem target minimum negativeOne = .defined result at execution
  rw [IntegerArithmetic.signedRem_min_neg_one target minimum negativeOne rfl rfl] at execution
  cases execution

theorem signedRem_nonzero_not_certified (target : Target) (dialect : Dialect)
    (post : Inputs target [.sint, .sint] → Value target .sint → Prop) :
    ¬ Certificate (signedReturn target dialect .rem)
      (fun inputs => (inputs.get (.there .here)).val ≠ 0) post := by
  intro certificate
  exact signedRem_nonzero_not_verified target dialect post certificate.verified

/-- Unsigned subtraction followed by addition recovers the original operand,
including cases where either intermediate operation wraps. -/
def subtractAdd (target : Target) (dialect : Dialect) :
    Program target [.uint, .uint] .uint :=
  ⟨dialect, .gnuModulo, Expr.usualAdd
    (Expr.usualSub (.param .here) (.param (.there .here))) (.param (.there .here))⟩

theorem subtractAdd_verified (target : Target) (dialect : Dialect) :
    Verifies (subtractAdd target dialect) (fun _ => True)
      (fun inputs result => result = inputs.get .here) := by
  intro inputs _
  let x := inputs.get .here
  let y := inputs.get (.there .here)
  obtain ⟨difference, subtraction, borrow, borrowBound, differenceEquation⟩ :=
    IntegerArithmetic.unsignedSub_spec target x y
  let operands : Inputs target [.uint, .uint] := .cons difference (.cons y .nil)
  obtain ⟨result, addition, carry, carryBound, sumEquation⟩ :=
    Examples.add_verified target dialect operands trivial
  refine ⟨result, ?_, ?_⟩
  · change (unsignedSub target x y).andThen
      (fun difference => unsignedAdd target difference y) = .defined result
    rw [subtraction]
    exact addition
  · apply Fin.ext
    have residue := congrArg (fun n : Nat => n % target.modulus) sumEquation
    change (result.val + carry * target.modulus) % target.modulus =
      (difference.val + y.val) % target.modulus at residue
    rw [differenceEquation] at residue
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.add_zero,
      Nat.mod_mod, Nat.zero_mod, Nat.mod_eq_of_lt result.isLt, Nat.mod_eq_of_lt x.isLt] using residue

theorem subtractAdd_certificate (target : Target) (dialect : Dialect) :
    Certificate (subtractAdd target dialect) (fun _ => True)
      (fun inputs result => result = inputs.get .here) where
  useful := ⟨.cons (Division.zero target) (.cons (Division.zero target) .nil), trivial⟩
  verified := subtractAdd_verified target dialect

theorem subtractAdd_noUB (target : Target) (dialect : Dialect) :
    NoUB (subtractAdd target dialect) (fun _ => True) :=
  (subtractAdd_certificate target dialect).noUB

/-- Char8 operands promote to int32 before multiplication. -/
def byteProduct (dialect : Dialect) :
    Program Target.int32 [.small .uchar, .small .uchar] .sint :=
  ⟨dialect, .gnuModulo, Expr.usualMul (.param .here) (.param (.there .here))⟩

/-- Overflow freedom follows from byte ranges, with no result-range assumption
on the admitted inputs. The result is their exact mathematical product. -/
theorem byteProduct_verified (dialect : Dialect) :
    Verifies (byteProduct dialect) (fun _ => True)
      (fun inputs result => result.toInt =
        (inputs.get .here).toInt * (inputs.get (.there .here)).toInt) := by
  intro inputs _
  let left := inputs.get .here
  let right := inputs.get (.there .here)
  let promotedLeft := IntegerPromotions.promoteValue left
  let promotedRight := IntegerPromotions.promoteValue right
  have leftValue : promotedLeft.val = left.toInt :=
    IntegerPromotions.promoteValue_toInt left
  have rightValue : promotedRight.val = right.toInt :=
    IntegerPromotions.promoteValue_toInt right
  have leftBounds := left.range
  have rightBounds := right.range
  change 0 ≤ left.toInt ∧ left.toInt < 256 at leftBounds
  change 0 ≤ right.toInt ∧ right.toInt < 256 at rightBounds
  have nonnegative : 0 ≤ left.toInt * right.toInt :=
    Int.mul_nonneg leftBounds.1 rightBounds.1
  have rightBound : left.toInt * right.toInt ≤ left.toInt * 255 :=
    Int.mul_le_mul_of_nonneg_left (by omega) leftBounds.1
  have leftBound : left.toInt * 255 ≤ (255 : Int) * 255 :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by decide +kernel)
  have fits : IntegerArithmetic.SignedRange Target.int32 (left.toInt * right.toInt) := by
    change -2147483648 ≤ left.toInt * right.toInt ∧ left.toInt * right.toInt < 2147483648
    omega
  let result : Value Target.int32 .sint := ⟨left.toInt * right.toInt, fits⟩
  have promotedFits : IntegerArithmetic.SignedRange Target.int32
      (promotedLeft.val * promotedRight.val) := by
    rw [leftValue, rightValue]
    exact fits
  have primitive := IntegerArithmetic.signedMul_defined Target.int32
    promotedLeft promotedRight promotedFits
  have execution := eval_primitiveBinary_defined .mul .sint .gnuModulo inputs
    (.convert .sint (.promote (.param .here)))
    (.convert .sint (.promote (.param (.there .here))))
    promotedLeft promotedRight ⟨promotedLeft.val * promotedRight.val, promotedFits⟩
    rfl rfl primitive
  have sameResult : (⟨promotedLeft.val * promotedRight.val, promotedFits⟩ :
      Value Target.int32 .sint) = result := by
    apply Subtype.ext
    change promotedLeft.val * promotedRight.val = left.toInt * right.toInt
    rw [leftValue, rightValue]
  exact ⟨result, execution.trans (congrArg Outcome.defined sameResult), rfl⟩

theorem byteProduct_certificate (dialect : Dialect) :
    Certificate (byteProduct dialect) (fun _ => True)
      (fun inputs result => result.toInt =
        (inputs.get .here).toInt * (inputs.get (.there .here)).toInt) where
  useful := ⟨.cons (PromotionContracts.zeroValue Target.int32 (.small .uchar))
    (.cons (PromotionContracts.zeroValue Target.int32 (.small .uchar)) .nil), trivial⟩
  verified := byteProduct_verified dialect

theorem byteProduct_noUB (dialect : Dialect) :
    NoUB (byteProduct dialect) (fun _ => True) :=
  (byteProduct_certificate dialect).noUB

end EDSL.Source.ArithmeticContracts
