/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ByteQuotation
import Init.Data.List.Basic

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Pure, untrusted length-certificate construction for the existing byte
quotation. Returned expressions require independent kernel checking. These
source bounds do not promise admission under packet or runtime budgets; the
whole producer still needs its external process bound. Length alone does not
establish exact-file identity or provenance. -/
namespace EDSLGrader.Export.ByteLength
open Lean EDSL
universe u

/-- Symbolic append-length composition, with no environmental assumptions.
Export this as an ordinary checked theorem dependency, not a trusted root. -/
theorem appendLength {α : Type u} (xs ys : List α) (m n total : Nat)
    (hx : xs.length = m) (hy : ys.length = n)
    (sum : Nat.add m n = total) :
    (List.append xs ys).length = total :=
  Eq.trans (List.length_append (as := xs) (bs := ys))
    (Eq.trans (congrArg (fun k : Nat => Nat.add k ys.length) hx)
      (Eq.trans (congrArg (fun k : Nat => Nat.add m k) hy) sum))

#print axioms appendLength

/-- Syntax only: `claim` is `List.length Byte value = literalLength`.
Construction makes no typing claim. The kernel must check the claim and the
proof against it, or check the proof against the independently fixed target. -/
structure Candidate where
  value : Expr
  literalLength : Nat
  claim : Expr
  proof : Expr

private def byteType : Expr := toTypeExpr X86.Byte
private def natType : Expr := mkConst ``Nat

private def reflNat (n : Nat) : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) natType (mkRawNatLit n)

private def lengthClaim (value : Expr) (n : Nat) : Expr :=
  let len := mkApp2 (mkConst ``List.length [Level.zero]) byteType value
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) natType len (mkRawNatLit n)

private def candidate (value : Expr) (n : Nat) (proof : Expr) : Candidate :=
  { value, literalLength := n, claim := lengthClaim value n, proof }

-- Match the current quotation's exact constructor/type syntax. Byte heads are
-- retained without inspection; their typing remains the kernel's obligation.
private def appendParts? : Expr → Option (Expr × Expr)
  | .app (.app (.app (.const name [.zero]) elementType) xs) ys =>
      if name == ``List.append && Expr.equal elementType byteType then
        some (xs, ys)
      else none
  | _ => none

private def isNil : Expr → Bool
  | .app (.const name [.zero]) elementType =>
      name == ``List.nil && Expr.equal elementType byteType
  | _ => false

private def consTail? : Expr → Option Expr
  | .app (.app (.app (.const name [.zero]) elementType) _) tail =>
      if name == ``List.cons && Expr.equal elementType byteType then some tail else none
  | _ => none

private def leafCount : Nat → Nat → Expr → Except String Nat
  | 0, _, e =>
      if isNil e then pure 0 else .error "literal leaf exceeds bound or shape"
  | fuel + 1, maxBytes, e => do
      if isNil e then return 0
      let some tail := consTail? e | throw "literal leaf shape"
      if maxBytes == 0 then throw "byte count bound"
      let n ← leafCount fuel (maxBytes - 1) tail
      return n + 1

private def leaf (maxBytes : Nat) (e : Expr) : Except String Candidate := do
  let n ← leafCount 16 maxBytes e
  -- Checking this against the claim reduces only this short leaf's length.
  return candidate e n (reflNat n)

private def fromQuotationAux : Nat → Nat → Expr → Except String Candidate
  | 0, maxBytes, e =>
      match appendParts? e with
      | some _ => .error "quotation depth bound"
      | none => leaf maxBytes e
  | fuel + 1, maxBytes, e => do
      match appendParts? e with
      | none => leaf maxBytes e
      | some (xs, ys) =>
          let left ← fromQuotationAux fuel maxBytes xs
          let right ← fromQuotationAux fuel (maxBytes - left.literalLength) ys
          let n := left.literalLength + right.literalLength
          if n > maxBytes then throw "byte count bound"
          let proof := mkAppN (mkConst ``appendLength [Level.zero]) #[
            byteType, xs, ys,
            mkRawNatLit left.literalLength,
            mkRawNatLit right.literalLength,
            mkRawNatLit n,
            left.proof, right.proof, reflNat n]
          return candidate e n proof

/-- Recognize the actual prepared `byteExpr` value without rebuilding it.
`value` and every append subtree are retained exactly as supplied. At most 16
append edges per path and 16 cons cells per leaf are supported; total cons
count must be at most `maxBytes`. Other list forms, type syntax, and universes
are rejected. No term evaluation, type inference, or environment access occurs.
Success is neither typing evidence nor an admission decision. -/
def fromQuotation (maxBytes : Nat) (value : Expr) : Except String Candidate :=
  fromQuotationAux 16 maxBytes value

/-- Alias of `fromQuotation`, for callers holding an existing prepared Expr. -/
def fromExpr (maxBytes : Nat) (value : Expr) : Except String Candidate :=
  fromQuotation maxBytes value

private def boundedCount (maxBytes : Nat) (bytes : List X86.Byte) :
    Except String Nat := do
  let mut rest := bytes
  let mut count := 0
  for _ in [:maxBytes] do
    match rest with
    | [] => return count
    | _ :: tail =>
        rest := tail
        count := count + 1
  if !rest.isEmpty then throw "byte count bound"
  return count

/-- Quote once with the existing `byteExpr`, then construct length syntax for
that same Expr. Before quotation, count at most `min maxBytes 1048576` bytes:
`1048576 = 16 * 2^16` bounds the current quotation's all-short-leaf domain.
Larger inputs fail; there is no long-leaf reflexivity fallback. This source
bound is not measured packet, kernel, time, or memory acceptance. -/
def quoteWithLength (maxBytes : Nat) (bytes : List X86.Byte) :
    Except String Candidate := do
  let observedCount ← boundedCount (min maxBytes 1048576) bytes
  let value := EDSLGrader.byteExpr bytes
  let result ← fromQuotation maxBytes value
  if result.literalLength != observedCount then throw "quotation/count mismatch"
  return result

end EDSLGrader.Export.ByteLength
