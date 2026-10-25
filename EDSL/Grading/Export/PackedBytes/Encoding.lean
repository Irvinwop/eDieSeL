/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export.PackedBytes
import Init.Data.Nat.Lemmas

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Numeric certificates for exact little-endian byte regions.

Each region records both its byte count and its numeric encoding. Independent
append trees can therefore share a numeric specification without first reducing
their complete byte lists to compare them. The outer-list certificates below
also quantify over a symbolic tail, so composition need not reassociate or
flatten a concrete collection of chunks in the proof.

These are generic arithmetic and list contracts. They make no performance or
external-file authenticity claim. No environmental assumptions are needed.
-/
namespace EDSLGrader.Export.PackedBytes.Encoding

/-- The low `count` bytes remaining after discarding `offset` bytes of `word`.
The count is retained separately, including when high bytes are zero. -/
def rangeValue (word offset count : Nat) : Nat :=
  (word / 256 ^ offset) % 256 ^ count

/-- Adjacent numeric regions concatenate in little-endian order. No bound on
`word` and no positivity assumption on either byte count is required. -/
theorem rangeValue_append (word offset leftCount rightCount : Nat) :
    rangeValue word offset (leftCount + rightCount) =
      rangeValue word offset leftCount +
        256 ^ leftCount * rangeValue word (offset + leftCount) rightCount := by
  unfold rangeValue
  rw [Nat.pow_add 256 leftCount rightCount, Nat.mod_mul,
    Nat.div_div_eq_div_mul, ← Nat.pow_add 256 offset leftCount]

/-- Join numeric certificates for adjacent byte lists. Only the left length is
needed for this value equation; a complete equality certificate must also retain
the right length. All binders are explicit, in the producer-facing fixed order. -/
theorem encodeAppend (word offset leftCount rightCount : Nat)
    (left right : List (BitVec 8))
    (leftLength : left.length = leftCount)
    (leftEncoding : PackedBytes.natOfBytes left = rangeValue word offset leftCount)
    (rightEncoding : PackedBytes.natOfBytes right =
      rangeValue word (offset + leftCount) rightCount) :
    PackedBytes.natOfBytes (List.append left right) =
      rangeValue word offset (leftCount + rightCount) := by
  change PackedBytes.natOfBytes (left ++ right) =
    rangeValue word offset (leftCount + rightCount)
  rw [PackedBytes.natOfBytes_append, leftLength, leftEncoding, rightEncoding]
  exact (rangeValue_append word offset leftCount rightCount).symm

/-- An outer-list context certified for every chunk-list tail. The first
component records the exact additional byte count. The second records the
prefix value and the tail shifted by that count. Keeping both components is
necessary: numeric equality alone cannot distinguish trailing zero bytes.

No syntactic restriction is placed on `F`, and chunks may have arbitrary or
zero lengths. `tail` is the only binder introduced by the predicate. -/
def EncodedRun (word offset count : Nat)
    (F : List (List (BitVec 8)) → List (List (BitVec 8))) : Prop :=
  ∀ tail : List (List (BitVec 8)),
    (List.flatten (F tail)).length = count + (List.flatten tail).length ∧
      PackedBytes.natOfBytes (List.flatten (F tail)) =
        rangeValue word offset count +
          256 ^ count * PackedBytes.natOfBytes (List.flatten tail)

/-- The identity context adds zero bytes at any offset. -/
theorem emptyRun (word offset : Nat) :
    EncodedRun word offset 0 (fun tail => tail) := by
  intro tail
  constructor
  · exact (Nat.zero_add (List.flatten tail).length).symm
  · simp only [rangeValue, Nat.pow_zero, Nat.mod_one, Nat.one_mul, Nat.zero_add]

/-- Insert one chunk whose length and encoding are independently certified. -/
theorem oneRun (word offset count : Nat) (bytes : List (BitVec 8))
    (length : bytes.length = count)
    (encoding : PackedBytes.natOfBytes bytes = rangeValue word offset count) :
    EncodedRun word offset count (fun tail => bytes :: tail) := by
  intro tail
  constructor
  · rw [List.flatten_cons, List.length_append, length]
  · rw [List.flatten_cons, PackedBytes.natOfBytes_append, length, encoding]

/-- Compose contexts for adjacent ranges. `F` contributes the low region,
`G` contributes the following region, and the resulting context is `F (G tail)`.
Only the two run certificates and generic arithmetic are used. -/
theorem spliceRun (word offset leftCount rightCount : Nat)
    (F G : List (List (BitVec 8)) → List (List (BitVec 8)))
    (left : EncodedRun word offset leftCount F)
    (right : EncodedRun word (offset + leftCount) rightCount G) :
    EncodedRun word offset (leftCount + rightCount)
      (fun tail => let t := G tail; F t) := by
  intro tail
  have leftFacts := left (G tail)
  have rightFacts := right tail
  constructor
  · change (List.flatten (F (G tail))).length =
      (leftCount + rightCount) + (List.flatten tail).length
    rw [leftFacts.1, rightFacts.1, Nat.add_assoc]
  · change PackedBytes.natOfBytes (List.flatten (F (G tail))) =
      rangeValue word offset (leftCount + rightCount) +
        256 ^ (leftCount + rightCount) * PackedBytes.natOfBytes (List.flatten tail)
    rw [leftFacts.2, rightFacts.2, rangeValue_append word offset leftCount rightCount,
      Nat.pow_add 256 leftCount rightCount, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]

/-- Prefix a certified chunk to a context for the following region. This is
`spliceRun` with `oneRun`, retaining both lengths and the offset of the rest. -/
theorem consRun (word offset leftCount rightCount : Nat)
    (F : List (List (BitVec 8)) → List (List (BitVec 8)))
    (bytes : List (BitVec 8))
    (length : bytes.length = leftCount)
    (encoding : PackedBytes.natOfBytes bytes = rangeValue word offset leftCount)
    (rest : EncodedRun word (offset + leftCount) rightCount F) :
    EncodedRun word offset (leftCount + rightCount)
      (fun tail => bytes :: F tail) :=
  spliceRun word offset leftCount rightCount (fun tail => bytes :: tail) F
    (oneRun word offset leftCount bytes length encoding) rest

/-- Close a context with an empty outer tail. The two returned components are
the exact flattened length and the numeric encoding of the closed result. -/
theorem closeRun (word offset count : Nat)
    (F : List (List (BitVec 8)) → List (List (BitVec 8)))
    (run : EncodedRun word offset count F) :
    (List.flatten (F [])).length = count ∧
      PackedBytes.natOfBytes (List.flatten (F [])) = rangeValue word offset count := by
  have closed := run []
  simpa only [List.flatten_nil, List.length_nil, PackedBytes.natOfBytes,
    Nat.add_zero, Nat.mul_zero] using closed

/-- Two byte lists with the same certified count and numeric range are exactly
equal, regardless of their append associations. Length hypotheses are essential. -/
theorem eq_of_encoding (word offset count : Nat) (left right : List (BitVec 8))
    (leftLength : left.length = count) (rightLength : right.length = count)
    (leftEncoding : PackedBytes.natOfBytes left = rangeValue word offset count)
    (rightEncoding : PackedBytes.natOfBytes right = rangeValue word offset count) :
    left = right :=
  PackedBytes.eq_of_length_eq_of_natOfBytes_eq left right
    (Eq.trans leftLength rightLength.symm) (Eq.trans leftEncoding rightEncoding.symm)

/-- Bridge an independently certified byte quotation to a closed chunk context.
The quotation's exact count and value remain explicit obligations. -/
theorem closeRun_eq (word offset count : Nat) (bytes : List (BitVec 8))
    (F : List (List (BitVec 8)) → List (List (BitVec 8)))
    (length : bytes.length = count)
    (encoding : PackedBytes.natOfBytes bytes = rangeValue word offset count)
    (run : EncodedRun word offset count F) :
    bytes = List.flatten (F []) := by
  have closed := closeRun word offset count F run
  exact eq_of_encoding word offset count bytes (List.flatten (F []))
    length closed.1 encoding closed.2

#print axioms rangeValue
#print axioms rangeValue_append
#print axioms encodeAppend
#print axioms EncodedRun
#print axioms emptyRun
#print axioms oneRun
#print axioms spliceRun
#print axioms consRun
#print axioms closeRun
#print axioms eq_of_encoding
#print axioms closeRun_eq

end EDSLGrader.Export.PackedBytes.Encoding
