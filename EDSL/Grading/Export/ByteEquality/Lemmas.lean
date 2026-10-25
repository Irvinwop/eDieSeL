/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Init.Data.List.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.Data.Nat.Lemmas

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Symbolic list algebra for untrusted byte-certificate producers. These facts
make equality and prefix-length obligations explicit. They authenticate no input
bytes and add no execution or environmental assumptions. When used in a packet,
absent helpers remain ordinary declarations checked by the independent kernel. -/
namespace EDSLGrader.Export.ByteEquality
universe u
variable {α : Type u}

theorem appendCongr (x y a b : List α) (hx : x = a) (hy : y = b) :
    List.append x y = List.append a b :=
  Eq.trans (congrArg (fun z : List α => List.append z y) hx)
    (congrArg (fun z : List α => List.append a z) hy)

theorem cutLeft (x y a b : List α) (hx : x = List.append a b) :
    List.append x y = List.append a (List.append b y) :=
  Eq.trans (congrArg (fun z : List α => List.append z y) hx)
    (List.append_assoc a b y)

theorem cutRight (x y a b : List α) (hy : y = List.append a b) :
    List.append x y = List.append (List.append x a) b :=
  Eq.trans (congrArg (fun z : List α => List.append x z) hy)
    (Eq.symm (List.append_assoc x a b))

theorem join (x y whole a b : List α)
    (hx : x = a) (hy : y = b) (cut : whole = List.append a b) :
    List.append x y = whole :=
  Eq.trans (appendCongr x y a b hx hy) (Eq.symm cut)

theorem flattenJoin (whole left right : List (List α)) (x y : List α)
    (cut : whole = List.append left right)
    (hx : List.flatten left = x) (hy : List.flatten right = y) :
    List.flatten whole = List.append x y :=
  Eq.trans
    (congrArg (fun z : List (List α) => List.flatten z) cut)
    (Eq.trans (List.flatten_append (L₁ := left) (L₂ := right))
      (appendCongr (List.flatten left) (List.flatten right) x y hx hy))

/-- An outer-list context with one symbolic tail. It records flattened prefix
bytes without traversing those bytes during the symbolic proof. -/
abbrev Run (F : List (List α) → List (List α)) (r : List α) : Prop :=
  ∀ tail, List.flatten (F tail) = List.append r (List.flatten tail)

theorem emptyRun : Run (fun tail : List (List α) => tail) [] :=
  fun tail => Eq.symm (List.nil_append (List.flatten tail))

theorem oneRun (b : List α) :
    Run (fun tail : List (List α) => b :: tail) b :=
  fun _ => List.flatten_cons

theorem consRun (F : List (List α) → List (List α)) (b r : List α)
    (h : Run F r) :
    Run (fun tail => b :: F tail) (List.append b r) :=
  fun tail => Eq.trans List.flatten_cons
    (Eq.trans (congrArg (fun z : List α => List.append b z) (h tail))
      (Eq.symm (List.append_assoc b r (List.flatten tail))))

theorem spliceRun (F G : List (List α) → List (List α)) (x y : List α)
    (hf : Run F x) (hg : Run G y) :
    Run (fun tail => let t := G tail; F t) (List.append x y) :=
  fun tail => Eq.trans (hf (G tail))
    (Eq.trans (congrArg (fun z : List α => List.append x z) (hg tail))
      (Eq.symm (List.append_assoc x y (List.flatten tail))))

theorem closeRun (F : List (List α) → List (List α)) (r : List α)
    (h : Run F r) : List.flatten (F []) = r :=
  Eq.trans (h [])
    (Eq.trans (congrArg (fun z : List α => List.append r z) List.flatten_nil)
      (List.append_nil r))

/-- Compose exact endpoint exposure and an internal equality certificate. -/
theorem finish (q qp rp flat : List α)
    (hq : q = qp) (ha : qp = rp) (hc : flat = rp) : q = flat :=
  Eq.trans hq (Eq.trans ha (Eq.symm hc))

theorem lengthFromBridge (file : List α) (chunks : List (List α)) (n : Nat)
    (equal : file = List.flatten chunks)
    (length : (List.flatten chunks).length = n) : file.length = n :=
  Eq.trans (congrArg List.length equal) length

/-- Split at an arbitrary chunk boundary using explicit file equality. -/
theorem splitAtChunks (file : List α) (chunks : List (List α)) (q : Nat)
    (equal : file = List.flatten chunks) :
    file = List.append (List.flatten (List.take q chunks))
      (List.flatten (List.drop q chunks)) :=
  Eq.trans equal
    (Eq.trans
      (congrArg List.flatten (Eq.symm (List.take_append_drop q chunks)))
      (List.flatten_append (L₁ := List.take q chunks) (L₂ := List.drop q chunks)))

/-- Normalize an arbitrary offset using checked file equality, prefix length and
index decomposition. Nonuniform chunk layouts are allowed. -/
theorem dropAtChunks (file : List α) (chunks : List (List α))
    (n q r bytesBefore : Nat)
    (equal : file = List.flatten chunks)
    (prefixLength : (List.flatten (List.take q chunks)).length = bytesBefore)
    (index : n = bytesBefore + r) :
    List.drop n file = List.drop r (List.flatten (List.drop q chunks)) := by
  let front := List.flatten (List.take q chunks)
  let back := List.flatten (List.drop q chunks)
  have offset : n = front.length + r :=
    Eq.trans index (congrArg (fun k : Nat => k + r) (Eq.symm prefixLength))
  exact Eq.trans (congrArg (List.drop n) (splitAtChunks file chunks q equal))
    (Eq.trans (congrArg (fun k : Nat => List.drop k (List.append front back)) offset)
      (List.drop_length_add_append (l₁ := front) (l₂ := back) r))

/-- Quotient/remainder convenience form. The checked prefix-length obligation
remains explicit; no comparison of whole-file representations is implicit. -/
theorem dropAt (file : List α) (chunks : List (List α)) (n width : Nat)
    (equal : file = List.flatten chunks)
    (prefixLength : (List.flatten (List.take (n / width) chunks)).length =
      n / width * width) :
    List.drop n file = List.drop (n % width) (List.flatten (List.drop (n / width) chunks)) :=
  dropAtChunks file chunks n (n / width) (n % width) (n / width * width)
    equal prefixLength (Eq.symm (Nat.div_add_mod' n width))

#print axioms appendCongr
#print axioms cutLeft
#print axioms cutRight
#print axioms join
#print axioms flattenJoin
#print axioms emptyRun
#print axioms oneRun
#print axioms consRun
#print axioms spliceRun
#print axioms closeRun
#print axioms finish
#print axioms lengthFromBridge
#print axioms splitAtChunks
#print axioms dropAtChunks
#print axioms dropAt
end EDSLGrader.Export.ByteEquality
