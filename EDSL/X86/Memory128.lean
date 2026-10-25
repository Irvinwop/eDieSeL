/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory64
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

namespace EDSL.X86

/-- Two little-endian qword lanes, low addresses first. -/
def joinOWord (low high : Word) : BitVec 128 :=
  low.setWidth 128 ||| (high.setWidth 128 <<< 64)

/-- A functional ordinary-RAM read, using the existing DATA fault profile.
This primitive provides no interleaving, atomicity or SIMD instruction claim. -/
def loadOWord (memory : Memory) (address : Word) : Except Error (BitVec 128) := do
  if address.toNat + 15 ≥ 2^64 then throw (.inaccessibleData address)
  let low ← loadQWord memory address
  let high ← loadQWord memory (address + 8)
  return joinOWord low high

/-- All sixteen bytes are preflighted in the original memory. No wrapped or
noncanonical byte, absent mapping or denied write is accepted. -/
def canStoreOWord (memory : Memory) (address : Word) : Bool :=
  decide (address.toNat + 15 < 2^64) &&
    canStoreQWord memory address && canStoreQWord memory (address + 8)

/-- Functional byte updates only; neither qword nor whole-vector visibility is
inferred from this composition. An interleaving model needs separate rules. -/
def writeOWordUnchecked (memory : Memory) (address : Word) (value : BitVec 128) : Memory :=
  writeQWordUnchecked
    (writeQWordUnchecked memory address (value.extractLsb' 0 64))
    (address + 8) (value.extractLsb' 64 64)

def storeOWord (memory : Memory) (address : Word) (value : BitVec 128) : Except Error Memory :=
  if canStoreOWord memory address then .ok (writeOWordUnchecked memory address value)
  else .error (.writeDenied address)

theorem oword_join_extracts (value : BitVec 128) :
    joinOWord (value.extractLsb' 0 64) (value.extractLsb' 64 64) = value := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i inside
  by_cases low : i < 64
  · simp [joinOWord, low, inside]
  · simp [joinOWord, low, inside, show i - 64 < 64 by omega,
      show 64 + (i - 64) = i by omega]

private theorem oword_halves_disjoint (address : Word) :
    QWordDisjoint (address + 8) address 8 := by
  intro offset inside
  have small : offset < 2^64 := by omega
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  bv_omega

theorem writeOWord_preserves_permissions (memory : Memory) (address : Word)
    (value : BitVec 128) :
    (writeOWordUnchecked memory address value).executable = memory.executable ∧
    (writeOWordUnchecked memory address value).writable = memory.writable := by
  exact ⟨rfl, rfl⟩

/-- All bytes outside the sixteen-byte footprint retain their original values. -/
theorem writeOWord_frame (memory : Memory) (address query : Word) (value : BitVec 128)
    (outside : 16 ≤ (query - address).toNat) :
    (writeOWordUnchecked memory address value).read query = memory.read query := by
  have highOutside : 8 ≤ (query - (address + 8)).toNat := by bv_omega
  unfold writeOWordUnchecked
  rw [writeQWord_frame _ _ _ _ highOutside,
    writeQWord_frame _ _ _ _ (by omega)]

theorem oword_load_after_write (memory : Memory) (address : Word) (value : BitVec 128)
    (noWrap : address.toNat + 15 < 2^64)
    (lowCanonical : qwordAddressable address = true)
    (highCanonical : qwordAddressable (address + 8) = true) :
    loadOWord (writeOWordUnchecked memory address value) address = .ok value := by
  have lowRead := loadQWord_congr
    (writeOWordUnchecked memory address value)
    (writeQWordUnchecked memory address (value.extractLsb' 0 64)) address
    (writeQWord_agrees _ (address + 8) address (value.extractLsb' 64 64) 8
      (oword_halves_disjoint address))
  unfold loadOWord
  rw [ite_eq_right (by omega), lowRead,
    qword_load_after_write memory address (value.extractLsb' 0 64) lowCanonical]
  simp only [ok_bind]
  rw [writeOWordUnchecked, qword_load_after_write _ _ _ highCanonical]
  simp only [ok_bind, pure_ok, oword_join_extracts]

theorem oword_store_sound (memory : Memory) (address : Word) (value : BitVec 128)
    (allowed : canStoreOWord memory address = true) :
    storeOWord memory address value = .ok (writeOWordUnchecked memory address value) ∧
    loadOWord (writeOWordUnchecked memory address value) address = .ok value := by
  have parts := Bool.and_eq_true_iff.mp allowed
  have low := Bool.and_eq_true_iff.mp parts.1
  exact ⟨by simp only [storeOWord, allowed, ↓reduceIte],
    oword_load_after_write memory address value (of_decide_eq_true low.1)
      (Bool.and_eq_true_iff.mp low.2).1 (Bool.and_eq_true_iff.mp parts.2).1⟩

#print axioms oword_join_extracts
#print axioms writeOWord_frame
#print axioms oword_load_after_write
#print axioms oword_store_sound
end EDSL.X86
#audit_edsl
