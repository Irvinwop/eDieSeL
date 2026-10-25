/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Mutex.Facts

namespace EDSL.OS.Mutex
open X86 AddressSpace

theorem register_ok (state : State) (config : Config) (after : State)
    (valid : Borrowing.WellFormed state.shared) (success : register state config = .ok after) :
    state.mutex = none ∧ config.lockTicket.identifier ≠ config.dataTicket.identifier ∧
      WordValid state.shared config.owner config.lockTicket config.lockAddress ∧
      WordValid state.shared config.owner config.dataTicket config.dataAddress ∧
      atomicAddressable config.lockAddress = true ∧ NoReaders state.shared config ∧
      loadDWord (toMemory state.shared.resources.space) config.lockAddress = .ok 0 ∧
      Closed state.shared config ∧ after = { state with mutex := some ⟨config, none⟩ } := by
  unfold register at success
  cases present : state.mutex with
  | some record => simp [present] at success
  | none =>
    simp only [present, Option.isSome, Bool.false_eq_true, ↓reduceIte, pure_ok] at success
    by_cases sameId : config.lockTicket.identifier = config.dataTicket.identifier
    · simp [sameId] at success
    · simp only [sameId, ↓reduceIte] at success
      cases lockAuth : Ownership.authorize state.shared.resources config.owner config.lockTicket with
      | error fault => simp [lockAuth, Except.mapError] at success
      | ok lock =>
        simp only [lockAuth, Except.mapError, ok_bind] at success
        cases dataAuth : Ownership.authorize state.shared.resources config.owner config.dataTicket with
        | error fault => simp [dataAuth] at success
        | ok data =>
          simp only [dataAuth, ok_bind] at success
          by_cases lockFits : Ownership.containsWord lock config.lockAddress = true
          · simp only [lockFits, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success
            by_cases dataFits : Ownership.containsWord data config.dataAddress = true
            · simp only [dataFits, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success
              by_cases supported : atomicAddressable config.lockAddress = true
              · simp only [supported, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success
                by_cases lockWritable : canStoreDWord (toMemory state.shared.resources.space) config.lockAddress = true
                · simp only [lockWritable, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success
                  by_cases dataWritable : canStoreDWord (toMemory state.shared.resources.space) config.dataAddress = true
                  · simp only [dataWritable, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success
                    simp only [BitVec.ofNat_eq_ofNat] at success
                    by_cases lockLoans : Borrowing.allowed state.shared (.store config.owner config.lockTicket config.lockAddress 0) = true
                    · change Borrowing.allowed state.shared (.store config.owner config.lockTicket config.lockAddress (0#32)) = true at lockLoans
                      simp only [lockLoans, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success
                      by_cases dataLoans : Borrowing.allowed state.shared (.store config.owner config.dataTicket config.dataAddress 0) = true
                      · change Borrowing.allowed state.shared (.store config.owner config.dataTicket config.dataAddress (0#32)) = true at dataLoans
                        simp only [dataLoans, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success
                        cases lockRead : loadDWord (toMemory state.shared.resources.space) config.lockAddress with
                        | error fault => simp [lockRead] at success
                        | ok old =>
                          simp only [lockRead, ok_bind] at success
                          by_cases zero : old = 0
                          · change old = (0#32) at zero
                            simp only [zero, ne_eq, not_true_eq_false, ↓reduceIte] at success
                            cases dataRead : loadDWord (toMemory state.shared.resources.space) config.dataAddress with
                            | error fault => simp [dataRead] at success
                            | ok value =>
                              simp only [dataRead, ok_bind] at success
                              by_cases invariant : config.invariant value = true
                              · simp [invariant] at success
                                obtain ⟨lockAt, lockOwner, lockEpoch⟩ := Ownership.authorize_ok _ _ _ _ lockAuth
                                obtain ⟨dataAt, dataOwner, dataEpoch⟩ := Ownership.authorize_ok _ _ _ _ dataAuth
                                refine ⟨rfl, sameId, ⟨lock, lockAt, lockOwner, lockEpoch, lockFits, lockWritable⟩,
                                  ⟨data, dataAt, dataOwner, dataEpoch, dataFits, dataWritable⟩,
                                  supported, ?_, by simp only [zero, BitVec.ofNat_eq_ofNat],
                                  ⟨value, dataRead, invariant⟩, success.symm⟩
                                intro identifier loan live
                                constructor
                                · have excluded := Borrowing.allowed_sound _ _ valid lockLoans identifier loan live
                                  simpa [Ownership.Mutation.target, eq_comm] using excluded
                                · have excluded := Borrowing.allowed_sound _ _ valid dataLoans identifier loan live
                                  simpa [Ownership.Mutation.target, eq_comm] using excluded
                              · simp [invariant] at success
                          · change old ≠ (0#32) at zero
                            simp [zero] at success
                      · change ¬ Borrowing.allowed state.shared (.store config.owner config.dataTicket config.dataAddress (0#32)) = true at dataLoans
                        simp [dataLoans] at success
                    · change ¬ Borrowing.allowed state.shared (.store config.owner config.lockTicket config.lockAddress (0#32)) = true at lockLoans
                      simp [lockLoans] at success
                  · simp [dataWritable] at success
                · simp [lockWritable] at success
              · simp [supported] at success
            · simp [dataFits] at success
          · simp [lockFits] at success

theorem register_wellFormed (state : State) (config : Config) (after : State)
    (valid : WellFormed state) (success : register state config = .ok after) : WellFormed after := by
  obtain ⟨_, separate, lock, data, atomic, readers, observed, closed, same⟩ :=
    register_ok _ _ _ valid.1 success
  rw [same]
  refine ⟨valid.1, ?_⟩
  intro record live
  simp only [Option.some.injEq] at live
  cases live
  exact ⟨lock, data, separate, atomic, readers, observed, closed⟩

end EDSL.OS.Mutex
