/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import tests.RexData32Base
import tests.TSO64Fixtures
import tests.Support.ExceptDecidable
namespace EDSL.Tests.RexData32TSO
open X86 OS.TSO64
open scoped EDSL.Tests.Support
private theorem output_ok {ε α : Type} (x : Except ε α) (h : x.toOption.isSome = true) :
    x = .ok (x.toOption.get h) := by cases x <;> first | rfl | cases h
private instance errorDecision {ε α : Type} [DecidableEq ε]
    (x : Except ε α) (e : ε) : Decidable (x = .error e) :=
  match x with
  | .ok _ => isFalse (by intro same; cases same)
  | .error a => match decEq a e with
    | .isTrue h => isTrue (congrArg Except.error h)
    | .isFalse h => isFalse (by intro same; exact h (Except.error.inj same))
-- Owned synthetic code installed by the existing checked OS fixture:
-- MOV [RDX],ESI; MOV R9D,[R14]; RET; padding. No native execution here.
private def setup := TSO64.fixture 0x9090c30e8b453289 0x9090909090909090 19
private theorem present : setup.toOption.isSome = true := by decide +kernel
private def ready : TSO64.Ready := setup.toOption.get present
private def world : World := ready.checked.world
private def context (withoutGrant : Bool) : Context where
  registers r := if r = .rsp then 262144 else if r = .rdx ∨ r = .r14 then 131072
    else if r = .rsi then 0xdeadbeef92345678 else RexData32.registers r
  rip := if withoutGrant then 393218 else 393216
  flags := 0xfedcba9876543210
private def make (withoutGrant : Bool) := makeWorker world 11 (context withoutGrant)
  ready.codeA ready.callerA (if withoutGrant then [] else [ready.dataA]) []
private theorem made_present (withoutGrant : Bool) :
    (make withoutGrant).toOption.isSome = true := by cases withoutGrant <;> decide +kernel
private def worker (withoutGrant : Bool) : Worker := (make withoutGrant).toOption.get (made_present withoutGrant)
private def initial (withoutGrant : Bool) : OS.TSO64.State := ⟨world,[worker withoutGrant]⟩
-- Actual validated resources, including the no-grant state; no future load
-- success is an admission premise and no resource checker is mocked.
private theorem singleton_current (checked : TSO64.Checked) (w : Worker) (profile : Profile)
    (valid : WorkerValid checked.world w profile) : WellFormed ⟨checked.world,[w]⟩ profile := by
  refine ⟨checked.valid,?_⟩
  intro other member
  have same := List.mem_singleton.mp member
  subst other
  exact valid

theorem current_states (b : Bool) (profile : Profile) : WellFormed (initial b) profile := by
  apply singleton_current ready.checked (worker b) profile
  exact (makeWorker_valid_for (world := world) (worker := worker b) profile
    (output_ok (make b) (made_present b))).1

private def store (profile : Profile) := issue (initial false) 0 false profile
private theorem stored (profile : Profile) : (store profile).toOption.isSome = true := by
  cases profile <;> decide +kernel
private def queued (profile : Profile) : OS.TSO64.State := ((store profile).toOption.get (stored profile)).1
-- This projects only actual production outputs and the actual published RAM.
private structure LoadView where
  value : Word
  flags : Word
  rip : Word
  event : Observation
  pending : Nat
  nextStore : Nat
  publishedValue : BitVec 32
  deriving DecidableEq
private def view (x : Except Fault (OS.TSO64.State × Observation)) :
    Except Fault LoadView := do
  let (s,o) ← x
  let some w := s.workers[0]? | throw .missingWorker
  let v ← (loadDWord (published s.world) 131072).mapError Fault.machine
  return ⟨w.context.registers .r9,w.context.flags,w.context.rip,o,w.pending.length,w.nextStore,v⟩
-- The real load reads its own buffered DWORD, clears upper32, preserves every
-- flag and keeps the store queued/unpublished under both authority profiles.
theorem pending_load (profile : Profile) (af : Bool) :
    view (issue (queued profile) 0 af profile) =
      .ok ⟨0x92345678,0xfedcba9876543210,393221,.ordinary 0,1,1,0⟩ := by
  cases profile <;> cases af <;> decide +kernel

private def rawView (af : Bool) : Except Error (Word × Word × List X86.Sequential.Read) := do
  let o ← X86.Sequential.step af (localCPU (initial true) (worker true))
  match o.result with
  | .next f => return (f.registers .r9,f.rip,o.reads)
  | _ => throw .unexpectedReturn
-- Mapped, readable DATA and even a successful decoded load do not supply a
-- current capability. DATA4 never falls back to the managed DATA8 profile.
theorem readable_without_grant (profile : Profile) (af : Bool) :
    rawView af = .ok (0,393221,[⟨.data,131072,4⟩]) ∧
    issue (initial true) 0 af profile = .error .noGrant := by
  cases profile <;> cases af <;> decide +kernel

-- Arbitrary existing FIFOs are not consumed, extended or published by the
-- load's queue preparation. Actual read authority is checked by ordinary/issue.
theorem no_queue_change (s : OS.TSO64.State) (w : Worker)
    (d : Register) (a : X86.Sequential.Address) (profile : Profile) :
    prepareQueue s w (.loadMem32Rex d a) profile = .ok ⟨w.pending,w.nextStore⟩ := rfl
end EDSL.Tests.RexData32TSO
#audit_edsl
