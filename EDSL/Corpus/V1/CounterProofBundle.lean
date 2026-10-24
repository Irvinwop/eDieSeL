/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterRanks
import EDSL.Corpus.V1.CounterCohort
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankedEntry

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Explicit proofs for one independently admitted frozen counter call. A bundle
retains one exact local-rule object: its rank laws, entry, running saved-frame
projection and initial current invariant all refer to that same object. GCC
and Clang construct their bundles directly from their own existing proofs.
Generic clients receive the selected proof instead of dispatching on compiler.

The selected bytes remain the complete row40 `c_counter_worker` windows at
their original symbol addresses: GCC has 49 bytes at 4207440, and Clang has
86 bytes at 4201344. The graphs, byte checks, inputs and contracts are unchanged.
Successful finite returned schedules yield full-log counts, event properties
and original resource records through the retained annotations and entry.
The saved projection concerns each current running invariant; returned saved
facts come from current Post and its existing authenticated idle stability.

The imported represented-memory, protected-resource, CET/IBT-off, scalar WB
RAM, translation/no-alias and synchronization contracts remain assumptions.
These adapters do not establish physical CPU/OS or compiler refinement, new
corpus credit, native joining or resource retirement. They do not strengthen
the void result contract or turn source admission into a future-run premise.
A finite ranked cohort uses explicit slot equations, owned-only profiles and
caller-policy laws; initial validity, complete worker coverage and empty queues
remain separate requirements of the generic execution engine.
-/

namespace EDSL.Corpus.V1.CounterCommon
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

/-- One explicit selected proof, including the saved frame of its retained
running invariant. No compiler dispatcher or future execution is a field. -/
structure ProofBundle {c : Compiler} (site : Site c) (call : Call) (initial : S) where
  ranked : Mixed.RankedEntry (descriptor site call) (Post site call) initial
  saved : ∀ {node state history}, ranked.rules.Inv node state history →
    ∃ worker, state.workers[site.tid]? = some worker ∧ Saved site worker.context

/-- Construct present proof data for this compiler from independent admission.
Clients explicitly choose the provider; no universal selection is performed. -/
def ProofProvider (compiler : Compiler) :=
  ∀ {site : Site compiler} {call : Call} {initial : S},
    Pre site call initial → ProofBundle site call initial

namespace ProofBundle

variable {c : Compiler} {site : Site c} {call : Call} {initial : S}

/-- The annotations generated from the bundle's exact retained rules. -/
def annotations (bundle : ProofBundle site call initial) :
    Mixed.Annotations (descriptor site call) (Post site call) :=
  bundle.ranked.annotations

/-- Present entry for these exact generated annotations and retained node. -/
theorem entry (bundle : ProofBundle site call initial) :
    Mixed.Entry bundle.annotations initial bundle.ranked.node :=
  bundle.ranked.entry

/-- The exact initial ghost selected by the bundle's retained entry node. -/
def ghost (bundle : ProofBundle site call initial) :
    Mixed.Ghost (descriptor site call) initial (Post site call) :=
  bundle.ranked.ghost

/-- Both residual and running local invariant hold on that same initial ghost. -/
theorem current (bundle : ProofBundle site call initial) :
    bundle.ranked.rules.LocalRelated initial bundle.ghost :=
  bundle.ranked.current

/-- Entire-log count through this bundle's annotation and entry proofs. -/
theorem completed_count (bundle : ProofBundle site call initial) {final : S}
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions site.profile .arithmetic = .ok (final, observations))
    {worker : Worker} (live : final.workers[site.tid]? = some worker)
    (returned : worker.phase = .returned) :
    Mixed.Counts.countRMW site.tid observations = call.iterations.toNat :=
  CounterCommon.completed_count bundle.annotations bundle.entry actual live returned

/-- Every own event in the complete observation log satisfies the independent
counter event contract, through this bundle's annotation and entry proofs. -/
theorem completed_events (bundle : ProofBundle site call initial) {final : S}
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions site.profile .arithmetic = .ok (final, observations))
    {worker : Worker} (live : final.workers[site.tid]? = some worker)
    (returned : worker.phase = .returned) :
    ∀ event, .rmw site.tid event ∈ observations → EventOK site call event :=
  CounterCommon.completed_events bundle.annotations bundle.entry actual live returned

/-- The completed current worker retains the exact original resource record;
its live lookup is aligned with this bundle's current Post witness. -/
theorem completed_resources (bundle : ProofBundle site call initial) {final : S}
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions site.profile .arithmetic = .ok (final, observations))
    {worker : Worker} (live : final.workers[site.tid]? = some worker)
    (returned : worker.phase = .returned) : worker.resources = site.original.resources := by
  obtain ⟨_next, _related, _trace, _authentic, post, _actions, _observations⟩ :=
    bundle.annotations.schedule_completion bundle.entry (stablePost site call) actual live returned
  obtain ⟨current, currentLive, resources, _phase, _pc, _stack, _saved⟩ := post.returned
  have same : worker = current := Option.some.inj (live.symm.trans currentLive)
  exact (congrArg Worker.resources same).trans resources

#print axioms annotations
#print axioms entry
#print axioms ghost
#print axioms current
#print axioms completed_count
#print axioms completed_events
#print axioms completed_resources

end ProofBundle

/-- Present admitted subject retaining an explicitly selected proof. Resource
actors remain independent of physical scheduler-slot numbers. -/
structure ProvedSubject (initial : S) where
  compiler : Compiler
  site : Site compiler
  call : Call
  pre : Pre site call initial
  ownedOnly : site.profile = .ownedOnly
  proof : ProofBundle site call initial

/-- Assemble exact scheduler slots from their explicit same-rule proof bundles.
No compiler selection is performed in this generic cohort constructor. -/
def provedRankedCohort {n : Nat} {initial : S}
    (subjects : Fin n → ProvedSubject initial)
    (slots : ∀ i : Fin n, (subjects i).site.tid = i.val) :
    Mixed.RankedCohort n .ownedOnly .arithmetic where
  descriptor i := descriptor (subjects i).site (subjects i).call
  post i := Post (subjects i).site (subjects i).call
  rules i := (subjects i).proof.ranked.rules
  rankLaws i := (subjects i).proof.ranked.rankLaws
  profile_eq i := (subjects i).ownedOnly
  family_eq _i := rfl
  tid_eq := slots
  callerPolicy i state := descriptor_policy (subjects i).site (subjects i).call state

/-- The collection uses each explicit proof's own initial state, empty history
and retained entry node, rather than another chosen ghost. -/
def provedInitialGhosts {n : Nat} {initial : S}
    (subjects : Fin n → ProvedSubject initial)
    (slots : ∀ i : Fin n, (subjects i).site.tid = i.val) :
    (provedRankedCohort subjects slots).Ghosts initial :=
  fun i => (subjects i).proof.ranked.ghost

/-- The initial every-node invariant belongs to each exact retained ghost. -/
theorem provedInitialGhosts_current {n : Nat} {initial : S}
    (subjects : Fin n → ProvedSubject initial)
    (slots : ∀ i : Fin n, (subjects i).site.tid = i.val) :
    (provedRankedCohort subjects slots).Current initial (provedInitialGhosts subjects slots) := by
  intro i
  exact (subjects i).proof.ranked.current

#print axioms ProofBundle
#print axioms ProofProvider
#print axioms ProvedSubject
#print axioms provedRankedCohort
#print axioms provedInitialGhosts
#print axioms provedInitialGhosts_current

end EDSL.Corpus.V1.CounterCommon

namespace EDSL.Corpus.V1.CounterGCC
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation CounterCommon

/-- Direct GCC proof data from its complete local rules, independent rank laws
and present entry. Every field refers to the same retained GCC rules. -/
def proofBundle {site : Site .defaultGCC} {call : Call} {initial : S}
    (pre : Pre site call initial) : ProofBundle site call initial where
  ranked := {
    rules := rules site call pre.callerCanonical
    rankLaws := rankLaws pre
    node := (⟨0, by decide +kernel⟩ : Index)
    entry := entry_of_pre pre }
  saved := by
    intro node state history invariant
    obtain ⟨worker, binding, data, _increments, _arithmetic⟩ := invariant
    exact ⟨worker, binding.live, data.saved⟩

#print axioms proofBundle

end EDSL.Corpus.V1.CounterGCC

namespace EDSL.Corpus.V1.CounterClang
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation CounterCommon

/-- Direct Clang proof data from its complete local rules, independent rank
laws and present entry, including its original protected stack fact. -/
def proofBundle {site : Site .defaultClang} {call : Call} {initial : S}
    (pre : Pre site call initial) : ProofBundle site call initial where
  ranked := {
    rules := rules site call pre.callerCanonical pre.stack
    rankLaws := rankLaws pre
    node := (⟨0, by decide +kernel⟩ : Index)
    entry := entry_of_pre pre }
  saved := by
    intro node state history invariant
    obtain ⟨worker, binding, data, _increments, _arithmetic⟩ := invariant
    exact ⟨worker, binding.live, data.saved⟩

#print axioms proofBundle

end EDSL.Corpus.V1.CounterClang

#audit_edsl
