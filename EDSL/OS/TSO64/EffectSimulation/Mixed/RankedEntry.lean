/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankedLocal
import EDSL.OS.TSO64.EffectSimulation.Mixed.RankedCohort

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Explicit present-entry proof bundles for independently supplied mixed graphs.
Each bundle selects its own local rules, independent rank laws and current
entry node. Its annotations and initial ghost are derived from those same
rules and node, retaining the every-node invariant on that exact ghost.

A finite collection can share a production profile and RMW family when supplied
with explicit descriptor equations, scheduler-slot equations and caller-policy
laws. The resulting ranked cohort retains these exact bundles' initial ghosts
and current invariants. No compiler domain, future execution, successful
schedule, returned state, desired result or fairness assumption is introduced.
The target, resource, ownership, lifetime, synchronization and memory-model
contracts already present in each entry and local rule remain explicit.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

/-- Present local proof data for one independently supplied graph and contract.
The rank laws and entry use exactly the retained local rules. -/
structure RankedEntry (d : Descriptor) (Post : Assertion) (initial : S) where
  rules : LocalRules d Post
  rankLaws : RankLaws rules
  node : d.graph.Index
  entry : Entry rules.annotations initial node

namespace RankedEntry

variable {d : Descriptor} {Post : Assertion} {initial : S}

/-- Generated annotations from this bundle's retained local rules. -/
def annotations (bundle : RankedEntry d Post initial) : Annotations d Post :=
  bundle.rules.annotations

/-- The exact initial state, empty history and this bundle's retained node. -/
def ghost (bundle : RankedEntry d Post initial) : Ghost d initial Post :=
  initialGhost d initial Post bundle.node

/-- Present entry initializes both the residual and independent every-node
invariant on this bundle's exact initial ghost. -/
theorem current (bundle : RankedEntry d Post initial) :
    bundle.rules.LocalRelated initial bundle.ghost :=
  bundle.rules.localRelated_initial bundle.entry

section Cohort

variable {n : Nat}
    {descriptors : Fin n → Descriptor} {posts : Fin n → Assertion}
    (bundles : ∀ i : Fin n, RankedEntry (descriptors i) (posts i) initial)
    (profile : Profile) (family : RMWFamily)
    (profile_eq : ∀ i : Fin n, (descriptors i).profile = profile)
    (family_eq : ∀ i : Fin n, (descriptors i).family = family)
    (tid_eq : ∀ i : Fin n, (descriptors i).tid = i.val)
    (callerPolicy : ∀ (i : Fin n) (state : S),
      (descriptors i).policy state = authorityCallerPolicy (descriptors i) state)

/-- Assemble finite scheduler slots from explicit present-entry proof bundles.
Shared production configuration and caller authority remain supplied laws. -/
def cohort : RankedCohort n profile family where
  descriptor := descriptors
  post := posts
  rules i := (bundles i).rules
  rankLaws i := (bundles i).rankLaws
  profile_eq := profile_eq
  family_eq := family_eq
  tid_eq := tid_eq
  callerPolicy := callerPolicy

/-- The collection retains each bundle's own exact initial ghost. -/
def initialGhosts :
    (cohort bundles profile family profile_eq family_eq tid_eq callerPolicy).Ghosts initial :=
  fun i => (bundles i).ghost

/-- All initial local invariants belong to the same explicit ghosts used by
the assembled cohort, without selecting any future execution. -/
theorem initialCurrent :
    (cohort bundles profile family profile_eq family_eq tid_eq callerPolicy).Current initial
      (initialGhosts bundles profile family profile_eq family_eq tid_eq callerPolicy) := by
  intro i
  exact (bundles i).current

end Cohort

#print axioms annotations
#print axioms ghost
#print axioms current
#print axioms cohort
#print axioms initialGhosts
#print axioms initialCurrent

end RankedEntry

#print axioms RankedEntry

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
