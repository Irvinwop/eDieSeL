# Proof checking in CI

GitHub-hosted CI performs authoritative project builds, dependency audits and
fresh kernel replay. Local scoped checks support development. A cache hit is
never proof acceptance: Lake validates dependency traces, the audits run, and
fresh replay checks the stored proof closure.

## Preparation and replay

The `Frozen compiler corpus` workflow retains the legacy final-ELF regression
gate. Its preparation job checks frozen inputs, builds the full project and
private certificate CLI, runs audits and changed-input rejection controls, then
seals a same-run transport artifact. Preparation records `PREPARED.md`; it cannot
record full success or `READY.md` without replay.

Twenty mandatory matrix jobs import disjoint sets of replay roots. Their
transitive dependencies may overlap. The planner expands only the import-only
`EDSL.All` and `CorpusFullReplay` catalogues; it preserves the named certificate
checks and private CLI as replay roots. It rejects a catalogue with declarations
instead of silently dropping them. The existing `frozen-corpus` status requires
both preparation and every shard to succeed, including on reruns and failures.

Each shard verifies the transported source/build manifests, invokes Lake to
validate restored outputs, audits theorem dependencies and defining modules,
and runs `leanchecker --fresh`. It rereads source, generated-source and proof
object identities after replay. The tar transport preserves executable modes;
the artifact is scoped to the same workflow run and attempt. The payload has a
one-day retention period. Hashes bind the checked bytes and do not replace any
semantic proof.

The `Lean proofs` workflow builds and audits the full catalogue. It relies on
the mandatory corpus shards for fresh replay of that catalogue, avoiding a
second monolithic replay. Its source-policy job also checks the scanner and
replay planner against synthetic rejection and coverage fixtures.

## Cache and resource policy

Toolchain caches are keyed by platform and the pinned `lean-toolchain`. Lake
cache keys also include package configuration and the commit; older compatible
outputs may be restored, but Lake always runs. One build job publishes the shared
cache. Replay receives sealed same-run outputs rather than treating a cross-run
cache as an acceptance receipt.

The full build and corpus preparation/replay jobs allow **360 minutes** each.
This raises the former 45-minute full-build and 60-minute corpus limits to
accommodate cold elaboration and large checked certificates. The twenty replay
jobs use `max-parallel: 20` and `fail-fast: false`. Wall-clock limits, heartbeat
limits, recursion depth, packet size and action budgets are engineering limits;
they do not establish soundness. This change leaves the existing Lean, packet
and action limits intact. Future changes must record their scope and reason.

GitHub jobs use their isolated working directories rather than a shared local
Lean lock. Local tools retain their existing lock behavior.

## Final proof policy

Ordinary `decide` and `decide +kernel` are permitted. Final tracked Lean sources
and retained generated proof sources are scanned for forbidden native-evaluation
identifiers. `native_decide` and `ofReduceBool` are forbidden there, including in
comments and quoted text. Development oracles belong only in ignored local
scratch and must not enter final modules, CI evidence or accepted proof packets.
The spelling scan supplements the compiled dependency audits; it is not a Lean
parser or a replacement for replay. Project axioms, proof holes and unchecked
solver facts remain forbidden in proved claims.
