# Corpus diagnostic after REX DATA4 loads

The unchanged production read-only CFG checker accepts **22/40 GCC** and
**20/40 Clang** function windows with REX DATA4 support. Running the same probe
against the preceding published source, commit `b7d6e55`, accepts **21/40 GCC**
and **20/40 Clang**. The only changed result is GCC `c_dot_mod64`: its complete
55-byte window now produces a 19-node CFG.

These are structural diagnostics. Conditional end-to-end coverage remains
**20/40 functions, 40/80 artifacts and three concurrent functions**. The reports'
zero certification fields describe this probe's scope; they do not replace the
separate accepted certificates. No frozen compiler output was executed or rebuilt.

## Evidence

All four runs use the unchanged `corpus/Probe.lean`, specification and
production `CFG.analyze` profile: 64 bytes and 32 static instructions. Both
20-module source/object closures and their 48 import joins were checked.
The baseline's sources were compared directly with its published Git blobs;
the candidate source hashes are recorded in `checker-sources.sha256`.

All 80 windows match their manifest bytes, unique defined global function
symbol, executable section and readable/executable file-backed PT_LOAD mapping.
Source, object, toolchain and frozen-input hashes were checked before and after
the runs. Every process and postflight completed successfully under the pinned
Lean 4.35 profile: one thread, 300000 heartbeats, recursion 128, warnings as
errors, explicit binders, 3 GiB memory, no swap and a 120-second process bound.
No profile or proof limit was increased.

`gcc.json`, `clang.json` and their `baseline-` counterparts are exact emitted
reports. `WINDOWS.json` records the authenticated extraction inventory.
`validation.json` records the source identities, completed runs and sole delta,
without machine-specific paths. Run its source and frozen-input hash manifests
from the repository root; run `SHA256SUMS` from this measurement directory.
Hash checks establish provenance, not semantic correctness.

With independently verified `SYMBOL.bin` files for one compiler, reproduce the
probe using:

```sh
lake env lean -j1 -DwarningAsError=true -DautoImplicit=false \
  -DmaxHeartbeats=300000 -DmaxRecDepth=128 --run corpus/Probe.lean \
  corpus/v1/specifications.tsv VERIFIED_WINDOWS_DIR OUTPUT.json
```

Baseline reproduction requires its recorded source revision. Build dependencies
through Lake so stale objects are invalidated.

## What remains

The default checker first refuses oversized windows for ten uncovered functions.
Three functions encounter supported stores excluded by its read-only policy;
two first encounter unsupported SIMD loads. A size or policy refusal does not
show that another backend lacks the instruction. The supported structural,
effect and managed concurrency routes retain their own proof obligations.

The [blocker queue](../../../docs/corpus-blockers.md) separates these observed
outcomes from source-audited later frontiers and existing behavioral proofs.
Triangular and counted-worker model certificates already exist; task export,
installed acceptance and corpus registration remain separate gates. The new
GCC dot-product CFG still needs its independent loop/buffer/caller proof, while
its Clang counterpart exceeds the default profile and needs SIMD semantics.

This measurement establishes no new behavioral certificate, physical CPU or
kernel refinement, external-call contract, packet admission or security finding.
