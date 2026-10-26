# eDieSeL

[![Lean proofs](https://github.com/Irvinwop/eDieSeL/actions/workflows/lean.yml/badge.svg)](https://github.com/Irvinwop/eDieSeL/actions/workflows/lean.yml)

**Source-first program verification in Lean 4.**

eDieSeL is building a shared executable semantics for GNU C23 and GNU++26.
The intended workflow proves a program free of undefined behavior and proves
its contract in that semantics. Memory, inputs, threads, synchronization and OS
services belong to the execution model. Their implementation assumptions stay
explicit until the corresponding sources have been verified.

The planned compiler trust chain starts with exactly one small, verified binary
seed. Each
subsequent bootstrap stage needs source-level safety and correctness proofs,
including the compiler's semantic-preservation contract. The eventual target is
a verified chain capable of building GCC and the programs it compiles.

The initial `EDSL.Source` API is a finite expression/return fragment: typed
`int` and `unsigned int`, addition/division, explicit same-rank conversions and
a fixed GNU conversion policy, UB/unsupported outcomes, structural verification
conditions, and independent unsigned-addition
and division contracts. Definedness is proved on each stated input domain.
Its [API guide](docs/source-core-api.md) records the exact scope. It has no
source-text parser, memory operations or OS effects.

This source-language foundation is under development. Complete GNU semantics,
source parsing, a verified bootstrap compiler and source-verified kernels are
not implemented. The repository also retains substantial **legacy binary
verification** infrastructure and proofs; those results keep their original
scope and assumptions.

## Start here

- [Source verification](docs/source-semantics.md): the shared semantics,
  definedness obligations and initial scope.
- [Roadmap](docs/roadmap.md): dependency order and acceptance criteria.
- [Implementation status](docs/implementation-status.md): implemented components
  and remaining gaps.
- [Trust model](docs/trust.md): kernel checking, environmental assumptions and
  bootstrap obligations.
- [Documentation index](docs/README.md): source work and retained legacy guides.

```sh
git clone https://github.com/Irvinwop/eDieSeL.git
cd eDieSeL
lake build SourceSemanticsTests
```

This builds the source-core examples and dependency audit. `lake build` builds
the broader library, including the retained binary infrastructure.

Lean is pinned to **4.35.0**, with warnings treated as errors and no third-party
Lean packages. Heavy proof checking and replay belong in GitHub-hosted CI;
[validation](docs/validation.md) describes the checks. Every advertised theorem
must have checked proof evidence.

## Verification obligations

1. Represent the source in the shared semantics with its dialect, types and
   implementation choices recorded.
2. State an independent contract and the allowed inputs and environment.
3. Prove defined execution: no undefined behavior, unsupported construct or
   missing semantic rule can satisfy this obligation.
4. Prove the contract for every covered source execution. State termination
   and progress guarantees separately when needed.
5. Preserve those results through source-proved bootstrap stages rooted in the
   single verified seed.

A program's proof of definedness is an output of verification. It is never a
replacement for proving safety. OS interfaces, compiler behavior and hardware
correspondence also require explicit evidence.

## Legacy results

The x86-64 models, verification-condition generators, ELF certificates and
managed OS/concurrency proofs remain available. The [binary-search proof](docs/binary-search.md)
is a worked example of that infrastructure. The historical
[GCC/Clang corpus](docs/compiler-corpus.md) is retained for regression testing;
its 20/40 score is a legacy measurement, not the source-first progress metric.
No source-language, compiler-bootstrap or whole-OS theorem follows from that
score.

## Project layout

| Path | Contents |
| --- | --- |
| `EDSL/` | Lean semantics, contracts and proof infrastructure |
| `EDSL/Source.lean` | Shared source-core interface and nonvacuous certificates |
| `EDSL/Semantics.lean` | Generic behavior and refinement interfaces |
| `EDSL/All.lean` | Full proof catalogue for audits and replay |
| `Tools/` | Command-line entrypoints |
| `docs/` | Scope, trust boundaries, guides and roadmap |
| `tests/`, `fixtures/` | Independent regressions and owned synthetic inputs |
| `corpus/` | Legacy frozen compiler outputs and measurements |

The project uses [Apache-2.0](LICENSE). See [contribution guidance](CONTRIBUTING.md)
and the [security policy](SECURITY.md). Citation metadata is available through
[CITATION.cff](CITATION.cff).
