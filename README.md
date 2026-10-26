# eDieSeL

[![Lean proofs](https://github.com/Irvinwop/eDieSeL/actions/workflows/lean.yml/badge.svg)](https://github.com/Irvinwop/eDieSeL/actions/workflows/lean.yml)

**Source-first program verification in Lean 4.**

eDieSeL is building a shared executable semantics for GNU C23 and GNU++26.
The intended workflow proves a program free of undefined behavior and proves
its contract in that semantics. The execution model must represent memory,
inputs, threads, synchronization and OS services. Their implementation
assumptions stay explicit until the corresponding sources have been verified.

The planned compiler trust chain starts with exactly one small, verified binary
seed. Each subsequent bootstrap stage needs source-level safety and correctness
proofs, including the compiler's semantic-preservation contract. The eventual
target is a verified chain capable of building GCC and the programs it compiles.

The `EDSL.Source` API is a finite expression/return fragment with bool, plain
char and the signed/unsigned char, short and int types, integer promotions,
addition, subtraction, multiplication, division, remainder and comparisons.
Integral unary plus, minus, complement and logical NOT reuse the same core;
complement has a generic proof that every value bit is inverted.
Conditional expressions and built-in logical AND/OR evaluate only the selected
arm or needed operand; comparison/logical results are int in C and bool in C++.
Explicit casts connect every admitted integral type: bool conversion distinguishes zero
from nonzero; other destinations use the value in range congruent modulo
`2^width`, under a recorded GNU policy. These operations share one evaluator and
structural verification conditions. Independent source contracts use arithmetic
equations and ranges, with definedness proved on each stated input domain.
The expression engine also exposes typed effectful lookup. An internal
[declared-object foundation](docs/source-objects.md) provides initialization,
lifetime, authority and capacity contracts. A [finite statement API](docs/source-statements.md)
connects mutable parameters and locals to those operations, with exact structural
verification conditions and normal-return cleanup. A checked copy/increment
client derives its unsigned result, caller/old-object frames, resource restoration
and absence of failure for every typed input. Native source-order and OS
correspondence remain open.
Composition examples discharge overflow from operand ranges and account for
unsigned wrapping. Guarded quotient programs admit all typed inputs and derive
definedness from their guards. Public evaluation first checks model coverage of
the complete body, including skipped arms.

An [internal control API](docs/source-control.md) adds sequencing, branches,
loops and early return over already-bound objects. Shared trace and finite-progress
rules let clients prove completion and independent state/result contracts without
writing a new evaluator. A structural VC generator reuses the same expression
transformer and checks annotated loop invariants and ranks. Its division client derives finite
return, an independent quotient/remainder equation and caller/object frames for
every admitted uint input and positive denominator. Source loop classification,
required C++ yield effects and native source correspondence remain open.

The [function-control driver](docs/source-functions.md) connects parameters,
local declarations and normal cleanup to those control bodies. A generic exact
compatibility theorem transports existing finite program contracts without
new per-program execution proofs. Its function VC layer composes entry,
initializers, annotated control and actual cleanup; a loop-bearing division
client proves its result, caller frames and restored resources through that API.
Reusable entry contracts handle literal/absent declarations and fresh bindings,
so each new function can focus on its body invariants and result.

The [source-core API guide](docs/source-core-api.md) records its exact scope.
Inputs are immutable typed values in the expression-only specialization; the
finite statement API allocates mutable object bindings. These interfaces have
no source-text parser or source-connected OS effects.

This source-language foundation is under development. Complete GNU semantics,
source parsing, a verified bootstrap compiler and source-verified kernels are
not implemented. The repository also retains substantial **legacy binary
verification** infrastructure and proofs; those results keep their original
scope and assumptions.

## Start here

- [Typed memory foundation](docs/source-memory.md): types, layout contracts and payload laws; pointer execution remains open.
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
