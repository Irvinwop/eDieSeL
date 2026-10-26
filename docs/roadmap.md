# Roadmap

The primary objective is source-first verification: one shared executable Lean
semantics for GNU C23 and GNU++26, proofs of source definedness and contracts,
explicit OS semantics, and a source-proved bootstrap chain rooted in exactly one
binary seed. Existing binary-first results are retained as legacy evidence and
regressions. Their corpus score is not the main progress measure.

## Current foundation

The initial `EDSL.Source` implementation is a finite pure expression/return
fragment with bool, plain char and the signed/unsigned char, short and int
types, integer promotions, addition/subtraction/multiplication/division/remainder,
explicit integral casts, six comparisons, built-in logical AND/OR and lazy
integral conditional expressions, with defined/UB/unsupported outcomes. Its
unsigned-addition client proves an independent bounded-carry equation for every
typed input. `Certificate` combines
the execution/contract theorem with an inhabited domain; domain and contract
independence still need review. See the [API](source-core-api.md) and
[implementation status](implementation-status.md) for exact limits. There is
no source-text frontend, mutable source statement execution or bootstrap stage yet. Structural
verification conditions are proved exact for this grammar. Unsigned division
has an independent interval contract and a synthetic candidate proved safe
but functionally incorrect; these reuse the same executable semantics.
A shared construction now normalizes all five arithmetic operations through
promotion and common-type conversion. Generic signed/unsigned source contracts
state the necessary numeric domains and derive NoUB from actual execution.
Universal quotient bounds establish the minimum/-1 exception for signed division
and remainder. Subtract/add cancellation and byte multiplication demonstrate
composition and safety derived from input ranges.

The fixed GNU conversion policy and explicit casts cover every admitted
bool/char/short/int source and destination. Bool conversion uses zero/nonzero
semantics; other destinations use their numeric range and congruence modulo
`2^width`. Casts, promotions and common-type arithmetic share the evaluator
and structural verification-condition interface. The profile records numeric
widths and plain-char signedness. Promotions preserve values; arithmetic source
certificates discharge overflow from input ranges, including the equal-width
unsigned-short promotion case. Comparison/logical helpers return C int or C++
bool. Conditional helpers cover unqualified integral prvalue arms: C uses the arithmetic common type; C++
first preserves matching arm types. No source lvalues or general C++ value
categories are implemented. Wider integer types, effectful sequencing, objects,
memory, statements, loops and source-connected OS effects remain dependencies.

Public program evaluation checks coverage of the whole expression before
execution, including skipped arms. Inhabited certificates derive this structural
support and actual raw execution. The raw evaluator and structural VCs remain
lazy: they evaluate the condition and only the selected arm. Skipped modeled UB
is inert; an unsupported marker anywhere still prevents public certification.
All-input unsigned and signed guarded division clients derive their branch
preconditions inside the body, rather than requiring nonzero input or absence of
the minimum/-1 pair at admission. Their independent contracts give zero on the
exceptional paths and a mathematical quotient law otherwise, with NoUB derived
from execution. A universal negative theorem rejects the signed candidate whose
guard checks only for a nonzero divisor.

Integral unary plus, minus, complement and logical NOT reuse the shared core.
The arithmetic operators apply integer promotions; NOT returns the dialect's
predicate type. Generic numeric laws identify signed minimum as negation's
exception, and a width-general bridge connects complement's arithmetic equations
to independently specified inverted value bits. These rules do not model object
storage, source parsing or overloaded C++ operators.

## 1. Establish the GNU C23 semantics foundation

The expression implementation now has one traversal with explicit lookup and
outcome handling. The [declared-object foundation](source-objects.md) supplies
checked internal state/resource primitives and contracts, with a pure-state
compatibility theorem. The next connection is finite declarations, assignment,
branch and return with actual object reads, structural stateful VCs and
independent program/frame contracts. Primitive contracts alone do not certify
a mutable source program. Read-order correspondence, storage representation,
source-connected OS behavior and larger language features remain dependencies.

Start with a small, executable, typed source fragment. Record its language
profile and implemented rules before extending it. GNU++26 shares the same
semantic machinery; genuine dialect differences are explicit rules or profile
choices, rather than a second interpreter or per-program evaluator.

The first foundation must distinguish defined results, undefined behavior and
unsupported constructs. It must expose actual execution through the shared
semantics. A bare behavior relation, sample output or successful compilation
cannot establish language support.

Extend in this dependency order:

1. Integer types, target widths, values, arithmetic and conversions, including
   promotions, usual arithmetic conversions and signed-overflow rules.
2. Extend the current pure comparison/logical/conditional expressions with
   value categories, evaluation order, sequencing and side effects.
3. Objects, byte representations, initialization, storage duration, lifetimes,
   pointer provenance, alignment, bounds and permitted aliasing.
4. Statements, control flow, function calls, recursion, translation units,
   preprocessing and checked source-to-embedded-program correspondence.
5. Volatile accesses, atomics, synchronization and first-class external effects,
   only after their memory/resource/environment state and failure rules exist.
6. GNU extensions required by selected real sources, with their compiler options
   and implementation choices pinned.

Unsupported syntax or behavior remains unsupported. Constraint violations,
unspecified choices, implementation-defined choices, undefined behavior and
C++ erroneous behavior need their proper classifications. A timeout is an
engineering outcome, not a language behavior.

Acceptance: each supported feature has executable rules, an identified language
reference, independent positive/negative evidence and checked shared lemmas.
Complete GNU C23 support must not be inferred from an arithmetic fragment.

## 2. Prove source definedness and independent contracts

Every target program uses the shared semantics. A reusable verification
judgement must require proved defined executions on the admitted input domain,
and a separately stated result/effect contract. It must reject vacuous success
from missing rules or unsupported constructs.

Input domains describe independently meaningful inputs. They cannot contain an
assumption that the program has no UB or already satisfies its result. Safety
obligations such as bounds, initialization, lifetime, alignment, arithmetic
range and synchronization must be discharged by program proofs.

Build reusable source verification-condition generation and reflection, with a
soundness theorem checked once. Clients provide their mathematics, invariants
and termination arguments. They do not introduce their own interpreter.

The present integer clients include guards with all typed inputs admitted.
Next establish statement/state semantics, then loops and small memory routines
as their execution and memory rules become available. Include independently
specified counterexamples
that expose real semantic mistakes, such as signed overflow and invalid memory
access. Keep partial correctness, termination, deadlock freedom and scheduling
progress distinct. The current finite `NoUB` requires defined completion;
separate general UB freedom, coverage and erroneous behavior before extending
the syntax with loops or effects.

Acceptance: each supported source example has an actual definedness theorem,
contract theorem, nonvacuous inputs and audited kernel-checked dependencies.
A proof about an embedded term must not be advertised as a proof about an
unconnected source-text file.

## 3. Extend the shared foundation to GNU++26

Reuse scalar values, objects, memory, effects and source verification machinery.
Add the C++ rules required by pinned bootstrap sources: references, object
construction/destruction, lifetime, classes, casts, overload resolution,
templates and constant evaluation, exceptions and runtime/library behavior.
Track newer C++26 features and erroneous behavior explicitly.

Acceptance: C and C++ constructs with shared meaning use the same rules;
differences are covered by explicit dialect-sensitive cases. No unsupported
C++ feature is erased during elaboration.

## 4. Make OS and input semantics first-class

Model processes, threads, scheduler choices, memory mappings, allocation,
capabilities, I/O, files, synchronization, atomics and the selected memory model.
Inputs and environment transitions are part of executions. Kernel and userspace
profiles may need different GNU extensions and compiler flags; record those
choices instead of silently importing ordinary ISO C assumptions.

Existing managed resources and concurrency models are reusable components.
They become source-level evidence only after an explicit connection to source
steps is proved. An abstract syscall or scheduler contract remains an external
assumption until its implementation is proved in the same system.

Acceptance: source proofs expose the environment contracts they use, quantify
covered scheduling/input choices and preserve current resource obligations.
Replace interface assumptions with source proofs one implementation at a time.
A kernel or distribution is verified only to the extent of its checked closure.

## 5. Specify and verify one minimal binary seed

Choose one small seed implementation, exact artifact and hardware boundary.
Specify its loader, memory, entry, input and output contracts. Reuse the legacy
machine models where they actually discharge these obligations.

The seed is the single program-level binary proof in the primary bootstrap
chain. Hardware-model correspondence is an explicit separate boundary. No seed
has yet been selected or proved for this chain; existing unrelated binary
certificates do not automatically constitute it.

Acceptance: one fixed binary theorem with complete dependency and environment
accounting, suitable to execute the first verified source stage.

## 6. Prove and compose bootstrap stages

For every stage, prove its source implementation free of UB and prove its
compiler/interpreter contract. A compiler contract includes semantic
preservation for the supported input language and target. Proving that the
compiler's own source executes safely is necessary and insufficient on its own.

Then prove chain induction: the already justified stage builds or executes the
next verified source stage, preserving the next stage's specification. Pin
source inputs, generated files, target choices and all runtime dependencies.
Assemblers, linkers, libraries and build-time generators must either be included
in that verified closure or remain explicit outstanding boundaries.

The [bootstrap dependency plan](bootstrap.md) details the single root, chain
induction, malformed-input/failure domains and complete build/runtime closure.
It does not select or claim a proved sequence of compilers.

Acceptance: each stage has source safety, functional/preservation evidence and
a composition theorem connected to the preceding stage. Ordinary self-hosting,
reproducible builds or a three-stage bootstrap do not substitute for these proofs.

## 7. Reach a pinned GCC build and larger systems

Select a GCC revision/configuration after the earlier stages expose a realistic
feature inventory. Modern GCC requires C++ in its host bootstrap; C-only support
will not close this step. Include the required language/library/build closure,
including arithmetic libraries, runtime interfaces and generated sources.
GCC's [official prerequisites](https://gcc.gnu.org/install/prerequisites.html)
are the starting inventory, not a proof that those dependencies are verified.

Prove the compiler source's safety and its semantic-preservation contract,
build it through the justified chain, and compose its output guarantees with
source-level program proofs. Apply the same source/resource framework to
applications, kernel components and eventually their full dependency closures.

## Progress and trust

Track these separately:

| Measure | Required evidence |
| --- | --- |
| Language features | Executable rules, scope/reference and checked semantic lemmas |
| Source programs | Definedness plus independent contracts under stated inputs/effects |
| OS components | Explicit interfaces and completed source-level discharges |
| Seed | One selected artifact and its binary/hardware-boundary evidence |
| Bootstrap stages | Source safety, preservation and chain composition |

None of the complete GNU semantics, source-verified GCC, selected seed or closed
bootstrap chain is implemented yet. The legacy 20/40 binary-corpus score remains
historical evidence only. [Implementation status](implementation-status.md)
must distinguish plans, implemented definitions, checked proofs and accepted CI.

Final terms are checked by Lean's kernel and audited for project axioms and
holes. `decide +kernel` is allowed. `native_decide` is a development oracle only
in ignored scratch; it and `ofReduceBool` are excluded from final/audited source.
Use GitHub-hosted CI for authoritative heavy proof checking and fresh replay,
with cached builds and independent shards. Packet sizes, heartbeats, action
counts and timeouts are documented engineering limits that may be raised when
needed; they do not make an unchecked result a proof. Keep pursuing large Nat
encodings and small sound reflective checkers to make kernel work scale.
