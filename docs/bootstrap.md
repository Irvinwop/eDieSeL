# Bootstrap dependency plan

The intended chain starts with exactly one verified binary seed and continues
through source-proved compiler/tool stages to a pinned GCC configuration.
No seed, sequence of stages, GCC version or complete bootstrap theorem has
been selected or implemented. This page defines the obligations for choosing
and verifying that chain.

## The single binary root

Choose one fixed artifact with exact bytes, entry/load/ABI requirements and an
independently defined compilation or interpretation contract. Its theorem
must establish machine safety and behavior for every admitted invocation under
named hardware, loader and environment assumptions. Decoding the artifact or
proving that it returns some output is insufficient.

The seed's reachable executable dependencies must be closed: startup code,
runtime helpers, assemblers, linkers or dynamic libraries cannot enter as
additional unproved executable roots. Include necessary code in the seed or
derive it through later source-proved stages. Untrusted tools may propose data
when a proved checker independently verifies the required properties and
complete bindings; a hash alone does not establish those properties.

ISA adequacy remains an explicit hardware boundary. OS and scheduler contracts
remain explicit until matching implementation-source proofs discharge them.
Existing unrelated binary certificates do not automatically constitute this seed.

## Three obligations for every later stage

Let a stage's exact source closure be `S`, and its built executable be `B`.
Every edge in the chain needs:

1. **Source safety.** Prove absence of UB and, where applicable, C++ erroneous
   behavior on an independently meaningful invocation domain. Include the
   claimed malformed-input, diagnostic, allocation-failure and cleanup paths.
   Safety only for valid compiler inputs leaves rejection behavior unproved.
2. **An independent compiler/tool contract.** Prove the source implementation
   computes the required result. For a compiler, successful output must
   preserve the supported input language's semantics, observations, faults,
   effects and stated progress guarantees under related inputs/environments.
3. **Artifact transport and closure.** Use the preceding justified stage to
   build `S`, bind the proof to the actual source/build/output, and transport
   its source contract to `B`. Cover assembly, linking, relocations, startup
   and runtime dependencies before claiming a runnable-artifact theorem.

Compiler source safety and compiler semantic preservation are distinct.
A safely implemented optimizer could replace unsigned `x + 1u > x` with true,
which is wrong at the maximum unsigned value. Proving that the optimizer returns
its own output cannot establish preservation.

A preservation theorem may require the compiled program to be UB-free; each
verified client must discharge that premise. Related executions must retain
the same external inputs and compatible OS responses. Behavior inclusion cannot
justify a target fault by omitting it or inventing a different source input.
Add existence and progress obligations wherever the advertised contract needs them.

## Chain induction

The invariant is that each derived executable implements its independently
specified compiler/tool contract, conditional only on named outstanding
hardware/environment contracts. Its proof uses the previous-stage invariant,
the next stage's source safety and preservation theorems, exact build binding
and complete dependency closure.

The predecessor's supported language/profile must cover the actual successor
source. Self-hosting has the same obligations as any other edge; it provides
no new base case. Reproducible builds and agreement between ordinary bootstrap
stages are useful tests rather than semantic proofs.

## Dependency inventory

| Boundary | Required evidence |
| --- | --- |
| Source and preprocessing | Exact translation units, headers, macros, generated tables/includes, options and include resolution; source-to-term correspondence |
| Compiler libraries | Source safety, independent arithmetic/runtime contracts and artifact transport for reachable GMP/MPFR/MPC and host library operations |
| Runtime and native code | Actual allocator, initialization/destruction, exceptions/unwinding, TLS, support helpers, assembly and intrinsic dependencies |
| Assembler, linker and loader | Preservation through symbols, relocations, final layout, startup and all reachable static/dynamic dependencies |
| Build generators | Verified executed tools, or frozen generated inputs with independently checked properties and complete build bindings |
| OS and environment | Filesystem, resource, failure, signal, input and scheduling contracts, with compatible source/target memory and synchronization models |

A narrow configuration may reduce this closure. It does not prove excluded
components or remove the obligations of dependencies that remain reachable.
Freezing generated files proves only the chosen inputs and checked properties;
a claim about their original grammar/templates needs further correspondence.

## Reaching GCC

[GCC's installation prerequisites](https://gcc.gnu.org/install/prerequisites.html)
identify a C++ host compiler, arithmetic libraries and configuration-dependent
build tools. Its [build instructions](https://gcc.gnu.org/install/build.html)
distinguish ordinary bootstrap stages, comparisons and runtime builds. These
manuals are dependency-planning sources; a later milestone must pin the exact
GCC source revision, configuration and actual tool/library closure.

The shared engine must cover the dialects actually used by each stage. A host
C++14 requirement does not justify relabeling those sources GNU++26; prove a
common-subset relation or use an explicit version profile. Likewise, kernel
sources need their real extension set, effective overflow/aliasing policies,
builtins and inline-assembly contracts. Freestanding compilation does not remove
startup, support-library, allocator or OS obligations.

## Acceptance and open decisions

| Milestone | Evidence required |
| --- | --- |
| Source foundation | Executable shared fragment, meaningful admitted domains, independent contracts, proved safety and audited dependencies |
| Seed and first successor | One exact binary root, closed dependencies, source safety/preservation for the first stage and exact artifact transport |
| Reusable composition | A checked chain-induction theorem and a nontrivial successor edge |
| Pinned GCC configuration | Actual language/library/build closure, source safety and semantic preservation for the advertised supported subset |
| Smaller environment boundary | Matching source proofs of runtime/OS implementations and checked contract composition |

Open decisions are the seed artifact/language/target; language version profiles;
the first compiler's restricted input functionality; a stage sequence reaching
needed C++ support; the GCC source/configuration and dependency closure;
generated-input policy; termination/resource-failure scope; and static versus
verified dynamic-link composition. Choose these from source and dependency
evidence. The [roadmap](roadmap.md) orders the work; binary-corpus coverage is
retained only as legacy evidence.
