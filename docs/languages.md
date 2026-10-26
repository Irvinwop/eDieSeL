# Language and target semantics plan

eDieSeL is implemented in Lean 4. The primary route uses one shared executable
semantics for GNU C23 and GNU++26. The current [source core](source-core-api.md)
is a finite typed expression/return fragment, with actual evaluation and
definedness/contract obligations. Complete languages, source-text frontends
and preservation proofs remain planned.

The retained binary library accepts restricted machine-code windows and ELF
selections. Its compiler fixtures establish only their documented binary
results; see [legacy coverage](coverage.md).

An eDSL is an embedded domain-specific language; `EDSL` is the library's actual
Lean namespace. Source eDSLs represent programs as Lean values.
Their semantics must describe program effects explicitly rather than perform
those effects while constructing syntax.

The [binary-first route](binary-first.md) does not require a frontend for every
implementation language. Code compiled from another language can be a candidate
only where its final bytes, ABI, dependencies and effects fit an implemented
profile. The reachable instructions, runtime dependencies, and effects must
all fit that profile.

## 1. Share contracts without erasing differences

GNU C23 and GNU++26 share source representations, values, execution machinery
and proof infrastructure, with explicit rules for genuine dialect differences.
They must not grow independent interpreters for each program or dialect.
LLVM IR and machine code need separate representations and explicit relations
to source semantics. Shared bit widths, layouts, events, resources or OS
vocabulary do not identify C pointers, LLVM pointers and machine addresses.

A supported construct needs syntax and well-formedness, execution semantics,
independent proof rules, an explicit import/emission boundary, and a lowering
proof or sound artifact validator where preservation is claimed. Unsupported
features require a clear rejection path.

A C atomic, LLVM atomic, locked x86 instruction and mutex operation have
related purposes but different obligations. Runtime calls must expose memory,
ownership, synchronization, failure and progress effects.

## 2. Define the supported subset precisely

| Status | Evidence |
| --- | --- |
| Planned | A design or requirement |
| Represented | Typed syntax |
| Modeled | Reviewed Lean semantics |
| Executable | An interpreter, emitter or helper |
| Proven | Named theorems for stated obligations |
| Validated artifact | A checked proof for particular bytes and assumptions |

These stages do not imply each other automatically. A compiler accepting a
`-std` option supplies no source-semantics theorem. Support claims need a
language/model revision, target profile, feature subset and named proof scope.
The current x86-64 userspace profiles are described in the
[platform model](platform-model.md).

## 3. GNU C23

The implemented pure [source core](source-core-api.md) covers full-rank `int`
and `unsigned int` values, addition/division, same-rank conversion/common-type
rules under an explicitly recorded GNU conversion policy, and a single expression
return. It has no smaller-type promotions, objects, pointers, memory, statements, calls, threads or
source-text importer. The separate retained
[atomic event-graph fragment](c23-atomic-events.md) provides
scoped source ordering and coherence constraints. It supplies neither a GNU C
frontend nor a machine-to-source preservation theorem.

Extending the GNU C23 foundation requires pinning the language text, compiler
revision, extension set, layout and semantic options associated with
`-std=gnu23`. The obligations
include:

- Integer types, promotions, conversions, overflow, shifts and division;
  aggregate layout, padding, alignment and byte representations.
- Evaluation order and sequencing, calls, function pointers, control flow,
  loops and recursion, with definedness conditions.
- Objects, subobjects, provenance, effective types, aliasing, initialization,
  lifetime, pointer arithmetic and access permissions. Integer/pointer round
  trips need a chosen contract before admission.
- Atomic objects and memory orders, reads-from and happens-before relations,
  data races, TLS, and separate GNU atomic-builtin contracts.
- Volatile access, inline assembly, allocation, libraries, threads, signals,
  I/O and failures. Volatile alone supplies no synchronization theorem.

GNU extensions and additional C23 features need their own semantics and
lowering evidence. The [roadmap](roadmap.md) starts from the implemented
arithmetic fragment, then adds conversions, sequencing, objects and control
flow. No C text importer
is implemented.

## 4. GNU C++26

The same source core records `Dialect.gnuCpp26` and proves dialect-independent
evaluation only for its present pure common fragment. Extending it requires a
pinned language revision, `-std=gnu++26` frontend boundary, standard library and
ABI configuration. Sequencing, lifetimes and erroneous behavior need explicit
C++ rules; shared syntax does not justify silently importing C rules.

| Area | Required semantics and preservation obligations |
| --- | --- |
| Expressions and types | Value categories, references, conversions, overload resolution, evaluation order and undefined behavior |
| Initialization and lifetime | Construction, destruction, temporaries, storage reuse and cleanup after partial construction |
| Classes and layout | Subobjects, inheritance, virtual dispatch, vtables, thunks and ABI layout |
| Templates and constant evaluation | Instantiation, constraints, specialization and correspondence to submitted source |
| Exceptions | Cleanup edges, unwinding runtime, `noexcept`, termination and foreign boundaries |
| Libraries | Contracts and implementation boundaries for allocators, containers, atomics, threads, locks and I/O |
| Linkage and other facilities | ODR, initialization order, modules, coroutines and other explicitly selected features |

A proof about lowered code does not establish correct template instantiation
or frontend elaboration. Disabling exceptions or RTTI restricts a build profile;
it supplies no proof for programs that use them. General GNU C++26 ingestion
and source preservation are outside current support.

## 5. LLVM IR

LLVM IR is a separate, versioned domain. A future model must pin its dialect,
reader, target triple, data layout, address spaces, calling conventions and
intrinsics. It needs SSA/PHI, blocks and terminators, arithmetic, memory,
alignment, attributes, calls, exceptional control flow, atomics and linkage.

Immediate undefined behavior, poison, `undef` and `freeze` have distinct roles.
Overflow flags, in-bounds promises, nonnull/alignment attributes and memory-effect
annotations generate obligations. Unsupported attributes, intrinsics, metadata
with semantic effects and address spaces must be rejected rather than ignored.

Source-to-LLVM and LLVM-to-machine preservation are separate proofs, including
atomic-order mappings and runtime helpers introduced by compilation. IR can
already serve as an untrusted proof hint for machine code; there is no current
general LLVM input validator or Lean bridge to an external LLVM verifier.

## 6. Assembly and machine code

The retained binary-verification library implements enumerated x86-64 profiles.
Typed instructions have register, flag, memory and control-flow semantics. A
checked decoder connects exact encodings, instruction lengths, prefixes,
extensions and relative addressing to those semantics. An external disassembly
cannot choose the instruction that executes.

The [reusable checker](reusable-checker.md) handles restricted read-only
sequential CFGs; writable calls, atomic operations and syscalls use their own
models. Supporting an encoding in one model does not admit it in every profile.
See [machine coverage](coverage.md) and the ISA references in the
[documentation index](README.md#machine-semantics-and-artifacts).

ABI obligations are separate from instruction semantics: arguments, returns,
preserved registers, stack ownership/alignment, TLS and unwinding all need a
contract appropriate to the selected interface. GNU inline assembly additionally
needs constraints, tied operands, clobbers and control-flow effects justified
against the frontend. A raw instruction string with an asserted postcondition
is insufficient evidence.

## 7. Undefinedness and nondeterminism across languages

| Category | Required treatment |
| --- | --- |
| Ill-formed input | Reject before execution reasoning |
| Unsupported feature | Report the missing capability; produce no certificate |
| Undefined behavior | Prove unreachable for all executions covered by the precondition |
| Implementation-defined behavior | Fix and record the selected choice |
| Permitted nondeterminism | Model allowed choices and quantify over the covered behaviors |
| OS or library failure | Specify outcomes, partial effects and cleanup obligations |
| Trap or fault | Model explicitly and prove absent or permitted |
| C++ erroneous behavior | Model separately and exclude it in a clean-code certificate; UB freedom alone is insufficient |
| Deadlock or divergence | Preserve the outcome; prove progress separately when claimed |

A machine instruction producing a wrapped value does not make an undefined
source operation defined. A preservation proof must connect the actual
contracts. Likewise, one successful run says little about other inputs,
weak-memory executions, schedules, I/O replies or resource availability.
[Verification contracts](verification.md) describes the required quantifiers.

## 8. Program ingress and cross-language boundaries

The primary route starts with Lean-authored source eDSL terms and proves their
definedness and independent contracts. The current arithmetic fragment has no
source emission or lowering theorem. Extending its artifact connection requires:

- Lean-authored source eDSLs: justify any emitted text and every lowering used
  in a preservation claim.
- External source/IR import: bind exact text, preprocessing inputs, parsing,
  typing, elaboration and language revision. Any trusted frontend boundary must
  remain visible in the resulting claim.

Cross-language linking needs symbol, layout, ABI, pointer/lifetime, aliasing,
error and threading contracts. Callbacks and exceptions across a foreign
boundary require more than a function type. Dynamic symbol resolution and
libraries that create threads add loading and interference obligations.
A modular proof needs compatible contracts for the actual dependency closure.

## 9. Required deliverables for a new feature

Each extension needs a documented semantic choice and references, Lean syntax
and semantics, independently stated behavioral theorems, artifact/preservation
evidence where applicable, capability reporting and explicit failure behavior.
Independent examples and rejection cases should catch plausible arithmetic,
lifetime, ordering, ABI or failure-path defects.

The [architecture](architecture.md), [OS contracts](os-semantics.md),
[verification requirements](verification.md) and [roadmap](roadmap.md) describe
composition and acceptance. The [research map](research-map.md) collects semantic
references and possible reuse; those references are not integrated frontends
or proof dependencies merely because they are listed.
