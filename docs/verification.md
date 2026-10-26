<a id="verification-plan-source-compiler-output-architecture-and-os"></a>

# Verification obligations

The primary route proves source definedness and contracts in one shared GNU
C23/GNU++26 semantics. Its implementation is being built in the dependency order
in the [roadmap](roadmap.md). The existing machine-code proofs remain
[legacy results](binary-first.md) with their own scopes and assumptions.

## State the source claim

Specify the embedded source program, dialect and implementation profile,
input domain, environment effects and independent result. Then prove:

1. Defined executions exist for admitted inputs and all covered choices.
2. No such execution has undefined behavior. Unsupported constructs and missing
   rules do not establish definedness.
3. Every covered execution satisfies the result and effect contract.
4. Any claimed termination, progress or scheduling guarantee holds under its
   separately stated conditions.

Input preconditions may constrain the supported use of an interface, but cannot
simply assume that the program has no UB or returns the required result.
Bounds, initialization, lifetime, sequencing, arithmetic and synchronization
obligations must be discharged in the source proof.

A theorem about an embedded program concerns a source-text file only after
its parsing/elaboration correspondence is established. Sample runs, successful
compilation and an uninterpreted behavior relation supply no such theorem.

The current finite API packages these obligations in `Certificate`: its
`useful` field witnesses an admitted input, and `verified` proves actual defined
evaluation plus the independent result for every admitted input. Its derived
`NoUB` requires defined completion. A witness alone does not justify the chosen
domain or postcondition; both still need specification review. Before adding
loops and effects, safety, coverage, erroneous behavior and termination must
be given their separate general meanings. See the [source core API](source-core-api.md).

## Keep the environment explicit

The current source core is pure and accepts typed parameter values; it has
no memory, threads or OS effects. Before admitting effectful source constructs,
the model must represent their inputs, memory, object lifetimes, threads,
scheduler choices, atomicity, synchronization and OS effects explicitly. An
abstract interface remains an assumption until its implementation sources
are proved in the same system and the composition is checked.

Safety, functional correctness, termination, deadlock freedom, confidentiality
and side-channel properties are different statements. A source result theorem
does not establish all of them. See [trust](trust.md) for the remaining boundaries.

## Close the bootstrap chain

Select and verify one minimal binary seed, with its exact artifact and hardware
boundary. For every later stage, prove the implementation's source safety and
compiler/interpreter contract, then compose it with the preceding stage.

For a compiler, that contract includes semantic preservation. Safe execution
of compiler source alone does not establish correctness of the generated
programs. The compiler's libraries, runtime, assembler/linker and build-time
inputs must belong to the justified closure or remain explicit outstanding
boundaries. Ordinary self-hosting or repeated bootstrap agreement is not a
replacement for these proofs.

The goal is a source-proved chain up to a pinned GCC build. No seed or complete
chain is implemented yet.

## Check the evidence

Each completed milestone records its exact supported source fragment, input
and environment domain, actual definedness/contract theorems and kernel audit.
Heavy authoritative checks and replay run in CI. `decide +kernel` is permitted;
development-only `native_decide` must remain in ignored scratch, and final
proofs must not depend on it or `ofReduceBool`.

Engineering resource limits can change with documented justification. A larger
budget can allow a proof to finish; a passing budget check cannot establish a
proof. Unsupported behavior, timeout and failed verification are distinct
outcomes and do not establish a defect.
