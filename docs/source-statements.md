# Finite object-backed statements

`EDSL.Source.Objects` contains a typed finite declaration and statement eDSL.
It uses the same scalar expression engine as the expression-only API. Formal
parameters and local variables denote actual objects; reading a variable loads
its current contents rather than its original external call value.

This is an executable internal source fragment with checked operational and
verification-condition laws. It does not establish a correspondence with parsed
C/C++ files or all behavior permitted by the language standards.

The separate [control API](source-control.md) adds loops over already-bound
objects and transports this finite statement body's exact results, failures,
state and events. It does not extend `StateSyntax.Program` with loops or yet
transport full declaration, function-entry and cleanup behavior.

## Constructing a program

`StateSyntax.Program target parameters result` fixes the dialect and integer
conversion policy for its whole body. Parameter and local object kinds are
full signed or unsigned int. RHS expressions retain the existing scalar types,
casts, promotions and arithmetic operations.

A body has a finite `Decls` prefix followed by `Stmt`:

| Syntax | Meaning |
| --- | --- |
| `Decls.declare kind initial rest` | A local, optionally initialized using only previously visible parameters/locals |
| `Decls.body statement` | End of the declaration prefix |
| `Stmt.set variable rhs next` | Evaluate the RHS, write the object, then execute the continuation |
| `Stmt.branch condition yes no` | Evaluate the condition, then execute exactly one branch |
| `Stmt.ret rhs` | Compute the returned scalar |
| `Stmt.unsupported feature` | Explicit coverage refusal |

Typed source indices cannot refer to their own declaration or a future local.
`Env` carries matching typed identities, without cached scalar values. Its
uniqueness and lookup laws help establish binding invariants; uniqueness alone
is not a registry, authority or safety proof.

`BlockEquations` supplies generic constructor equations for parameter entry,
reservation, declarations and cleanup. Clients can rewrite these fixed APIs
without unfolding the driver or reconstructing its dependent matches. Object-kind
projections remain visible to implicit elaboration in mapped variable contexts.

## Execution and resources

`BlockEval.runProgram` first scans the complete original body for unsupported
syntax, including skipped branches and initializers. It then:

1. Allocates and initializes mutable parameter objects from the external inputs.
2. Reserves **all** local objects before the first local initializer.
3. Runs initializers in declaration order and executes the finite statement tree.
4. Computes the return value before ending locals and parameters, each in reverse
   source order, and returning their abstract object slots.

C non-VLA local lifetime begins at block reservation; C++ initialization
completion precedes lifetime begin, including vacuous initialization. `none`
never invents zero. Every demanded variable read checks the actual object;
assignments check current write authority even when storing the same value.

A terminal failure retains accepted state changes and events. This fragment
models normal-return cleanup; it does not promise rollback or reclamation of
pending reservations after a failure. Ended records retain their identities.
Slots count abstract objects, not physical stack bytes.

`BlockEval.Entry` describes metadata well-formedness and capacity for all
parameters and locals. It has an explicit inhabited-state construction. It
contains no target execution, NoUB or postcondition premise. It is a resource
entry predicate, not a certificate that arbitrary source expressions are safe.

`BlockContracts.reserveAll_contract` derives fresh ordered identities,
unique bindings, matching pending records, resource deltas and complete external
and old-object frames from metadata and capacity. `closeAll_contract` derives
reverse cleanup, tombstones and slot restoration from independent live/owned
bindings and uniqueness.

## Checked mutable program

`CopyIncrement.program` copies an unsigned parameter object into a local,
increments the local, and returns its current value before cleanup. Its useful
certificate covers every admitted target, dialect and typed input, with arbitrary
old well-formed objects and two free slots. Admission mentions only metadata and
capacity. The result contract states an independent bounded-carry equation:

`result + carry × modulus = input + 1`, with `carry ≤ 1`.

The proof also preserves external inputs/environment/actor and old objects,
advances the fresh identity by two, restores all slots, and retains distinct
ended parameter/local records. Completion derives rejection of every scalar or
object UB, erroneous result, resource/authority refusal and unsupported stop.
It is a finite source-AST theorem; source text and compiler output are outside it.

`ParameterContracts.enterParameters_contract` generalizes the entry portion to
arbitrary signed/unsigned parameter lists, with typed initial values, fresh
ordered bindings, read/write authority, old-object frames and capacity deltas.
New clients can reuse it rather than unfold parameter allocation.

## Reusable verification conditions

`Protocol.WP` characterizes successful actual operations with their complete
final state and event trace. `StateVC.vcStmt` recurses over statement syntax;
`BlockVC.vcDecls` extends this to declarations, and `vcProgram` includes entry,
reservation, whole-body coverage and normal cleanup. Exactness theorems connect
these generated conditions to the fixed evaluator. No execution fuel or solver
answer is trusted. `ObjectWP` supplies exact rewrite rules for independent
load/store snapshots, reservation freshness/quota, initialization, cleanup and
scalar outcomes. These rules quantify over the whole state and actual event
trace, including arbitrary malformed states; global consistency and capacity
conservation require their own invariants.

Expression obligations use `ExpressionVC`: the same expression traversal runs
in a predicate-transformer carrier whose connection to actual execution is
proved once. It exposes demanded `CanLoad` snapshots and scalar arithmetic
conditions, with no second expression interpreter. Statement RHSs and local
initializers use this reflected interface. Primitive WP rules expose the
remaining access and lifecycle obligations. Program admissions and result contracts must
be independently stated; certificates additionally require an inhabited entry
domain. Successful execution excludes scalar/object UB, erroneous production,
resource/authority refusal and unsupported syntax through their separate stop
constructors. These conclusions must be proved, never assumed at admission.
Successful-completion WP is false on failure; exact failure diagnostics and
retained effects are separate raw-execution properties.

The expression specialization preserves the complete state on success and
failure and emits only internal ordinary-read events, including retained prefixes
before failure. Any two successfully verified RHS computations at one frozen
state commute up to the returned pair and `List.Perm` of their traces; each
computation retains lazy demand. Failed diagnostics are not reordered. These
facts do not establish general native C/C++ operand-order adequacy. The
internal evaluation order supplies diagnostic priority; it is not a native
C/C++ sequencing or concurrent-interference theorem.

## Limits

This finite grammar has no loops or nested scopes. Self/forward initialization,
assignment expressions, qualifiers, pointers, object bytes/layout/provenance,
atomics and source-connected OS/scheduler effects are also absent. There is no
source-text frontend, compiler preservation or bootstrap-stage proof. The existing
expression-only `Source.Program` remains a separate specialization with immutable
inputs; it does not acquire mutable statements implicitly.

See the [object model](source-objects.md), [source API](source-core-api.md) and
[roadmap](roadmap.md) for the dependency order and environmental boundaries.

The [function-control driver](source-functions.md) generalizes the terminal body
to internal loop control. Existing finite contracts transport through one exact
whole-program theorem, including entry/body/cleanup failures and complete events.
Source-standard loop mapping and progress remain separate obligations.
