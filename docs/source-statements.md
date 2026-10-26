# Finite object-backed statements

`EDSL.Source.Objects` contains a typed finite declaration and statement eDSL.
It uses the same scalar expression engine as the expression-only API. Formal
parameters and local variables denote actual objects; reading a variable loads
its current contents rather than its original external call value.

This is an executable internal source fragment with checked operational and
verification-condition laws. It does not establish a correspondence with parsed
C/C++ files or all behavior permitted by the language standards.

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

## Reusable verification conditions

`Protocol.WP` characterizes successful actual operations with their complete
final state and event trace. `StateVC.vcStmt` recurses over statement syntax;
`BlockVC.vcDecls` extends this to declarations, and `vcProgram` includes entry,
reservation, whole-body coverage and normal cleanup. Exactness theorems connect
these generated conditions to the fixed evaluator. No execution fuel or solver
answer is trusted.

Expression obligations currently use the exact WP of the shared expression
computation. The stateful generator does not yet expose every expression as
small independent reflective obligations. Primitive contracts discharge object
access and lifecycle conditions. Program admissions and result contracts must
be independently stated; certificates additionally require an inhabited entry
domain. Successful execution excludes scalar/object UB, erroneous production,
resource/authority refusal and unsupported syntax through their separate stop
constructors. These conclusions must be proved, never assumed at admission.

The expression specialization preserves the complete state on success and
failure while retaining demanded-read events. Successful primitive reads
commute under independent access conditions, with traces related by `List.Perm`.
These facts do not yet prove arbitrary expression operand-order adequacy. The
internal evaluation order supplies diagnostic priority; it is not a native
C/C++ sequencing or concurrent-interference theorem.

## Limits

There are no nested scopes, loops, self/forward initialization, assignment
expressions, qualifiers, pointers, object bytes/layout/provenance, atomics or
source-connected OS/scheduler effects in this fragment. There is no source-text
frontend, compiler preservation or bootstrap-stage proof. The existing
expression-only `Source.Program` remains a separate specialization with immutable
inputs; it does not acquire mutable statements implicitly.

See the [object model](source-objects.md), [source API](source-core-api.md) and
[roadmap](roadmap.md) for the dependency order and environmental boundaries.
