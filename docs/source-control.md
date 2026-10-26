# Internal control and loop proofs

`EDSL.Source.Objects.Control` provides one executable control machine over
already-bound signed/unsigned int objects. It reuses the shared expression
engine and actual object loads/stores. Clients supply typed code, independent
input/resource conditions, a result/state contract and proof annotations.
They do not supply another interpreter.

This is an internal semantics. It does not yet establish correspondence with
native C/C++ syntax, source-standard loop definedness, compiler output or OS
execution. The [finite function API](source-statements.md) remains available. The separate
[function-control driver](source-functions.md) now connects declarations, actual
parameter/local entry and normal cleanup to these control bodies.

## Code and execution

`Control.Code target context result` contains:

| Constructor | Execution |
| --- | --- |
| `skip` | Continue with pending control |
| `assign variable rhs` | Evaluate the RHS, then store through the current binding |
| `seq first next` | Schedule the two statements in order |
| `branch condition yes no` | Evaluate the condition and schedule one branch |
| `loop condition body` | Test before each iteration; schedule the body followed by the loop when true |
| `ret rhs` | Compute a value and discard remaining control |
| `unsupported feature` | Refuse an unmodeled construct |

Conditions use the internal bool expression type and zero/nonzero truth rule.
The typed environment stores object identities, not cached values. Accesses
check actual current metadata, lifetime and authority. Reads additionally require
initialized contents; assignment can initialize an otherwise admitted object.
A full expression is one control transition with its entire internal
trace; that boundary is not a scheduler atomicity or native operand-order claim.

`Config` records pending control, complete object state, accumulated events
and a status: `running`, `returned value`, `fellThrough` or `stopped reason`.
Return, fallthrough and stop are absorbing. Fallthrough is a control endpoint,
not a scalar return or an invented language-UB classification.

`tick` is the single deterministic transition. `run steps config` observes a
finite number of transitions and returns the actual configuration. A running
configuration at the bound is neither an error nor completion. `Reaches` means
that some finite observation reaches the specified complete configuration;
`Diverges` means every finite observation remains running.

Public `start` scans the entire code tree before execution. Unsupported code
in a skipped branch/body or after an infinite loop is still a coverage refusal.
`startUnchecked` is available for internal composition and compatibility proofs;
its execution alone does not establish whole-code coverage.

## Reusable proof interfaces

Import the relevant module under `EDSL.Source.Objects.Control`:

| Module | Reusable interface |
| --- | --- |
| `Syntax`, `Machine` | Typed code, coverage, one transition function and finite observation |
| `Trace` | Run composition/resumption, terminal stability/uniqueness, invariants and event-prefix laws |
| `Frames` | Caller-world preservation for actual transitions and every finite prefix |
| `Contracts` | Separate prefix, partial-correctness and value-completion contracts |
| `Rules` | Sound finite-progress annotations yielding actual value completion |
| `StructuredVC`, `AnnotationRules` | Backward formulas, loop hints, consequence and checked composition with manual invariants/ranks |
| `FunctionSyntax`, `FunctionEval`, `FunctionCompatibility`, `FunctionContracts`, `FunctionVC` | Shared declarations, entry/cleanup conditions, observation and exact finite-program contract transport |
| `Division` | Repeated-subtraction client with an independent quotient/remainder and state contract |
| `Legacy` | Exact transport of the existing finite statement body |

The judgments have deliberately separate meanings:

| Judgment | Obligation |
| --- | --- |
| `PrefixUBSafe` | Every finite prefix excludes the modeled scalar/object UB stops |
| `PrefixNoFailure` | Every finite prefix excludes every stop, including erroneous production, denied resources, binding faults and unsupported code |
| `PartiallyVerifies` | Every actual returned endpoint satisfies the independent postcondition; safety and termination do not follow |
| `Verifies` | Every admitted initial state reaches an actual finite value return satisfying the postcondition |

A postcondition sees original state, returned value, final state and the entire
actual event history. `PrefixCertificate`, `PartialCertificate` and `Certificate`
also require an admitted-state witness. A useful completion certificate derives
whole-code coverage, prefix NoFailure, modeled UB exclusion and partial
correctness. Safety or success is proved from execution, not placed in admission.
The client must still justify that its admission and postcondition are meaningful
and independent of the candidate execution.

`Control.WorldFrame` preserves external inputs, environment, actor, fresh identity
and automatic-object capacity over every prefix. Assignments can change object
values; unrelated-object frames need their own access/store proofs. This control
fragment has no allocation, cleanup or environmental/interference transition.
Accepted state changes and events survive later failure. Event histories are
append-only, including observations accepted before a failing expression/store.

## Proving a new loop

Use the same steps for each new body:

1. Construct `Code` over typed existing bindings. State readable/writable object
   and input requirements directly, without assuming execution or its result.
2. State a mathematical result and required frames using original/final state.
3. Choose an invariant and a natural rank at useful segment boundaries, such as
   loop headers. Reuse expression, load/store and trace equations for each segment.
4. Prove `FiniteProgress`: every invariant configuration has an **actual finite
   execution** either returning with the postcondition or reaching another
   invariant configuration with a strictly smaller rank.
5. Apply `verifies_of_finiteProgress`, or `Certificate.of_finiteProgress` with an
   admission witness. Derive safety and coverage through the shared projections.

Ranks, invariants and segment bounds occur only in proofs. They are not
execution inputs or loop fuel. Requiring actual finite segments matters: rank
decrease conditional on a body finishing would say nothing about a divergent
body. The shared strong-induction rule excludes that gap, supports early return
and retains the original state and complete event history through composition.
It proves annotation soundness; annotation synthesis and completeness are not
implemented. The structural `StructuredVC.vc` generator automates constructor
composition using annotations for each loop; its soundness is proved once.
Expressions use `ExpressionVC`; assignments expose current registry/write
obligations. No generated clause calls the operational runner or assumes a
result. `verifies_of_vc` additionally requires whole-tree support.

The checked division-VC client proves the loop-plus-return contract through
this generator in 96 lines, reusing local arithmetic/access lemmas. It uses none
of the earlier division run, progress or completion theorems and does not unfold
`tick`, `perform` or `run`. Initialization is outside that demonstration.

For prefix safety without termination, use `PrefixCertificate.of_invariant`
with membership, actual-step preservation and exclusion of stopped states.
That proves a different property from finite value completion. An internally
safe divergent loop cannot satisfy a useful completion certificate.

## Checked division body

`Control.Division` proves repeated-subtraction unsigned division using those
shared rules. Its embedded body has the following shape:

```c
q = 0;
r = n;
while (r >= d) {
    r = r - d;
    q = q + 1;
}
return q;
```

Here q, r and d are distinct, already-bound uint objects. The typed numerator
is an entry value embedded in the initial assignment, rather than a fourth
object. Admission requires reached live q/r objects with current read/write
authority, a readable positive denominator and distinct identities. Old q/r
contents may be uninitialized because initialization by assignment precedes
every read. Admission assumes neither execution nor its result.

`Control.Division.verified` proves actual finite value return for every admitted
target, dialect, typed numerator and positive denominator. The independent
postcondition exhibits a remainder satisfying

`n = d × returned + remainder`, with `0 ≤ remainder < d`.

The final q/r objects hold the quotient/remainder. All other registry entries,
including the denominator, are unchanged; caller inputs, environment, actor,
fresh identity, capacity and old object metadata are preserved. The useful
`Control.Division.certificate` constructs an admitted-state witness, with safety
and coverage derived through the shared certificate projections.

The proof uses invariant `n = d × q + r` and rank r. Each true iteration has an
actual finite header-to-header execution; the guard proves subtraction has no
borrow, the invariant proves quotient increment cannot wrap, and r decreases.
This is a reusable-rule example, not a new interpreter or a constant execution
bound. It ends at internal return and claims no declaration allocation, function
cleanup, native source correspondence or compiler preservation. Large quotients
can still make executing this deliberately simple algorithm expensive.

## Compatibility with finite statements

`Code.ofStmt` embeds the existing `StateSyntax.Stmt` without changing expression
semantics. `Control.Legacy.evalStmt_reaches` and its terminal converse preserve
exact outcome, complete state and appended events for every initial state, including
failures and malformed states. Earlier histories and pending continuations are
supported. `Control.Legacy.runStmt_terminal_iff` additionally preserves public
eager preflight and its exact first unsupported diagnostic.

This compatibility theorem is for an already-bound **statement body**. It does
not transport `Decls`, parameter allocation, local reservation, function entry
or normal-return cleanup. Their full transport is proved separately in
`FunctionCompatibility` for the [function driver](source-functions.md).

## Source progress is a separate obligation

Internal tick counts and ordinary object-read/write events are not evidence of
source-standard forward progress. In particular:

- C23 permits an implementation to assume termination for certain iterations
  with nonconstant controlling expressions that perform no qualifying I/O,
  volatile, synchronization or atomic operations. Constant-expression status is
  a source classification, not runtime truth. See dated
  [N3096 §6.8.5 ¶4](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf#page=173).
- The reviewed C++ draft states a per-thread progress condition. A function
  return is not thread termination, and one qualifying activity does not justify
  a permanently silent suffix. See
  [N5001 §6.9.2.3, intro.progress](https://open-std.org/jtc1/sc22/wg21/docs/papers/2024/n5001.pdf#page=103).
- C++ trivial infinite loops depend on native loop form, constant-expression
  interpretation and body shape. Hosted implementations replace their body by
  a yield invocation; whether this replacement occurs for a freestanding
  implementation is implementation-defined. See
  [N5001 §8.6.1 ¶3](https://open-std.org/jtc1/sc22/wg21/docs/papers/2024/n5001.pdf#page=184)
  and [P2809R3 §6](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2024/p2809r3.html).
  Yield offers rescheduling opportunity without guaranteeing a context switch,
  fairness or synchronization.

Current `Code.loop` retains none of that native classification and has no yield,
volatile, atomic, I/O or scheduler effects. Its `Supported` predicate means
coverage of its internal grammar. A checked source mapping and the required
progress effects must precede general GNU C23/GNU++26 loop claims. Proving an
internal loop terminates is useful evidence; it cannot repair omitted source
operations or establish a source-file correspondence.

See the [source semantics](source-semantics.md), [object model](source-objects.md)
and [roadmap](roadmap.md) for the remaining memory, function, OS and bootstrap
boundaries. The cited dated drafts define the reviewed reference points, not
complete GNU or final C++26 conformance.
