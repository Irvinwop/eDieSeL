# Source semantics and definedness

The primary verification route uses one shared executable Lean semantics for
GNU C23 and GNU++26. The immediate task is the GNU C23 foundation, extended in
the dependency order in the [roadmap](roadmap.md). Complete language support,
a source-text frontend and the bootstrap chain are not implemented.

## Implemented fragment

`EDSL.Source` is a finite typed expression/return eDSL. It currently has:

- Bool, plain char and the signed/unsigned char, short and int types, with explicit
  numeric-width and plain-char-signedness profiles and typed external parameters.
- Addition, subtraction, multiplication, division and remainder after integer
  promotion/common-type conversion. Unsigned arithmetic wraps; signed
  addition/subtraction/multiplication check the mathematical result. Division
  truncates toward zero; signed remainder follows the dividend sign. Zero
  divisors and unrepresentable signed quotients are UB for division and remainder.
- Value-preserving integer promotions and common-type normalization before
  arithmetic, plus explicit casts between every admitted integral type under
  a fixed GNU conversion policy. Conversion to bool tests zero versus nonzero;
  other destinations select the congruent value within their numeric range.
- Six integral comparisons after promotion/common-type conversion, built-in
  logical AND/OR, and lazy conditional expressions with explicit dialect types.
- Distinct defined, undefined and unsupported outcomes, with complete-body
  model-coverage checking before public evaluation.
- Shared execution and verification interfaces, independent arithmetic
  contracts, structural verification conditions, and a certificate requiring a
  useful input domain. Shared composition lemmas support larger expressions;
  guarded quotient clients prove safety for all typed inputs.

The same evaluator interprets both dialect selections. Its present expressions
are pure, so the left-first failure diagnostic does not resolve a C/C++
sequencing question. Wider integer types, lvalues, objects, pointers, memory
operations, calls, loops, OS effects and threads remain unsupported. `Target`
records integer value ranges, not an ABI, storage representation or
compiler/hardware relation.
The [source core API](source-core-api.md) lists exact declarations and limits.
The [rule-reference table](source-rules.md) maps current integer rules to
dated C/C++ draft clauses and records the limits of that review.

The `gnuModulo` conversion policy is recorded once per program. For C23 this
is a GNU implementation choice: ISO C23 allows implementation-defined results
or signals for some conversions to signed, whereas the reviewed C++ rule uses
a modulo result. The shared rule follows the documented GNU choice and keeps
signed arithmetic overflow as UB. It does not claim all ISO C implementations
choose the same conversion behavior.

Casts and promotions are different operations: a promotion preserves the value
while selecting its arithmetic type; an explicit cast may narrow or change its
signed interpretation. Narrowing may discard information; no general cast
round-trip guarantee follows. Converting the integer `2` to bool yields `1`, rather
than reduction modulo two. Other cast destinations use congruence modulo
`2^width`, with plain char following the recorded signedness. Casts
use the shared evaluator and verification-condition interface and propagate an
operand's existing UB or unsupported outcome. A cast after overflowing signed
arithmetic cannot make that arithmetic defined. No implicit return conversion
is added: the current program body and return value still have the same type.

## Comparisons and conditional execution

The comparison helpers cover `==`, `!=`, `<`, `<=`, `>` and `>=` for the admitted
integral types. They promote and convert operands to the common arithmetic
type, then compare mathematical integers. Their independent contract relates
the original inputs to their common-type representatives through range and
carry equations, and states the corresponding equality or order relation.
The result is exactly zero or one. Source-facing helpers return `int` in C
and `bool` in C++; the internal comparison flag is canonical bool.

Truth uses the existing zero/nonzero conversion. Built-in logical AND evaluates
its right operand only when the left is nonzero; OR does so only when the left
is zero. Their source-facing result types follow the same C `int` / C++ `bool`
rule. These helpers concern integral built-in operators, not overloaded C++
operators.

The conditional helper covers integral value arms, restricted to prvalues in
C++. C applies the common arithmetic type to both arms. C++ preserves matching
arm types and otherwise applies the common arithmetic type. The result type
is determined from both arms before execution; conversions stay inside their
respective arms. When the condition succeeds, raw expression execution
evaluates exactly one arm. Condition failure and a selected arm's failure
propagate.

All inputs are immutable typed mathematical values. Reusing a parameter after
a guard observes that same value. These proofs do not concern volatile
accesses or reads of shared/mutable objects, where a denominator might change
between the check and division. The dialect-specific helpers construct the
source result types; changing program metadata alone does not elaborate source
syntax or establish correspondence with a C/C++ text file.

## Coverage before execution

Public `eval` first scans the original complete body for unsupported markers,
including both conditional arms and both logical operands. An unsupported
marker anywhere produces a coverage result before raw execution, even if its
subexpression would be skipped. This is a tool coverage policy, not native
execution or a UB diagnosis. The indexed syntax and this scan do not validate
all language constraints or source text.

A fully modeled arm whose execution would overflow or divide by zero can be
skipped safely. Executing that arm still reports its specified UB. Coverage
therefore checks that rules exist throughout the body; execution proofs
establish safety along the actual selected branches.

`evalExpr` and its raw verification conditions describe this lazy execution.
The public program verification conditions additionally enforce full-body
coverage and remain exact for public evaluation. A nonvacuous `Certificate`
therefore establishes supported syntax as well as actual defined behavior and
the independent result. Success of a raw expression or raw VC alone cannot
certify a program containing a skipped unsupported marker.

## One semantic implementation

Source eDSL terms describe programs. A shared evaluator or transition system
specifies their behavior. C and C++ reuse common rules; language differences,
implementation choices and compiler flags are explicit. A program supplies
syntax, a contract, invariants and proofs. It does not install a new evaluator.

Each extension must add actual language rules and checked consequences.
A parser or elaborator also needs a checked link between source text and the
embedded program before a theorem concerns a file. An arithmetic AST theorem
does not by itself establish a theorem about similar-looking C/C++ text.

## Definedness and correctness

State the input domain and independent contract first. For the present finite
deterministic fragment, `Verifies program admitted post` requires:

```text
For every admitted typed input,
there is an actual defined evaluation whose result satisfies post.
```

`NoUB` is derived from that execution proof. In this fragment it deliberately
means **defined completion**, excluding unsupported outcomes as well as UB.
It is stronger than a general UB-freedom judgment for a language with loops.
Before admitting loops or effects, coverage, safety, erroneous behavior,
termination and scheduling progress need separate obligations.

Conditional judgments can hold for an empty domain. `Certificate` therefore
also requires an admitted-input witness, and its theorem covers every admitted
input. This rules out an empty claim; it does not establish that the domain
or postcondition is appropriate. Those must be reviewed independently of the
candidate evaluator. Defining admission as “this program is UB-free” or the
contract as “the evaluator's answer” would evade the intended proof obligation.

The first positive contract is unsigned addition for all typed inputs and every
admitted width, under both dialect selections. Its mathematical specification
is a bounded-carry equation, independent of the evaluator's modular reduction.
Boundary examples distinguish signed overflow, zero division, signed-division
overflow and truncation toward zero. An unsupported nested expression cannot
be certified as a successful return, regardless of the chosen result predicate.

The unsigned-division certificate covers every typed numerator and nonzero
denominator, using the independent interval `q*d ≤ n < (q+1)*d`. A synthetic
`(n+1u)/d` candidate is proved free of UB on the same domain, but its result
violates that interval at `UINT_MAX, d=1`. This separates proved safety from
functional correctness. Structural verification conditions are proved exact
for this grammar and construct the same execution-based certificates.

The guarded quotient clients instead use admission `True` over all typed
parameter values. Their guards derive the conditions required by division:

| Embedded client | Independent result contract |
| --- | --- |
| Unsigned quotient with a nonzero-divisor guard | Return zero when `d = 0`; otherwise prove `q*d ≤ n < (q+1)*d`. |
| Signed quotient guarded against zero and minimum-signed-value divided by `-1` | Return zero on either exceptional class; otherwise exhibit `r` with `n = q*d + r`, `abs(r) < abs(d)`, and either `r = 0` or `sign(r) = sign(n)`. |

Both certificates provide inhabited domains and derive `NoUB` from actual
defined execution; they assume neither a nonzero divisor nor program safety
in admission. A synthetic signed client checking only `d != 0` reaches UB
at minimum-signed-value / `-1`, so no result predicate can give it an
all-input certificate. These are proofs of embedded core programs, not parsed
source files.

## Outcomes as the language grows

| Outcome | Required treatment |
| --- | --- |
| Defined execution | Actual execution evidence and an independent result/effect contract |
| Undefined behavior | Visible language violation, proved absent for all covered executions |
| Unsupported construct | Missing semantics; no successful verification or defect verdict |
| Unspecified choice | Represent all permitted choices and prove the contract for each |
| Implementation-defined choice | Record one consistent policy or quantify over compatible profiles |
| C++ erroneous behavior | Separate classification and clean-code exclusion obligation |
| Divergence, blocking or deadlock | Explicit behavior; termination and progress proved separately |
| Translation/constraint error | Source validation outcome, distinct from runtime UB |
| OS or library failure | Explicit outcomes, partial effects and cleanup obligations |

A missing transition cannot establish safety by leaving no executions. An
extension must establish behavior existence, coverage of legal choices and
appropriate terminal/blocked/error classifications. Fuel exhaustion and proof
timeouts are incomplete engineering results, not language behaviors.

## Environment and bootstrap

OS resources, scheduler choices, memory, synchronization and inputs are semantic
objects. Effectful source constructs require their state, traces, failure rules
and contracts before admission. Existing machine/resource models become source
evidence only through checked connections to source steps. Abstract interfaces
remain explicit until their implementation sources and composition are proved.

The bootstrap chain begins with exactly one minimal binary seed, then source
proofs of each stage's safety and compiler/interpreter contract. Compiler
preservation is an additional theorem: safe execution of a compiler does not
establish the correctness of its output. See the [bootstrap dependency plan](bootstrap.md)
and [trust boundaries](trust.md).

## Language references

The initial reference inventory includes the public
[WG14 N3096 C23 draft](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf),
[WG21 N5001 C++ draft](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2024/n5001.pdf),
[GCC language standards](https://gcc.gnu.org/onlinedocs/gcc/Standards.html) and
[GNU extensions](https://gcc.gnu.org/onlinedocs/gcc/C-Extensions.html).
The [current rule review](source-rules.md) records the arithmetic reference
inventory. Comparison, logical and conditional rules are reviewed against
[N3096 §§6.5.8–6.5.15](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf)
and N5001
[`[expr.rel]`, `[expr.eq]`, `[expr.log.and]`, `[expr.log.or]` and `[expr.cond]`](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex).
Future features need the same dated traceability.
These documents and manual reviews do not establish full conformance. In particular,
recording the dialect name in the current AST does not implement every rule
of that dialect.
