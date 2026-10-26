# Source semantics and definedness

The primary verification route uses one shared executable Lean semantics for
GNU C23 and GNU++26. The immediate task is the GNU C23 foundation, extended in
the dependency order in the [roadmap](roadmap.md). Complete language support,
a source-text frontend and the bootstrap chain are not implemented.

## Implemented fragment

`EDSL.Source` is a finite typed expression/return eDSL. It currently has:

- Full-rank `int` and `unsigned int` values under an explicit integer-width
  profile, with typed externally supplied parameters.
- Unsigned modular addition, checked signed addition, unsigned division and
  signed division toward zero.
- Distinct defined, undefined and unsupported outcomes.
- Shared execution and verification interfaces, independent unsigned-addition
  and division contracts, structural verification conditions, and a certificate
  requiring a useful input domain.

The same evaluator interprets both dialect selections. Its present expressions
are pure, so the left-first failure diagnostic does not resolve a C/C++
sequencing question. There are no conversions, lvalues, objects, pointers,
memory operations, calls, loops, OS effects or threads. `Target` records integer
value ranges, not an ABI, storage representation or compiler/hardware relation.
The [source core API](source-core-api.md) lists exact declarations and limits.
The [rule-reference table](source-rules.md) maps current integer rules to
dated C/C++ draft clauses and records the limits of that review.

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
The [current rule review](source-rules.md) records the dated clauses for integer
ranges, addition and division; future features need the same traceability.
These documents and manual reviews do not establish full conformance. In particular,
recording the dialect name in the current AST does not implement every rule
of that dialect.
