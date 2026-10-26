# Source-core rule references

This is a feature-level reference review for the finite source core, dated
2026-10-26. It maps the implemented integer rules to dated primary drafts.
It is not a formal conformance theorem, a source-text correspondence proof,
or a claim of complete GNU C23/GNU++26 support. Lean proofs establish properties
of the declared model; adequacy of that model still needs review.

## Reference identity

- C: [WG14 N3096](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf),
  working draft dated 2023-04-01. Paragraph numbers below refer to that draft.
- C++: [WG21 N5001](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2024/n5001.pdf),
  working draft dated 2024-12-17. Clause content was reviewed in the draft
  project's `n5001` tagged sources:
  [basic.tex](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/basic.tex) and
  [expressions.tex](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex).
  Its [configuration identifies N5001](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/config.tex).

These dated ISO-language drafts do not specify the complete GNU dialects or
pin a GCC implementation. The current dialect selectors record intent; only
the finite shared fragment and explicit dialect-sensitive helpers listed below
have executable rules. Later draft changes, GNU extensions and effective
compiler options need separate review.

## Integer rules

Let `N = target.intBits`. The declarations are in `EDSL.Source`;
[Syntax.lean](../EDSL/Source/Syntax.lean) defines the value profile and
[Operations.lean](../EDSL/Source/Operations.lean) defines scalar operations;
[ExpressionCore.lean](../EDSL/Source/ExpressionCore.lean) provides the shared
traversal and [Eval.lean](../EDSL/Source/Eval.lean) its scalar specialization.

| Feature and current Lean rule | C23 draft reference | C++ draft reference |
| --- | --- | --- |
| `Target.atLeast16`: `N ≥ 16`; `Value` admits unsigned `[0, 2^N)` and signed `[-2^(N-1), 2^(N-1))` values | [N3096 §5.2.4.2.1 ¶1; §6.2.5 ¶11; §6.2.6.2 ¶1–2](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[basic.fundamental]` ¶1–4 and minimum-width table](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/basic.tex#L5019-L5088) |
| `unsignedAdd`: addition modulo `2^N` | [N3096 §6.2.5 ¶11; §6.5.6 ¶6](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[basic.fundamental]` ¶2](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/basic.tex#L5019-L5088), [`[expr.add]` ¶3](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L6346-L6396) |
| `signedAdd` / `checkedSigned`: mathematical addition; an unrepresentable result yields `signedAdditionOverflow` | [N3096 §6.5 ¶5; §6.5.6 ¶6](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[expr.pre]` ¶4](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L59-L73), [`[expr.add]` ¶3](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L6346-L6396) |
| `unsignedDiv`: a zero divisor yields `divisionByZero`; otherwise return the integer quotient | [N3096 §6.5.5 ¶6–7](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[expr.mul]` ¶4](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L6297-L6344) |
| `signedDiv`: division toward zero; reject zero and an unrepresentable quotient, including minimum-signed-value divided by `-1` | [N3096 §6.5.5 ¶6–7 and footnote 118](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[expr.mul]` ¶4](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L6297-L6344) |
| `unsignedSub`, `unsignedMul`: difference/product modulo `2^N`; subtraction does not saturate | [N3096 §6.2.5 ¶11; §6.5.6 ¶7; §6.5.5 ¶5](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[basic.fundamental]` ¶2](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/basic.tex#L5019-L5088), [`[expr.add]`](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L6346-L6396), [`[expr.mul]`](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L6297-L6344) |
| `signedSub`, `signedMul`: mathematical result, checked against the signed range | [N3096 §6.5 ¶5; §6.5.6 ¶7; §6.5.5 ¶5](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[expr.pre]` ¶4](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L59-L73), [`[expr.add]`](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L6346-L6396), [`[expr.mul]`](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L6297-L6344) |
| `unsignedRem`, `signedRem`: reject zero; signed remainder follows the dividend sign and also rejects an unrepresentable quotient | [N3096 §6.5.5 ¶6–7 and footnote 118](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[expr.mul]` ¶4 and footnote 63](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L6297-L6344) |

The last overflow case follows from the reviewed quotient and value-range
rules; the drafts need not enumerate that operand pair. The model's explicit
UB reason is a diagnostic representation, not a claim about a native trap.

## Comparisons, truth and conditional expressions

The core primitives are same-type full-integer comparison and lazy
same-type selection. Source helpers insert promotion, common-type conversion,
truth conversion and the dialect's result typing. The following references
were reviewed at the pinned draft identities above.

| Implemented rule | C23 draft reference | C++ draft reference |
| --- | --- | --- |
| Six integral comparisons after promotion/common conversion; source result C int or C++ bool, numerically 0/1 | [N3096 §6.5.8 ¶4,7; §6.5.9 ¶4–5](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[expr.rel]` ¶2,3,6](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L6679-L6743), [`[expr.eq]` ¶2,7](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L6768-L6887) |
| Integral truth uses the existing zero/nonzero conversion; built-in AND/OR skip the right operand as appropriate | [N3096 §6.3.1.2 ¶1; §6.5.13–14 ¶2–4](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[conv.bool]` ¶1](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L1154-L1161), [`[expr.log.and]`, `[expr.log.or]` ¶1–2](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L6965-L7017) |
| Integral prvalue conditional: execute the condition and one arm; C uses common arithmetic typing; C++ first preserves matching arm types | [N3096 §6.5.15 ¶2–6](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[expr.cond]` ¶1](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L7030-L7039), [¶5–7](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L7142-L7170) |

Conditional helpers cover only unqualified admitted integral **prvalue** arms.
They do not model conditional glvalues, source parameter-name lvalues,
references, cv qualification, bit-fields, classes, pointer/void arms or overloaded
operators. Both arm types determine the result before evaluation. Inserted
conversions stay inside their arm; they do not force skipped evaluation.
Comparisons require both operand values for successful completion. Their
left-first failure diagnostics do not settle general source operand ordering.

Public `eval` performs a whole-body model-coverage preflight, including both
arms, before calling raw `evalExpr`. A marker anywhere produces unsupported,
even if a branch would skip it. This is a tool coverage rule, not an ISO static
constraint or native execution diagnostic. Raw evaluation and its exact VCs
remain lazy. An unselected fully modeled UB expression is not evaluated.
Inhabited certificates derive structural support and the actual raw execution;
`certificate_iff_supported_useful_raw_vc` states the complete boundary.

The guard clients admit all typed inputs. Unsigned division returns zero for a
zero denominator; signed division also returns zero for minimum/-1. The selected
division branch proves its arithmetic premises from the actual guard. Independent
interval/reconstruction contracts yield completion-style NoUB. A nonzero-only
signed guard is universally rejected using actual minimum/-1 UB. These are
embedded-model proofs: no source parsing, volatile/effectful access, compiler
preservation, native correspondence or complete GNU support follows.

## Integral unary expressions

The helpers cover built-in admitted integral values (prvalues in C++).
Unary plus, minus and complement apply integer promotion and return that type.
Logical NOT tests zero/nonzero and returns C int or C++ bool. The reviewed
references are [N3096 §6.5.3.3 ¶1–5 and §6.5 ¶5](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf)
and [N5001 `[expr.unary.op]` ¶7–10](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L4792-L4838),
at the dated identities above. Unrepresentable signed negation follows the
ordinary arithmetic UB rule, rather than wrapping through an unsigned cast.

The pure helper uses promotion for plus, typed zero subtraction for minus,
and signed -1 or unsigned-maximum subtraction for complement. The subtraction
encodes a total complement even at signed endpoints; decomposing it as
negation followed by subtraction would introduce intermediate overflow.
Logical NOT uses truth conversion and selection. Operands occur once.
The inherited minus failure reason is `signedSubtractionOverflow`, an explicit
diagnostic choice, without a native-trap claim.

The `ComplementBits` bridge proves that the unsigned sum-to-all-ones equation,
and the signed sum-to-minus-one equation under the admitted ranges, are
equivalent to flipping every retained value bit. The per-bit specification
does not invoke the subtraction helper or evaluator. These are numeric value
bits, not an object-layout theorem. The current profile's reviewed two's-complement
choice and plain-char policy are described in the
[GCC 15.2 integer implementation](https://gcc.gnu.org/onlinedocs/gcc-15.2.0/gcc/Integers-implementation.html)
and [character implementation](https://gcc.gnu.org/onlinedocs/gcc-15.2.0/gcc/Characters-implementation.html)
documentation. Full GNU and final-C++26 conformance remain outside this review.

## Arithmetic construction and proof scope

`ArithmeticOp` selects the five admitted integer arithmetic operations.
The common construction promotes both operands, selects their common full
integer type, inserts explicit conversions and builds the primitive expression.
It does not perform arithmetic at the original small type's width. Generic
normalization laws connect every operation/type pair to the same evaluator;
the VC generator retains its exactness theorem for the extended grammar.

Independent contracts use bounded borrow, unrestricted product carry,
reconstruction equations and remainder magnitude/sign. The signed quotient-range
proof establishes exactly the minimum/-1 exception for nonzero divisors at every
admitted int width. Although its remainder is mathematically zero, that source
operation remains UB. A nonzero-divisor-only certificate is therefore rejected.
Diagnostic names and the pure evaluator's left-first failure convention are
model interfaces; they do not specify native traps or operand sequencing.

## Scope of the correspondence

The primitive arithmetic constructors accept same-type full-rank operands.
Ordinary small types are promoted before common-type conversion and arithmetic.
Explicit casts cover all admitted integral endpoints. There is no source
literal-token typing or complete integer-rank engine. Relevant rules are
[N3096 §6.3.1.8 and §6.5.5 ¶4 / §6.5.6 ¶5](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf)
and [N5001 `[expr.arith.conv]`](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L1165-L1245).
The implemented subset does not cover the full scope of those rules.

`Target` models value ranges. It does not model object storage, padding bits,
byte order, layout, alignment, ABI or a compiler target. A range restriction
on `Value` does not prove an arbitrary source expression safe; the evaluator
must still check its actual arithmetic. All admitted parameter values are
already typed values, not unvalidated bytes or a parsed call.

The evaluator is finite and pure. Its left-first failure diagnostic is not a
C/C++ operand-sequencing rule. Logical and conditional evaluation have explicit
lazy dependencies.
No source step currently accesses memory, ends a lifetime, calls a function,
interacts with an OS or executes another thread.
Those features require their own language rules and explicit semantic state
before their programs can receive source certificates.

`Verifies`, `NoUB`, `Certificate`, the unsupported marker and their exclusion
lemmas are verification-library interfaces. They are not draft syntax or a
claim that every language diagnostic has been modeled. In particular, finite
`NoUB` means defined completion and excludes unsupported outcomes. See the
[source core API](source-core-api.md) for its precise judgment and existing
example theorems.

## Integral-conversion policy

`Program.conversions` records the fixed `gnuModulo` choice explicitly. The
[versioned GCC 15.2 integer implementation page](https://gcc.gnu.org/onlinedocs/gcc-15.2.0/gcc/Integers-implementation.html)
documents destination-range modulo conversion without a signal. This is the
selected GNU C policy, rather than the full set of behaviors allowed by
[N3096 §6.3.1.3 ¶1–3](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf).
The C++ arithmetic result is justified separately by
[N5001 `[conv.integral]` ¶1–4](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L946-L969).
The same executable conversion code implements this common selected result.
This does not establish correspondence to a real GCC executable or source file.

The supported `int`/`unsigned int` types have equal rank. `commonType` and the
addition/division smart constructors implement only that pair's common-type
rules from N3096 §6.3.1.8 and N5001 `[expr.arith.conv]`: mixed operands convert to
unsigned before arithmetic; two signed operands keep signed arithmetic and its
UB checks. The small-type promotion stage is described below. Explicit casts
cover the admitted small types; extended integer ranks, bit-fields, floats and
pointer conversions remain unsupported. Conversion does not imply a wrapping
policy for signed addition or division. Effective overflow options and their implementation
correspondence remain separate future profile obligations.

## Boolean and cross-width casts

The existing `Expr.convert` covers every source/destination pair among the
admitted bool, plain/signed/unsigned char, signed/unsigned short, and full int
and unsigned int types. Conversion TO bool follows
[N3096 §6.3.1.2 ¶1](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf)
and [N5001 `[conv.bool]` ¶1](https://github.com/cplusplus/draft/blob/6b9b2e9f31aff143334e379e49807488872003e4/source/expressions.tex#L1154-L1161):
zero becomes zero, every nonzero integer becomes one. It is not reduction modulo
two. Bool's existing values 0/1 are representable in all other admitted types.

Other destinations use a value within their half-open numeric range, congruent
to the input modulo that range's span. Representable values are preserved.
The span is `2^width` for these non-bool types, including the sign bit for
signed types. This follows N3096 §6.3.1.3 with the documented GNU signed-result
choice, and N5001 `[conv.integral]` ¶2–4. Explicit source casts are covered by
N3096 §6.5.4 ¶6 and N5001 `[expr.static.cast]` within this common value subset.
Plain char uses the explicit profile choice; the
[GCC 15.2 character implementation page](https://gcc.gnu.org/onlinedocs/gcc-15.2.0/gcc/Characters-implementation.html)
records that native defaults depend on the ABI and signed/unsigned-char options.
No host default is inferred here.

`IntegerCasts.CastSpec` characterizes output integers using zero/nonzero or
bounds and residue equality; it contains no evaluator or conversion helper.
Numeric uniqueness and representability-preservation laws feed the shared
source evaluator and VC. The source cast certificate uses `CastResult`, with
a separate zero/nonzero relation or an integer-carry equation in its postcondition.
The round-trip certificate requires the original
input to fit the intermediate type, a sufficient condition rather than a
necessary one for every signedness-changing pair. Arbitrary narrowing may lose
information. Operand UB and unsupported outcomes propagate through casts.

These rules add no implicit assignment, initialization or return conversion,
source-text frontend, pointer/float cast, storage width, or compiler correspondence.

## Ordinary small integer promotions

The implementation adds bool, plain char, signed/unsigned char and signed/unsigned
short as distinct typed value domains. The range profile explicitly records
`8 ≤ charBits ≤ shortBits ≤ intBits`, `16 ≤ shortBits` and plain-char signedness.
Rank remains bool below char below short below int even when widths coincide.
These are mathematical value widths; bool's `rangeBits = 1` describes 0/1,
not a shared C/C++ object or storage representation.

The primary review used N3096 §5.2.4.2.1, §6.2.5, §6.2.6.2, §6.3.1.1 and
§6.3.1.8, and N5001 `[basic.fundamental]`, `[conv.rank]`, `[conv.prom]` and
`[expr.arith.conv]`. The C++ tagged source identity is
[`6b9b2e9f31aff143334e379e49807488872003e4`](https://github.com/cplusplus/draft/tree/6b9b2e9f31aff143334e379e49807488872003e4).
These dated primary rules require value-preserving promotion based on the whole
source type's range, before common-type arithmetic. They do not choose a type
from the particular operand value.

Signed small types and bool promote to int. An unsigned small w-bit range fits
signed N-bit int exactly when `w < N`; otherwise, within the admitted profiles,
it promotes to unsigned int. Thus unsigned short and int both having 16 bits
does not make their ranks equal or allow signed-int promotion. Proved numeric
range inclusion and preservation support the executable rule. Separate source
contracts prove the subsequent arithmetic safe on their stated domains;
operand representability alone does not establish safe addition/division.

Bit-fields, enums, `_BitInt`, extended/wider types and C++'s distinct Unicode
character types remain outside this rule. Initialization, assignments, implicit
returns, wider types, floats and pointer conversions are not implemented here.
Unsupported constructs remain coverage failures, not source UB.
The model does not infer typedef/token identity, source parsing, ABI/storage
properties or native compiler conformance from these value-level results.
