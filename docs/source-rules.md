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
  [basic.tex](https://github.com/cplusplus/draft/blob/n5001/source/basic.tex) and
  [expressions.tex](https://github.com/cplusplus/draft/blob/n5001/source/expressions.tex).
  Its [configuration identifies N5001](https://github.com/cplusplus/draft/blob/n5001/source/config.tex).

These dated ISO-language drafts do not specify the complete GNU dialects or
pin a GCC implementation. The current dialect selectors record intent; only
the common fragment listed below has executable rules. Later draft changes,
GNU extensions and effective compiler options need separate review.

## Integer rules

Let `N = target.intBits`. The declarations are in `EDSL.Source`;
[Syntax.lean](../EDSL/Source/Syntax.lean) defines the value profile and
[Eval.lean](../EDSL/Source/Eval.lean) defines the operations.

| Feature and current Lean rule | C23 draft reference | C++ draft reference |
| --- | --- | --- |
| `Target.atLeast16`: `N ≥ 16`; `Value` admits unsigned `[0, 2^N)` and signed `[-2^(N-1), 2^(N-1))` values | [N3096 §5.2.4.2.1 ¶1; §6.2.5 ¶11; §6.2.6.2 ¶1–2](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[basic.fundamental]` ¶1–4 and minimum-width table](https://github.com/cplusplus/draft/blob/n5001/source/basic.tex#L4733-L4833) |
| `unsignedAdd`: addition modulo `2^N` | [N3096 §6.2.5 ¶11; §6.5.6 ¶6](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[basic.fundamental]` ¶2](https://github.com/cplusplus/draft/blob/n5001/source/basic.tex#L4759-L4785), [`[expr.add]` ¶3](https://github.com/cplusplus/draft/blob/n5001/source/expressions.tex#L5966-L5969) |
| `signedAdd` / `checkedSigned`: mathematical addition; an unrepresentable result yields `signedAdditionOverflow` | [N3096 §6.5 ¶5; §6.5.6 ¶6](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[expr.pre]` ¶4](https://github.com/cplusplus/draft/blob/n5001/source/expressions.tex#L53-L67), [`[expr.add]` ¶3](https://github.com/cplusplus/draft/blob/n5001/source/expressions.tex#L5966-L5969) |
| `unsignedDiv`: a zero divisor yields `divisionByZero`; otherwise return the integer quotient | [N3096 §6.5.5 ¶6–7](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[expr.mul]` ¶4](https://github.com/cplusplus/draft/blob/n5001/source/expressions.tex#L5908-L5922) |
| `signedDiv`: division toward zero; reject zero and an unrepresentable quotient, including minimum-signed-value divided by `-1` | [N3096 §6.5.5 ¶6–7 and footnote 118](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf) | [N5001 `[expr.mul]` ¶4](https://github.com/cplusplus/draft/blob/n5001/source/expressions.tex#L5908-L5922) |

The last overflow case follows from the reviewed quotient and value-range
rules; the drafts need not enumerate that operand pair. The model's explicit
UB reason is a diagnostic representation, not a claim about a native trap.

## Scope of the correspondence

The arithmetic constructors accept two operands of the same full-rank type.
There is no source literal-token typing, promotion, implicit conversion or
usual-arithmetic-conversion engine yet. The relevant surrounding rules are
[N3096 §6.3.1.8 and §6.5.5 ¶4 / §6.5.6 ¶5](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf)
and [N5001 `[expr.arith.conv]`](https://github.com/cplusplus/draft/blob/n5001/source/expressions.tex#L1078-L1133).
Their presence in the references does not implement their full scope.

`Target` models value ranges. It does not model object storage, padding bits,
byte order, layout, alignment, ABI or a compiler target. A range restriction
on `Value` does not prove an arbitrary source expression safe; the evaluator
must still check its actual arithmetic. All admitted parameter values are
already typed values, not unvalidated bytes or a parsed call.

The evaluator is finite and pure. Its left-first failure diagnostic is not a
C/C++ operand-sequencing rule. No source step currently accesses memory, ends
a lifetime, calls a function, interacts with an OS or executes another thread.
Those features require their own language rules and explicit semantic state
before their programs can receive source certificates.

`Verifies`, `NoUB`, `Certificate`, the unsupported marker and their exclusion
lemmas are verification-library interfaces. They are not draft syntax or a
claim that every language diagnostic has been modeled. In particular, finite
`NoUB` means defined completion and excludes unsupported outcomes. See the
[source core API](source-core-api.md) for its precise judgment and existing
example theorems.
