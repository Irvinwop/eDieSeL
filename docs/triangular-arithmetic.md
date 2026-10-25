# Triangular arithmetic contracts

The mathematical result is the natural number n(n+1)/2, reduced modulo 2^64.
The API keeps that specification separate from a loop or a compiler's algebraic
transformation. It supplies reusable arithmetic for a countdown loop and for
the closed expression in the frozen Clang triangular routine.

| Module | Checked interface |
| --- | --- |
| [WordMath.Triangular](../EDSL/WordMath/Triangular.lean) | Natural triangular numbers, modular result existence/uniqueness, one-step and two-step recurrences, and accumulated-budget conservation |
| [WordMath.Triangular32](../EDSL/WordMath/Triangular32.lean) | Unsigned widening/product bounds, wrapped low32 decrements and universal correctness of the reduced word expression |
| [Arithmetic64.Triangular](../EDSL/Arithmetic64/Triangular.lean) | Independent callable Spec with an unsigned low32 argument and full64 result |

The first module imports only Init. The width-specific arithmetic imports that
module; it has no decoder, executor, code bytes or OS assumptions.

## Use in a program proof

For a countdown that adds two consecutive terms, use the invariant

~~~text
accumulated + triangular remaining = triangular input
~~~

The theorem triangular_budget_two preserves this equality after adding
2*remaining−1 and reducing remaining by two. Its only range premise is
2≤remaining; it does not assume remaining is even. A concrete loop still needs
a decreasing rank, actual instruction/branch behavior, entry/exit handling and
the caller's register, flag and memory frames.

For the reduced closed form, reducedTriangular32_toNat covers every BitVec32
input. It treats zero separately and proves that the wrapped decrement at one
is harmless because its companion factor is zero. It establishes the unsigned
64-bit product and addition bounds before the logical division by two.
No signed-IMUL fit assumption is made: a product can fit unsigned64 while
overflowing signed64. A machine proof must retain the executor's independent
undefined flag choices and cannot infer flag facts from the unsigned bound.

The independent triangularModulo Spec binds only RDI's low32 bits and constrains
the full64 RAX result. triangularModulo_bound_iff permits arbitrary upper32
argument bits. Its domain is True, so zero and one are included; the separate
useful predicate selects inputs at least two without narrowing that domain.
Its result exists uniquely for every input. The ordinary PureCall admission,
ABI, loaded-code and current-resource obligations remain separate.

## Current scope

All 22 arithmetic/Spec theorems are checked without project axioms or proof
holes. The modules are included in the full audit catalogue and fresh replay;
CI also checks their source with warnings as errors, autoImplicit=false,
heartbeats 300000 and recursion depth 128.

These theorems do not certify either frozen triangular binary. The Clang
routine has an accepted 14-node CFG; its vector execution and loaded-resource
proof remain open. GCC needs its exact NOP7 encoding and a complete loop proof,
with a compatible callable execution/resource adapter. The reusable
[Bool-to-flags adapter](bool-policy-refinement.md) can transport a bounded Bool
proof and its actual read policy without changing the callable contract.
Source/IR preservation,
native CPU or OS correspondence, concurrency and performance minima are not
established. The accepted corpus score remains 20/40 functions and 40/80
compiler artifacts.
