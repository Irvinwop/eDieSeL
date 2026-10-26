# Source core API

Import `EDSL.Source` for the reusable semantics and certificate interface, or
`EDSL.Source.Certificates` for its first certified clients. All core declarations
below are in `EDSL.Source`; example declarations are in `EDSL.Source.Examples`.

This API is a finite, typed source expression/return eDSL. It does not accept
native C/C++ text and is not a full GNU language implementation.

## Profile and values

| Declaration | Meaning |
| --- | --- |
| `Dialect.gnuC23`, `Dialect.gnuCpp26` | Recorded language selection. |
| `Target` | Fields `intBits : Nat`, `atLeast16 : 16 ≤ intBits`. |
| `Target.modulus target` | `2 ^ target.intBits`. |
| `Target.signedBound target` | Integer `2 ^ (target.intBits - 1)`. |
| `Target.modulus_pos` | Positivity of the unsigned modulus. |
| `Target.int32` | Convenience value-range profile with 32 bits. |
| `IntType.uint`, `IntType.sint` | Only `unsigned int` and `int`, respectively. |
| `Value target .uint` | `Fin target.modulus`. |
| `Value target .sint` | Integers in `[-signedBound, signedBound)`. |
| `valueDecidableEq`, `valueRepr` | Value equality and executable printing instances. |

`intBits` counts the sign bit for `int`. These are two's-complement value ranges
with ordinary source signed-overflow UB. A `Target` is an admitted abstract
value-range profile, not a description of an available GCC target, object
representation, ABI, integer storage layout, or compiler flag set. No theorem
identifies it with the host machine. Both types have full `int` rank; smaller
types and their promotions are absent.

## Source syntax and external inputs

`Param parameters ty` is a typed parameter reference, using `Param.here` and
`Param.there`. `Inputs target parameters` is a heterogeneous list of external
values, constructed with `Inputs.nil` and `Inputs.cons`. `Inputs.get inputs index`
retrieves a value with the parameter's type.

`Expr target parameters ty` has these constructors:

| Constructor | Operand/result types |
| --- | --- |
| `Expr.literal value` | A representable, already typed `Value target ty`. |
| `Expr.param index` | The type selected by `Param`. |
| `Expr.uadd left right` | `uint × uint → uint`. |
| `Expr.sadd left right` | `sint × sint → sint`. |
| `Expr.udiv left right` | `uint × uint → uint`. |
| `Expr.sdiv left right` | `sint × sint → sint`. |
| `Expr.unsupported feature` | A coverage marker at any result type. |

There are no implicit conversions, usual arithmetic conversions, smaller
integer promotions, lvalues, implicit reads, pointer operations, or overflow
by literal construction. Literal token parsing, suffix selection and unary
negation syntax are not implemented.

`Program target parameters result` has fields `dialect : Dialect` and
`body : Expr target parameters result`. Its sole source program form is
`return expression;`, whose result type equals the expression type.

## Executable evaluation

```lean
evalExpr (inputs : Inputs target parameters)
  (body : Expr target parameters ty) : Outcome (Value target ty)

eval (program : Program target parameters result)
  (inputs : Inputs target parameters) : Outcome (Value target result)
```

`Outcome.defined value`, `Outcome.undefined reason`, and
`Outcome.unsupported feature` are disjoint. `UBReason` has
`signedAdditionOverflow`, `divisionByZero`, and `signedDivisionOverflow`.
`UnsupportedFeature` has `conversion`, `memoryAccess`, `functionCall`, and
`dialectExtension`; these names diagnose missing coverage, not implemented
operations. `Outcome.andThen` propagates either failure outcome.

Arithmetic helpers are `unsignedAdd`, `checkedSigned`, `signedAdd`,
`unsignedDiv`, and `signedDiv`. Unsigned addition reduces modulo `2^intBits`.
Signed addition checks the mathematical sum's range. Both divisions reject
zero; signed division uses `Int.tdiv` (toward zero) and rejects an
unrepresentable quotient.

Evaluation is structural recursion on finite expressions, without fuel or a
divergence outcome. Left-first failure diagnostics are not a C/C++ operand
sequencing guarantee. All supported operands are pure.
`eval_dialect_independent` states that changing only `Program.dialect` leaves
the result unchanged. Dialect extensions must extend this model explicitly.

## Verification and generic semantics

The defining obligation of `Verifies program admitted post` is:

```lean
∀ inputs, admitted inputs →
  ∃ value, eval program inputs = .defined value ∧ post inputs value
```

State `post` as an independent mathematical result property. `admitted` records
external input conditions; callers must prove this equality for every admitted
typed valuation. There is no supplied `NoUB` or definedness premise. An empty
admission predicate makes no claim about any concrete input. Such conditional
judgments remain useful internally but cannot alone constitute a useful
program certificate.

`NoUB program admitted` means that each admitted input has an actual defined
evaluation. This deliberately requires successful completion rather than merely
the absence of an `undefined` outcome; `unsupported` fails it. Theorems
`Verifies.noUB`, `Verifies.excludesUB`, and `Verifies.excludesUnsupported` derive
these consequences from the execution proof.

`semantics target parameters result` instantiates the public `EDSL.Semantics`:

```lean
behaves program inputs observation := eval program inputs = observation
```

`hasBehavior` supplies its concrete evaluator outcome unconditionally, including
failure outcomes. `behavior_unique` proves determinism. `Verifies.satisfies`
exports the postcondition through `EDSL.Satisfies`, rejecting both failure
constructors. Generic refinement/satisfaction alone does not certify source
definedness.

There is no memory, effect trace, OS resource, scheduler or frame component in
this pure grammar. The judgement makes no claim about them. Adding any such
operation requires an explicit semantic state/effect model and corresponding
contract obligations first.

## Nonvacuous certificates

`Certificate program admitted post` contains two proof fields:

| Field | Required evidence |
| --- | --- |
| `useful` | `∃ inputs, admitted inputs` |
| `verified` | `Verifies program admitted post` |

`Certificate.noUB` derives finite completion safety, and
`Certificate.defined_behavior` exhibits an admitted input and its actual defined
result satisfying the postcondition. `no_certificate_for_empty_domain` rules
out certification when admission is false for every input. An inhabited
predicate can still be an inappropriate restriction, and a postcondition can
still encode the candidate evaluator; independent specification review remains
necessary. A certificate covers its entire stated domain, not only its witness.

## First clients and extension point

`Examples.add target dialect` returns the unsigned sum of two parameters.
`Examples.ModularSum target x y result` states the independent equation
`result + carry * 2^intBits = x + y` for a natural carry at most one; result bounds
come from `Value`. `Examples.add_verified` proves this contract for all typed
inputs at every admitted width and for either dialect.
`Examples.add_noUB` is derived from it. `Examples.add_certificate` additionally
constructs a useful admitted input without restricting the all-input theorem.
`divideByZero_not_certified` and `unsupportedReturn_not_certified` show that
no result predicate can hide these programs' safety/coverage failures on their
stated domains.

The remaining checked example theorem names are
`divideByZero_undefined`, `overflowingAdd_undefined`,
`underflowingAdd_undefined`, `overflowingDiv_undefined`,
`negativeDiv_defined`, `unsupportedReturn_outcome`, and
`unsupportedReturn_not_noUB`.

The next syntax feature is explicit same-rank `int`/`unsigned int` conversion
and its usual arithmetic conversion rules, with numeric correctness lemmas.
It remains unsupported here. Additional signed-operation contracts can use the
current API without changing the evaluator.
