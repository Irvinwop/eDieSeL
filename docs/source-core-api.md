# Source core API

Import `EDSL.Source` for the reusable finite expression/return eDSL. It uses one
executable semantics and structural verification-condition generator. It does
not parse native source text or implement complete GNU C23/GNU++26.

## Types and value profiles

`Dialect` records `gnuC23` or `gnuCpp26`. The current common pure fragment has
identical execution under the same target and conversion policy.

`Target` records mathematical integer ranges:

| Field | Constraint or meaning |
| --- | --- |
| `intBits`, `atLeast16` | Full integer range width, including the signed sign bit; at least 16 |
| `charBits`, `charAtLeast8` | Ordinary character range width; at least 8 |
| `shortBits`, `shortAtLeast16` | Short integer range width; at least 16 |
| `charLeShort`, `shortLeInt` | Non-strict width ordering; equal widths are allowed |
| `plainCharSigned` | Explicit signedness choice for plain char |

`Target.int32` selects int32/char8/short16 and signed plain char. `Target.int16`
selects int16/char8/short16 and signed plain char. These are value profiles, not
ABI, object-size, padding, byte-order, compiler-target or hardware descriptions.
`Target.modulus` is `2^intBits`; `Target.signedBound` is `2^(intBits-1)`.

`IntType.uint` and `.sint` are full `unsigned int` and `int`.
`IntType.small` takes one of `SmallType.boolean`, `plainChar`, `schar`, `uchar`,
`sshort`, or `ushort`. `SmallType.rank` records bool below char below short;
`IntType.rank` places both full int types above them. Rank does not collapse
when widths coincide. Long, enums, bit-fields, extended and bit-precise types
are not implemented.

`Value target .uint` is `Fin target.modulus`; `.sint` is the bounded signed Int
subtype. Small values are bounded Int subtypes using `SmallType.lowerBound`
and the exclusive `upperBound`. Signed ranges use two's complement; unsigned
ranges are nonnegative. `Value.toInt`, `Value.range`, and
`Value.toInt_injective` expose their mathematical meaning. Bool has exactly 0
and 1, as proved by `Value.boolean_values`. Its `rangeBits = 1` describes that
value set; it makes no claim of one-bit storage.

## Syntax and execution

`Inputs target parameters` is a heterogeneous list of externally supplied typed
values. `Param.here` / `.there` select them; `Inputs.get` retrieves a value.
No input generator, memory load, object initialization or ABI is hidden here.

| Expression constructor | Behavior |
| --- | --- |
| `literal value` | An already representable typed value, without token parsing or truncation |
| `param index` | A supplied parameter |
| `promote operand` | Value-preserving integer promotion to a full arithmetic type |
| `convert destination operand` | Explicit cast between every admitted integral source and destination |
| `uadd`/`sadd`, `usub`/`ssub`, `umul`/`smul`, `udiv`/`sdiv`, `urem`/`srem` | Same-type full-rank addition, subtraction, multiplication, division and remainder |
| `compare operation kind left right` | Compare same-type full-rank integers; canonical internal bool result |
| `select condition yes no` | Evaluate a bool condition, then exactly one same-typed arm |
| `unsupported feature` | Explicit missing coverage, never successful verification |

`Program target parameters result` contains `dialect`, an explicitly supplied
`conversions : IntegerConversionPolicy`, and `body`. Its only form is
`return expression;`, with exactly the body's result type. There is no implicit
return, assignment or initialization conversion.

Only `IntegerConversionPolicy.gnuModulo` is implemented: bool conversion tests
zero/nonzero; other integral destinations select the destination-range modulo
representative without a signal.
For C23 this records a GNU choice, rather than all ISO C implementations. It
never changes signed arithmetic overflow into wrapping. See the
[rule references](source-rules.md).

```lean
evalExpr (policy : IntegerConversionPolicy) (inputs : Inputs target parameters)
  (body : Expr target parameters ty) : Outcome (Value target ty)

eval (program : Program target parameters result)
  (inputs : Inputs target parameters) : Outcome (Value target result)
```

The disjoint outcomes are `defined value`, `undefined reason`, and
`unsupported feature`. UB reasons distinguish signed addition, subtraction and multiplication overflow,
zero division, and division/remainder quotient overflow. Signed division
truncates toward zero and signed remainder follows the dividend sign.
An unrepresentable quotient makes remainder undefined even when its mathematical
value is zero, including the signed minimum with divisor -1. Missing coverage
is not a UB witness or a security defect.

All evaluation is structural recursion on pure finite expressions. Public
`eval` first checks `Expr.firstUnsupported` across the complete body, including
both conditional arms. Any marker gives an unsupported outcome before execution
diagnostics. This is a tool-coverage phase, not source execution or type checking.
`Expr.Supported` means this scan returned `none`.

Raw `evalExpr` evaluates only the selected arm. Thus an unselected, fully modeled
division-by-zero expression does not fail execution; an unselected missing-rule
marker still prevents public certification. `eval_defined_iff` characterizes
public success as full-body support together with actual raw defined execution.
Left-first arithmetic/comparison failure diagnostics make no general C/C++
operand-sequencing promise. The evaluator
executes each operand before promotion/conversion; neither operation repairs
operand UB or unsupported coverage. Casts are total on defined integral operand
values; this does not make unsupported operands or arithmetic UB defined.

## Integral casts

`IntegerCasts.castValue destination value` implements numeric conversion for
all admitted type/profile pairs. Bool maps zero to zero and every nonzero integer
to one. Every other destination selects the representative in its half-open
range with the same residue modulo `IntType.span = upperBound - lowerBound`.
`CastSpec` states these rules independently using only mathematical integers,
bounds and residues. It does not call the cast implementation or evaluator.

`castValue_spec`, `castValue_unique` and `castValue_eq_iff` prove the
characterization. `castValue_preserves` proves mathematical-value preservation
when the input fits the destination, and `castValue_self` proves same-type
identity. Boolean zero/nonzero corollaries are distinct from modular congruence.
The full int/unsigned-int round trips reuse `IntegerConversions`; arbitrary
narrowing can lose information and cannot generally be reversed.

These numeric lemmas are used by the existing `Expr.convert`, `convertValue`,
`evalExpr` and `vcExpr`. They do not add a second source interpreter, implicit
return conversions, storage semantics, or conversions of pointers/floats.

## Promotion and usual arithmetic

`ArithmeticType.sint` / `.uint` embed into `IntType` through `asIntType`.
`promotedType target source` depends on the whole source type and profile:

- Full int types stay unchanged.
- Bool and signed small types promote to signed int.
- An unsigned small type promotes to signed int if its width is strictly smaller
  than `intBits`; otherwise it promotes to unsigned int.
- Plain char follows its recorded signedness.

`IntegerPromotions.small_range_embeddable` proves that every value fits the
chosen type. `promoteValue` embeds it without truncation or modulo, and
`promoteValue_toInt` proves exact mathematical preservation at every admitted
width. Sign and zero corollaries follow. Promotion of a valid value is total;
a later signed operation can still overflow.

`commonType target left right` selects a full arithmetic type **after** these
promotions. `ArithmeticOp` selects addition, subtraction, multiplication, division
or remainder. `Expr.usualBinary` inserts promotion and common-type conversions;
`Expr.promotedBinary` handles already promoted operands, and `Expr.primitiveBinary`
builds the corresponding same-type grammar node. These construct syntax rather
than executing it. `Expr.usualAdd`, `.usualSub`, `.usualMul`, `.usualDiv` and
`.usualRem` are convenience forms of that shared construction.

`commonBinary` selects the evaluator's existing numeric primitive. The generic
`eval_promotedBinary` and `eval_usualBinary` laws bind every operation/type pair
to the same operand evaluation, conversions and primitive, including failures.
Existing addition/division helpers and evaluation laws remain available. This
is not a complete rank engine or source frontend.

For example, unsigned short 65535 plus 65535 returns signed 131070 on the int32
profile, but unsigned 65534 on the int16 profile. With int17/short16 both inputs
fit signed int, yet 65535 plus 1 causes signed-add overflow. Representable
promoted operands do not establish safe arithmetic by themselves.

## Comparisons and lazy expressions

`ComparisonOp` includes `eq`, `ne`, `lt`, `le`, `gt` and `ge`.
`Expr.usualCompare` promotes both operands, converts them to their common
arithmetic type and uses the primitive comparison. `Expr.sourceCompare` then
adapts the result to `Dialect.logicalType`: signed int in C, bool in C++.
Both have the integer value 0 or 1. `ComparisonOp.Relates` specifies the
mathematical relation; generic comparison certificates use independently
specified common-type representatives through `CastContracts.CastResult`.

`Expr.truth` converts an integral expression by zero/nonzero. `Expr.logicalAnd`
and `Expr.logicalOr` build lazy selections and adapt the final logical result
to the dialect. The right operand executes only when the left requires it;
a failed condition or selected operand propagates its failure.

`Expr.conditional dialect condition yes no` covers unqualified integral
**prvalue** arms. C uses `commonType`; C++ preserves identical arm types and
otherwise uses `commonType`. `conditionalType` records that result index.
Conversions stay inside each arm so the unselected arm is not evaluated.
This is not the full C++ conditional type algorithm: lvalues, cv qualification,
classes and pointers are outside this grammar.

These operations read immutable typed parameters. A guarded denominator cannot
change between the test and division in this model. A proof here does not
justify volatile/shared reads, overloaded operators, or effectful sequencing.

## Integral unary operators

`UnaryOp` selects `plus`, `minus`, `complement` or `logicalNot`.
`Expr.unary dialect operation operand` builds the corresponding expression.
The individual helpers are `Expr.unaryPlus`, `.unaryMinus`, `.unaryComplement`
and `.logicalNot`. The first three return the integer-promoted operand type;
logical NOT returns C int or C++ bool. `unaryType` records this result index.

These are constructions over the existing evaluator and exact VC generator.
Plus promotes the operand. Minus subtracts it from a correctly typed zero;
unsigned results wrap, while signed minimum negation is UB. Complement
subtracts from signed -1 or unsigned maximum after promotion; it is defined
even at signed minimum and maximum. NOT evaluates truth once and inverts it.
Each construction contains one occurrence of its operand. Its failure and
unsupported markers remain observable through raw execution and public coverage.

`IntegerUnary` proves the arithmetic laws and the exact minimum exception.
`ComplementBits.NatBits` and `.IntBits` independently require every value bit
below the width to flip. `nat_sum_iff_bits` and `int_sum_iff_bits` connect these
predicates to the arithmetic equations, including signed-range uniqueness.
They concern mathematical width-bounded residues, without object-storage,
padding or ABI claims.

The inherited signed-minus diagnostic is `signedSubtractionOverflow` because
the helper uses the existing checked subtraction. This is a tool diagnostic,
not a native exception. Arithmetic negation and complement remain different:
the former rejects signed minimum, while the latter is total on typed values.
For example, complementing uchar255 on the int32/char8 profile returns int-256.
It complements the promoted int value, not an eight-bit object.

The helpers cover admitted integral values and built-in C++ prvalues. They
do not add pointer, floating, enum, overloaded, lvalue or source-text rules.

## Verification and reuse

`Verifies program admitted post` requires, for every admitted input, an actual
defined evaluation and the independent result predicate. It accepts no supplied
NoUB premise. `Verifies.noUB`, `.excludesUB`, `.excludesUnsupported` and
`.satisfies` export its consequences through the shared `EDSL.Semantics` adapter.
`hasBehavior` includes failure outcomes and is not a safety certificate.

`NoUB` in this finite fragment means **defined completion**, excluding unsupported
outcomes too. Before loops/effects, safety, supported coverage, erroneous behavior
and termination must be separated. This API currently expresses no divergence.

`Certificate` adds `useful : ∃ inputs, admitted inputs` to `verified : Verifies`.
Its `.noUB` and `.defined_behavior` derive actual safety/behavior, and
`no_certificate_for_empty_domain` rejects empty claims. A witness does not
establish that the chosen domain or result is the intended specification;
review both independently. Do not define admission by this candidate's NoUB or
postconditions by rerunning its evaluator.

`Certificate.supported` derives whole-body coverage, including skipped arms,
from the certificate's inhabitation and successful execution. Its
`.raw_verified` exposes defined raw execution with the same postcondition.
`no_certificate_with_unsupported` rejects any public certificate containing a
missing-rule marker. `certificate_iff_supported_useful_raw_vc` characterizes
certification as support, inhabited admission and the exact raw conditions.

`vcExpr policy inputs expression post` generates structural conditions using
the shared primitives. `vcExpr_iff` and `vc_iff_verifies` prove exactness for the
implemented grammar. Raw `vcExpr` follows selected execution; public `VC`
adds the same full-body preflight as `eval`. An unselected modeled-UB arm has
no runtime obligation. `certificate_of_vc` packages an inhabited domain and proved
conditions. The shared `eval_sadd_defined` lemma composes defined operand
executions and proved signed-sum bounds without unfolding the whole program.
Clients reuse numeric lemmas rather than new execution interpreters
or soundness proofs. It does not solve arbitrary conditions automatically.

## Reusable arithmetic laws

`IntegerArithmetic` connects the shared primitives to independent result
relations. Unsigned subtraction uses a borrow equation with borrow at most one;
unsigned multiplication uses an unrestricted natural carry for the whole product.
Unsigned remainder uses a reconstruction equation and a result below the divisor.
Signed subtraction/multiplication state exact mathematical results and overflow
boundaries. These laws derive primitive definedness from typed operands and numeric conditions.

`TruncatingDivision` specifies quotient/remainder by reconstruction, remainder
magnitude and the dividend's sign, without calling division or remainder.
`signedDiv_quotient_fits_iff` identifies the minimum/-1 exception for every
typed nonzero signed divisor. `signedRem_defined_iff` proves actual remainder
existence exactly for a nonzero divisor outside that pair; its zero and overflow
reasons have separate iff characterizations. A remainder's own representability
does not excuse an unrepresentable quotient.

## Certified clients

Import client modules explicitly; the reusable umbrella excludes synthetic clients.
Every listed positive certificate derives NoUB on its stated domain.

| Module and client | Domain and independent specification |
| --- | --- |
| `Examples.add` / `Examples.add_certificate` (module `Source.Certificates`) | All typed unsigned inputs; bounded carry equation for their sum |
| `Division.quotient` | Every numerator and nonzero unsigned denominator; quotient interval |
| `ConversionContracts.toUnsigned`, `.toSigned` | All typed inputs; bounded representative equations |
| `ConversionContracts.roundTrip` | All signed inputs; original mathematical value |
| `ConversionContracts.mixedAdd`, `.mixedDiv` | All mixed-add inputs or nonzero mixed-division denominators; carry equations or quotient interval |
| `PromotionContracts.promoteReturn` | All types/profiles/inputs; exact mathematical-value preservation through the shared VC path |
| `PromotionContracts.booleanAdd` | All boolean inputs/profiles; exact sum, overflow discharged from 0/1 bounds |
| `PromotionContracts.unsignedShortAdd` | All typed inputs on int32 or int16 profiles; exact signed sum or unsigned carry equation respectively |
| `CastContracts.castReturn` | All admitted types/profiles/inputs; `CastResult` states zero/nonzero or bounds and an integer-carry equation |
| `CastContracts.representableRoundTrip` | Input fits the intermediate type; exact original value, with an inhabited numeric domain |
| `CastContracts.lowByteAdd` | All unsigned int inputs on int32/char8; exact sum of the two residues modulo 256, bounded by 510 |
| `ArithmeticContracts.unsignedReturn` | All five operations; all unsigned inputs, except a nonzero denominator for division/remainder; independent equations or quotient interval |
| `ArithmeticContracts.signedReturn` | All five operations; explicit mathematical result ranges for add/sub/mul, nonzero denominator and exclusion of minimum/-1 for division/remainder; exact results or truncating reconstruction |
| `ArithmeticContracts.subtractAdd` | All unsigned inputs/profiles; subtraction then addition recovers the first operand, including wrapping intermediates |
| `ArithmeticContracts.byteProduct` | All uchar inputs on int32/char8; exact signed product, overflow discharged from operand ranges |
| `ComparisonContracts.compareReturn` | All six comparisons, admitted integral type pairs, profiles and typed inputs; independent normalized representatives and mathematical relations |
| `GuardContracts.guardedUnsigned` | All typed numerator/denominator inputs; return zero for zero denominator, otherwise satisfy an independent quotient interval |
| `GuardContracts.guardedSigned` | All typed inputs; return zero for zero denominator or minimum/-1, otherwise satisfy truncating reconstruction with bounded, correctly signed remainder |
| `UnaryContracts.unaryReturn` | All four unary operations, types/profiles/dialects; plus/complement/NOT admit all typed inputs; minus excludes numeric minimum only when the promoted type is signed. Independent value, carry, per-bit and zero/nonzero contracts |

The synthetic `Division.wrappedIncrement` candidate is proved NoUB yet incorrect
for the quotient contract. Zero division, signed boundaries, unsupported coverage,
conversion order and promotion behavior have independent positive/negative checks.
`signedRem_nonzero_not_certified` rejects the overbroad signed-remainder domain
that excludes only zero divisors, for every target and result postcondition.
`GuardContracts.nonzeroGuardedSigned_not_certified` likewise rejects a program
whose internal guard checks only nonzero: minimum/-1 actually executes UB.
The positive guarded clients have admission `True`; their guards establish the
division preconditions locally instead of requiring them of callers.
`UnaryContracts.signedMinus_all_inputs_not_certified` rejects an all-input
signed-negation certificate for every postcondition. The generic minimum
counterexample also covers signed small types that promote at equal widths.
These are embedded-program theorems, without source-file or native correspondence.

```sh
lake build EDSL.Source SourceSemanticsTests
```

The scoped target audits principal theorem dependencies and actual defining
modules. Hosted CI performs authoritative fresh replay, source/object rereads
and final-source policy audits. Memory, lvalues, calls, loops, OS effects,
schedulers, object representations, and the bootstrap chain remain unimplemented
in this source grammar.
