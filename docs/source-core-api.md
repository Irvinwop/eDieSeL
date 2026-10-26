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
| `uadd`, `sadd`, `udiv`, `sdiv` | Existing same-type full-rank arithmetic primitives |
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
`unsupported feature`. UB reasons include signed-add overflow, zero division,
and signed-division overflow. Division truncates toward zero. Missing coverage
is not a UB witness or a security defect.

All evaluation is structural recursion on pure finite expressions. Left-first
failure diagnostics make no C/C++ operand-sequencing promise. The evaluator
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
promotions. `Expr.usualAdd` and `.usualDiv` insert promotion, common-type
conversion and the existing primitive. `Expr.promotedAdd` / `.promotedDiv` handle
already promoted operands. Their evaluation laws bind normalization to the
same evaluator. These are not a complete rank engine or source frontend.

For example, unsigned short 65535 plus 65535 returns signed 131070 on the int32
profile, but unsigned 65534 on the int16 profile. With int17/short16 both inputs
fit signed int, yet 65535 plus 1 causes signed-add overflow. Representable
promoted operands do not establish safe arithmetic by themselves.

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

`vcExpr policy inputs expression post` generates structural conditions using
the shared primitives. `vcExpr_iff` and `vc_iff_verifies` prove exactness for the
implemented grammar. `certificate_of_vc` packages an inhabited domain and proved
conditions. The shared `eval_sadd_defined` lemma composes defined operand
executions and proved signed-sum bounds without unfolding the whole program.
Clients reuse numeric lemmas rather than new execution interpreters
or soundness proofs. It does not solve arbitrary conditions automatically.

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

The synthetic `Division.wrappedIncrement` candidate is proved NoUB yet incorrect
for the quotient contract. Zero division, signed boundaries, unsupported coverage,
conversion order and promotion behavior have independent positive/negative checks.
These are embedded-program theorems, without source-file or native correspondence.

```sh
lake build EDSL.Source SourceSemanticsTests
```

The scoped target audits principal theorem dependencies and actual defining
modules. Hosted CI performs authoritative fresh replay, source/object rereads
and final-source policy audits. Memory, lvalues, calls, loops, OS effects,
schedulers, object representations, and the bootstrap chain remain unimplemented
in this source grammar.
