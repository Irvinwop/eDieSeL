# Binary search

The library proves the behavior of the complete frozen Clang binary-search
function through the shared x86-64 verification-condition generator. The
contract accepts a nondecreasing array of unsigned 32-bit values, including
duplicates, and returns any matching index or the full 64-bit `SIZE_MAX` value
if the key is absent.

```lean
import EDSL.BinarySearch.Clang.Resources

#check EDSL.BinarySearch.Clang.semantics
#check EDSL.BinarySearch.Clang.resources
```

The proof covers all admitted input lengths and keys, every independent modeled
AF choice, and both empty and nonempty arrays. It preserves the complete memory
and permission map, the caller's return address and stack adjustment, the
callee-saved registers, and all nonarithmetic flag bits. Every actual data read
requires the original snapshot and current buffer authority. Empty arrays
require no DATA loan or readable data address.

This is a machine-body and resource result. Named-ELF custody, installation,
packet admission and the GCC counterpart remain open. It adds no corpus credit;
conditional corpus coverage remains 20/40 functions and 40/80 artifacts.

## Independent contract and interval rules

[`EDSL.BinarySearch.Contract`](../EDSL/BinarySearch/Contract.lean) binds the
array base, full-width count and low32 key to the shared buffer-call API. Upper
bits of the key argument are unrestricted. The independent result requires an
in-range equal element or absence from the complete input; a truncated 32-bit
sentinel cannot satisfy it.

[`EDSL.WordMath.BinarySearch`](../EDSL/WordMath/BinarySearch.lean) supplies the
natural-number mathematics. For `values : Nat → Nat` and length `size`,
`Sorted values size` describes nondecreasing order. The invariant records
`low ≤ high ≤ size`, values strictly below the key before `low`, and values
strictly above it from `high` onward.

| Rule | Result |
| --- | --- |
| `initial` | Establish the interval `[0, size)`, including empty input. |
| `midpoint_bounds` | The midpoint lies inside a nonempty interval. |
| `matches_remain` | Every match remains in the current interval. |
| `advance_low`, `retreat_high` | Preserve the invariant after an unequal midpoint. |
| `found`, `exhausted` | Establish the independent match or absence relation. |
| `advance_low_rank`, `retreat_high_rank` | Both continuing branches decrease `high - low`. |

The [`Word`](../EDSL/WordMath/BinarySearch/Word.lean) and
[`Transitions`](../EDSL/WordMath/BinarySearch/Transitions.lean) modules connect
full-width machine arithmetic to these bounds. They justify subtraction-based
midpoints and endpoint updates without a low32 index restriction or a
nonoverflow assumption on the sum of the endpoints.

## Reuse for another branching program

The search client supplies its contract, register frame, two cutpoint
invariants, decreasing rank and seven whole-block cases. Decoder, executor,
read policy, call resources and branch reasoning come from shared APIs:

| API | Responsibility |
| --- | --- |
| `EDSL.X86.VCGen.Proposal` | `vcgen_proposal` and `vcgen_cfg_data` propose finite graph data; each consumer independently proves `CFG.Valid`. |
| `EDSL.X86.VCGen.Branch` | Checked short-branch WP rules retain destination, taken-target canonicality, fuel, invariant and strict rank obligations. |
| `EDSL.X86.VCGen.BranchTactics` | `vcgen_branch_block` selects the decoded branch family before state expansion, then uses the existing block generator. |
| `EDSL.X86.VCGen.BufferCall` | Derive universal execution, read-policy and resource claims from checked blocks. |
| `EDSL.Audit.Owners` | `#audit_edsl_owners` audits every imported project declaration by its actual defining module, including private and generated names. |

Proposal evaluation emits data only. It supplies no validity proof or semantic
assumption. Tactics generate ordinary Lean proof terms. A different program
still needs its own mathematical contract, invariant, termination argument and
proof of the resulting VCs; it reuses the same machine and resource model.

The checked Clang window contains all 58 bytes and 21 decoded nodes, including
padding and both return sites. The original default 64-byte/32-node CFG profile
is unchanged. Controls reject missing padding or the final return, false
absence, out-of-range hits, the truncated sentinel, and data access on empty
input. Shared branch controls reject noncanonical taken targets, missing
destinations, exhausted interior fuel and a nondecreasing dynamic rank.

The [contract-refinement bridge](call-contract-transport.md) also derives this
any-match contract from an existing earliest-u32-match claim on sorted input.
That proof reuse concerns the same verified bytes; the GCC counterpart still
requires its own body and artifact evidence.

## Build and scope

```sh
lake build BinarySearchTests
lake env lean -j1 -DwarningAsError=true -DautoImplicit=false \
  -DmaxHeartbeats=300000 -DmaxRecDepth=128 -DElab.async=false \
  tests/BinarySearchAudit.lean
```

The dedicated target checks the complete body/resource proof, independent
controls and defining-module axiom audit. The proof also participates in the
full catalogue build through `EDSL.All`.

The environment is `sequentialReadOnlyX86CallableV1`: stable ordinary RAM,
no asynchronous interference, four-level canonical addresses, alignment checks
and CET disabled. Current OS ownership, loan, code and caller-stack premises
remain explicit. Physical CPU/Linux correspondence, concurrent access and
source/compiler preservation require separate proofs.
