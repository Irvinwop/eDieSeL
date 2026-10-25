# Binary-search interval rules

[`EDSL.WordMath.BinarySearch`](../EDSL/WordMath/BinarySearch.lean) provides
checked mathematics for searching a nondecreasing sequence. It supports
repeated values and accepts any matching index. The independent `Correct`
relation requires either an equal in-range element or absence from the whole
input.

```lean
import EDSL.WordMath.BinarySearch
```

Represent unsigned element values by `values : Nat → Nat` and the input length
by `size`. `Sorted values size` describes order within that finite extent.
`Invariant values key size low high` records `low ≤ high ≤ size`, elements
strictly below the key before `low`, and elements strictly above it from
`high` onward. The remaining interval is `[low, high)`.

Use the rules at loop cutpoints:

| Rule | Proof obligation it supplies |
| --- | --- |
| `initial` | Establish the initial interval `[0, size)`, including empty inputs. |
| `midpoint_bounds` | The midpoint lies inside every nonempty interval. |
| `matches_remain` | Every matching input position remains in the interval. |
| `advance_low` | Preserve the invariant after a midpoint value below the key. |
| `retreat_high` | Preserve the invariant after a midpoint value above the key. |
| `found` | An equal midpoint satisfies the independent result relation. |
| `exhausted` | An empty interval establishes absence from the complete input. |
| `advance_low_rank`, `retreat_high_rank` | Both continuing branches strictly decrease `high - low`. |

All rules quantify over the complete admitted sequence and key. They are
ordinary Lean theorems with audited dependencies. No example inputs or sampled
executions restrict their domains.

A machine-code proof additionally connects register arithmetic to these natural
bounds, binds `values` to a stable input snapshot, authorizes actual reads with
current OS loans, and proves the caller and outside-memory frames. The shared
[VCG and call adapters](verify-a-function.md) supply the execution framework.
The frozen corpus's binary-search functions still need that integration and
their complete artifact and grader checks; these mathematics alone add no
corpus credit.

To build the module:

```sh
lake build EDSL.WordMath.BinarySearch
```
