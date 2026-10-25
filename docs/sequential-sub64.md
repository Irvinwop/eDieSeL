# Register and immediate SUB64

The Lean `X86.Sequential` backend accepts register subtraction with one REX.W
prefix `48`–`4f` followed by `29 /r` or `2b /r`, with ModRM mod=11. Opcode
`29` writes r/m from r/m−reg; `2b` writes reg from reg−r/m. R/B extend those
register fields and X is ignored. Both forms occupy three bytes and read both
operands from the pre-state, including self-subtraction and RSP aliases.

Sign-extended immediate subtraction accepts exactly `48` or `49` followed by
`83 /5 ib`, with mod=11. B extends the destination; the immediate is extended
from signed8 to full64 and the instruction occupies four bytes. Other REX.R/X
aliases, memory operands, imm32, repeated/extra prefixes and unsupported group
selectors reject. The existing ADD64 and CMP64 group restrictions are retained.
Instruction bytes must be executable, including the final immediate byte.
These rules use the existing CET-off target profile.

Both instruction forms share `sub64State` and the independent `Sub64Contract`
in [`Sequential.Sub64`](../EDSL/X86/Sequential/Sub64.lean). The contract covers
the modular full64 result, its signed interpretation, every nondestination
register, complete memory, exact next PC and every nonarithmetic flag bit. All
six arithmetic flags are defined: CF is unsigned borrow, PF is even parity of
the result's low byte, AF is low-nibble borrow, ZF tests equality, SF is the
result's sign bit and OF detects a signed difference outside the full64 range.
For a negative immediate, CF uses its full unsigned sign-extended
representation. For example, `0 − SX64(ff)` produces `1` with both CF and AF
set. The generic distance/decrement lemmas additionally relate suitable
nonborrowing cases to natural subtraction.

SUB has empty operand reads, no store intent, locked event or syscall, and
requires no undefined-flag choice. The Bool and full flag-vector execution
APIs use the same state transformer.

## Composing program proofs

[`VCGen.Sub64`](../EDSL/X86/VCGen/Sub64.lean) provides register and immediate
continuation rules for the Bool WP and vector WP. Each rule retains the actual
successor PC, remaining fuel, one retired instruction and the caller's
independent postcondition. The Bool cutpoint rules retain the successor
invariant and strict dynamic rank decrease. This addition supplies no vector
cutpoint-loop extension. Vector continuations retain every later independent
flag choice, including the undefined status bits of a following IMUL.

[`Sub64Resources`](../EDSL/X86/Sequential/Sub64Resources.lean) transports the
current code and caller resources in the same complete OS world through both
execution APIs. Updating RSP preserves the original caller-slot loan and
bytes; it grants no loan or return-read permission at the new address. The
same principle applies when SUB computes a writable pointer: address-space mapping
permissions alone do not satisfy the borrowing mutation gate.

New clients can reuse these arithmetic, continuation and resource rules with
their own authenticated code, graph and independent result contract. The rules
leave byte authentication, graph admission, authorized reads/effects, termination
and the final postcondition as explicit program obligations.

## Regression coverage and limits

The `Sub64Tests` Lake target includes finite production decode/step vectors and
17 integration theorems across four modules:

| Module | Integration theorems | Behavior covered |
| --- | ---: | --- |
| `Sub64IntegrationCFG` | 6 | Signed/unsigned branch paths, exact successors, missing-node rejection, fuel/retirement rejection, cutpoint invariant and rank controls |
| `Sub64ReturnPolicy` | 5 | Original-world preservation, inaccessible replacement stack fault, readable duplicate with forbidden read, caller-policy rejection, balanced SUB/ADD restoration |
| `Sub64StoreAuthority` | 2 | Actual SUB-derived pointer and successful modeled store, followed by rejection through the real effect WP's borrowing gate |
| `Sub64VectorContinuation` | 4 | SUB followed by IMUL and RET, independent later flag choices, rejected correlated-flag contract, complete frame and exact trace |

The separate `SequentialSub64` vectors cover full64 arithmetic and status
boundaries, sign extension, both opcode directions, extended banks and ignored
X, self aliases including RSP, full64/low32 separation, truncated/nonexecutable
instruction fetches, ten unsupported encodings and retained ADD/CMP identities.
Expected arithmetic/status observations use literal architectural results and
the universal contract; they do not obtain expected values from the SUB state
transformer. The integration fixtures are synthetic code owned by this project.

The target and explicit CI source checks use warnings as errors,
`autoImplicit=false`, `maxHeartbeats=300000` and `maxRecDepth=128`. Public SUB64
modules are included in `EDSL.All` for the full audit and fresh production
replay. The full-project corpus gate also imports all five regression modules
into its generated fresh-replay aggregate.

These are claims about the stated sequential machine and OS-resource models.
They establish no physical CPU or operating-system correspondence, source or
compiler preservation, concurrent behavior, atomicity, timing or whole-kernel
safety. This ISA extension adds no end-to-end corpus certificate; coverage
remains **20/40**.
