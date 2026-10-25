# Corpus blockers and extension order

The frozen corpus currently has **20/40 functions and 40/80 compiler artifacts
certified under the recorded model assumptions**, including **three distinct
concurrent functions**. Both compiler outputs must satisfy the independent
contract before a function counts. The
[latest accepted measurement](../corpus/measurements/signed-signum32-v1/)
identifies the 20 covered functions; [implementation status](implementation-status.md)
lists their contracts. The 20 remaining identities are the work queue below.

## How to read the queue

This is a **source audit dated 2026-10-25**, not a new CFG or certification run.
The exact bytes, lengths and symbol-relative hexadecimal offsets come from the
[GCC](../corpus/v1/gcc/manifest.json) and
[Clang](../corpus/v1/clang/manifest.json) manifests, cross-checked against their
complete frozen ELFs. Instruction gaps were checked against the current
[sequential decoder](../EDSL/X86/Sequential/Decode.lean) and
[instruction model](../EDSL/X86/Sequential/Model.lean). The queue names the first
missing decoding or contract capability in address order, after the size gate;
removing it can expose another gap in the same function.

**A** means a current source-audit prediction, with no new checker execution.
**H** marks a retained historical checker/test result and is qualified in the
row. **D** means the current demonstrated integration frontier. Confidence in
an opcode's absence is higher than confidence in the effort needed to certify
the whole function. None of these labels grants corpus credit.

A **†** on a byte length means the unchanged default CFG profile rejects the
window at its **64-byte size gate before decoding**. That is the first outcome
on the default path; the table also exposes the next ISA/contract work so that
a larger profile cannot be mistaken for a solution. The default also caps
static graphs at 32 nodes. An explicit complete-window profile, checked graph
and compatible execution/resource adapter are required; no truncation, blanket
cap increase or change to the frozen inputs is proposed. Writable and atomic
routines need an effect-aware route: the read-only checker can reject an effect
earlier than the structural gaps listed here. Row 40 already has a checked
explicit 128-byte Clang profile, so its default-size marker is not its current
integration blocker.

## The 20 uncovered functions

| ID and function | Bytes GCC / Clang | GCC: first missing capability after the size gate | Clang: first missing capability after the size gate | Remaining contract work and evidence |
| --- | ---: | --- | --- | --- |
| 13 `c_gcd_u32` | 37 / 31 | `DIV32` (`F7 /6`), `+0x14` | Exact NOP8, `+0x08`; then the same `DIV32` at `+0x14` | **A.** Euclidean invariant, nonzero divisor, quotient range/no divide fault, termination and independent gcd result. |
| 14 `c_factorial_mod64` | 54 / 38 | Register `SUB64` with imm8, `+0x23` | `DEC32` (`FF /1`), `+0x19` | **A.** GCC also needs register `TEST8` at `+0x27`. Reuse implemented vector IMUL semantics; prove product invariant, early-zero exit and all-uint32 termination. |
| 15 `c_triangular_mod64` | 60 / 37 | Exact NOP7, `+0x21`; then `SUB64` imm8 at `+0x2d` | Register `SUB64`, `+0x1e` | **A.** GCC uses a two-at-a-time loop; Clang uses a closed formula. Both must meet the same natural triangular-number contract modulo 2^64. |
| 16 `c_pow_mod64` | 41 / 51 | Count-one `SHR32` (`D1 /5`), `+0x1e` | The same encoding, `+0x23` | **A.** Immediate `C1` SHR32 and full64 `D1` SHR already exist; this low32 encoding does not. Reuse IMUL/CMOV; prove exponentiation invariant and decreasing exponent. |
| 17 `c_strlen_bytes` | 35 / 28 | Stack `SUB64` imm8, `+0x09`; reachable `strlen@plt` call at `+0x11` then needs a justified external-call contract | DATA1 compare with SIB+disp8, `+0x10` | **A.** Unbounded first-NUL snapshot/extent and termination; GCC additionally needs actual reachable libc/PLT binding and private-call-stack composition. A source symbol name is no external proof. |
| 22 `c_sum_u32` | 35 / 124† | Independent modular-fold invariant and current-buffer/caller adapter; no missing instruction identified | `AND64` imm8, `+0x17`; then XMM operations | **A/H.** GCC's complete read-only CFG was accepted by the [comparison/padding measurement](../corpus/measurements/cmp32-endbr-nop-v1/); that is not a current end-to-end certificate. Clang needs lane-wise sum/reduction, exact widened-read authority and scalar-tail composition. |
| 23 `c_max_u32` | 74† / 305† | Register `SUB64`, `+0x17` | Near conditional branch (`0F 82 rel32`), `+0x06` | **A.** GCC later needs displaced DATA4 loads. Clang also needs AND64 immediates, XMM unsigned-max reduction and a RIP-relative constant read. Prove nonempty membership/maximality, bounds and termination. |
| 24 `c_count_zero_u32` | 43 / 161† | DATA4 compare with imm8, `+0x10` | `AND64` imm8, `+0x17` | **A.** Both later need carry-consuming `ADC64` for the scalar count; GCC also has NOP7. Clang adds XMM comparisons/reduction and a RIP-relative constant. Prove cardinality and exact read extents. |
| 26 `c_reverse_u32` | 48 / 144† | Register `SUB64` imm8, `+0x20` | Near conditional branch (`0F 82 rel32`), `+0x04` | **A.** Mutable-array permutation/frame invariant. GCC later needs displaced stores; Clang adds full64 AND-immediate/MOV-immediate/NOT, stack save/restore and extended DATA4 addressing. |
| 27 `c_fill_u32` | 48 / 92† | DATA4 store with disp8, `+0x26` | `AND64` imm8, `+0x12` | **A.** Effect-aware writable-array invariant, complete outside-byte frame and unrolled/tail progress; Clang also needs XMM broadcast/stores and exact widened-write authority. |
| 28 `c_copy_u32` | 25 / 15 | `SHL64` immediate, `+0x09` | The same family, `+0x05` | **A.** Both tail-jump via `E9 rel32` to `memcpy@plt`. Prove exact external target/dependency closure, length scaling, disjointness, source preservation and destination frame; a shift rule alone cannot certify either output. |
| 29 `c_dot_mod64` | 55 / 168† | W=0 REX DATA4 load into R9D, `+0x13` | `AND64` imm8, `+0x17` | **A.** GCC's register IMUL and REX.W ADD already exist. Clang needs XMM widening-product/reduction and later extended DATA4 loads. Prove two-input modular dot-product invariant and complete read authority. |
| 30 `c_prefix_sum_u32` | 31 / 111† | DATA4 store with disp8, `+0x16` | `AND64` imm8, `+0x16` | **A.** Mutable prefix-fold invariant preserving the initial sequence, exact stores, outside-byte frame and unrolled-tail progress. Clang later needs displaced DATA4 accesses and exact NOP14. |
| 31 `c_struct_copy` | 21 / 15 | XMM `MOVDQU` load, `+0x04` | XMM `MOVUPS` load, `+0x00` | **A.** XMM state and 128-bit load/store semantics, object layout, disjoint source/destination authority and complete outside-byte frame. All 32 bytes remain in the contract. |
| 32 `c_struct_sum` | 20 / 28 | DATA8 load with disp8, `+0x04` | XMM `MOVDQU` load, `+0x00` | **A.** GCC later needs displaced DATA8 additions; Clang adds `PADDQ`/`PSHUFD`/XMM-to-GPR transfer. Prove the same four-field modular sum and read-only frame. |
| 33 `c_binary_search_u32` | 67† / 58 | Register `SUB64`, `+0x1c` | Register `SUB64`, `+0x21` | **A.** GCC later needs extended DATA4 loads/comparisons. Both need a sorted-interval exclusion invariant, midpoint bounds, shrinking interval and iff-absent result. |
| 37 `c_spinlock_acquire` | 25 / 12 | Exact NOP7, `+0x09` | Protocol/ownership composition for the decoded DWORD XCHG loop | **A/H.** [Structural discovery](structural-cfg.md#evidence-and-limits) already covers the complete Clang graph, including actual XCHG; the read-only route rejects that effect. Both need invariant transfer, interleaved linearization, per-prefix safety and explicitly conditional progress. |
| 38 `c_spinlock_release` | 11 / 7 | DATA4 immediate store (`C7 /0`), `+0x04` | The same family, `+0x00` | **A.** Current C7 support is register-only REX.W. Prove ordinary FIFO store publication, preceding critical-section ordering and relinquishment/transfer of lock authority. Return need not publish the store. |
| 39 `c_futex_wait_loop` | 105† / 126† | Stack `SUB64` imm8, `+0x0b`, even when using the existing CallReturn PUSH/POP decoder | Stack `SUB64` imm8, `+0x04`, on that same sibling route | **A.** The sequential-only route rejects the initial PUSH earlier. Further DATA/stack forms and `syscall@plt`/`__errno_location@plt` closure, Linux errno/TLS, wait/recheck/interference and error contracts remain. Existing restricted futex clients do not certify these bytes. |
| 40 `c_counter_worker` | 49 / 86† | Complete-file proof-packet admission, installed Counted64 route and corpus registration | The same integration gates; the complete 86-byte graph already uses an explicit 128-byte profile | **D.** [Complete model certificates](counted-certificates.md) and loaded overlapping completion exist for both compilers. The current frozen packet attempt was refused by the cumulative kernel budget before final acceptance. No accepted Counted64 packet or installed route is established. |

The first instruction gap is deliberately encoding-specific. ENDBR64 under the
recorded CET-off target, NEG32, BSWAP64, register IMUL64, CMOV32/64, immediate
`C1` SHR/SAR32, and `D1` SHR64 are already implemented. Their old baseline
failures must not re-enter this queue as present limitations. Likewise,
CallReturn already has direct relative CALL and register PUSH/POP; general
PLT/libc/TLS closure does not follow from those instruction rules.

## Ranked reusable features

The counts below are **distinct function identities**, taking the union of the
two compiler columns, after each complete-window size gate. They count a next
frontier the feature would remove, **not predicted end-to-end certifications**.
Rows overlap and their counts must not be added. The nine identities
other than row 40 marked † above also need an explicit suitable profile before
those frontiers are reachable on a diagnostic path.

| Rank by first-frontier count | Reusable feature | Distinct IDs whose listed frontier it addresses | What success would mean |
| --- | --- | --- | --- |
| 1 | Register and sign-extended imm8 `SUB64`, with complete flags | **7:** 14, 15, 17, 23, 26, 33, 39 | Removes an early arithmetic gap; 17/39 still require external/OS composition. |
| 2 | Register `AND64` with sign-extended imm8 | **5:** 22, 24, 27, 29, 30 | Reaches Clang vector or unrolled bodies; establishes none of their loop or SIMD contracts. |
| 3 | Reuse decoded disp8 addresses for ordinary DATA1/4/8 operations | **4:** 17, 27, 30, 32 | Removes the listed load/compare/store gap; LEA's existing address support alone supplies no memory permissions. |
| 4 | Exact frozen NOP7/NOP8 encodings | **3:** 13, 15, 37 | Removes a padding-only decoding gap; DIV, arithmetic and lock ownership remain. |
| 5= | Near conditional branches, with exact rel32 successors | **2:** 23, 26 | Structural progress for the large Clang bodies, which still need SIMD or mutable effects. |
| 5= | XMM state, 128-bit moves and lane operations | **2:** 31, 32 | Starts complete struct contracts. Later XMM families also occur in 22, 23, 24, 27, 29: **7 distinct functions in total**, but they are not all first frontiers. |
| 7= | W=0 REX DATA4 register/address dispatch | **1:** 29 | Removes the first extended load; relevant later to 23, 26, 33 too. |
| 7= | Unsigned `DIV32`, including divide-fault conditions | **1:** 13 | Enables the gcd loop body after Clang padding is supported. |
| 7= | `DEC32` (`FF /1`) | **1:** 14 | Removes Clang's decrement gap; GCC TEST8/SUB64 and factorial mathematics remain. |
| 7= | Count-one `SHR32` (`D1 /5`) | **1:** 16 | Reuses shift mathematics for a missing encoding; power invariant/termination remain. |
| 7= | Immediate `SHL64` | **1:** 28 | Reaches a tail jump and external memcpy obligation. |
| 7= | DATA4 compare with sign-extended imm8 | **1:** 24 | Reaches the scalar carry-consuming ADC64 count, whose own rule and cardinality invariant remain. |
| 7= | Ordinary DATA4 immediate store (`C7 /0`) | **1:** 38 | Enables release-store decoding, with publication and ownership work still required. |
| 7= | Independent modular-fold/current-buffer adapter | **1:** 22 | Advances GCC beyond its accepted CFG; Clang SIMD obligations prevent function credit. |
| 7= | DWORD lock-invariant/interleaving adapter | **1:** 37 | Advances the decoded Clang loop beyond structure, with GCC padding still open. Shared protocol work also supports 38. |
| 7= | Bounded full-file Counted64 packet export/admission | **1:** 40 | Closest existing model proof to a new numerator; both compiler packets, isolated installed acceptance, negative controls and corpus registration must pass first. |

Next work should combine the highest shared-feature counts with the distance to
a complete independent contract. Finish the demonstrated row-40 packet gate;
then prefer shared SUB64, AND64-immediate and DATA-address rules over more
per-program proof copies. Small exact-padding additions can accompany those
rules. Keep separate tracks for XMM lanes, mutable-array ownership and
interleaved lock protocols. After each milestone, remove newly covered IDs,
record newly exposed first blockers and update the ranking from the unchanged
40-function denominator.

## Artifact representation and OS boundaries

Full-file packet representation is a shared scaling concern, not a missing
counter instruction. Packed little-endian regions and generic length/slice
bridges are candidates for reducing repeated list normalization. They must
still bind the independently reread complete file and preserve the existing
expected proposition, audit, cumulative kernel budget, parser/decimal limits
and fresh replay. No accepted large-file packed bridge is claimed here.
Checking only selected regions would need a proved dependency/noninterference
rule for every byte the contract ignores; a function window or a successful
small packing diagnostic does not provide that rule.

Every row retains the [common corpus obligations](../corpus/v1/contracts.md):
actual code/ABI and resource authority, stable readable snapshots or exclusive
writable extents, full caller/outside-memory frames and explicit external
contracts. Concurrent model results require their declared scheduling,
publication, lifetime and ordering assumptions. Published/physical x86-TSO,
source/compiler ordering and native Linux/kernel correspondence remain separate
obligations. Decoding, a completed example, proof failure or resource rejection
establishes no security finding.

## Historical baseline

The immutable [initial reports](../corpus/v1/) recorded **0/40 end-to-end
functions**, **0/80 artifacts**, and read-only CFG acceptance **0/40 GCC,
4/40 Clang**. The next [comparison/padding measurement](../corpus/measurements/cmp32-endbr-nop-v1/)
recorded CFG acceptance **5/40 GCC, 4/40 Clang**, still without end-to-end credit.
At the original freeze, 37 GCC functions stopped on leading ENDBR64; that
historical result does not describe the present CET-off decoder.

Later immutable [measurements](../corpus/measurements/) record the growth to
20/40. `corpus/v1/coverage.tsv`, each extraction manifest's `unverified` fields,
and the old CFG reports preserve their freeze-time meaning; they are not the
current score or a current decoder probe. Milestone history is summarized in
[compiler-corpus.md](compiler-corpus.md). Keep old evidence intact and publish
new results separately, with source identity, exact files, scope and assumptions.
