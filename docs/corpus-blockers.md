# Corpus blockers and extension order

The frozen corpus currently has **20/40 functions and 40/80 compiler artifacts
certified under the recorded model assumptions**, including **three distinct
concurrent functions**. Both compiler outputs must satisfy the independent
contract before a function counts. The
[latest accepted measurement](../corpus/measurements/signed-signum32-v1/)
identifies the 20 covered functions; [implementation status](implementation-status.md)
lists their contracts. The 20 remaining identities are the work queue below.

## How to read the queue

The latest [REX DATA4 diagnostic](../corpus/measurements/rex-data32-v1/)
ran the unchanged production read-only checker on all 80 frozen windows.
It accepted **22/40 GCC and 20/40 Clang** windows; the preceding published
source accepted **21/40 GCC and 20/40 Clang**. Only GCC `c_dot_mod64` changed:
its complete 55-byte window now yields a 19-node CFG. These structural results
add no certificates and do not replace the 20/40 behavioral coverage score.

The table below retains source-audited later frontiers for oversized functions
and separate effect, call and concurrency routes. The diagnostic's first
observed refusals are: the 64-byte span limit for ten uncovered functions,
supported stores excluded by the read-only policy for three, and SIMD loads
for two. A read-only-route refusal does not imply missing semantics elsewhere.
Existing checked triangular and counted-worker model certificates retain their
export, installed-grader and corpus-registration gates.

The exact bytes, lengths and symbol-relative hexadecimal offsets come from the
[GCC](../corpus/v1/gcc/manifest.json) and
[Clang](../corpus/v1/clang/manifest.json) manifests. Remaining gaps were audited
against the [sequential decoder](../EDSL/X86/Sequential/Decode.lean),
[instruction model](../EDSL/X86/Sequential/Model.lean) and explicitly named
sibling routes. The queue records the first missing decoding or contract
capability in address order after the size gate; removing it can expose
another gap in the same function.

**P** means an actual result in the identified default-profile production
probe. The historical SUB64 reports remain unchanged; the latest measurement
records later results separately.
**A** means a source-audit prediction, including every after-size instruction
frontier for a window longer than 64 bytes; no larger-profile or sibling-route
execution is implied. **H** marks a retained historical checker/test result and
is qualified in the row. **D** means the current demonstrated integration
frontier. None of these labels grants corpus credit.

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
| 13 `c_gcd_u32` | 37 / 31 | `DIV32` (`F7 /6`), `+0x14` | `DIV32` (`F7 /6`), `+0x14` | **A.** Euclidean invariant, nonzero divisor, quotient range/no divide fault, termination and independent gcd result. |
| 14 `c_factorial_mod64` | 54 / 38 | Register `TEST8` (`84 /r`), `+0x27` | `DEC32` (`FF /1`), `+0x19` | **P.** SUB64 is implemented. Reuse the register IMUL semantics; prove product invariant, early-zero exit and all-uint32 termination. |
| 15 `c_triangular_mod64` | 60 / 37 | Task registration, certificate export and grader acceptance; no missing instruction identified | The same integration gates; no missing instruction identified | **D.** Complete GCC (21 nodes) and Clang (14 nodes) graphs, independent arithmetic, universal body/current-resource/actual-return proofs and full named-ELF/caller certificates are checked. GCC uses a two-at-a-time loop; Clang uses a closed formula. [Triangular proofs](triangular-arithmetic.md) preserve the same all-uint32 specification. Registered export and installed grader acceptance remain open. |
| 16 `c_pow_mod64` | 41 / 51 | Count-one `SHR32` (`D1 /5`), `+0x1e` | The same encoding, `+0x23` | **A.** Immediate `C1` SHR32 and full64 `D1` SHR already exist; this low32 encoding does not. Reuse IMUL/CMOV; prove exponentiation invariant and decreasing exponent. |
| 17 `c_strlen_bytes` | 35 / 28 | Sequential route stops on reachable `CALL` (`E8`), `+0x11`; the sibling CallReturn decoder already supports that instruction | Independent first-NUL loop/snapshot and caller adapter; no missing instruction identified | **P/A.** The Clang disp8 compare at `+0x10` is now supported by source audit; no new whole-window probe is claimed. Prove first-NUL extent, result and termination. GCC needs reachable `strlen@plt` target/dependency binding and private-call-stack composition through the existing sibling route. A source symbol name is no external proof. |
| 22 `c_sum_u32` | 35 / 124† | Independent modular-fold invariant and current-buffer/caller adapter; no missing instruction identified | XMM `PXOR`, `+0x1b` | **A/H.** GCC's complete read-only CFG was accepted by the [comparison/padding measurement](../corpus/measurements/cmp32-endbr-nop-v1/); that is not a current end-to-end certificate. Clang needs lane-wise sum/reduction, exact widened-read authority and scalar-tail composition. |
| 23 `c_max_u32` | 74† / 305† | Independent maximum-loop/current-buffer adapter; no missing instruction identified | Near conditional branch (`0F 82 rel32`), `+0x06` | **P/A.** Both default probes stop only at the size gate; the later frontiers are source-audited. GCC's former disp8 load at `+0x37` is supported. Clang also needs XMM unsigned-max reduction and a RIP-relative constant read. Prove nonempty membership/maximality, bounds and termination. |
| 24 `c_count_zero_u32` | 43 / 161† | DATA4 compare with imm8, `+0x10` | XMM `PXOR`, `+0x1b` | **A.** Both later need carry-consuming `ADC64` for the scalar count; Clang adds XMM comparisons/reduction and a RIP-relative constant. Prove cardinality and exact read extents. |
| 26 `c_reverse_u32` | 48 / 144† | Mutable-array permutation/current-resource adapter; no missing instruction identified | Near conditional branch (`0F 82 rel32`), `+0x04` | **P/A.** The historical GCC probe reached the now-supported disp8 store at `+0x24`; the current frontier is source-audited. Clang's default probe stops at the size gate. Prove permutation, exact write authority, outside-byte frames and termination. Clang later needs full64 MOV-immediate/NOT and stack save/restore; W=0 REX DATA4 loads are supported. |
| 27 `c_fill_u32` | 48 / 92† | Writable-array fill/current-resource adapter; no missing instruction identified | GPR-to-XMM `MOVD`, `+0x16` | **A.** GCC's disp8 store at `+0x26` is supported. Prove an effect-aware fill invariant, complete outside-byte frame and unrolled/tail progress; Clang also needs XMM broadcast/stores and exact widened-write authority. |
| 28 `c_copy_u32` | 25 / 15 | `SHL64` immediate, `+0x09` | The same family, `+0x05` | **A.** Both tail-jump via `E9 rel32` to `memcpy@plt`. Prove exact external target/dependency closure, length scaling, disjointness, source preservation and destination frame; a shift rule alone cannot certify either output. |
| 29 `c_dot_mod64` | 55 / 168† | Independent dot-product/current-buffer adapter; complete 19-node CFG accepted | XMM `PXOR`, `+0x1b` | **P/A.** GCC's register IMUL and REX.W ADD already exist. Clang needs XMM widening-product/reduction; extended DATA4 loads are supported. Prove two-input modular dot-product invariant and complete read authority. |
| 30 `c_prefix_sum_u32` | 31 / 111† | Mutable prefix-fold/current-resource adapter; no missing instruction identified | Exact NOP14, `+0x52` | **A.** GCC's disp8 store at `+0x16` and Clang's disp8 add/store sequence at `+0x26..+0x3a` are supported. The default Clang size gate remains first. Prove a prefix-fold invariant preserving the initial sequence, exact stores, outside-byte frame and unrolled-tail progress. |
| 31 `c_struct_copy` | 21 / 15 | XMM `MOVDQU` load, `+0x04` | XMM `MOVUPS` load, `+0x00` | **A.** XMM state and 128-bit load/store semantics, object layout, disjoint source/destination authority and complete outside-byte frame. All 32 bytes remain in the contract. |
| 32 `c_struct_sum` | 20 / 28 | Independent four-field sum/current-buffer adapter; no missing instruction identified | XMM `MOVDQU` load, `+0x00` | **A.** GCC's disp8 DATA8 load at `+0x04` and additions at `+0x0b`/`+0x0f` are supported. Clang adds `PADDQ`/`PSHUFD`/XMM-to-GPR transfer. Prove the same four-field modular sum and read-only frame. |
| 33 `c_binary_search_u32` | 67† / 58 | Complete-window body/resource proof; no missing instruction identified after the size gate | Named-ELF binding, useful installed call and artifact admission; no missing instruction identified | **P/D.** The [published Clang proof](binary-search.md) covers the complete 58-byte/21-node body through the shared VCG, including full-width arithmetic, snapshot reads, every AF choice and original current-resource authority. GCC still needs its complete-window body proof under an explicit profile; no larger-profile production diagnostic is published. Both retain exact named-file binding, useful loaded calls, trusted registration and admission gates. |
| 37 `c_spinlock_acquire` | 25 / 12 | Protocol/ownership composition for the DWORD XCHG loop | Protocol/ownership composition for the decoded DWORD XCHG loop | **A/H.** [Structural discovery](structural-cfg.md#evidence-and-limits) already covers the complete Clang graph, including actual XCHG; the read-only route rejects that effect. Both need invariant transfer, interleaved linearization, per-prefix safety and explicitly conditional progress. |
| 38 `c_spinlock_release` | 11 / 7 | DATA4 immediate store (`C7 /0`), `+0x04` | The same family, `+0x00` | **A.** Current C7 support is register-only REX.W. Prove ordinary FIFO store publication, preceding critical-section ordering and relinquishment/transfer of lock authority. Return need not publish the store. |
| 39 `c_futex_wait_loop` | 105† / 126† | Sequential-only PUSH, `+0x04`; on the existing sibling CallReturn route, immediate PUSH (`6A 00`), `+0x25` | Sequential-only PUSH, `+0x00`; on that sibling route, DATA4 immediate stack store (`C7 /0`), `+0x27` | **P/A.** Both default probes stop only at the size gate; no larger-profile/sibling run is claimed. GCC's zero-disp8 load at `+0x10` and SUB64 are supported. Clang's preceding W=0 REX DATA4 load at `+0x20` is supported. Both still need `syscall@plt`/`__errno_location@plt` closure, Linux errno/TLS and wait/recheck/interference/error contracts. Existing restricted futex clients do not certify these bytes. |
| 40 `c_counter_worker` | 49 / 86† | Complete-file proof-packet admission, installed Counted64 route and corpus registration | The same integration gates; the complete 86-byte graph already uses an explicit 128-byte profile | **D.** [Complete model certificates](counted-certificates.md) and loaded overlapping completion exist for both compilers. The current frozen packet attempt was refused by the cumulative kernel budget before final acceptance. No accepted Counted64 packet or installed route is established. |

The first instruction gap is deliberately encoding-specific. ENDBR64 under the
recorded CET-off target, NEG32, BSWAP64, register IMUL64, CMOV32/64, immediate
`C1` SHR/SAR32, `D1` SHR64, register/sign-extended-imm8 SUB64, canonical
register AND64 with a sign-extended imm8, and the documented mod01 signed-disp8
ordinary DATA1/4/8 forms are implemented in this integration. Their old baseline
failures must not re-enter this queue as present limitations. Likewise,
W=0 REX DATA4 loads also share the checked address, frame and resource rules.
CallReturn already has direct relative CALL and register PUSH/POP; general
PLT/libc/TLS closure does not follow from those instruction rules.

## Ranked reusable features

The counts below are **distinct function identities**, taking the union of the
two compiler columns, after each complete-window size gate. They count a listed
frontier the feature would remove, **not predicted end-to-end certifications**.
Rows overlap and their counts must not be added. The nine identities other
than row 40 marked † also require explicit suitable profiles. Row 39's later
frontiers and their counts are conditional on the named existing CallReturn
route: Sequential alone still rejects PUSH earlier, and no sibling-route probe
was run. A decoded sibling instruction supplies no external-call or OS contract.
The delivered disp8 extension is no longer a missing-feature row; its newly
exposed contract frontiers remain source-audit predictions.

| Rank by first-frontier count | Reusable feature | Distinct IDs whose listed frontier it addresses | What success would mean |
| --- | --- | --- | --- |
| 1 | XMM state, transfers, 128-bit moves and lane operations | **6:** 22, 24, 27, 29, 31, 32 | Removes the listed PXOR/MOVD/MOVDQU/MOVUPS frontiers; complete lane/reduction and memory-authority proofs remain. Also needed later in 23: **7 distinct functions in total**. |
| 2 | Mutable-array loop/current-resource adapters | **3:** 26, 27, 30 | Connects GCC's supported instruction sequences to permutation, fill and prefix-fold contracts with exact stores and complete frames; no new whole-window acceptance is claimed. Clang retains separate ISA/profile gaps. |
| 3 | Near conditional branches, with exact rel32 successors | **2:** 23, 26 | Structural progress for the large Clang bodies, which still need SIMD or mutable effects. |
| 4= | Register `TEST8` (`84 /r`) | **1:** 14 | Removes GCC's byte-test gap; Clang DEC32 and factorial mathematics remain. |
| 4= | Unsigned `DIV32`, including divide-fault conditions | **1:** 13 | Enables the gcd loop body; arithmetic and termination obligations remain. |
| 4= | `DEC32` (`FF /1`) | **1:** 14 | Removes Clang's decrement gap; GCC TEST8 and factorial mathematics remain. |
| 4= | Count-one `SHR32` (`D1 /5`) | **1:** 16 | Reuses shift mathematics for a missing encoding; power invariant/termination remain. |
| 4= | Immediate `SHL64` | **1:** 28 | Reaches a tail jump and external memcpy obligation. |
| 4= | DATA4 compare with sign-extended imm8 | **1:** 24 | Reaches the scalar carry-consuming ADC64 count, whose rule and cardinality invariant remain. |
| 4= | Ordinary DATA4 immediate store (`C7 /0`) | **1:** 38 | Enables release-store decoding, with publication and ownership work still required. Also needed later in 39. |
| 4= | Exact fourteen-byte hint NOP | **1:** 30 | Removes Clang's newly exposed padding gap at `+0x52`; its complete-window profile and mutable prefix-fold contract remain. |
| 4= | Immediate PUSH (`6A ib`) in CallReturn | **1:** 39 | Removes GCC's newly exposed sibling-route frontier at `+0x25`; exact stack effects, external dependencies and futex/errno contracts remain. |
| 4= | Independent modular-fold/current-buffer adapter | **1:** 22 | Advances GCC beyond its accepted CFG; Clang SIMD obligations prevent function credit. |
| 4= | Independent maximum-loop/current-buffer adapter | **1:** 23 | Connects GCC's supported loads and comparisons to nonempty maximum and bounds; its larger profile and Clang ISA gaps remain. |
| 4= | Independent first-NUL loop/current-buffer adapter | **1:** 17 | Connects Clang's supported loop to snapshot extent, first-NUL result and termination; GCC still needs its actual external call contract. |
| 4= | Independent four-field sum/current-buffer adapter | **1:** 32 | Connects GCC's supported qword reads/additions to the complete modular-sum and frame contract; Clang still needs SIMD. |
| 4= | Triangular registration and certificate export | **1:** 15 | Both compiler bodies, current resources, return/read traces and named-ELF/caller certificates are checked; task/export/grader acceptance remains. |
| 4= | Binary-search proof reuse and exact artifact binding | **1:** 33 | Reuse the checked Clang body/resources and shared interval/branch rules for GCC, then complete both named-file, useful-call and admission gates. |
| 4= | Reachable libc/PLT contract via existing CallReturn rules | **1:** 17 | Justifies GCC's actual strlen call target, dependency bytes and private stack; Clang still needs its first-NUL loop contract. |
| 4= | DWORD lock-invariant/interleaving adapter | **1:** 37 | Advances the decoded Clang loop beyond structure, with the GCC protocol proof still open. Shared protocol work also supports 38. |
| 4= | Bounded full-file Counted64 packet export/admission | **1:** 40 | Closest existing model proof to a new numerator; both compiler packets, isolated installed acceptance, negative controls and corpus registration must pass first. |

Next work should combine shared-feature counts with the distance to a complete
independent contract. Complete registered acceptance for the checked triangular
certificates and the demonstrated row-40 packet gate. The disp8 extension
exposes several smaller scalar/read-only and writable-loop contracts, while
XMM support leads the remaining ISA queue; W=0 REX DATA4 loads are implemented. Exact NOP7/NOP8,
signed-byte AND64 and ordinary disp8 DATA addresses share the existing decoder,
frame, WP and permission model. SUB64, AND64, disp8 DATA addressing and REX DATA4 loads are
complete for their documented subsets and no longer belong in the missing-feature
rank. Reuse the triangular arithmetic and loop/resource bridges for later functions;
reuse the checked Clang binary-search body/resource proof and shared interval
and branch APIs for GCC, then complete the exact artifact and admission gates. Keep separate tracks
for XMM lanes, mutable-array ownership and interleaved lock protocols. After each
milestone, remove newly covered IDs, record newly exposed first blockers and
update the ranking from the unchanged 40-function denominator.

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
