# Finite native SUB64 conformance

The native fixture covers the sequential backend's register SUB64 (`29 /r`
and `2b /r`, one REX.W byte `48`–`4f`) and sign-extended immediate SUB64
(`48`/`49 83 /5 ib`). Every positive window is register-only. This is a
reusable instruction-family fixture, independent of any particular verified
program or graph. It does not change accepted encodings, the compiler corpus,
or the generic SUB64 proofs.

The assembly puts project-owned byte windows and their direct capture jumps
in a dedicated final linked executable ELF section. Before executing any
window, the observer compares the entire extracted section with the linked
section in its address space, including negative windows and jumps. It also
requires the extraction's exact length. A deliberately changed extraction
must reject with exit 2, zero captures, empty Lean output and no JSON output.

The C requests separately name operation, source, destination and signed
immediate. There is no C opcode, REX or ModRM decoder. Expected register values
come from a nonnegative unsigned 128-bit modular difference. Unsigned
comparison defines borrow; low-nibble comparison defines AF; low-byte
population count defines PF; an independent signed 128-bit interval defines
OF. ZF and SF have their exact result meanings. All six arithmetic flags
are defined. The oracle compares every GPR and every captured RFLAGS bit,
preserving the effective pre-state's other flags.

The 68 positive windows each run ten profiles, for 680 positive observations:

- 48 register windows cover both opcode directions, every register as source
  and destination in each direction, eight aliases including RSP/R12, every
  REX.W byte, and ignored X with every R/B combination in each direction.
- 20 immediate windows cover every destination and `-128`, `-1`, `0`, `1`,
  `127` in both register banks, with extra RSP and R12 cases.
- Inputs include zero, unsigned borrow and wrap, signed overflow in both
  directions, auxiliary borrow, parity variation, and nonzero high halves.
  Both operands are captured from the pre-state, including aliases.
- Eight owned negative controls change source, direction, operand width,
  operation, destination write, carry, immediate sign extension, or register
  bank. Each must fail the C request contract. They are excluded from replay.

The assembly capture reuses the sequential arithmetic64 fixture's critical
ordering: no stack access occurs after installing arbitrary modeled RSP
until RIP-relative stores capture all GPRs and restore the host RSP. Only
then does `pushfq` record flags. The capture clears DF and restores saved
callee registers and the caller's original flags before returning. Requested
flags alternate `0x202`/`0xed7`, including DF, while expectations use the
effective user-mode flags captured immediately before the instruction.
The observer blocks maskable signals around probes. It is single-threaded
and non-reentrant; the modeled RSP may be noncanonical because no window
dereferences it.

The C program buffers all positive observations until the byte-identity,
native-contract and negative-control gates pass. It emits raw literal Lean
propositions and decimal-string JSON snapshots without loss of 64-bit values.
The separate replay generator changes only the decision tactic to
`decide +kernel` and partitions the unchanged 680 propositions into eight
85-case files, with asynchronous declaration checking disabled. This avoids
the elaborator recursion depth encountered by ordinary `decide` and excess
declaration-checking tasks, with the same heartbeat and recursion settings.

Every replay calls production `Sequential.stepWith`, which fetches the exact
executed instruction bytes using production `decodeAt`, then calls production
`executeWith`. Expected outputs are the captured CPU states. It compares all
16 registers, full flags, and the linked continuation RIP. The state supplies
only the exact instruction bytes as readable executable memory. The empty
operand-read list is an independently requested model footprint, not a CPU
memory-access trace. A mixed flag-choice vector is used; generic SUB64 theorems
separately establish that all six flags are defined. Each generated theorem's
axioms are printed, followed by the transitive `#audit_edsl` audit.

Run the complete native and kernel replay gate:

~~~sh
EDSL_CLANG=clang-18 bash scripts/verify-sequential-sub64.sh
~~~

The script requires Linux x86-64, the pinned Lean toolchain, Lake, clang,
binutils, Node and systemd. A non-root caller needs passwordless sudo to create
the bounded transient units; their processes still run as that caller. Missing
privileges fail the gate. There is no fallback that omits resource bounds.

A fresh run directory is created under artifacts/sequential-sub64/; an
optional argument selects a new output directory. The output includes the
linked ELF, extraction hashes, compiler/platform/CPU data, disassembly, raw
snapshots, extraction-tamper evidence, coverage audit, generated propositions
and all replay logs. The --native-only option skips Lake/kernel replay and
records that limitation in scope.txt; it cannot establish a replay result.

Compiler execution is capped at 30 seconds and 512 MiB. Each native probe run
has 30 seconds and 128 MiB; all use one CPU and no swap. The full gate builds
the current production dependencies with Lake, then checks eight 85-observation
Lean files serially. Each Lean invocation uses one thread/job,
warningAsError=true, autoImplicit=false, heartbeats 300000, recursion depth
128, 3 GiB/no swap, one CPU, 64 tasks, a 130-second unit and 120-second timeout.
Generated files set Elab.async=false; kernel checking remains enabled.
The shared /tmp/edsl-lean-build.lock serializes replay, with readiness checks
after acquisition. Waiting for the lock occurs before starting a bounded unit.

The existing sequential native CI domain runs the complete gate and preserves
its synthetic observations and kernel logs. Generic SUB64 proofs remain
separate from these finite CPU/model comparisons.

This finite evidence assumes the selected Linux user-mode environment,
ordinary effective flags, disabled alignment checking and CET, and the
single-threaded capture arrangement. A VPS identifies its guest CPU and
hypervisor; it does not identify a physically inspected processor. These
checks establish no universal CPU/model equivalence, source preservation,
current OS/kernel safety, exception-delivery correctness, asynchronous
interference guarantee, timing, speculation, concurrency or performance bound.
These synthetic checks establish no defect in external software.
