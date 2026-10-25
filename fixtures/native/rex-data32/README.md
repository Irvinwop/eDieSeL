<!-- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -->
# Owned REX DATA4 native conformance

From any working directory, invoke `scripts/verify-rex-data32-native.sh` using
its checkout-relative or absolute path, optionally followed by a **new** output
directory. A relative output argument is relative to the caller. With no argument,
the driver creates `artifacts/rex-data32/run.XXXXXXXX` in its checkout. Existing
paths, dangling symlinks, unknown options and extra arguments are refused.

```sh
scripts/verify-rex-data32-native.sh
EDSL_CC=gcc-13 scripts/verify-rex-data32-native.sh artifacts/rex-data32/gcc-run
```

This is **native conformance and binding only**. It captures 148 actual
observations of 37 owned literal probes (two seeds, two positions), rejects 16
actual native mutants, 41 parser controls and 15 authentication controls. It
performs no fresh Lean kernel replay, generates no proofs and establishes no
CPU/OS refinement or corpus credit. Lean model and theorem checks run separately from this native driver. Timeout, unsupported
input and refusal are failures to complete this harness, not defect findings.

Requirements are Linux x86-64, 4096-byte pages, `/proc`, fixed-address mappings
with `MAP_FIXED_NOREPLACE`, cgroup v2 and a running system systemd manager.
The caller needs root or noninteractive `sudo -n systemd-run` permission. GNU
binutils and core utilities, Bash, Node.js (orchestration/reporting only), and
a GNU C compiler accepting `-std=gnu2x` is required. `EDSL_CC`, then `CC`, selects a
single compiler executable; the default is `gcc`. Shell command strings and
implicit compiler flag variables are not interpreted. GCC 13.3.0 is validated.
The termination helper is declared `_Noreturn` so both GCC and Clang can
check the actual failure paths without suppressing warnings.
GNU tools must be on `PATH` for the
transient services. The driver uses `-O2 -Wall -Wextra -Werror`, disables PIE
and LTO, and links a nonexecutable stack. **OpenSSL headers and linked
`libcrypto` are required** (`openssl/evp.h`, `-lcrypto`; commonly the existing
`libssl-dev` package). The driver does not install dependencies.

Every compile, native, control, parser and report phase runs in a fresh bounded
systemd service: at most 512 MiB, no swap, CPUQuota=100%, TasksMax=64, core size
zero, inner timeout at most 30 seconds and unit runtime at most 35 seconds.
Native and parser phases have 15-second inner/20-second unit bounds. These are
below the shared 3 GiB/120-second inner/130-second unit ceiling. `phase.sh`
checks the actual cgroup memory, swap, CPU and task limits before executing the
command. Failure to establish the limits fails closed. The service has a
read-only filesystem except the fresh output directory; its working directory
and temporary directory are inside that output. Fixed-name control artifacts
therefore cannot overwrite public source files. The fixture requires the fixed
operand/decoy address ranges to be free; it never replaces existing mappings.

The storage guard reserves 32 MiB for outputs and 200,000,000 bytes for other
work under a 5,000,000,000-byte allocated-storage ceiling. `EDSL_STORAGE_ROOT`
may name an enclosing storage directory; the default is the source checkout.
An output directory outside that root is counted separately. The source must
be inside the storage root. Actual `du -s -B1` measurements occur before output
creation, before compilation and on exit. The full unused output reservation
is retained while checking capacity; reserves are never reduced on failure.
Initial reservation refusal writes no output and prints the exact measurement.

`contracts.h` declares destinations, address expressions and exact literal
bytes independently of `probe.S`. No production decoder or Lean evaluator
generates the C oracle result. `oracle.c` reads exactly four bytes from the
measured before-page snapshot using `uint32_t memcpy`, zero extends the result,
changes only the declared destination in the measured GPR vector, and compares
all 16 GPRs, every measured flag bit and all bytes of three pages. Native setup
checks actual read-only, nonexecutable operand and decoy pages, each between
two inaccessible guard pages. Positions include unaligned interior addresses
and the last four readable bytes. Distinct low32/wrong-bank decoys, high-half
address/destination witnesses, all prefix banks/scales, displacements and aliases
exercise plausible width, truncation, bank, direction and successor defects.

Authentication compares the whole supplied ELF with `/proc/self/exe`, then
checks the complete linked `.rex32_native` section against both its extraction
and live bytes, executable load segments, all probe/harness symbols, literal
bytes and canonical metadata. Whole-section coverage includes dispatch,
snapshots, recovery and every positive/negative probe. Altered ELFs are data
inputs to the unchanged owned checker and are never executed. Fourteen native
mutants produce actual complete negative captures. Two children terminate with
SIGSEGV (an eight-byte guard-crossing load and a read-only store); they retain
before pages and null measured afterstates. No signal handler or recovery
fabricates a fault afterstate.

Read `exit`, `postflight.exit`, `scope.txt`, `REPORT.json` and `OUTPUTS.sha256`
together. Only exit 0 with postflight 0 and PASS scope establishes a completed
run. `INPUTS.sha256` covers every fixture file and the driver; membership and
hashes are checked before compilation and on every normal/trapped exit.
`TOOLS.sha256` pins tool executables, `PREFLIGHT.sha256` binds launch/version
records, `ELF.sha256` pins the freshly compiled executable, `NATIVE.sha256`
binds the ELF, extraction, canonical metadata, capture and binding report.
`OUTPUTS.sha256` covers all retained regular outputs except itself, including
controls, logs, manifests, final report and exit/scope. It is an integrity
manifest, not an external trust anchor; retain its digest independently when
moving evidence. Input mutation, missing files and manifest failures propagate
to nonzero exit even if all compute phases completed. After output creation,
failure also records exit, incomplete scope and a report; uncatchable termination
or filesystem failure can prevent finalization. The driver does not recover or
reuse partial output directories.

`runner.txt`, `commands.txt`, `platform.txt`, `tool-versions.txt`, linked ELF
inspection and `limits/` record launch and compute provenance, not proof.
This fixture uses the public `rex-data32-native-v1` identity and
`REX32-DATA4-V1` binary magic. Captures must be generated fresh for this schema;
older differently identified captures must never be relabeled. See
[FORMAT.md](FORMAT.md) for the stable low-level entrypoints and wire layout.
