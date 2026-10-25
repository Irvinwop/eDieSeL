<!-- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -->
# REX DATA4 capture format v1

The public schema is `rex-data32-native-v1`. Its binary magic is
`REX32-DATA4-V1` followed by two zero bytes. This is a new public format identity,
not a relabeling of previous captures. The driver compiles and captures fresh
evidence; it does not import old captures. A wire-layout, interpretation or
literal-contract change requires a new schema version and fresh capture.

All integer fields are unsigned 64-bit little-endian values. Signed metadata
uses its two's-complement representation; absent index is `UINT64_MAX`.
`encode_record` and `decode_record` explicitly encode fields and byte arrays;
C struct padding is never written. Inputs larger than 8 MiB are refused before
decoding. The positive file has exactly 3,708,464 bytes, with no trailing data.

The 160-byte header is:

| Offset | Bytes | Meaning |
| --- | --- | --- |
| 0 | 16 | Public binary magic and two zero bytes |
| 16 | 8 | Version 1 |
| 24 | 8 | Record count 148 |
| 32 | 8 | Page size 4096 |
| 40 | 8 | Page count 3 |
| 48 | 32 | SHA256 of complete final linked owned ELF |
| 80 | 32 | SHA256 of complete `.rex32_native` section |
| 112 | 32 | SHA256 of exact canonical `PROBES.json` bytes |
| 144 | 8 | Executable section begin label |
| 152 | 8 | Executable section end label |

Each record has 25,056 bytes: 60 integer fields (480 bytes), three whole before
pages (12,288 bytes), then three whole after pages (12,288 bytes). Page order
is operand, low32 decoy, wrong-bank decoy. Integer indices in `common.h` are:

| Indices | Meaning |
| --- | --- |
| 0..4 | Ordinal, declared case, actual probe, seed, position profile |
| 5..7 | Actual instruction length, start label, end label |
| 8..12 | Declared destination, base, index, scale exponent, signed disp8 |
| 13..17 | Operand address, requested flags, measured before/after flags, successor label |
| 18..20 | Actual page addresses |
| 21..23 | Checked page permissions: R=1, W=2, X=4 |
| 24..39 | All 16 measured before GPRs |
| 40..55 | All 16 measured after GPRs |
| 56 | Exact instruction bytes packed little-endian, zero padded |
| 57 | Complete measured capture marker, exactly 1 |
| 58..59 | Reserved, exactly zero |

GPR order is RAX, RCX, RDX, RBX, RSP, RBP, RSI, RDI, R8, R9, R10, R11, R12,
R13, R14, R15. No hardware RIP is sampled. The successor is the authenticated
label immediately after the exact instruction span. Recovery code begins at
that label and is bound as part of the whole executable section, outside the
instruction span. Requested flags are separate from measured flags because
POPFQ cannot freely assign every flag bit.

The last 16 bytes are `ENDR32V1` and the little-endian record count. Case order
is the separate literal contract order. Each case has four records ordered
seed0/interior, seed0/end, seed1/interior, seed1/end. Duplicate, missing,
reordered and substituted identities fail. The strict parser also checks all
spans, literal bytes, independent destination/address declarations, measured
full64 addresses, GPRs, full flags, permissions and three whole-page frames.
The separate four-byte memcpy oracle supplies expected native results.

Canonical `PROBES.json` includes schema, register order, section and harness
labels, and all 53 probe objects (37 positive, 16 native controls). Objects
contain id, name, symbol, start/end/return-end labels, exact lowercase bytes,
length, destination, base, signed index, scale exponent, signed displacement
and positive status. Authentication regenerates and compares the exact bytes,
so changed whitespace, fields, missing/duplicate objects and truncation fail.
The capture header binds this exact metadata, ELF and extraction. The checker
also requires a trusted lowercase capture SHA256 argument. Rehashing an
untrusted replacement does not establish origin. Forty parser controls rehash
their mutations to reach semantic checks; one keeps the original bound digest.

The executable's stable low-level commands are below. `ELF` always names that
same freshly compiled executable, `SECTION` its extracted `.rex32_native`
bytes, `METADATA` its canonical description, and `HASH` the independently
retained capture digest. Use a fresh isolated working directory: some commands
write fixed-name reports there. The public shell driver supplies sandboxing,
resource limits, manifests and failure handling around every invocation.

```text
probe.elf describe ELF SECTION
probe.elf capture ELF SECTION METADATA NEW_CAPTURE
probe.elf verify ELF SECTION METADATA CAPTURE HASH
probe.elf native-controls ELF SECTION METADATA
probe.elf parser-controls ELF SECTION METADATA CAPTURE
probe.elf auth-controls ELF SECTION METADATA CAPTURE HASH
probe.elf dump ELF SECTION METADATA CAPTURE HASH
```

`describe` writes metadata to stdout. `capture` writes the named binary file.
`verify` writes `BINDING.json`. Control commands write `NATIVE-CONTROLS.json`,
`PARSER-CONTROLS.json`, `AUTH-CONTROLS.json` and applicable `failures/` artifacts.
Success returns 0; rejected or unsupported checker input returns 2. Native
control children are checked for the exact expected exit/signal by their parent;
an unexpected crash or acceptance fails the control phase. Altered ELF inputs
in authentication controls are never executed.

Fourteen completed negative native captures use the same encoding with count 1
and ordinal 0, and a different actual probe from declared contract. They are
control evidence, never accepted by the 148-record parser. Two fault controls
retain only 12,288 bytes of actual before pages. Their JSON records planned
inputs/requested flags, actual termination signal and null measured register/
flag observations. There is no invented fault afterstate.

`dump` first verifies the capture, then emits `REPLAY-INPUTS.jsonl`: one JSON
object per actual observation with independent literal/address metadata, all
measured GPRs/flags, a 12-byte operand neighborhood (eight before, four operand
bytes), and before/after page digests. `hardware_RIP` is null. The entry 4096
and successor 4096+length are synthetic model relocations. `modeled_operand_read`
describes the intended DATA4 contract, not a sampled hardware read trace. This
file is data only; no Lean proposition, theorem, proof or kernel replay is
emitted. Complete page images remain in the binary capture.

`REPORT.json` uses `rex-data32-native-run-v1` and summarizes counts/hashes only
after all phases succeed. On failure it may contain an incomplete phase record.
Completion also requires `exit` and `postflight.exit` both 0, PASS `scope.txt`
and intact input/output manifests. Native results do not establish ownership,
synchronization, universal instruction/OS semantics or corpus coverage.
