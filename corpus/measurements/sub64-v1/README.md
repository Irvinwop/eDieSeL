# Corpus v1 diagnostic after SUB64

The unchanged production read-only `CFG.analyze` accepts **19/40 GCC and
19/40 Clang windows** under its existing 64-byte/32-static-node profile. The
reports use the unchanged `corpus/Probe.lean` on all 80 frozen function windows.
Every extracted window was compared byte for byte with its manifest and its
complete original ELF; those comparisons were repeated before publication.
Input, extracted-data, dependency-source and dependency-object seals were
checked before and after the two successful probe processes.

This measurement supplies decoding/control-flow diagnostics. It attempts no
end-to-end certification or native execution. The reports' `certified_end_to_end:
0` means this probe certifies no artifacts; the existing certificate score
remains **20/40 distinct functions, 40/80 compiler artifacts**, including
**three distinct concurrent functions**. CFG acceptance supplies no functional,
termination, external-call, resource, concurrency or physical-system contract.

The new register/sign-extended-imm8 SUB64 support exposes these next frontiers:

- GCC factorial stops at register TEST8 (`+0x27`); Clang still stops at DEC32.
- GCC triangular stops at NOP7 (`+0x21`). Clang triangular's complete CFG is
  accepted with 14 nodes, leaving its independent arithmetic/resource contract.
- GCC strlen stops at CALL (`+0x11`) on the sequential route. The existing
  sibling CallReturn decoder supports direct CALL, but binding the actual
  reachable libc/PLT code and composing its private stack remains work.
- GCC reverse stops at a DATA4 disp8 store (`+0x24`).
- Clang binary search's complete CFG is accepted with 21 nodes, leaving its
  sorted-interval/result/resource contract.

Windows longer than 64 bytes still stop at the byte-size gate. No larger-profile
or sibling CallReturn probe was run in this measurement. Their later DATA,
branch, stack and external-call gaps in the
[blocker queue](../../../docs/corpus-blockers.md) are explicitly source-audited
predictions. Writable/atomic instructions may also be rejected by the read-only
policy before a later ISA gap. This diagnostic is not a complete inventory of
the project's effect-aware and sibling backends.

`gcc.json` and `clang.json` are exact copies of the emitted reports.
`WINDOWS.json` is the exact 80-window extraction inventory, with full-file and
window hashes; its `certification: unverified` entries retain the frozen
manifest's historical meaning. The immutable inputs and previous measurements
are unchanged. Final ELF SHA-256s:

- GCC: `3accb2f86b13dfac93c717aa1ac825b6cdf106de09bb2efa7cc5519fcf4646b3`.
- Clang: `d74c7b71cdcc3107c870b7765d589b28f51bd5d451ef1f4e5e07425f05f53b61`.

`checker-sources.sha256` records the exact 95-source available dependency tree
and the probe source with repository-relative paths. All recorded source bytes
were also compared with this published tree. The inventory does not assert that
every available module was imported by each process. `frozen-inputs.sha256`
binds the toolchain pin, probe, specifications, manifests and complete ELFs.
`validation.json` summarizes the completed process/stability checks and records
the original receipt digests without machine-specific paths. `SHA256SUMS` binds
these published diagnostic files. These manifests record provenance; successful
hash checks do not establish decoder soundness or independent proof acceptance.

The probe consumes a directory containing one `SYMBOL.bin` per manifest
function, extracted from the unchanged complete ELF. With those verified
windows and the pinned project dependencies, its command shape is:

```sh
lake env lean -j1 -DwarningAsError=true -DautoImplicit=false \
  -DmaxHeartbeats=300000 -DmaxRecDepth=128 --run corpus/Probe.lean \
  corpus/v1/specifications.tsv VERIFIED_WINDOWS_DIR OUTPUT.json
```

This diagnostic creates no new function certificate and changes no frozen
compiler option, source definition, function identity or model assumption.
