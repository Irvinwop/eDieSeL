# Sixteen-byte ordinary RAM

`EDSL.X86.Memory128` provides functional 128-bit loads and stores over the
existing byte-addressed `Memory`. It composes the checked eight-byte primitives,
with low addresses holding the low 64-bit lane. Unaligned addresses are allowed
under the existing ordinary-RAM target assumptions.

`loadOWord` rejects a sixteen-byte extent that wraps the address space. Each
byte must be canonical and readable; failures retain the original DATA fault
address. `storeOWord` checks all sixteen original bytes for mappedness and write
permission before returning an updated functional memory value.

`oword_load_after_write` and `oword_store_sound` establish the complete 128-bit
result. `writeOWord_frame` preserves every byte outside the modular sixteen-byte
footprint. Execute and write permissions remain unchanged. These theorems apply
to arbitrary memories, addresses and values under their stated premises.

The module supplies RAM operations for future vector instructions. It does not
add XMM registers, SIMD opcodes or a concurrent memory event. Functional updates
do not establish hardware atomicity, visibility, fault atomicity or a physical
CPU refinement. Ownership, loans and concurrent access still require separate
OS and instruction-level contracts.

Run `lake build Memory128Tests` for independent little-endian byte vectors,
complete store images, inaccessible or unwritable final bytes, address wrapping
and canonical-hole boundaries. The byte-order checks use literal bytes and
integer values, rather than only round-tripping the writer through its reader.
All proofs and tests use the pinned Lean version and existing proof budgets.
