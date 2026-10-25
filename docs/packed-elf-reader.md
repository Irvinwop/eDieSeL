# Packed ELF field reads

`EDSL.ELF.PackedRead` proves that the existing ELF reader can inspect packed
little-endian bytes through arithmetic on their numeric encoding. New clients
can import this module without importing the frozen corpus or writing a
separate proof of byte-list traversal for each field.

A region is represented by `PackedBytes.bytesOfNat byteCount word`. Its byte
count is explicit: trailing zero bytes remain part of the region. The word need
not be canonical or bounded by that count.

For every natural offset and width, `readNat_bytesOfNat` establishes the exact
original reader result:

```lean
readNat (PackedBytes.bytesOfNat n word) offset width =
  if offset + width ≤ n then
    .ok ((word >>> (8 * offset)) % (1 <<< (8 * width)))
  else .error .truncated
```

In-range zero-width reads return zero; even a zero-width read truncates when
its offset is beyond the region. These are the existing reader's rules.

`field_holds_iff` gives the corresponding arithmetic form of
`FunctionWindow.Field.Holds`. `checkField` and `checkFields` have soundness and
true-if-and-only-if-held theorems. `checkFields_eq_readNat_all` also connects
the numeric check to the exact original aggregate of field reads. A producer
can therefore prove the arithmetic checks and apply that bridge to discharge
an existing reader obligation, preserving its statement.

The implementation reuses the existing packed-byte round-trip, length and
slice theorems. It adds no environmental assumptions or axioms. Client proofs
still need independent file binding, ELF layout, resource and execution facts.
The bridge alone does not authenticate a file or certify a program.

The synthetic integration checks all ten fields of an ELF64 section row
against independently written bytes and numeric field specifications. It covers
limb-crossing reads, high bits, exact trailing-zero counts, truncation and
zero-width boundaries. Changed values, reversed byte order and narrowed field
widths are rejected by both the original and numeric consumers. The fixture
is deliberately not a valid ELF mapping.

Run `lake build PackedReadTests` for the integration and transitive axiom audit.
Whole-file expected-expression quotation and installed compiler-packet
integration remain open. No corpus coverage or full-file performance result
is claimed by this module.
