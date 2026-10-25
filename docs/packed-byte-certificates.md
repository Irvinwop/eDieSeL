# Packed byte certificates

Large file certificates should share arithmetic and list proofs instead of
repeatedly normalizing every byte at each file offset. The ordinary Lean modules
[PackedBytes](../EDSL/Grading/Export/PackedBytes.lean) and
[PackedBytes.Views](../EDSL/Grading/Export/PackedBytes/Views.lean) provide the
representation laws for that work.
[PackedBytes.Balanced](../EDSL/Grading/Export/PackedBytes/Balanced.lean) adds a
balanced append-tree view with a checked equivalence to ordinary decoding.
[PackedBytes.Encoding](../EDSL/Grading/Export/PackedBytes/Encoding.lean)
composes numeric certificates across different list and chunk representations.
They are certificate-construction helpers;
they add no trusted input declarations and do not change a grading contract.

## Representation

A region has an explicit byte count and a little-endian natural-number value.
For example, the ELF magic bytes `7f 45 4c 46` have value `0x464c457f`.
The count matters: `[1]` and `[1, 0]` have the same numeric value.
`bytesOfNat count value` returns exactly `count` bytes and discards higher digits.

The checked laws cover:

- Both round trips: decoding an encoded list recovers every byte; encoding a
  decoded value gives its residue modulo `256^count`.
- Canonical bounds, and list equality from equal lengths and encoded values.
- Concatenation as addition and a shift by the left region's byte count.
- Prefixes, suffixes and slices as bounded decoding with arithmetic shifts.
- Splitting a region into adjacent parts, including empty and out-of-range slices.

The balanced decoder splits regions larger than sixteen bytes while fuel
remains. Fuel exhaustion falls back to ordinary decoding. Its generic equivalence
proof holds for every fuel, byte count and value; fuel changes the tree shape,
not the represented bytes. Length, round-trip, equality from an independently
established encoding, and drop/take/slice/split laws follow from that equivalence.
These laws do not establish a performance bound or authenticate an external file.

For example, the reusable suffix law is

```lean
List.drop count (bytesOfNat byteCount value) =
  bytesOfNat (byteCount - count) (value >>> (8 * count))
```

Its proof works for arbitrary lengths and values, including `count > byteCount`.
It does not require a new proof for each program or file offset. Source compilation
uses the pinned Lean version, warnings as errors, 300,000 heartbeats and recursion
limit 128. Every theorem prints its transitive axiom dependencies; only the
existing standard set is used.

## Composing independently shaped lists

The numeric API gives every region a shared specification:

```lean
rangeValue word offset count = (word / 256 ^ offset) % 256 ^ count
```

`encodeAppend` joins adjacent length and encoding certificates. It works with
ordinary byte lists and keeps the length needed for the right-hand shift
explicit. [EncodingFacts.appendFacts](../EDSL/Grading/Export/PackedBytes/EncodingFacts.lean)
accepts and returns a conjunction of the length and encoding facts. A producer
can therefore pass one proof per child at each append, sharing the same
certificate when either component is needed. The theorem retains both child
lengths, including empty regions and trailing zero bytes. Each leaf can be
checked locally; the generic append theorem joins those facts without a whole-list reflexivity proof.

For a chunk collection, `EncodedRun word offset count F` certifies a context
`F` for every outer-list tail. It records the additional flattened length and
the numeric prefix plus the appropriately shifted tail. `oneRun`, `consRun`
and `spliceRun` compose those contracts; `closeRun` supplies length and value
facts after applying the context to an empty tail. Theorems accept arbitrary
contexts, empty regions and nonuniform chunks.

Finally, `eq_of_encoding` proves exact list equality from two independent
length and encoding certificates. `closeRun_eq` specializes that bridge to a
byte list and a closed chunk context. Separate length premises prevent a
trailing zero byte from disappearing. These universal proofs are reusable for
new files and list associations; their source checks do not establish that a
particular generated packet fits the runtime limits.

## Serialization and exact input binding

The unchanged packet format permits at most 128 decimal characters per Nat
literal. A general 4 KiB region therefore cannot be serialized as one literal.
It can be represented by balanced addition/shift expressions over smaller
literal limbs: at most 53 bytes fit in each limb. The byte count preserves
high zero bytes. These are lossless positional values, not hashes.

Pinned [Lean v4.35.0 kernel source](https://github.com/leanprover/lean4/blob/v4.35.0/src/kernel/type_checker.cpp)
implements native literal arithmetic. That reduces expression-level work; CPU,
memory and full byte-list conversion still depend on input size. No constant-time
or fixed-budget acceptance claim follows from choosing Nats.

A packed value must still be proved equal to the independently read original
bytes. The library does not authenticate a file, construct that complete equality
certificate, emit page declarations, or install a Counted64 grading route.
Successful source compilation or a small conversion diagnostic is not a corpus
certification. The packet, audit, recursion and cumulative kernel limits remain
unchanged.

Checking only selected regions is a separate extension. It needs a proved
importer/execution dependency rule showing that every omitted byte is irrelevant
to the externally chosen contract. Until then, full-file contracts retain all
original bytes. The [corpus queue](corpus-blockers.md) records the current
integration frontier and the next shared instruction/resource work.
