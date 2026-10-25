# Signed displacements for ordinary memory operands

Supported ordinary x86-64 memory instructions can use a signed eight-bit
address displacement through the shared decoder. Existing address values,
execution rules, VCG continuations and OS-resource contracts apply directly.
A new function needs its own invariant and independent result contract; it
does not need another memory executor or a per-program displacement model.

Import `EDSL`, or the narrower `EDSL.X86.Sequential.DisplacedData` module.

## Address subset

The extension admits ModRM `mod = 01` for the already supported ordinary
DATA1/4/8 loads, stores, additions, comparisons and byte-zero-extension forms.
Each operation retains its existing opcode, register-bank, prefix and width
restrictions. This does not add every width or REX encoding of those operations.

A base form uses `base + signExtend(disp8)`. A supported SIB form uses the
pre-instruction base and optional scaled index, then adds that signed
displacement. Register arithmetic remains full64 modular arithmetic. RBP/R13
are real bases in this form; a zero displacement still consumes its byte.
An absent SIB index retains the encoded SIB and scale for length accounting.

The shared suffix reader accepts an explicit suffix offset, so unprefixed,
REX and MOVZX instruction layouts reuse the same logic. The original
offset-three `decodeDisp8AddressAt` API remains available to LEA and the
CallReturn decoder. SIB is fetched before its displacement; truncated,
nonexecutable and noncanonical fetches retain their actual errors. The decoder
requires only the instruction's encoded bytes.

Existing `mod = 00` forms retain their behavior. Additional prefix, displacement
and addressing families remain unsupported unless separately documented in
the [machine profile](coverage.md#supported-machine-profile).

## Execution and resource obligations

This changes address decoding, with no new instruction or address constructor.
The normal production executor still performs the actual operand access and
its width, flags and register updates. Generic decoding transport connects the
same exact instruction bytes in a code window to current executable memory.

An address expression grants no authority. Reads still need the complete
current readable extent. Stores still need their current owner/ticket, writable
mapping and compatible loans, and evolve the same OS world. Caller-stack
permission remains tied to the original slot even when an instruction loads
or changes RSP. The existing target assumptions and interference boundaries
remain; see [ownership](ownership.md), [borrowing](borrowing.md) and
[the platform model](platform-model.md).

## Checks and limitations

`DisplacedDataTests` includes exact decoding, register-bank/SIB/scale and
signed-boundary cases, full value/flag/frame observations, fetch and DATA
failures, denied stores, stale ownership, conflicting loans, and actual
store/load/current-resource and original-caller-slot checks. Existing move,
logical, arithmetic and CallReturn regressions are retained.

The owned Linux x86-64 native fixture covers 20 windows and 80 observations,
with measured initial and final GPRs, flags, and a whole-page RAM oracle.
Four semantic mutants and malformed or altered capture inputs must be rejected.
Fresh generated Lean propositions replay the recorded operand neighborhood
through the production step. Their RIP is relocated from the exact instruction
length; hardware RIP is not separately sampled. Finite native evidence is
separate from universal model theorems and physical CPU/OS refinement.

```sh
lake build DisplacedDataTests
bash scripts/verify-displaced-data.sh
```

The address extension removes shared instruction barriers in several frozen
functions. Complete-loop, external-call, memory-ownership and full-artifact
obligations remain. It adds no corpus certification: coverage remains
20/40 functions and 40/80 compiler artifacts.
