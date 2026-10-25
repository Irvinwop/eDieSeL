# Full64 AND with a signed byte immediate

The sequential x86-64 model supports register `AND r64, imm8` through the
shared decoder, executor, verification-condition generator and OS-resource
adapters. A new program can use these rules with its own postcondition and
caller resources; it does not need a separate instruction semantics or a
program-specific AND proof.

## Supported encoding

The accepted four-byte form is `48/49 83 /4 ib`, with ModRM register mode.
`48` selects RAX–RDI and `49` selects R8–R15. All 16 destinations and all 256
immediate bytes are covered. The byte is sign-extended to 64 bits before the
operation: `f8` denotes the mask `fffffffffffffff8`, while `07` denotes `7`.

This subset requires one canonical REX prefix. REX.R/X aliases, additional
prefixes, memory operands, imm32 forms (`81` and `25`), and OR/XOR immediates
remain unsupported. Existing low32 operations retain their own width rules.
Unsupported forms keep the existing decoder errors. Truncated, nonexecutable
or noncanonical instruction fetches retain the actual fetch failure; the
instruction does not require a readable byte after its four-byte encoding.

## Contracts and reuse

Import `EDSL` for the reusable verification API, or use the narrower modules
below. The constructor is
`EDSL.X86.Sequential.Instruction.andImm64 destination immediate`.

| Module | Main reusable interface |
| --- | --- |
| [`AndImmediate64`](../EDSL/X86/Sequential/AndImmediate64.lean) | `AndImmediate64Contract`, `andImm64_contract`, and Bool/vector execution and step laws |
| [`AndImmediate64Decode`](../EDSL/X86/Sequential/AndImmediate64Decode.lean) | `decodeAt_andImm64`, ordered fetch/error laws and exact decoding transport |
| [`AndImmediate64Resources`](../EDSL/X86/Sequential/AndImmediate64Resources.lean) | `current_andImm64_step`, `current_andImm64_stepWith`, and array-admission preservation |
| [`ChoiceNext`](../EDSL/X86/VCGen/ChoiceNext.lean) | Generic Bool/vector next-step WP rules and a Bool cutpoint rule, retaining choice-dependent successor states |
| [`VCGen.AndImmediate64`](../EDSL/X86/VCGen/AndImmediate64.lean) | `wp_andImm64_iff` and `wpWith_andImm64_iff` over the production executor |

The result contract independently specifies bit membership in the intersection
of the original full64 destination and the signed mask. It also proves:

- Other GPRs, all memory and permissions, and nonarithmetic flags are preserved.
- RIP advances by four; the observation is an ordinary next step with no operand
  read or store.
- CF and OF are zero. ZF tests the complete 64-bit result, SF is bit 63, and PF
  is even population parity of the low byte.
- AF remains an independent choice at each step. Vector continuations retain
  the other independent flag choices required by later instructions.

The resource rules preserve the original call/array admission and shared OS
state. RSP may be a destination, but changing its numeric value supplies no
permission to read a new stack. A following RET must still satisfy the
original caller's current-memory and return-stack contract.

For a new function, import its exact bytes, prove the independent result and
frame obligations through the shared VCG, then connect the execution to its
caller resources and artifact certificate. See [the worked verification
example](verify-a-function.md) and [reusable checker](reusable-checker.md).

## Complete example and regression evidence

[`And64MaskSplit`](../tests/And64MaskSplit.lean) checks this complete 21-byte,
seven-instruction function against the existing full64 intersection contract:

```asm
mov rax, rdi
and rax, rsi
mov r8, rax
and r8, -8
and rax, 7
or  rax, r8
ret
```

The proof accepts arbitrary full64 arguments, uses the production byte-checked
CFG and VCG, and establishes the independent result, full memory/permission
frame, preserved nonarithmetic flags and every GPR outside RAX/R8/RSP. Its trace
retires exactly seven instructions and reads exactly the original eight-byte
return slot. The complete-flags extension retains independent choices; the
resource theorem returns the original current OS resources.

The `And64Tests` target includes symbolic all-bank decoding for every immediate,
high-bit and signed-mask boundaries, fetch and unsupported-form failures,
resource preservation, an actual invalid replacement-stack return, and a
continuation through IMUL that rejects a false correlation between future flag
choices. Wrong-width and wrong-mask functions violate independently specified
result bits. Existing ADD/SUB/CMP, logical64 and parity regressions remain.

Run:

```sh
lake build And64Tests
lake env lean -j1 -DwarningAsError=true -DautoImplicit=false \
  -DmaxHeartbeats=300000 -DmaxRecDepth=128 tests/And64Audit.lean
bash scripts/verify-and64-immediate.sh
```

The audit checks theorem dependencies. The native script uses project-owned
synthetic probes and an independent bit-membership/flag oracle, then replays
captured observations through Lean. Native observations are finite evidence
alongside the universal model theorems. Requested pre-GPRs are installed rather
than independently measured; the continuation address is a linked label and
the empty read list is a model footprint. Observed AF supplies an allowed
witness; it does not demonstrate every physically possible AF value.

## Scope

The target remains 64-bit mode with four-level canonical addresses, stable
ordinary RAM and live mappings, controlled interference, CET/IBT/shadow stacks
disabled, and the existing ABI and ownership/loan premises. No new instruction
feature or resource authority is assumed. See [the platform
model](platform-model.md) and [trust boundaries](trust.md).

This extension removes AND-immediate instruction gaps in several larger Clang
functions. Their SIMD, displaced-memory, loop and artifact obligations remain;
no new full-window corpus probe or certificate follows. Validated coverage
remains **20/40 functions and 40/80 artifacts**. These results establish no
physical CPU/OS refinement, compiler preservation, concurrent atomicity,
timing or unrestricted minimum-operation claim.
