# REX-prefixed four-byte loads

The sequential x86-64 model supports `8B /r` memory loads with one W=0 REX
prefix (`40`–`47`). These instructions load four bytes, zero-extend the result
into the full destination register, and preserve flags and memory. The address
uses the full pre-instruction register values, including when the destination
also supplies the base or index. REX.R/B/X select the extended register banks.

The decoded form is `Instruction.loadMem32Rex destination address`. Its length
is `3 + address.suffixBytes`. It reuses the existing supported base/SIB and
signed-disp8 address forms and the checked `loadDWord` primitive. Existing
instruction constructor signatures remain unchanged. Register operands,
unsupported address forms, additional prefixes and other MOV directions are
refused. W=1 loads retain their separate eight-byte semantics.

## Reuse in a proof

Import `EDSL.X86.Sequential.Machine` for
`execute_loadMem32Rex_success_iff` and `execute_loadMem32Rex_context`. These
lemmas expose the actual four-byte load, exact DATA read, destination update,
other-register preservation, complete memory/flag frame and successor RIP.
They require no distinctness premise between destination, base, index or RSP.

The instruction participates in the existing read-only CFG checker and the
Bool, flag-vector and effect VCGs. Use those shared checkers and an independently
stated postcondition for a new program. A successful decode or CFG check supplies
structure; it does not establish the program's result.

`EDSL.OS.WordResources.current_load32Rex_step` transports current DATA4
authority and the original caller slot. The existing loan, epoch, permission
and owner requirements remain in force. The managed TSO ordinary-step path
supports the same load and buffered forwarding; the load does not consume or
publish the pending store queue. It remains outside the caller-only profile.

## Checked scope

Run `lake build RexData32Tests`, then:

```sh
lake env lean -j1 -DwarningAsError=true -DautoImplicit=false \
  -DmaxHeartbeats=300000 -DmaxRecDepth=128 tests/RexData32Audit.lean
```

The tests cover prefix/bank/scale/displacement selection, aliases and high
addresses, zero extension, full frames, fetch and operand permission failures,
four-byte boundaries, CFG/VCG composition and current OS authority. Resource
controls reject stale/wrong owners, undersized loans and absent grants. TSO
controls exercise real buffered forwarding and retained queues.

This extension adds no end-to-end corpus certificate. Whole-function proofs
still require the independent contract, exact final-ELF binding, caller and
resource premises, and the applicable execution model. Physical CPU, loader,
kernel and source/compiler correspondence remain separate obligations.
