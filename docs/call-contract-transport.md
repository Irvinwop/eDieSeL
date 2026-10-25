# Reuse callable proofs and ELF bindings

A new callable verification can reuse an existing behavior proof, current OS
resources, and complete executable binding. The buffer-call transport APIs keep
these obligations separate so each can be proved once and composed.

```lean
import EDSL.BufferCall.ELFRefinement
import EDSL.BufferCall.ELFTransport
import EDSL.BufferCall.RegisteredELFCertificate
import EDSL.BinarySearch.LinearRefinement

open EDSL

#check BufferCall.Refinement.semantics
#check BufferCall.ELFCertificate.ofRetargetInstalledWith
#check BufferCall.ELFCertificate.refine
#check BufferCall.ELFCertificate.toRegistered
```

## Reuse a behavioral contract

`BufferCall.Refinement source target` translates target inputs into source
inputs. It requires equality of the complete argument-binding functions and
buffer lists, a proof that target-domain inputs satisfy the source domain, and
a proof that source results imply target results. Its `semantics` theorem
transfers the existing machine and resource claim for the same candidate bytes.
Identity and composition are available as `Refinement.refl` and `.trans`.

The resource translation keeps the same manager, caller, return slot and input
loan identifiers. `contract_iff`, `current_iff` and `readAllowed_iff` establish
exact resource and read-permission equivalence. Universal AF choices, complete
memory and permissions, return address, stack adjustment, callee saves and
nonarithmetic flags remain in the claim.

For example, an earliest-match implementation satisfies the any-match search
contract on sorted input. `BinarySearch.semantics_of_first_match` derives that
claim from the existing independent first-u32-match contract without another
set of program VCs. Duplicates distinguish the contracts: index 1 in `[7,7]`
is an acceptable any-match result but fails earliest-match. A checked control
preserves this distinction. This implication establishes no logarithmic cost.

A refinement can restrict the domain. Useful target-domain nonvacuity therefore
requires separate evidence. Changing the candidate bytes also requires a
behavior proof for those bytes.

## Bind the proof to a complete executable

`BufferCall.ELFCertificate spec file name maxBytes` combines the existing
named-function checker, independent universal semantics and a useful call in
actual loaded resources. The certificate is indexed by the complete file,
requested byte name, specification and selected byte bound. The default bound
remains 64; the explicit-bound constructor records its argument in the type.

`ELFCertificate.ofLoadedCallWith` packages checked selection and a useful
`ELFLoadedCall`. The call retains every installed cell and all permission bits,
including unrelated segments. Its current resources bind the actual entry,
original caller slot and input snapshots. `binding`, `resource` and
`useful_execution` expose the resulting file and execution guarantees.

`ELFLoadedCall.retargetInstalledWith` reuses a current admitted resource call
and a checked code attachment. It derives installation and text from the
existing checker and complete-image retention. Original caller and input
handles, all existing live loans, allocation identities, snapshots and complete
memory survive the checked manager history. The convenience constructor
explicitly requires executable segment permissions equal `readExecute`;
`retargetWith` accepts an independently checked installation and current text.
`ELFCertificate.ofRetargetInstalledWith` composes this route with a body proof.

`ELFCertificate.refine` reuses complete file selection and source semantics
under another contract. It requires a useful loaded call for that target
contract at the same checked input. No additional file-selection proof is needed.

## Trusted tasks and validation

Library clients supply specifications and must review their domain, result and
usefulness independently of execution or admission. The generic `Spec` type
cannot enforce that review: a client domain is an arbitrary proposition, retained
unchanged by these constructors. A grader fixes its complete trusted contract
independently. `ELFCertificate.toRegistered` requires equality of the
entire specification to the explicitly selected trusted TaskID's registered
specification, including domain, arguments, snapshots, result and usefulness.
`ofRegistered` exposes the same specification from an existing fixed certificate.
These helpers add no task registration, packet admission or corpus credit.

```sh
lake build CallContractTransportTests
lake env lean -j1 -DwarningAsError=true -DautoImplicit=false \
  -DmaxHeartbeats=300000 -DmaxRecDepth=128 -DElab.async=false \
  tests/CallContractTransport.lean
```

The target checks the proof compositions, independent duplicate-result control
and defining-module axiom audit, including imported private declarations.
The APIs also participate in `EDSL.All`.

These are sequential read-only callable results under the existing stable-RAM,
no-asynchronous-interference profile, with four-level canonical addresses,
alignment checks and CET disabled. Native loading and OS authority, physical
CPU correspondence, concurrency, source/compiler preservation and cost results
retain their separate proof obligations.
