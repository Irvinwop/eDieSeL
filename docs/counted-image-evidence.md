# Per-image counted-call evidence

The counted-call builders separate an image's file and resource evidence from
its instruction and scheduling proofs. A program can supply one checked named
image and reuse the resource construction and execution assembly below.

```lean
import EDSL.Corpus.CountedResources.Image
import EDSL.Corpus.CountedCertificate.Assembly
```

These generic imports contain no frozen GCC or Clang clients.

## Construct current resources

Start with `Counted.NamedImage file name maxBytes`. Its checked input binds the
complete external ELF file, exact symbol name, entire declared function extent
and explicit byte cap. Function tables, metadata and byte windows are proposals
until the named checker validates them.

`CountedResources.Image` provides:

- `installed` and `admitted`: complete-file installation over the empty prior
  space, using the same name and cap.
- `RX`: executable segments have exactly read/execute permissions. This justifies
  the selected-function index while preserving the rest of the installed space.
- `setup`: the actual resource-manager operation for two callers of this image.
- `Total`: proof that this operation succeeds for every initial shared word.
- `resources`: the actual successful result, obtained using that proof.

`Total` is a construction obligation for the selected instance. It does not add
a premise to the independent program contract. A provider must prove it for its
actual image and layout.

The resulting theorems establish current executable code, preservation of every
originally installed cell, and target freshness. `full_image` preserves each
original byte and all permission bits, including inaccessible and non-code
cells. `target_fresh` concerns the actual registered target. Resource identities
come from the successful manager operations.

Build these modules with:

```sh
lake build EDSL.Corpus.CountedResources.Image EDSL.Corpus.CountedCertificate.Assembly
```

## Assemble admission and a useful execution

`Counted.pre_of_population` assembles the independent `Counted64.Pre` from
facts about the actual finite worker list. It supports any population size and
preserves each original slot and supplied request. Worker slots do not identify
the workers' resource actors.

`Counted.OverlapWitness batch` describes one execution of that exact loaded
batch. It requires two distinct actual slots, successful prefix and suffix
schedules at the same cut, a returned endpoint, and both workers running and
unfinished at the cut. An ordered own/peer/own RMW pattern uses original
observation indices and event payloads. Requests and instruction layouts are
not fixed by this interface.

`Counted.useful_of_witness` applies the independently proved `Counted64.Claim`
to the composed execution and supplies its Post. The returned `UsefulRun` keeps
the same participants, action lists, observation lists, cut and endpoint.
Existing corpus adapters use these equalities to retain their AF choices,
RET-order facts and correlated cleanup.

The unrestricted Claim remains a separate obligation. One useful execution
does not prove universal safety, enabledness or progress. The complete
[certificate interface](counted-certificates.md) combines these obligations.

## Compiler-local admission examples

`GCCAdmission` and `ClangAdmission` under
`EDSL.Corpus.V1.CountedCertificates` expose separate `input`, `checked`,
`named`, `rx`, `total` and `resources` declarations. Each uses the original
complete file and its own metadata:

| Module | File bytes | Function extent | Cap |
| --- | ---: | ---: | ---: |
| `GCCAdmission` | 41,016 | 49 | 64 |
| `ClangAdmission` | 44,240 | 86 | 128 |

```sh
lake build EDSL.Corpus.V1.CountedCertificates.GCCAdmission EDSL.Corpus.V1.CountedCertificates.ClangAdmission
```

Their admission and resource declarations have no transitive type/value
dependency on the other compiler's file or metadata. The tests inspect actual
compiled declarations, including private and recursor dependencies. The
shared-dispatch admission theorem is a control that reaches both files.
Module imports may still load shared corpus declarations; import closure and
proof-dependency closure are different properties.

These examples establish named admission and present resources. The complete
counted certificate constructors still use compiler-indexed loaded-state
builders. Their migration and installed Counted64 grading remain unfinished;
this API adds no corpus certification credit.

The existing coherent scalar RAM, protected resources, stable translations
without hidden aliases, represented CPU features and long-mode/CET-off
assumptions remain. These model theorems do not establish physical CPU or Linux
correspondence, native lifetime or source/compiler preservation.
