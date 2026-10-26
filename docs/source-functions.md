# Function control and source contracts

The internal function driver combines a finite typed declaration prefix with
control bodies that can contain loops. Parameters and locals currently use
full signed/unsigned int objects. Entry, initialization, expression evaluation
and normal cleanup use the shared object semantics. Source parsing, GNU loop
mapping, thread progress, interference and compiler preservation remain open.

## Declarations, execution and cleanup

`Control.Function` records dialect, conversion policy and a body-parameterized
`DeclarationSpine`. Initializers see only previously visible bindings.
Whole-tree coverage precedes every entry effect. Entry reserves all locals
before the first local initializer and keeps the original parameter/local plans.
`FunctionEval.Entry` describes registry metadata and required automatic slots;
it assumes neither defined execution nor a postcondition.

`Objects.Declarations` contains the shared spine and its typed reservation-plan
translation. `Objects.DeclarationEval` owns one executable initializer fold.
Both finite `BlockEval.evalDecls` and control-function entry use that definition.
The finite syntax remains a compatible wrapper: its translation changes syntax
and plan types without performing object operations. Neither neutral module
imports loop control or the function driver.

`FunctionEval.start` produces accepted finite entry effects and an active
control frame, or an exact failure retaining accepted effects. `observe` advances
that frame through the existing control machine. Exhausting an observation while
active is not a source error or successful completion. A body return computes its
scalar before normal cleanup. Only successful cleanup produces a public returned
observation. Body failure, cleanup failure and fallthrough retain distinct
outcomes and complete traces. No failure recovery or exception unwinding is
invented. Active observations can be resumed by the observation composition law.

## Reusing existing finite proofs

`FunctionCompatibility.runProgram_terminal_iff` transports every existing finite
`StateSyntax.Program` exactly to `Function.ofProgram`, for every initial state,
including malformed states, unsupported preflight and entry/body/cleanup failure.
Returned values, complete state and all accepted events agree. The generic
prepared-body/fold fusion proof applies to every finite program.

`FunctionContracts.Verifies` requires an actual finite returned observation and
an independent postcondition over original state, return value, final state and
complete events. A useful certificate adds an admitted-state witness. Actual
return derives exclusion of every modeled failure in every finite prefix,
including a body failure not yet settled by the wrapper. Existing finite source
contracts and useful certificates transport through `verifies_ofProgram_iff`
and `Certificate.ofProgram` without changing their admission or postcondition.

## Composing new function proofs

`Control.FunctionVC` connects declaration, control and cleanup obligations:

| Interface | Obligation |
| --- | --- |
| `vcFold`, `vcPrepare` | Generate initializer and terminal-body conditions over the shared declaration spine |
| `vcEntry` | Compose parameter entry, complete local reservation and initialization with a prepared-body contract |
| `vcCleanup` | Require actual reverse local cleanup, then reverse parameter cleanup, before accepting a returned scalar |
| `vcExecute` | Combine entry with annotated `StructuredVC` conditions and the cleanup continuation |
| `verifies_of_vc`, `certificate_of_vc` | Turn discharged conditions and whole-tree support into actual full-function completion |
| `verifies_of_entry_vc` | Compose a separately proved control segment with the same entry and cleanup rules |

Optional initializers reuse `BlockVC.vcInitializer` and the same expression
transformer. The operation-level leaves are existing entry, reservation,
initialization and lifetime-ending primitives. No formula evaluates a second
expression interpreter or calls the whole-function observer as its specification.

For a new function:

1. State its input/resource admission and result/frame contract independently.
2. Construct typed declarations and control. Prove whole-tree model coverage,
   including unreachable syntax.
3. Supply loop invariants and natural ranks. `Annotation.ofLoopHints` can build
   the annotation tree from a policy for loops in the current typed context.
4. Discharge the generated conditions. `StructuredVC.vc_mono` weakens normal and
   early-return postconditions while retaining the supplied invariants/ranks.
5. Apply a function verification rule and provide an admitted-state witness for
   a useful certificate. Completion derives modeled failure exclusion.

Annotations are proof data, not execution inputs. Their construction does not
synthesize valid invariants or prove termination. The formula and entry/cleanup
factorization laws are checked; the annotated control generator has a soundness
result, without a completeness or weakestness claim.

## Checked loop-bearing function

[The division client](../tests/SourceFunctionVC.lean) embeds a typed numerator
and accepts a divisor parameter. It declares remainder and quotient locals,
repeatedly subtracts the positive divisor, and returns the quotient. Its
admission is only well-formed caller metadata, three automatic slots and a
positive typed divisor. The proof covers all admitted targets, dialects,
conversion policies and typed numerators.

The postcondition exhibits a remainder satisfying
`numerator = divisor × returned + remainder`, with `remainder < divisor`.
It preserves caller inputs/environment/actor and all preexisting registered
objects, advances the fresh identity by three, restores the original slot count,
and retains ended records for both locals and the parameter. The trace ends
with the return read followed by ending the quotient, remainder and divisor.
A supported assignment after the return is skipped.

The client uses the entry/segment rule, shared structural control VCs, arithmetic
and access facts, and generic cleanup contracts. It proves a public returned
observation after cleanup, rather than stopping at an internal body return. It
does not directly instantiate the `vcExecute` annotation-family interface.

[Failure regressions](../tests/SourceFunctionFailures.lean) prove that a permitted
write survives a later denied read without cleanup, and that partial cleanup
retains its first successful end before a duplicate plan fails. The latter
exercises a malformed active frame outside successful-entry invariants. Both
preserve arbitrary earlier history and use compositional laws rather than
expensive whole-observer normalization.
