# Function control and source contracts

The internal function driver combines a finite typed declaration prefix with
control bodies that can contain loops. It reuses actual parameter allocation,
local reservation, initialization, expression evaluation, and normal cleanup.
This layer has no source parser, checked GNU loop mapping, thread-progress rule,
interference semantics or compiler preservation theorem.

`Control.Function` records dialect, conversion policy and a body-parameterized
`DeclarationSpine`. Its initializers see only previously visible bindings.
Whole-tree coverage precedes every entry effect. Entry reserves all locals
before the first local initializer and keeps the original parameter/local plans.
`FunctionEval.Entry` describes registry metadata and required automatic slots;
it does not assume defined execution or a postcondition.

`FunctionEval.start` produces either accepted finite entry effects and an active
control frame, or an exact failure retaining accepted effects. `observe` advances
that frame through the existing control machine. Exhausting an observation while
active is not a source error or successful completion. A body return computes its
scalar before normal cleanup. Only successful cleanup produces a public returned
observation. Body failure, cleanup failure and fallthrough retain their distinct
outcomes and complete traces. No failure recovery or exception unwinding is
invented. Active observations can be resumed by the observation composition law.

`FunctionCompatibility.runProgram_terminal_iff` transports every existing finite
`StateSyntax.Program` exactly to `Function.ofProgram`, for every initial state,
including malformed states, unsupported preflight and entry/body/cleanup failure.
Returned values, complete state and all accepted events agree. The generic
prepared-body/fold fusion proof makes this one theorem apply to every finite
program, rather than adding a migration proof for each client.

`FunctionContracts.Verifies` requires an actual finite returned observation and
an independent postcondition over original state, return value, final state and
complete events. A useful certificate adds an admitted-state witness. Actual
return derives exclusion of every modeled failure in every finite prefix,
including a body failure not yet settled by the wrapper. Admission does not
assume target safety, success or its result. Existing finite source contracts
and useful certificates transport through `verifies_ofProgram_iff` and
`Certificate.ofProgram` without changing their input domains or postconditions.

The declaration fold currently has an exact specialization theorem to the old
finite driver. The old driver still contains its original traversal. Extracting
one neutral declaration core and making both drivers thin specializations is
pending; do not mistake proven equivalence for physical deduplication.
