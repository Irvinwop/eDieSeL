# Reusing Bool proofs with complete flag choices

A sequential proof may use one Bool choice per instruction while a public task
requires independent choices for each undefined flag. Reusing that proof needs
both bounded correctness and a policy that covers every actual prefix.

[PureCall.semantics_of_bounded_bool](../EDSL/PureCall/ResourcesFromBool.lean)
provides the adapter. For every state admitted by the original PureCall Pre,
supply a bound uniform over all Bool streams, the original Post for every
execution, and the actual RawPolicy. The bound may depend on the input and
initial state. The conclusion uses the same Spec and bytes under the complete
flags task. Existing resource admission still supplies code and caller loans,
the return slot, memory permissions, ABI frames and the current OS world.

The reusable [policy transport](../EDSL/Grading/PolicyRefinement.lean) proves
that every actual new prefix reaches an old reachable state. At each prefix,
restricted simulation reproduces the complete next observation. This preserves
the Current predicate, each read's permission in its actual pre-state, memory
and effect restrictions. Bounded total correctness supplies the required
prefix safety; a list of instructions or byte-level metadata does not.

This adapter does not assert global Bool simulation. In particular, independent
undefined IMUL flags can prevent its use. Such programs need a direct complete
flags proof. It also establishes no body, ELF identity, registration, native
correspondence or corpus result by itself. The existing stable-memory and
no-asynchronous-interference assumptions remain explicit in the target model.
