# Declared-object foundation

Import `EDSL.Source.Objects` for the internal object model, executable
operations, contracts and pure-program embedding. These components are checked
Lean declarations. A separate [finite statement API](source-statements.md) now
connects typed declarations and mutable variables to these operations. The
expression-only `Source.Program` stays unchanged; neither API establishes a
theorem about native source files.

## State and resources

`Objects.State target parameters Environment` records typed external inputs,
an explicit environment, the current actor, fresh identity, remaining automatic
object slots and a registry. A slot is abstract capacity for one object, not
bytes or physical stack space. Objects have declared signed/unsigned int kind,
reserved/live/ended lifetime, declaration-reached flag, optional initialized
value, owner and separate read/write permissions. References are typed internal
identities, without a pointer representation.

`State.WellFormed` checks finite registration and consistent pending metadata.
It does not establish readability, authority, initialized contents, source
validity or program safety. These need their own conditions and proofs.
The current operations preserve external inputs, environment and actor; they
model one actor without asynchronous interference.

| Operation | Behavior |
| --- | --- |
| `reserve dialect kind` | Require fresh identity and available capacity; allocate an owned readable/writable record and consume one slot |
| `initialize dialect reference value?` | Complete a pending declaration once; `none` leaves contents uninitialized rather than inventing zero |
| `load dialect reference` | Check registration, kind, lifetime, declaration, current ownership, read permission and initialized contents |
| `store reference value` | Check current ownership and write permission; permit initialization by assignment; same-value writes still check authority and emit an event |
| `endLifetime reference` | End a reached live object, retain its tombstone and release one slot exactly once |

C non-VLA automatic lifetime starts at block entry; C++ reservation becomes live
when declaration initialization completes, including vacuous initialization.
The C++ event sequence places initialization completion before lifetime begin.
The internal kinds cover ordinary full int values: uninitialized C reads stop
as undefined, while the reviewed C++26 ordinary automatic case stops as erroneous
production. Character propagation exceptions, dynamic storage and
`[[indeterminate]]` are excluded.

`Stop` distinguishes scalar UB, object UB, C++ erroneous production, model
binding faults, resource/authority denial and unsupported coverage. A wrong-kind
binding or denied model permission is not automatically classified as ISO UB.
Failure stops certification at that boundary; permitted C++ continuation after
erroneous production is outside this model.

## Checked contracts

`CanLoad`, `CanStore` and the lifecycle admission predicates describe
registry, metadata, quota and authority directly. They do not call the candidate
operation, assume its success or use the target program's NoUB as admission.

The library proves actual execution, read-after-write, other-object and external
state frames, metadata preservation, initialization by assignment, rejection of
uninitialized/ended/unauthorized reads, and rejection of same-value unauthorized
writes. Lifecycle contracts prove fresh identity, once-only initialization/end,
well-formedness preservation, capacity deltas and a complete declaration cycle
that restores remaining capacity without reusing an ended identity.

These are primitive/protocol contracts. The finite statement API adds a fixed
source driver and exact structural statement/declaration VCs. Each mutable source
program still needs independent input and result contracts, discharged VCs and
an inhabited entry domain.

## One expression engine

`ExpressionCore.evalCore` is the shared traversal. Its typed lookup and scalar
outcome adapter are explicit. `EffectM` supplies a state/error/event carrier;
its composition laws and scalar adapter are checked. Resolver replacement and
carrier-mapping theorems concern complete computations, including failures,
state and events.

`PureEmbedding` proves that the existing scalar program uses the same traversal
without changing any object, input, environment or resource field and emits no
events. This holds for defined, UB and unsupported outcomes, with the original
whole-body coverage preflight. Useful state evidence requires an actual
environment witness; an empty environment type cannot manufacture a certificate.

This embedding uses pure supplied inputs. It is not a proof that a mutable
source parameter may be replaced by its initial value. Mutable parameters need
initialized objects and actual variable reads; the finite statement driver uses
that representation.

## Remaining connections

Source integration must fix one dialect, bind declarations injectively to
matching registered objects, reserve C declarations at block entry, sequence
full expressions and compute return values before scope cleanup. Pending
reservation recovery, lifetime restart, nested blocks and exceptions are not
implemented.

Raw events are internal observations. They do not assert native operand order.
Permitted RHS read reordering and lazy demand need checked correspondence before
source sequencing claims. A future OS/scheduler connection additionally needs
current-resource and representation relations plus transition simulations;
machine addresses do not become source pointers by identification.

This foundation models no object bytes, padding, layout, provenance, aliasing,
qualifiers, atomics, concurrent interference or physical OS/CPU refinement.

## Rule references

The reviewed identities are [N3096](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3096.pdf)
(2023-04-01), especially §§6.2.4, 6.3.2.1, 6.5.16 and 6.7.10, and
[N5001 at the pinned draft commit](https://github.com/cplusplus/draft/tree/6b9b2e9f31aff143334e379e49807488872003e4/source)
(2024-12-17), including `[basic.life]`, `[basic.stc.auto]`,
`[basic.indet]`, `[conv.lval]` and `[expr.ass]`. These dated reviews
do not establish complete GNU or final C++26 conformance.
