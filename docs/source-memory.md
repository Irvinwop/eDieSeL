# Typed memory foundation

The memory modules currently define types, raw pointer values, supplied layout
contracts and typed object contents. They do not execute source pointer
operations or establish native storage, ABI or provenance correspondence.
Existing scalar object evaluation is unchanged.

## Types and values

`EDSL.Source.Types` contains the shared integer types, target numeric profile and
values formerly declared in `Syntax`. Their names and definitions remain the
same. `Memory.ScalarValue target (.integer kind)` is definitionally the existing
`Value target kind`; memory introduces no second integer arithmetic semantics.

`Memory.ScalarType` distinguishes integers from pointers. `ObjectType` adds
fixed arrays. These raw grammars represent more types than the current data
profile admits. That profile permits integer scalars, pointers to integer
scalars or positive fixed integer arrays, and positive fixed integer arrays.
Nested arrays and pointer arrays have structural payload laws, but their source
rules are not admitted by this profile. Qualifiers, structs, unions and dynamic
array bounds remain open.

A pointer is null or a raw descriptor containing a root identity, a singleton
or array-element domain path, and a signed displacement in C bytes from that
domain's start. It is not a numeric machine address. Unknown roots, stale roots,
wrong domains or types, negative/misaligned displacements and one-past values
remain representable. A typed pointer value does not prove that dereferencing
it is valid. Descriptor equality is not a source pointer-equality operation.

## Layout and admission

`StorageLayout target` supplies scalar sizes and alignments independently of
numeric value widths. It requires positive sizes, power-of-two alignments that
divide those sizes, sufficient integer storage capacity, and the stated
character/signed-unsigned layout agreements. A C byte has `target.charBits`
bits, at least eight; it is not assumed to be an octet. A Boolean's numeric
range does not determine its storage size.

The structural size and alignment queries are mathematical layout operations,
not implementations of source `sizeof` or `alignof`. No concrete ABI, byte order,
padding representation, pointer encoding or `size_t`/`ptrdiff_t` choice is
provided.

`Memory.typeCovered` checks the supplied layout, the initial C23 data profile,
and object/direct-pointee extents. It is a data admission check, not a proof of
program definedness or an executable pointer-access check. It rejects new C++
memory types. Existing common C/C++ integer coverage does not use this gate and
remains available.

## One contents tree

`Payload target objectType` stores an optional scalar value at each leaf; array
children are subobjects, not fresh allocation roots. An absent leaf remains
uninitialized. `ScalarPath` carries the bounds and shape needed to select a
scalar leaf. Raw path resolution rejects out-of-bounds indices, stopping at an
array, and continuing past a scalar.

The checked laws establish lookup after update, preservation of every other
leaf, overwrite, restoration and extensional equality. They apply structurally
also to raw nested arrays. The old optional full-int contents embed exactly,
including an absent value. These laws establish typed contents behavior; they
supply no allocation, lifetime, permission or pointer-validity premise.

The existing object registry remains authoritative. Its record/state representation
is shared through `Objects.Registry`; the current executable specialization still
uses integer records. There is no second heap in these modules. Connecting the
typed payload to that registry, then implementing
checked designation, loads, stores and lifetime operations, is the next execution
dependency. The shared engine already has one expression/place traversal and complete-effect
transport; its memory leaves remain abstract. The concrete operations must
instantiate that engine and feed the existing statement/control machine. Source operand ordering, interference and OS effects
still need explicit semantics and correspondence proofs.
