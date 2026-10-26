# Repository guidance

- Implement the eDSLs, semantics, proof infrastructure, and validators in Lean 4.
  C (GNU23), C++ (GNU++26), LLVM IR, and assembly are modeled/generated domains.
  Native fixtures and necessary runtime shims may use C/C++/assembly.
- Keep Lean pinned, build with warnings as errors, and audit theorem dependencies.
  Do not introduce proof holes, project axioms, or unchecked solver results into
  claims advertised as proved. List environmental assumptions in theorem contracts.
- Treat OS resources, effects, ownership, and synchronization as first-class
  parts of the program model across every language/backend.
- Keep implementation status accurate. Design documents do not establish an
  implemented API or supported backend.
- The primary route is source-first. Use one shared executable Lean semantics
  for GNU C23 and GNU++26. Prove each target program free of undefined behavior
  and prove its source contract; never assume source definedness.
- Keep OS, scheduler, memory model, synchronization and inputs explicit until
  their implementation sources are proved in the same system.
- Close compilation through exactly one verified binary seed and source proofs
  of successive bootstrap stages, including each compiler preservation contract.
  Existing binary-first clients are legacy; machine-code proofs serve the seed
  and hardware-model boundary rather than new per-program verification.
- Final proofs may use decide +kernel. Keep native_decide development oracles
  in ignored scratch only; native_decide, ofReduceBool, proof holes and unchecked
  solver facts are forbidden in final proofs and audited modules.
- Use GitHub-hosted CI for authoritative heavy proof checking and replay. Treat
  resource budgets as documented engineering limits, separately from trust.
- The repository is public. Never commit real security findings, their metadata,
  traces, or reproducers, and do not put them in CI logs/artifacts. Use ignored
  local storage. Synthetic negative fixtures owned by this project are allowed.
  Proof failure, timeout, and unsupported code do not establish a defect.
- Document target limitations and failure behavior; never silently lower an
  operation to a weaker semantic contract.
- Tests must check independently defined behavior and catch plausible defects.
  Do not repeat implementation logic, assert fixture assignments, or mock away
  the behavior under test. Skip new tests without meaningful evidence.
- Run checks appropriate to the change. Keep bootstrap compiler checks distinct
  from future runtime, eDSL, ABI, and memory-model validation.

- Use descriptive branch names with normal prefixes such as `feature/`, `fix/`,
  `docs/`, or `test/`; do not include agent or tool names. Remove completed task
  branches after their changes are accepted on `main`. Preserve active work and
  cached proof dependencies when cleaning branch references.
