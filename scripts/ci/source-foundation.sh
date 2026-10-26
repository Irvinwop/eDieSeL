#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
# A scoped source proof gate; no binary corpus or native fixtures are required.
set -euo pipefail
export LC_ALL=C
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
output=${EDSL_SOURCE_CHECK_OUTPUT:-artifacts/source-foundation}
test ! -e "$output/PASSED.md"
mkdir -p "$output"
# Source identity includes the package and audit inputs, not only proof modules.
git ls-files --cached -z > "$output/tracked-before.z"
xargs -0 -r sha256sum -- < "$output/tracked-before.z" > "$output/source-before.sha256"
node scripts/audit-lean-source.cjs --tracked
lake build EDSL.Source SourceSemanticsTests
lake env lean -j1 -DwarningAsError=true -DautoImplicit=false -DElab.async=false \
    tests/SourceSemantics.lean > "$output/audit.log" 2>&1
grep -q '^OWNER_AUDIT_PASS ' "$output/audit.log"
find .lake/build/lib/lean -type f \
    \( -name '*.olean' -o -name '*.olean.private' -o -name '*.olean.server' \) \
    -print0 | sort -z | xargs -0 -r sha256sum -- > "$output/objects-before.sha256"
lake env leanchecker --fresh tests.SourceSemantics \
    > "$output/fresh.log" 2>&1
git ls-files --cached -z | cmp -- "$output/tracked-before.z" -
sha256sum --check "$output/source-before.sha256" > /dev/null
find .lake/build/lib/lean -type f \
    \( -name '*.olean' -o -name '*.olean.private' -o -name '*.olean.server' \) \
    -print0 | sort -z | xargs -0 -r sha256sum -- > "$output/objects-after.sha256"
cmp -- "$output/objects-before.sha256" "$output/objects-after.sha256"
node scripts/audit-lean-source.cjs --tracked --generated "$output"
printf 'Scoped source build, owner audit and fresh kernel replay passed for the recorded source/object bytes.\n' \
    > "$output/PASSED.md"
