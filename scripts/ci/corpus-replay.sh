#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
payload=.cache/ci-corpus-replay

hash_objects() {
    find .lake/build/lib/lean "$payload/private" -type f \
        \( -name '*.olean' -o -name '*.olean.private' -o -name '*.olean.server' \) \
        -print0 | sort -z | xargs -0 -r sha256sum --
}
check_sources() {
    git ls-files --cached -z | cmp -- "$payload/tracked-files.z" -
    sha256sum --check "$payload/tracked.sha256" > /dev/null
}
hash_proof_inputs() {
    find "$payload/roots" "$payload/prepared" -type f -print0 |
        sort -z | xargs -0 -r sha256sum --
}
check_proof_inputs() {
    # Compare against the pack-time baseline, including the file inventory.
    # Never replace it after compilation/audit, which could hide a changed root.
    hash_proof_inputs | cmp -- "$payload/proof-inputs.sha256" -
}
case "${1:-}" in
    pack)
        [[ $# == 1 ]]
        gate=$(< artifacts/corpus-certificates/LATEST)
        test -f "$gate/PREPARED.md"
        test ! -f "$gate/READY.md"
        test "$(< "$gate/scope.txt")" = full-project-and-corpus-cli
        # Re-read the gate's exact source, ELF, private input and object bytes
        # before creating a relocatable, same-run transport payload.
        for manifest in source-before frozen-before gate-inputs modules-before; do
            sha256sum --check "$gate/$manifest.sha256" > /dev/null
        done
        test ! -e "$payload"
        mkdir -p "$payload/private" "$payload/prepared"
        cp -a -- "$gate/lib/." "$payload/private/"
        cp -- "$gate/replay-build-targets.txt" "$payload/build-targets.txt"
        # Retain the exact generated assertion/CLI source and gate inputs that
        # preparation compiled. The original manifests are absolute; after
        # verifying them above, relocate these small proof inputs and seal them.
        cp -a -- "$gate/source" "$payload/prepared/source"
        cp -- "$gate/Audit.lean" "$gate/check-report.jq" "$gate/scope.txt" \
            "$gate/fresh-target.txt" "$gate/fresh-receipt-label.txt" "$payload/prepared/"
        node scripts/ci/replay-plan.cjs EDSL/All.lean \
            "$payload/prepared/source/CorpusFullReplay.lean" "$payload/roots"
        hash_proof_inputs > "$payload/proof-inputs.sha256"
        node scripts/audit-lean-source.cjs --tracked --generated "$payload/roots" \
            --generated "$gate"
        git ls-files --cached -z > "$payload/tracked-files.z"
        xargs -0 -r sha256sum -- < "$payload/tracked-files.z" > "$payload/tracked.sha256"
        hash_objects > "$payload/objects.sha256"
        find .lake/build "$payload/private" "$payload/roots" -type f -print0 |
            sort -z | xargs -0 -r sha256sum -- > "$payload/build.sha256"
        # tar preserves executable modes; artifact transport must not turn
        # restored Lake executables into non-executable, apparently valid hits.
        tar -cf "$payload/inputs.tar" .lake/build "$payload/private" "$payload/roots" \
            "$payload/prepared" "$payload/proof-inputs.sha256" \
            "$payload/build-targets.txt" "$payload/tracked-files.z" \
            "$payload/tracked.sha256" "$payload/objects.sha256" "$payload/build.sha256"
        (cd "$payload" && sha256sum inputs.tar > inputs.tar.sha256)
        check_sources
        check_proof_inputs
        sha256sum --check "$payload/objects.sha256" > /dev/null
        # Copying/packing must not silently reset preparation's original input
        # identities. A concurrent edit to the original gate fails here too.
        for manifest in source-before frozen-before gate-inputs modules-before; do
            sha256sum --check "$gate/$manifest.sha256" > /dev/null
        done
        ;;
    shard)
        [[ $# == 2 && $2 =~ ^(0[1-9]|1[0-9]|20)$ ]]
        id=$2
        log="$payload/receipts/$id"
        mkdir -p "$log"
        check_sources
        check_proof_inputs
        sha256sum --check "$payload/build.sha256" > /dev/null
        mapfile -t targets < "$payload/build-targets.txt"
        ((${#targets[@]} > 0))
        for target in "${targets[@]}"; do
            [[ $target =~ ^[A-Za-z_][A-Za-z0-9_.-]*$ ]]
        done
        # Always run Lake after restoring outputs. Its source/dependency traces
        # remain authoritative for invalidation, even with an exact artifact.
        lake build "${targets[@]}" > "$log/lake.stdout" 2> "$log/lake.stderr"
        sha256sum --check "$payload/objects.sha256" > /dev/null
        check_proof_inputs
        node scripts/audit-lean-source.cjs --tracked --generated "$payload/roots" \
            --generated "$payload/prepared"
        private_path="$PWD/$payload/private:$PWD/.lake/build/lib/lean"
        lean=(lake env env "LEAN_PATH=$private_path")
        module=KernelReplay$id
        args=(-j1 -DwarningAsError=true -DautoImplicit=false
            -DmaxHeartbeats=300000 -DmaxRecDepth=128 -DElab.async=false)
        "${lean[@]}" lean "${args[@]}" --root="$PWD/$payload/roots" \
            -o "$payload/private/$module.olean" "$payload/roots/$module.lean" \
            > "$log/compile.stdout" 2> "$log/compile.stderr"
        "${lean[@]}" lean "${args[@]}" "$payload/roots/Audit$module.lean" \
            > "$log/audit.stdout" 2> "$log/audit.stderr"
        hash_objects > "$log/objects-before.sha256"
        check_sources
        check_proof_inputs
        printf 'lake env env LEAN_PATH=<same-run-private>:<Lake> leanchecker --fresh %s\n' \
            "$module" > "$log/fresh.command"
        "${lean[@]}" leanchecker --fresh "$module" \
            > "$log/fresh.stdout" 2> "$log/fresh.stderr"
        # Success is created only after fresh replay and the final byte reread.
        check_sources
        check_proof_inputs
        sha256sum --check "$payload/objects.sha256" > /dev/null
        hash_objects > "$log/objects-after.sha256"
        cmp -- "$log/objects-before.sha256" "$log/objects-after.sha256"
        printf '0\n' > "$log/fresh.exit"
        printf 'Fresh replay shard %s passed for the sealed source and object bytes.\n' "$id" \
            > "$log/PASSED.md"
        ;;
    *) echo 'usage: scripts/ci/corpus-replay.sh pack | shard 01..20' >&2; exit 2 ;;
esac
