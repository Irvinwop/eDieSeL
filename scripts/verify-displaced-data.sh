#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C
ulimit -c 0
edsl_script=$(realpath -e -- "${BASH_SOURCE[0]}")
edsl_source=$(dirname -- "$(dirname -- "$edsl_script")")
cd "$edsl_source"
edsl_arguments=("$@")
edsl_native_only=false
if [[ ${1:-} == --native-only ]]; then edsl_native_only=true; shift; fi
if [[ $# -gt 1 || ${1:-} == --* ]]; then
    echo 'usage: scripts/verify-displaced-data.sh [--native-only] [NEW_OUTPUT_DIRECTORY]' >&2
    exit 2
fi
[[ $(uname -sm) == 'Linux x86_64' ]] || {
    echo 'Displaced DATA native conformance requires Linux x86-64' >&2
    exit 2
}
if [[ $# == 1 ]]; then
    edsl_out=$(realpath -m -- "$1")
    [[ ! -e "$edsl_out" ]] || { echo 'A new output directory is required' >&2; exit 2; }
    mkdir -p -- "$(dirname -- "$edsl_out")"
    mkdir -- "$edsl_out"
else
    mkdir -p artifacts/displaced-data
    edsl_out=$(mktemp -d "$edsl_source/artifacts/displaced-data/run.XXXXXXXX")
fi
edsl_finish() {
    local edsl_rc=$? edsl_post=0
    trap - EXIT
    set +e
    sha256sum --strict --quiet --check "$edsl_out/INPUTS.sha256" > "$edsl_out/postflight.log" 2>&1
    edsl_post=$?
    if [[ -f "$edsl_out/NATIVE.sha256" ]]; then
        sha256sum --strict --quiet --check "$edsl_out/NATIVE.sha256" >> "$edsl_out/postflight.log" 2>&1 || edsl_post=1
    fi
    [[ $edsl_post == 0 ]] || edsl_rc=1
    if [[ $edsl_rc != 0 ]]; then
        printf 'INCOMPLETE: the pipeline did not pass. See exit and phase logs; no completed fresh Lean replay is claimed.\n' > "$edsl_out/scope.txt"
    fi
    printf '%s\n' "$edsl_rc" > "$edsl_out/exit"
    exit "$edsl_rc"
}
trap edsl_finish EXIT
printf 'INCOMPLETE: fresh native capture and Lean replay have not finished.\n' > "$edsl_out/scope.txt"
edsl_fixture="$edsl_source/fixtures/native/displaced-data"
edsl_tag="displaced-data-$(date -u +%s)-$$"
edsl_systemd=(systemd-run)
if [[ $EUID != 0 ]]; then edsl_systemd=(sudo -n systemd-run); fi
edsl_user=$(id -un)
export TMPDIR="$edsl_out"
edsl_environment=("--setenv=TMPDIR=$edsl_out" --setenv=LC_ALL=C)
# Same fail-closed cgroup and timeout driver as the AND64 replay profile.
edsl_bounded() {
    local phase=$1 memory=$2 seconds=$3 runtime
    shift 3
    runtime=$((seconds + 5)); if [[ $seconds == 120 ]]; then runtime=130; fi
    local command=("${edsl_systemd[@]}" --quiet --wait --pipe --collect
        --unit="edsl-$edsl_tag-$phase" --working-directory="$edsl_source"
        "${edsl_environment[@]}" -p "User=$edsl_user" -p "MemoryMax=$memory"
        -p MemorySwapMax=0 -p CPUQuota=100% -p TasksMax=64
        -p "RuntimeMaxSec=$runtime" -p TimeoutStopSec=5s
        -- timeout --signal=TERM --kill-after=5s "${seconds}s" "$@")
    printf '%q ' "${command[@]}" >> "$edsl_out/commands.txt"
    printf '\n' >> "$edsl_out/commands.txt"
    "${command[@]}"
}
edsl_lean_host() {
    # Call only after acquiring the shared lock, including for dependencies.
    awk '/^MemAvailable:/ { found=1; exit !($2>=1572864) }
        END { if (!found) exit 1 }' /proc/meminfo || {
        echo 'Insufficient available memory after acquiring the Lean lock' >&2; return 1;
    }
    if pgrep -a -x 'lean|leanchecker|lake'; then
        echo 'Another Lean process is outside the shared serialization lock' >&2
        return 1
    fi
}
{
    printf 'cd %q\n' "$edsl_source"
    printf '%q ' "$edsl_script" "${edsl_arguments[@]}"
    printf '\n'
} > "$edsl_out/runner.txt"
# Includes the transitive project source imports of the unchanged public base
# and production step. Source identity is checked again even on phase failure.
node scripts/prepare-displaced-data-replay.cjs --sources > "$edsl_out/INPUTS.sha256"
edsl_compiler=${EDSL_CC:-clang-18}
"$edsl_compiler" --version > "$edsl_out/compiler.txt"
uname -srmo > "$edsl_out/platform.txt"
getconf PAGESIZE > "$edsl_out/page-size.txt"
objcopy --version > "$edsl_out/objcopy.txt"
nm --version > "$edsl_out/nm.txt"
edsl_bounded compile 536870912 30 "$edsl_compiler" -std=gnu2x -O2 -Wall -Wextra -Werror \
    -fno-pie -no-pie -fno-lto '-Wl,--build-id=none,-z,noexecstack' \
    "$edsl_fixture/check.c" "$edsl_fixture/probe.S" -o "$edsl_out/probe.elf" \
    > "$edsl_out/compiler.log" 2>&1
sha256sum "$edsl_out/probe.elf" > "$edsl_out/ELF.sha256"
objcopy --dump-section ".edsl_disp8=$edsl_out/instructions.bin" \
    "$edsl_out/probe.elf" "$edsl_out/extraction-copy.elf"
rm -- "$edsl_out/extraction-copy.elf"
nm -n --defined-only "$edsl_out/probe.elf" > "$edsl_out/symbols.txt"
objdump -d -j .edsl_disp8 "$edsl_out/probe.elf" > "$edsl_out/disassembly.txt"
sha256sum --strict --quiet --check "$edsl_out/ELF.sha256"
# The changed byte is in the harness, outside all positive instruction spans.
# Rejection must happen before any probe or capture output.
cp -- "$edsl_out/instructions.bin" "$edsl_out/altered.bin"
printf '\x00' | dd of="$edsl_out/altered.bin" bs=1 count=1 conv=notrunc status=none
edsl_status=0
edsl_bounded tamper 134217728 30 "$edsl_out/probe.elf" "$edsl_out/altered.bin" \
    > "$edsl_out/tamper.stdout" 2> "$edsl_out/tamper.stderr" || edsl_status=$?
printf '%s\n' "$edsl_status" > "$edsl_out/tamper.exit"
[[ $edsl_status == 2 && ! -s "$edsl_out/tamper.stdout" ]]
rg -q '^linked-section extraction mismatch$' "$edsl_out/tamper.stderr"
edsl_bounded native 536870912 30 "$edsl_out/probe.elf" "$edsl_out/instructions.bin" \
    > "$edsl_out/observations.txt" 2> "$edsl_out/result.log"
sha256sum --strict --quiet --check "$edsl_out/ELF.sha256"
sha256sum --strict --quiet --check "$edsl_out/INPUTS.sha256"
edsl_bounded prepare 536870912 30 node scripts/prepare-displaced-data-replay.cjs "$edsl_out" \
    > "$edsl_out/preparation.json" 2> "$edsl_out/preparation.log"
edsl_bounded controls 536870912 30 node tests/displaced-data-replay.cjs "$edsl_out" \
    > "$edsl_out/binding-controls.log" 2>&1
sha256sum "$edsl_out/probe.elf" "$edsl_out/instructions.bin" "$edsl_out/symbols.txt" \
    "$edsl_out/observations.txt" "$edsl_out/result.log" "$edsl_out/REPLAY.json" \
    "$edsl_out"/replay/FreshDisplacedData_*.lean > "$edsl_out/NATIVE.sha256"
edsl_bounded before 536870912 30 node scripts/prepare-displaced-data-replay.cjs --check "$edsl_out" \
    > "$edsl_out/binding-before.json" 2> "$edsl_out/binding-before.log"
if [[ $edsl_native_only == false ]]; then
    export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
    edsl_toolchain=$(cat lean-toolchain)
    [[ $edsl_toolchain == 'leanprover/lean4:v4.35.0' ]]
    export ELAN_TOOLCHAIN="$edsl_toolchain"
    edsl_lake=$(command -v lake)
    edsl_environment+=(--setenv=LEAN_NUM_THREADS=1 "--setenv=ELAN_TOOLCHAIN=$edsl_toolchain"
        "--setenv=PATH=$PATH")
    # Dependency construction remains distinct from the 20 fresh replay units.
    {
        exec 9>>/tmp/edsl-lean-build.lock
        flock 9
        edsl_lean_host
        edsl_bounded dependencies 3221225472 120 "$edsl_lake" build DisplacedDataTests
        edsl_lean=$("$edsl_lake" env which lean)
        "$edsl_lean" --version > "$edsl_out/lean-version.txt"
        [[ $(cat "$edsl_out/lean-version.txt") == 'Lean (version 4.35.0,'* ]]
        edsl_sysroot=$("$edsl_lean" --print-prefix)
        edsl_lean_path=$("$edsl_lake" env printenv LEAN_PATH)
        flock -u 9
        exec 9>&-
    } > "$edsl_out/build.log" 2>&1
    edsl_environment+=("--setenv=LEAN_SYSROOT=$edsl_sysroot" "--setenv=LEAN_PATH=$edsl_lean_path")
    for edsl_replay in "$edsl_out"/replay/FreshDisplacedData_*.lean; do
        edsl_name=$(basename -- "$edsl_replay" .lean)
        (
            exec 9>>/tmp/edsl-lean-build.lock
            flock 9
            edsl_lean_host
            sha256sum --strict --quiet --check "$edsl_out/INPUTS.sha256"
            sha256sum --strict --quiet --check "$edsl_out/NATIVE.sha256"
            edsl_bounded "$edsl_name" 3221225472 120 "$edsl_lean" -j1 \
                -DwarningAsError=true -DautoImplicit=false -DmaxHeartbeats=300000 \
                -DmaxRecDepth=128 "$edsl_replay"
        ) > "$edsl_out/$edsl_name.log" 2>&1
        printf '%s\n' "$edsl_name" >> "$edsl_out/kernel-passed.txt"
    done
    [[ $(wc -l < "$edsl_out/kernel-passed.txt") == 20 ]]
    edsl_bounded audit 536870912 30 node scripts/prepare-displaced-data-replay.cjs --kernel "$edsl_out" \
        > "$edsl_out/KERNEL.json" 2> "$edsl_out/kernel-audit.log"
    sha256sum "$edsl_out"/replay/FreshDisplacedData_*.lean > "$edsl_out/REPLAY.sha256"
    printf '80 fresh CPU observations passed all 20 kernel replay shards and transitive dependency audits.\n' > "$edsl_out/scope.txt"
else
    printf 'Native and binding checks only; fresh Lean kernel replay was not run (0/20 shards checked).\n' > "$edsl_out/scope.txt"
fi
edsl_bounded after 536870912 30 node scripts/prepare-displaced-data-replay.cjs --check "$edsl_out" \
    > "$edsl_out/binding-after.json" 2> "$edsl_out/binding-after.log"
sha256sum --strict --quiet --check "$edsl_out/NATIVE.sha256"
sha256sum --strict --quiet --check "$edsl_out/INPUTS.sha256"
cat >> "$edsl_out/scope.txt" <<'SCOPE'
Finite owned Linux x86-64 observations of 20 displaced ordinary DATA windows,
two seeds and two placement profiles. All 16 initial/final GPRs, full measured
flags and captured neighborhoods are bound to fresh propositions using the
unchanged public initial/view and production step. RIP is relocated to 4096
plus the exact linked instruction length; it was not separately CPU sampled.
The native independent C oracle checks the whole page. RAM replay covers only
eight leading bytes plus the operand width, with the public base's operand
writability; native page permissions are separate. No CPU/OS universal
refinement or corpus credit. Refusal, timeout and unsupported inputs are not
evidence of a program or compiler defect. Bounds are never increased on failure.
SCOPE
printf 'Displaced DATA native capture and binding controls passed. Evidence: %s\n' "$edsl_out"
if [[ $edsl_native_only == true ]]; then
    printf 'Fresh Lean kernel replay was not run.\n'
else
    printf 'All 80 actual observations passed 20 fresh Lean shards and transitive audits.\n'
fi
