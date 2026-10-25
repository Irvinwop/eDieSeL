#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
edsl_script=$(realpath -e -- "${BASH_SOURCE[0]}")
edsl_source=$(dirname -- "$(dirname -- "$edsl_script")")
cd "$edsl_source"
edsl_native_only=false
if [[ ${1:-} == --native-only ]]; then
    edsl_native_only=true
    shift
fi
if [[ $# -gt 1 ]]; then
    echo 'usage: scripts/verify-sequential-sub64.sh [--native-only] [NEW_OUTPUT_DIRECTORY]' >&2
    exit 2
fi
[[ $(uname -sm) == 'Linux x86_64' ]] || {
    echo 'SUB64 native conformance requires Linux x86-64' >&2
    exit 2
}
edsl_tag="sub64-$(date -u +%s)-$$"
if [[ $# == 1 ]]; then
    edsl_out=$(realpath -m -- "$1")
    [[ ! -e "$edsl_out" ]]
    mkdir -p -- "$(dirname -- "$edsl_out")"
    mkdir -- "$edsl_out"
else
    mkdir -p artifacts/sequential-sub64
    edsl_out=$(mktemp -d "$edsl_source/artifacts/sequential-sub64/run.XXXXXXXX")
fi
trap 'edsl_rc=$?; printf "%s\n" "$edsl_rc" > "$edsl_out/exit"' EXIT

# Fail if the host cannot enforce the requested cgroup bounds. GitHub-hosted
# Ubuntu runners use passwordless sudo; processes still run as the caller.
edsl_systemd=(systemd-run)
if [[ $EUID != 0 ]]; then
    edsl_systemd=(sudo -n systemd-run)
fi
edsl_user=$(id -un)
edsl_environment=()
edsl_bounded() {
    local phase=$1 memory=$2 tasks=$3 seconds=$4 runtime
    shift 4
    runtime=$((seconds + 5))
    if [[ "$seconds" == 120 ]]; then runtime=130; fi
    local command=("${edsl_systemd[@]}" --quiet --wait --pipe --collect
        --unit="edsl-$edsl_tag-$phase" --working-directory="$edsl_source"
        "${edsl_environment[@]}"
        -p "User=$edsl_user" -p "MemoryMax=$memory" -p MemorySwapMax=0
        -p CPUQuota=100% -p "TasksMax=$tasks" -p "RuntimeMaxSec=$runtime"
        -p TimeoutStopSec=5s -- /usr/bin/time -v
        timeout --signal=TERM --kill-after=5s "${seconds}s" "$@")
    printf '%q ' "${command[@]}" >> "$edsl_out/commands.txt"
    printf '\n' >> "$edsl_out/commands.txt"
    "${command[@]}"
}

edsl_inputs=(fixtures/sequential-sub64-check.c fixtures/sequential-sub64-probe.S
    scripts/verify-sequential-sub64.sh scripts/audit-sequential-sub64.cjs
    scripts/prepare-sequential-sub64-replay.cjs scripts/check-sequential-sub64-replay.cjs
    tests/check-sequential-sub64-replay.cjs lean-toolchain lakefile.lean
    EDSL/X86/Sequential/Model.lean EDSL/X86/Sequential/Decode.lean
    EDSL/X86/Sequential/Machine.lean EDSL/X86/Sequential/MachineChoices.lean
    EDSL/X86/Sequential/Flags.lean EDSL/Audit.lean)
sha256sum -- "${edsl_inputs[@]}" > "$edsl_out/SOURCES.before.sha256"
edsl_compiler=${EDSL_CLANG:-clang-18}
"$edsl_compiler" --version > "$edsl_out/compiler.txt"
uname -srmo > "$edsl_out/platform.txt"
lscpu > "$edsl_out/cpu.txt"
objcopy --version > "$edsl_out/objcopy.txt"
edsl_args=(-std=gnu23 -O2 -Wall -Wextra -Werror -fcf-protection=none -fno-lto -no-pie
    '-Wl,--build-id=none,-z,noexecstack' "$edsl_source/fixtures/sequential-sub64-check.c"
    "$edsl_source/fixtures/sequential-sub64-probe.S" -o "$edsl_out/native-check.elf")
printf '%q ' "$edsl_compiler" "${edsl_args[@]}" > "$edsl_out/arguments.txt"
printf '\n' >> "$edsl_out/arguments.txt"
edsl_bounded compiler 536870912 32 30 "$edsl_compiler" "${edsl_args[@]}" \
    > "$edsl_out/compiler.log" 2>&1
sha256sum "$edsl_out/native-check.elf" > "$edsl_out/ELF.before.sha256"
objcopy --dump-section ".edsl_sub64=$edsl_out/instructions.bin" \
    "$edsl_out/native-check.elf" "$edsl_out/objcopy-copy.elf"
sha256sum --strict --quiet --check "$edsl_out/ELF.before.sha256"
objdump -d -j .edsl_sub64 -j .text "$edsl_out/native-check.elf" > "$edsl_out/disassembly.txt"
readelf -h -l -S -s -r -W "$edsl_out/native-check.elf" > "$edsl_out/elf.txt"
nm -n --defined-only "$edsl_out/native-check.elf" > "$edsl_out/symbols.txt"

cp -- "$edsl_out/instructions.bin" "$edsl_out/altered.bin"
printf '\x00' | dd of="$edsl_out/altered.bin" bs=1 count=1 conv=notrunc status=none
edsl_status=0
edsl_bounded tamper 134217728 16 30 \
    "$edsl_out/native-check.elf" "$edsl_out/altered.bin" "$edsl_out/altered.jsonl" \
    > "$edsl_out/altered.lean" 2> "$edsl_out/altered-results.txt" || edsl_status=$?
printf '%s\n' "$edsl_status" > "$edsl_out/altered.exit"
[[ "$edsl_status" == 2 && ! -s "$edsl_out/altered.lean" && ! -e "$edsl_out/altered.jsonl" ]]
# The timeout/time diagnostics follow the program's own pre-probe rejection.
[[ $(head -n 1 "$edsl_out/altered-results.txt") == \
    'Final ELF section extraction differs from executed bytes (probes=0; observations=0)' ]]
edsl_bounded native 134217728 16 30 \
    "$edsl_out/native-check.elf" "$edsl_out/instructions.bin" "$edsl_out/observations.jsonl" \
    > "$edsl_out/NativeSequentialSub64.lean" 2> "$edsl_out/native-results.txt"
sha256sum --strict --quiet --check "$edsl_out/ELF.before.sha256"
node scripts/audit-sequential-sub64.cjs "$edsl_out"
node scripts/prepare-sequential-sub64-replay.cjs \
    "$edsl_out/NativeSequentialSub64.lean" "$edsl_out/replay"
node scripts/check-sequential-sub64-replay.cjs --snapshots "$edsl_out" \
    > "$edsl_out/snapshot-binding.json"
if [[ "$edsl_native_only" == false ]]; then
    export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
    flock /tmp/edsl-lean-build.lock lake build EDSL.X86.Sequential.MachineChoices EDSL.Audit \
        > "$edsl_out/build.log" 2>&1
    edsl_lean=$(lake env which lean)
    edsl_sysroot=$("$edsl_lean" --print-prefix)
    edsl_lean_path=$(lake env printenv LEAN_PATH)
    edsl_environment=(--setenv=LEAN_NUM_THREADS=1 "--setenv=LEAN_SYSROOT=$edsl_sysroot"
        "--setenv=LEAN_PATH=$edsl_lean_path")
    for edsl_replay in "$edsl_out"/replay/NativeSub64_*.lean; do
        edsl_name=$(basename "$edsl_replay" .lean)
        (
            exec 9>>/tmp/edsl-lean-build.lock
            flock 9
            awk '/^MemAvailable:/ { found=1; exit !($2>=1572864) }
                END { if (!found) exit 1 }' /proc/meminfo
            if pgrep -a -x 'lean|leanchecker|lake'; then
                echo 'Another Lean process is outside the shared serialization lock' >&2
                exit 1
            fi
            edsl_bounded "$edsl_name" 3221225472 64 120 \
                "$edsl_lean" -j1 -DwarningAsError=true -DautoImplicit=false \
                -DmaxHeartbeats=300000 -DmaxRecDepth=128 "$edsl_replay"
        ) > "$edsl_out/$edsl_name.log" 2>&1
        printf '%s\n' "$edsl_name" >> "$edsl_out/kernel-passed.txt"
    done
    [[ $(wc -l < "$edsl_out/kernel-passed.txt") == 8 ]]
    node scripts/check-sequential-sub64-replay.cjs --kernel "$edsl_out" \
        > "$edsl_out/kernel-evidence.json"
    node tests/check-sequential-sub64-replay.cjs "$edsl_out" "$edsl_out" \
        > "$edsl_out/binding-controls.json"
else
    printf 'Native-only mode: kernel replay was not run.\n' > "$edsl_out/scope.txt"
fi
sha256sum --strict --quiet --check "$edsl_out/SOURCES.before.sha256"
sha256sum -- "${edsl_inputs[@]}" "$edsl_out/native-check.elf" "$edsl_out/instructions.bin" \
    "$edsl_out/observations.jsonl" "$edsl_out/NativeSequentialSub64.lean" \
    "$edsl_out/axis-audit.json" "$edsl_out/replay/REPLAY.json" \
    "$edsl_out/snapshot-binding.json" "$edsl_out/replay/"*.lean > "$edsl_out/SHA256SUMS"
if [[ "$edsl_native_only" == false ]]; then
    sha256sum -- "$edsl_out/"NativeSub64_*.log "$edsl_out/kernel-evidence.json" \
        "$edsl_out/binding-controls.json" >> "$edsl_out/SHA256SUMS"
    printf '680\n' > "$edsl_out/kernel-proved.txt"
fi
cat "$edsl_out/native-results.txt"
printf 'SUB64 native contracts and extraction controls passed. Evidence: %s\n' "$edsl_out"
if [[ "$edsl_native_only" == false ]]; then
    printf 'All 680 actual CPU observations passed kernel replay and axiom audits.\n'
fi
