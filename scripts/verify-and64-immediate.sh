#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
edsl_script=$(realpath -e -- "${BASH_SOURCE[0]}")
edsl_source=$(dirname -- "$(dirname -- "$edsl_script")")
cd "$edsl_source"
edsl_native_only=false
if [[ ${1:-} == --native-only ]]; then edsl_native_only=true; shift; fi
if [[ $# -gt 1 ]]; then
    echo 'usage: scripts/verify-and64-immediate.sh [--native-only] [NEW_OUTPUT_DIRECTORY]' >&2
    exit 2
fi
[[ $(uname -sm) == 'Linux x86_64' ]] || {
    echo 'AND64 native conformance requires Linux x86-64' >&2
    exit 2
}
if [[ $# == 1 ]]; then
    edsl_out=$(realpath -m -- "$1")
    [[ ! -e "$edsl_out" ]]
    mkdir -p -- "$(dirname -- "$edsl_out")"
    mkdir -- "$edsl_out"
else
    mkdir -p artifacts/and64-immediate
    edsl_out=$(mktemp -d "$edsl_source/artifacts/and64-immediate/run.XXXXXXXX")
fi
edsl_fixture="$edsl_source/fixtures/native/and64-immediate"
edsl_tag="and64-$(date -u +%s)-$$"
edsl_systemd=(systemd-run)
if [[ $EUID != 0 ]]; then edsl_systemd=(sudo -n systemd-run); fi
edsl_user=$(id -un)
edsl_environment=()
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
edsl_inputs=("$edsl_fixture/check.c" "$edsl_fixture/probe.S" "$edsl_fixture/cases.h"
    "$edsl_fixture/cases.json" "$edsl_script" scripts/prepare-and64-replay.cjs
    tests/and64-replay.cjs lean-toolchain lakefile.lean tests/And64NativeBase.lean
    EDSL/X86/Sequential/Model.lean EDSL/X86/Sequential/Decode.lean
    EDSL/X86/Sequential/Machine.lean EDSL/X86/Sequential/Flags.lean)
sha256sum -- "${edsl_inputs[@]}" > "$edsl_out/INPUTS.sha256"
trap 'edsl_rc=$?; trap - EXIT; set +e; sha256sum --strict --quiet --check "$edsl_out/INPUTS.sha256" > "$edsl_out/postflight.log" 2>&1; edsl_post=$?; [[ $edsl_post == 0 ]] || edsl_rc=1; printf "%s\n" "$edsl_rc" > "$edsl_out/exit"; exit "$edsl_rc"' EXIT
edsl_compiler=${EDSL_CC:-gcc}
"$edsl_compiler" --version > "$edsl_out/compiler.txt"
uname -srmo > "$edsl_out/platform.txt"
edsl_bounded compile 536870912 30 "$edsl_compiler" -std=gnu2x -O2 -Wall -Wextra -Werror \
    -fno-lto -no-pie '-Wl,--build-id=none,-z,noexecstack' \
    "$edsl_fixture/check.c" "$edsl_fixture/probe.S" -o "$edsl_out/probe.elf" \
    > "$edsl_out/compiler.log" 2>&1
sha256sum "$edsl_out/probe.elf" > "$edsl_out/ELF.sha256"
objcopy --dump-section ".edsl_logical64=$edsl_out/instructions.bin" \
    "$edsl_out/probe.elf" "$edsl_out/extraction-copy.elf"
rm -- "$edsl_out/extraction-copy.elf"
nm -n --defined-only "$edsl_out/probe.elf" > "$edsl_out/symbols.txt"
objdump -d -j .edsl_logical64 "$edsl_out/probe.elf" > "$edsl_out/disassembly.txt"
# Independently altered extraction must be refused before executing the probes.
cp -- "$edsl_out/instructions.bin" "$edsl_out/altered.bin"
printf '\x00' | dd of="$edsl_out/altered.bin" bs=1 count=1 conv=notrunc status=none
edsl_status=0
edsl_bounded tamper 134217728 30 "$edsl_out/probe.elf" "$edsl_out/altered.bin" \
    > "$edsl_out/tamper.stdout" 2> "$edsl_out/tamper.stderr" || edsl_status=$?
[[ $edsl_status == 2 ]]
rg -q '^linked extraction mismatch$' "$edsl_out/tamper.stderr"
edsl_bounded native 536870912 30 "$edsl_out/probe.elf" "$edsl_out/instructions.bin" \
    > "$edsl_out/measured.jsonl" 2> "$edsl_out/result.log"
sha256sum --strict --quiet --check "$edsl_out/ELF.sha256"
node scripts/prepare-and64-replay.cjs "$edsl_out" > "$edsl_out/preparation.json"
node tests/and64-replay.cjs "$edsl_out" > "$edsl_out/binding-controls.log"
sha256sum "$edsl_out/probe.elf" "$edsl_out/instructions.bin" "$edsl_out/symbols.txt" \
    "$edsl_out/measured.jsonl" "$edsl_out/result.log" "$edsl_out/REPLAY.json" \
    "$edsl_out"/replay/FreshAnd64_*.lean > "$edsl_out/NATIVE.sha256"
if [[ $edsl_native_only == false ]]; then
    export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
    # Dependency construction is distinct from the bounded fresh replay units.
    (
        exec 9>>/tmp/edsl-lean-build.lock
        flock 9
        awk '/^MemAvailable:/ { found=1; exit !($2>=1572864) }
            END { if (!found) exit 1 }' /proc/meminfo
        if pgrep -a -x 'lean|leanchecker|lake'; then exit 1; fi
        lake build And64Tests
    ) > "$edsl_out/build.log" 2>&1
    edsl_lean=$(lake env which lean)
    edsl_sysroot=$("$edsl_lean" --print-prefix)
    edsl_lean_path=$(lake env printenv LEAN_PATH)
    edsl_environment=(--setenv=LEAN_NUM_THREADS=1 "--setenv=LEAN_SYSROOT=$edsl_sysroot"
        "--setenv=LEAN_PATH=$edsl_lean_path")
    for edsl_replay in "$edsl_out"/replay/FreshAnd64_*.lean; do
        edsl_name=$(basename -- "$edsl_replay" .lean)
        (
            exec 9>>/tmp/edsl-lean-build.lock
            flock 9
            awk '/^MemAvailable:/ { found=1; exit !($2>=1572864) }
                END { if (!found) exit 1 }' /proc/meminfo
            if pgrep -a -x 'lean|leanchecker|lake'; then exit 1; fi
            edsl_bounded "$edsl_name" 3221225472 120 "$edsl_lean" -j1 \
                -DwarningAsError=true -DautoImplicit=false -DmaxHeartbeats=300000 \
                -DmaxRecDepth=128 "$edsl_replay"
        ) > "$edsl_out/$edsl_name.log" 2>&1
        printf '%s\n' "$edsl_name" >> "$edsl_out/kernel-passed.txt"
    done
    [[ $(wc -l < "$edsl_out/kernel-passed.txt") == 25 ]]
    sha256sum "$edsl_out"/replay/FreshAnd64_*.lean > "$edsl_out/REPLAY.sha256"
    sha256sum --strict --quiet --check "$edsl_out/NATIVE.sha256"
    printf '100 fresh CPU observations passed the kernel replay and dependency audit.\n' > "$edsl_out/scope.txt"
else
    printf 'Native and binding checks only; fresh kernel replay was not run.\n' > "$edsl_out/scope.txt"
fi
sha256sum --strict --quiet --check "$edsl_out/NATIVE.sha256"
