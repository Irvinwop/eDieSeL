#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
set -euo pipefail
export LC_ALL=C
ulimit -c 0
rex_script=$(realpath -e -- "${BASH_SOURCE[0]}")
rex_source=$(dirname -- "$(dirname -- "$rex_script")")
rex_fixture="$rex_source/fixtures/native/rex-data32"
rex_arguments=("$@")
if [[ $# -gt 1 || ${1:-} == -* ]]; then
    echo 'usage: scripts/verify-rex-data32-native.sh [NEW_OUTPUT_DIRECTORY]' >&2
    exit 2
fi
[[ $(uname -sm) == 'Linux x86_64' && $(getconf PAGESIZE) == 4096 ]] || {
    echo 'REX DATA4 native conformance requires Linux x86-64 with 4096-byte pages' >&2
    exit 2
}
# Resolve a caller-relative path before changing directory. Dangling symlinks
# count as existing paths too. No supplied output directory is ever reused.
rex_out=''
if [[ $# == 1 ]]; then
    rex_out=$(realpath -m -- "$1")
    [[ ! -e $1 && ! -L $1 && ! -e $rex_out && ! -L $rex_out ]] || {
        echo 'A new output directory is required' >&2; exit 2;
    }
    if [[ $rex_out == "$rex_fixture" || $rex_out == "$rex_fixture/"* ||
          $rex_out == "$rex_source/scripts" || $rex_out == "$rex_source/scripts/"* ]]; then
        echo 'Output must be outside the fixture and driver input directories' >&2; exit 2
    fi
fi
rex_storage=$(realpath -e -- "${EDSL_STORAGE_ROOT:-$rex_source}")
[[ -d $rex_storage && ( $rex_source == "$rex_storage" || $rex_source == "$rex_storage/"* ) ]] || {
    echo 'EDSL_STORAGE_ROOT must contain the source checkout' >&2; exit 2;
}
rex_limit=33554432 rex_reserve=200000000 rex_global_limit=5000000000
rex_allocated=$(du -s -B1 -- "$rex_storage" | cut -f1)
if (( rex_allocated + rex_limit + rex_reserve > rex_global_limit )); then
    printf 'Storage reservation refused: allocated=%s output_reservation=%s other_reserve=%s cap=%s bytes\n' \
        "$rex_allocated" "$rex_limit" "$rex_reserve" "$rex_global_limit" >&2
    exit 2
fi
if [[ -n $rex_out ]]; then
    mkdir -p -- "$(dirname -- "$rex_out")"
    mkdir -- "$rex_out"
else
    mkdir -p -- "$rex_source/artifacts/rex-data32"
    rex_out=$(mktemp -d "$rex_source/artifacts/rex-data32/run.XXXXXXXX")
fi
rex_out=$(realpath -e -- "$rex_out")
rex_status='INCOMPLETE' rex_phase='setup'

rex_inventory() {
    find fixtures/native/rex-data32 -type f -print0 || return 1
    printf '%s\0' scripts/verify-rex-data32-native.sh
}
rex_regular_inputs() {
    local special
    special=$(find "$rex_fixture" ! -type d ! -type f -print) || return 1
    [[ -z $special ]]
}
rex_check_inputs() {
    (cd "$rex_source"; sha256sum --strict --quiet --check "$rex_out/INPUTS.sha256") || return 1
    (cd "$rex_source"; rex_inventory | sort -z) > "$rex_out/input-files-postflight.nul" || return 1
    cmp -- "$rex_out/input-files.nul" "$rex_out/input-files-postflight.nul" || return 1
    # Symlinks and special files are never unmanifested fixture inputs.
    rex_regular_inputs
}
rex_capacity() {
    local stage=$1 own aggregate extra=0
    own=$(du -s -B1 -- "$rex_out" | cut -f1) || return 1
    aggregate=$(du -s -B1 -- "$rex_storage" | cut -f1) || return 1
    if [[ $rex_out != "$rex_storage/"* ]]; then extra=$own; fi
    printf 'allocated=%s outside_outputs=%s own_outputs=%s output_limit=%s other_reserve=%s cap=%s bytes\n' \
        "$aggregate" "$extra" "$own" "$rex_limit" "$rex_reserve" "$rex_global_limit" \
        > "$rex_out/capacity-$stage.txt"
    if (( own > rex_limit || aggregate + extra + rex_reserve + rex_limit - own > rex_global_limit )); then
        cat "$rex_out/capacity-$stage.txt" >&2
        echo 'Storage reservation refused; no further compute phases will run' >&2
        return 1
    fi
}
rex_finish() {
    local rc=$? post=0 manifest_status=0
    trap - EXIT
    set +e
    rex_check_inputs > "$rex_out/postflight.log" 2>&1 || post=1
    for rex_manifest in TOOLS PREFLIGHT ELF NATIVE; do
        if [[ -f $rex_out/$rex_manifest.sha256 ]]; then
            (cd "$rex_out"; sha256sum --strict --quiet --check "$rex_manifest.sha256") \
                >> "$rex_out/postflight.log" 2>&1 || post=1
        elif [[ $rex_manifest == TOOLS || $rex_manifest == PREFLIGHT ]]; then
            post=1
        fi
    done
    rex_capacity after >> "$rex_out/postflight.log" 2>&1 || post=1
    printf '%s\n' "$post" > "$rex_out/postflight.exit"
    [[ $post == 0 ]] || rc=1
    if [[ $rc != 0 || $rex_status != PASS ]]; then
        [[ $rc != 0 ]] || rc=1
        rex_status=INCOMPLETE
    fi
    {
        printf '%s: native conformance and binding ONLY; last phase=%s.\n' "$rex_status" "$rex_phase"
        cat <<'SCOPE'
No fresh Lean kernel replay, CPU/OS refinement or corpus credit is claimed.
Finite owned synthetic Linux x86-64 observations; all 16 measured GPRs, full
measured flags and all bytes of three 4 KiB pages are checked by a separate
four-byte memcpy oracle. Page permissions and surrounding guards are checked
against /proc/self/maps. RIP is not sampled: successor means the authenticated
end label. JSON relocation and intended DATA4 read metadata are data only.
Native fault controls retain actual before pages and null measured afterstate.
Launch/tool/cgroup records describe provenance, not a machine-code proof.
Refusal, timeout and unsupported input do not establish a program defect.
SCOPE
    } > "$rex_out/scope.txt"
    printf '%s\n' "$rc" > "$rex_out/exit"
    if [[ $rex_status != PASS || ! -s $rex_out/REPORT.json ]]; then
        printf '{"schema":"rex-data32-native-run-v1","status":"INCOMPLETE","phase":"%s","exit":%s,"scope":"native and binding ONLY; no fresh Lean kernel replay, CPU/OS refinement or corpus credit"}\n' \
            "$rex_phase" "$rc" > "$rex_out/REPORT.json"
    fi
    # Seal every retained regular output, including report, failures, manifests,
    # terminal status and logs. The outer manifest cannot include itself.
    (
        cd "$rex_out" || exit 1
        # OUTPUTS.sha256 is deliberately excluded from its own manifest.
        # shellcheck disable=SC2094
        find . -type f ! -name OUTPUTS.sha256 -print0 | sort -z | xargs -0 -r sha256sum -- \
            > OUTPUTS.sha256 || exit 1
        sha256sum --strict --quiet --check OUTPUTS.sha256
    ) || manifest_status=1
    if [[ $manifest_status != 0 ]]; then
        rc=1
        printf '1\n' > "$rex_out/exit"
        printf 'INCOMPLETE: output manifest failed; native and binding ONLY. No fresh Lean kernel replay, CPU/OS refinement or corpus credit.\n' > "$rex_out/scope.txt"
    fi
    printf 'REX DATA4 native harness exit=%s postflight=%s output=%s\n' "$rc" "$post" "$rex_out"
    exit "$rc"
}
trap rex_finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
printf 'INCOMPLETE: native and binding ONLY; no fresh Lean kernel replay, CPU/OS refinement or corpus credit.\n' > "$rex_out/scope.txt"
printf '1\n' > "$rex_out/exit"
mkdir -- "$rex_out/failures" "$rex_out/limits" "$rex_out/tmp"
export TMPDIR="$rex_out/tmp"
rex_tag="rex-data32-$(date -u +%s)-$$"
rex_systemd=(systemd-run)
if [[ $EUID != 0 ]]; then rex_systemd=(sudo -n systemd-run); fi
rex_user=$(id -un)
rex_bounded() {
    local phase=$1 memory=$2 seconds=$3 runtime
    shift 3
    rex_phase=$phase
    (( memory <= 3221225472 && seconds <= 120 ))
    runtime=$((seconds + 5)); if [[ $seconds == 120 ]]; then runtime=130; fi
    local command=("${rex_systemd[@]}" --quiet --wait --pipe --collect
        --unit="edsl-$rex_tag-$phase" --working-directory="$rex_out"
        "--setenv=TMPDIR=$TMPDIR" --setenv=LC_ALL=C "--setenv=PATH=$PATH"
        -p "User=$rex_user" -p "MemoryMax=$memory" -p MemorySwapMax=0
        -p CPUQuota=100% -p TasksMax=64 -p "RuntimeMaxSec=$runtime" -p TimeoutStopSec=5s
        -p LimitCORE=0 -p ProtectSystem=strict -p "ReadWritePaths=\"$rex_out\""
        -- timeout --signal=TERM --kill-after=5s "${seconds}s"
        /bin/bash "$rex_fixture/phase.sh" "$phase" "$memory" "$@")
    printf '%q ' "${command[@]}" >> "$rex_out/commands.txt"
    printf '\n' >> "$rex_out/commands.txt"
    "${command[@]}"
}
{
    printf 'cd %q\n' "$PWD"
    printf '%q ' "$rex_script" "${rex_arguments[@]}"
    printf '\nEDSL_STORAGE_ROOT=%q\n' "$rex_storage"
} > "$rex_out/runner.txt"
cd "$rex_source"
rex_regular_inputs
rex_inventory | sort -z > "$rex_out/input-files.nul"
xargs -0 -r sha256sum -- < "$rex_out/input-files.nul" > "$rex_out/INPUTS.sha256"
rex_compiler=$(command -v -- "${EDSL_CC:-${CC:-gcc}}")
rex_compiler=$(realpath -e -- "$rex_compiler")
rex_tools=("$rex_compiler" bash node objcopy objdump readelf nm ld as ldd sha256sum timeout
    du realpath find sort xargs cmp sed cat cut date id uname getconf mkdir mktemp systemd-run)
[[ $EUID == 0 ]] || rex_tools+=(sudo)
for rex_tool in "${rex_tools[@]}"; do
    realpath -e -- "$(command -v -- "$rex_tool")"
done | sort -u > "$rex_out/tool-paths.txt"
while IFS= read -r rex_tool; do sha256sum -- "$rex_tool"; done \
    < "$rex_out/tool-paths.txt" > "$rex_out/TOOLS.sha256"
# The bounded child expands its own positional arguments.
# shellcheck disable=SC2016
rex_bounded versions 134217728 15 /bin/bash -c '
    set -euo pipefail
    for tool in "$@"; do printf "tool=%s\n" "$tool"; "$tool" --version; done
' bash "$rex_compiler" bash node objcopy objdump readelf nm ld as ldd sha256sum timeout \
    du realpath find sort xargs cmp sed systemd-run > "$rex_out/tool-versions.txt" 2> "$rex_out/versions.log"
uname -srmo > "$rex_out/platform.txt"
getconf PAGESIZE > "$rex_out/page-size.txt"
cat /proc/self/cgroup > "$rex_out/launcher-cgroup.txt"
rex_capacity before
(cd "$rex_out"; sha256sum INPUTS.sha256 input-files.nul TOOLS.sha256 tool-paths.txt \
    tool-versions.txt platform.txt page-size.txt launcher-cgroup.txt runner.txt capacity-before.txt \
    > PREFLIGHT.sha256)
rex_check_inputs > "$rex_out/preflight.log" 2>&1
(cd "$rex_out"; sha256sum --strict --quiet --check TOOLS.sha256; sha256sum --strict --quiet --check PREFLIGHT.sha256)
rex_bounded compile 536870912 30 "$rex_compiler" -std=gnu2x -O2 -g0 -Wall -Wextra -Werror \
    -fno-pie -no-pie -fno-lto '-Wl,--build-id=none,-z,noexecstack' \
    "$rex_fixture/auth.c" "$rex_fixture/oracle.c" "$rex_fixture/native.c" "$rex_fixture/parser.c" \
    "$rex_fixture/auth-controls.c" "$rex_fixture/main.c" "$rex_fixture/probe.S" \
    -lcrypto -o "$rex_out/probe.elf" > "$rex_out/compiler.log" 2>&1
(cd "$rex_out"; sha256sum probe.elf > ELF.sha256)
rex_bounded extraction 134217728 15 /bin/bash -c '
    set -euo pipefail
    objcopy --dump-section .rex32_native=linked-section.bin probe.elf extraction-copy.elf
    rm -- extraction-copy.elf
    readelf -h -l -S -s -n -d probe.elf > linked-elf.txt
    objdump -d -j .rex32_native probe.elf > linked-disassembly.txt
    nm -S --defined-only probe.elf > linked-symbols.txt
    ldd ./probe.elf > linked-libraries.txt
' > "$rex_out/extraction.log" 2>&1
(cd "$rex_out"; sha256sum --strict --quiet --check ELF.sha256)
rex_check_inputs >> "$rex_out/preflight.log" 2>&1
rex_probe=("$rex_out/probe.elf")
rex_binding=("$rex_out/probe.elf" "$rex_out/linked-section.bin" "$rex_out/PROBES.json")
rex_bounded describe 134217728 15 "${rex_probe[@]}" describe "${rex_binding[@]:0:2}" \
    > "$rex_out/PROBES.json" 2> "$rex_out/describe.log"
rex_bounded capture 536870912 15 "${rex_probe[@]}" capture "${rex_binding[@]}" "$rex_out/captures.bin" \
    > "$rex_out/capture.log" 2> "$rex_out/capture.err"
(cd "$rex_out"; sha256sum captures.bin > CAPTURE.sha256)
read -r rex_hash _ < "$rex_out/CAPTURE.sha256"
rex_bounded verify 536870912 15 "${rex_probe[@]}" verify "${rex_binding[@]}" "$rex_out/captures.bin" "$rex_hash" \
    > "$rex_out/verify.log" 2> "$rex_out/verify.err"
(cd "$rex_out"; sha256sum probe.elf linked-section.bin PROBES.json captures.bin CAPTURE.sha256 BINDING.json > NATIVE.sha256)
rex_bounded native-controls 536870912 15 "${rex_probe[@]}" native-controls "${rex_binding[@]}" \
    > "$rex_out/native-controls.log" 2> "$rex_out/native-controls.err"
rex_bounded parser-controls 536870912 15 "${rex_probe[@]}" parser-controls "${rex_binding[@]}" "$rex_out/captures.bin" \
    > "$rex_out/parser-controls.log" 2> "$rex_out/parser-controls.err"
rex_bounded auth-controls 536870912 15 "${rex_probe[@]}" auth-controls "${rex_binding[@]}" "$rex_out/captures.bin" "$rex_hash" \
    > "$rex_out/auth-controls.log" 2> "$rex_out/auth-controls.err"
rex_bounded dump 536870912 15 "${rex_probe[@]}" dump "${rex_binding[@]}" "$rex_out/captures.bin" "$rex_hash" \
    > "$rex_out/data.log" 2> "$rex_out/data.err"
rex_bounded verify-after 536870912 15 "${rex_probe[@]}" verify "${rex_binding[@]}" "$rex_out/captures.bin" "$rex_hash" \
    > "$rex_out/verify-after.log" 2> "$rex_out/verify-after.err"
rex_bounded report 134217728 15 node "$rex_fixture/report.cjs" > "$rex_out/REPORT.json" 2> "$rex_out/report.log"
rex_status=PASS
