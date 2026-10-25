#!/usr/bin/env bash
# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
# Invoked only inside the driver's bounded transient service and timeout.
set -euo pipefail
export LC_ALL=C
ulimit -c 0
rex_phase=$1 rex_memory=$2
shift 2
rex_cgroup=$(sed -n 's/^0:://p' /proc/self/cgroup)
[[ $rex_cgroup == /* && $rex_cgroup != *..* ]]
rex_controller="/sys/fs/cgroup$rex_cgroup"
{
    cat /proc/self/cgroup
    for rex_name in memory.max memory.swap.max cpu.max pids.max; do
        printf '%s=' "$rex_name"
        cat "$rex_controller/$rex_name"
    done
    printf 'core_limit=%s\n' "$(ulimit -c)"
} > "limits/$rex_phase.txt"
[[ $(cat "$rex_controller/memory.max") == "$rex_memory" ]]
[[ $(cat "$rex_controller/memory.swap.max") == 0 ]]
[[ $(cat "$rex_controller/pids.max") == 64 ]]
read -r rex_quota rex_period < "$rex_controller/cpu.max"
[[ $rex_quota =~ ^[0-9]+$ && $rex_period =~ ^[0-9]+$ ]]
(( rex_quota > 0 && rex_quota <= rex_period ))
exec "$@"
