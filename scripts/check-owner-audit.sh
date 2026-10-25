#!/usr/bin/env bash
set -euo pipefail

# Imported private declarations must not escape the defining-module audit.
edsl_audit_dir=$(mktemp -d /tmp/edsl-owner-audit.XXXXXX)
trap 'rm -rf -- "$edsl_audit_dir"' EXIT
mkdir -p "$edsl_audit_dir/EDSL"
cat > "$edsl_audit_dir/ExternalAuditDependency.lean" <<'LEAN'
axiom ExternalAuditDependency.untrusted : False
LEAN
cat > "$edsl_audit_dir/EDSL/OwnerAuditNegative.lean" <<'LEAN'
import ExternalAuditDependency
namespace EDSL.OwnerAuditNegative
private theorem hiddenDependency : False := ExternalAuditDependency.untrusted
end EDSL.OwnerAuditNegative
LEAN
cat > "$edsl_audit_dir/Check.lean" <<'LEAN'
import EDSL.Audit.Owners
import EDSL.OwnerAuditNegative
#audit_edsl_owners
LEAN

lake env bash -s -- "$edsl_audit_dir" <<'CHECK'
set -euo pipefail
edsl_audit_dir=$1
# Lean chooses a namespace root as a unit. Put the real checked audit object
# beside the negative project module so the temporary EDSL root is complete.
mkdir -p "$edsl_audit_dir/EDSL/Audit"
for edsl_owner_object in .lake/build/lib/lean/EDSL/Audit/Owners.olean*; do
  test -f "$edsl_owner_object"
  cp -- "$edsl_owner_object" "$edsl_audit_dir/EDSL/Audit/"
done
export LEAN_PATH="$edsl_audit_dir:$LEAN_PATH"
edsl_args=(-j1 -DwarningAsError=true -DautoImplicit=false
  -DmaxHeartbeats=300000 -DmaxRecDepth=128 -DElab.async=false
  "--root=$edsl_audit_dir")
timeout --signal=TERM --kill-after=5s 120s lean "${edsl_args[@]}" \
  -o "$edsl_audit_dir/ExternalAuditDependency.olean" "$edsl_audit_dir/ExternalAuditDependency.lean"
timeout --signal=TERM --kill-after=5s 120s lean "${edsl_args[@]}" \
  -o "$edsl_audit_dir/EDSL/OwnerAuditNegative.olean" "$edsl_audit_dir/EDSL/OwnerAuditNegative.lean"
if timeout --signal=TERM --kill-after=5s 120s lean "${edsl_args[@]}" \
    "$edsl_audit_dir/Check.lean" > "$edsl_audit_dir/negative.log" 2>&1; then
  echo 'Defining-module audit accepted an imported private untrusted dependency'
  exit 1
fi
edsl_negative_message=$(< "$edsl_audit_dir/negative.log")
if [[ $edsl_negative_message != *'depends on unapproved axiom ExternalAuditDependency.untrusted'* ]]; then
  cat "$edsl_audit_dir/negative.log"
  echo 'Defining-module audit failed for an unexpected reason'
  exit 1
fi
echo 'Defining-module audit rejected an imported private untrusted dependency'
CHECK
