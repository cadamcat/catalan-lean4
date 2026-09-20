#!/usr/bin/env bash
set -Eeuo pipefail
cd /srv/catalan-proof
export PATH=/opt/lean-4.33.1/bin:/opt/catalan-checkers:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
stamp() { date -u +%FT%TZ; }
run_check() {
  local name="$1"
  shift
  local result=0
  stamp > "/srv/catalan-audit/results/$name.started"
  "$@" > "/srv/catalan-audit/results/$name.log" 2>&1 || result=$?
  printf '%s\n' "$result" > "/srv/catalan-audit/results/$name.exit"
  stamp > "/srv/catalan-audit/results/$name.ended"
  printf '%s exit=%s\n' "$name" "$result"
  return "$result"
}
run_check preflight python3 /srv/catalan-audit/tools/audit.py preflight /srv/catalan-audit/audit/targets.json --out /srv/catalan-audit/results/preflight
run_check verify bash scripts/verify.sh
run_check official-audit python3 /srv/catalan-audit/tools/audit.py run /srv/catalan-audit/audit/targets.json --out /srv/catalan-audit/results/official-audit --lake /opt/lean-4.33.1/bin/lake --timeout 1800
run_check replay bash scripts/replay.sh
printf '%s\n' 'SUPPLEMENTAL_CHECKS_PASSED'
