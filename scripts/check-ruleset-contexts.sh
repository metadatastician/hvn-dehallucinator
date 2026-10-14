#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# check-ruleset-contexts.sh [ruleset-dir [workflow-dir]]
#
# Every status check a ruleset under .github/rulesets/ requires must be the
# exact check-run name of a job some workflow under .github/workflows/ emits.
# A required check that never reports stays pending forever and deadlocks the
# branch: that is how `estate-audit` blocked this repository from August to
# October 2026.
#
# A job's check-run name is its `name:` if it has one, otherwise its job id.
# A matrix job reports one check per combination with a suffix, and a
# reusable-workflow call reports as `caller / called`; neither can satisfy an
# exact context here, so pin required contexts to plain jobs.
#
# Exit: 0 = every required context is emitted; 1 = at least one is not;
#       2 = misuse (missing directory or jq).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RULESETS="${1:-$here/.github/rulesets}"
WORKFLOWS="${2:-$here/.github/workflows}"
command -v jq >/dev/null 2>&1 || { echo "check-ruleset-contexts: jq is required" >&2; exit 2; }
[ -d "$RULESETS" ] || { echo "check-ruleset-contexts: no such directory: $RULESETS" >&2; exit 2; }
[ -d "$WORKFLOWS" ] || { echo "check-ruleset-contexts: no such directory: $WORKFLOWS" >&2; exit 2; }

# Check-run names of plain (non-matrix, non-reusable) jobs, one per line.
emitted() {
  local f
  for f in "$WORKFLOWS"/*.yml "$WORKFLOWS"/*.yaml; do
    [ -f "$f" ] || continue
    awk '
      function flush() { if (id != "" && !matrix && !reusable) print (name != "" ? name : id) }
      /^jobs:[[:space:]]*$/              { injobs = 1; next }
      injobs && /^[^[:space:]#]/         { flush(); injobs = 0; id = "" }
      injobs && match($0, /^  [A-Za-z0-9_-]+:[[:space:]]*$/) {
        flush(); id = $0; sub(/^  /, "", id); sub(/:[[:space:]]*$/, "", id)
        name = ""; matrix = 0; reusable = 0; next
      }
      injobs && id != "" && /^    name:/ {
        name = $0; sub(/^    name:[[:space:]]*/, "", name); gsub(/^["'\'']|["'\'']$/, "", name)
      }
      injobs && id != "" && /^    strategy:/ { matrix = 1 }
      injobs && id != "" && /^    uses:/     { reusable = 1 }
      END { if (injobs) flush() }
    ' "$f"
  done | sort -u
}

names="$(emitted)"
fails=0; total=0
shopt -s nullglob
for r in "$RULESETS"/*.json; do
  while IFS= read -r ctx; do
    [ -n "$ctx" ] || continue
    total=$((total + 1))
    if grep -qxF -- "$ctx" <<<"$names"; then
      echo "  ok    $(basename "$r"): '$ctx'"
    else
      echo "  FAIL  $(basename "$r"): requires '$ctx', which no plain workflow job emits"
      fails=$((fails + 1))
    fi
  done < <(jq -r '.rules[]? | select(.type == "required_status_checks")
                  | .parameters.required_status_checks[]?.context' "$r")
done

if [ "$fails" -gt 0 ]; then
  echo "RESULT: FAIL ($fails of $total required context(s) never reported)"
  exit 1
fi
echo "RESULT: PASS -- all $total required context(s) are emitted by a workflow job"
