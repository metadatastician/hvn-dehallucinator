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
# A job that calls a reusable workflow reports one check per called job, as
# `<caller> / <called>` (e.g. `scan / gitleaks`): such a context is accepted
# when <caller> is a calling job here. The called job's name is defined in the
# reusable workflow at its pinned ref, often in another repository, and is not
# verified. A matrix job reports one check per combination with a suffix; its
# contexts are refused, so pin required contexts to non-matrix jobs.
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

# One line per non-matrix job: `exact<TAB><check-run name>` for a job that runs
# steps, `caller<TAB><check-run name>` for a job that calls a reusable workflow.
emitted() {
  local f
  for f in "$WORKFLOWS"/*.yml "$WORKFLOWS"/*.yaml; do
    [ -f "$f" ] || continue
    awk '
      function flush() {
        if (id != "" && !matrix) print (reusable ? "caller" : "exact") "\t" (name != "" ? name : id)
      }
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

jobs="$(emitted)"
exact="$(awk -F"\t" '$1 == "exact" { print $2 }' <<<"$jobs")"
callers="$(awk -F"\t" '$1 == "caller" { print $2 }' <<<"$jobs")"

# reported <context>: does some job here report a check-run with this name?
reported() {
  local ctx="$1" c
  grep -qxF -- "$ctx" <<<"$exact" && return 0
  while IFS= read -r c; do
    [ -n "$c" ] || continue
    case "$ctx" in "$c / "?*) return 0 ;; esac
  done <<<"$callers"
  return 1
}

fails=0; total=0
shopt -s nullglob
for r in "$RULESETS"/*.json; do
  while IFS= read -r ctx; do
    [ -n "$ctx" ] || continue
    total=$((total + 1))
    if reported "$ctx"; then
      echo "  ok    $(basename "$r"): '$ctx'"
    else
      echo "  FAIL  $(basename "$r"): requires '$ctx', which no workflow job here reports"
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
