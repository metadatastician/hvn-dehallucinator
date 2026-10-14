#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# Controls for scripts/check-ruleset-contexts.sh. Each way a required context
# can name a check that never reports must be refused; the positive controls
# are a well-formed fixture and the repository's own rulesets and workflows.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CHECK="$REPO_ROOT/scripts/check-ruleset-contexts.sh"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

mkdir -p "$WORK/wf"
cat > "$WORK/wf/ci.yml" <<'EOF'
name: CI
on: pull_request
jobs:
  plain-job:
    runs-on: ubuntu-24.04
    steps:
      - run: true
  renamed-job:
    name: Pretty Name
    runs-on: ubuntu-24.04
    steps:
      - run: true
  matrix-job:
    runs-on: ubuntu-24.04
    strategy:
      matrix:
        os: [a, b]
    steps:
      - run: true
  reusable-job:
    uses: org/repo/.github/workflows/x.yml@0123456789abcdef0123456789abcdef01234567
  reusable-named:
    name: Scan Name
    uses: org/repo/.github/workflows/x.yml@0123456789abcdef0123456789abcdef01234567
EOF

ruleset() { # ruleset <dir> <context>...
  mkdir -p "$WORK/$1"; local checks="" c
  for c in "${@:2}"; do checks="$checks{\"context\":\"$c\"},"; done
  printf '{"rules":[{"type":"required_status_checks","parameters":{"required_status_checks":[%s]}}]}\n' \
    "${checks%,}" > "$WORK/$1/r.json"
  printf '%s' "$WORK/$1"
}

pass=0; fail=0
expect() { # expect <name> <want-exit> <ruleset-dir> [workflow-dir]
  local out rc
  out="$(bash "$CHECK" "$3" "${4:-$WORK/wf}" 2>&1)"; rc=$?
  if [ "$rc" = "$2" ]; then printf '  PASS  %s (exit %s)\n' "$1" "$rc"; pass=$((pass+1))
  else printf '  FAIL  %s: want exit %s, got %s\n%s\n' "$1" "$2" "$rc" "$out"; fail=$((fail+1)); fi
}

echo "== positive controls =="
expect "plain job id and a job's name: are emitted" 0 "$(ruleset ok plain-job 'Pretty Name')"
expect "a reusable call reports caller / called (scan / gitleaks)" 0 "$(ruleset reusable-ok 'reusable-job / gitleaks')"
expect "a named reusable call reports under its name:" 0 "$(ruleset reusable-named-ok 'Scan Name / gitleaks')"
expect "this repository's rulesets and workflows" 0 "$REPO_ROOT/.github/rulesets" "$REPO_ROOT/.github/workflows"

echo "== negative controls (each must be refused) =="
expect "a context no job emits (estate-audit, the August deadlock)" 1 "$(ruleset missing estate-audit)"
expect "the job id of a job that sets name:" 1 "$(ruleset renamed renamed-job)"
expect "a matrix job's bare id" 1 "$(ruleset matrix matrix-job)"
expect "a reusable-workflow call's bare job id" 1 "$(ruleset reusable reusable-job)"
expect "a reusable call with no called job" 1 "$(ruleset reusable-empty 'reusable-job / ')"
expect "a named reusable call under its job id" 1 "$(ruleset reusable-id 'reusable-named / gitleaks')"
expect "caller / called whose caller is no reusable call here" 1 "$(ruleset reusable-plain 'plain-job / gitleaks')"
expect "a matrix job's combination" 1 "$(ruleset matrix-combo 'matrix-job (a)')"
expect "a missing ruleset directory is misuse" 2 "$WORK/absent"

printf '\n%s\n' "PASS=$pass FAIL=$fail"
[ "$fail" -eq 0 ] || exit 1
