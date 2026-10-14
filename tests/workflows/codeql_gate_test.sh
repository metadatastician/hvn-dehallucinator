#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# Controls for scripts/codeql-gate.sh. The gate must fail on a blocking result
# however CodeQL records its level, must not fail on notes or suppressed
# results, and must refuse to read a missing analysis as a pass.
# .github/workflows/codeql.yml runs this before trusting the gate's verdict.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
GATE="$REPO_ROOT/scripts/codeql-gate.sh"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# sarif <name> <results-json> [driver-rules-json] [extension-rules-json]
sarif() {
  printf '{"version":"2.1.0","runs":[{"tool":{"driver":{"name":"CodeQL","rules":%s},"extensions":[{"name":"codeql/actions-queries","rules":%s}]},"results":%s}]}\n' \
    "${3:-[]}" "${4:-[]}" "$2" > "$WORK/$1.sarif"
  printf '%s' "$WORK/$1.sarif"
}
loc='"locations":[{"physicalLocation":{"artifactLocation":{"uri":".github/workflows/ci.yml"},"region":{"startLine":12}}}]'
result() { # result <ruleId> [level]
  local lvl=""; [ -n "${2:-}" ] && lvl="\"level\":\"$2\","
  printf '{"ruleId":"%s",%s"message":{"text":"found it"},%s}' "$1" "$lvl" "$loc"
}

pass=0; fail=0
expect() { # expect <name> <want-exit> <file>...
  local name="$1" want="$2" out rc; shift 2
  out="$(bash "$GATE" "$@" 2>&1)"; rc=$?
  if [ "$rc" = "$want" ]; then printf '  PASS  %s (exit %s)\n' "$name" "$rc"; pass=$((pass+1))
  else printf '  FAIL  %s: want exit %s, got %s\n%s\n' "$name" "$want" "$rc" "$out"; fail=$((fail+1)); fi
}

echo "== passes =="
expect "no results" 0 "$(sarif empty '[]')"
expect "a note does not block" 0 "$(sarif note "[$(result actions/x note)]")"
expect "a suppressed warning does not block" 0 \
  "$(sarif supp '[{"ruleId":"actions/x","level":"warning","suppressions":[{"kind":"inSource"}],"message":{"text":"m"}}]')"
expect "a rule whose default level is note" 0 \
  "$(sarif extnote "[$(result actions/n)]" '[]' '[{"id":"actions/n","defaultConfiguration":{"level":"note"}}]')"

echo "== blocks (each must fail) =="
expect "an explicit error" 1 "$(sarif err "[$(result actions/x error)]")"
expect "an explicit warning" 1 "$(sarif warn "[$(result actions/x warning)]")"
expect "level from a driver rule" 1 \
  "$(sarif drv "[$(result actions/d)]" '[{"id":"actions/d","defaultConfiguration":{"level":"error"}}]')"
expect "level from an extension rule (CodeQL's layout)" 1 \
  "$(sarif ext "[$(result actions/e)]" '[]' '[{"id":"actions/e","defaultConfiguration":{"level":"warning"}}]')"
expect "no level anywhere: SARIF's default, warning" 1 "$(sarif bare "[$(result actions/b)]")"
expect "one blocking file among clean ones" 1 "$WORK/empty.sarif" "$WORK/err.sarif"

echo "== misuse (no analysis is not a pass) =="
expect "no arguments" 2
expect "a missing file" 2 "$WORK/absent.sarif"
: > "$WORK/zero.sarif"; expect "an empty file" 2 "$WORK/zero.sarif"
echo '{}' > "$WORK/notsarif.sarif"; expect "JSON that is not SARIF" 2 "$WORK/notsarif.sarif"

echo "== annotations =="
out="$(bash "$GATE" "$(sarif ann '[{"ruleId":"actions/a","level":"error","message":{"text":"line one\nline, two: 100%"},"locations":[{"physicalLocation":{"artifactLocation":{"uri":"dir/a,b.yml"},"region":{"startLine":7}}}]}]')" 2>&1)"
want='::error file=dir/a%2Cb.yml,line=7,title=CodeQL actions/a (error)::line one%0Aline, two: 100%25'
if grep -qxF -- "$want" <<<"$out"; then printf '  PASS  %s\n' "file, line and message escaped for the runner"; pass=$((pass+1))
else printf '  FAIL  annotation\n  want: %s\n  got:\n%s\n' "$want" "$out"; fail=$((fail+1)); fi

printf '\n%s\n' "PASS=$pass FAIL=$fail"
[ "$fail" -eq 0 ] || exit 1
