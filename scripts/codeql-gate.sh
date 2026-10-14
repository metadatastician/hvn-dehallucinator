#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# codeql-gate.sh <sarif-file>...
#
# The verdict of a CodeQL run, read from its SARIF, independent of whether the
# SARIF is ever uploaded to code scanning. .github/workflows/codeql.yml runs it
# after the analysis, so the job is red because CodeQL found something, never
# because GitHub refused an upload.
#
#   * every result is printed as a GitHub annotation at its file and line;
#   * a result at level `error` or `warning` blocks (exit 1); `note` and
#     `none` are reported and do not block;
#   * a result's level is its own `level`, else its rule's
#     defaultConfiguration.level (driver or extension rules, as CodeQL writes
#     them), else `warning`, the SARIF default;
#   * a suppressed result (non-empty `suppressions`) is not counted;
#   * a missing, empty or non-SARIF file is misuse (exit 2): no analysis is
#     not a pass.
#
# Exit: 0 = no blocking result; 1 = at least one; 2 = misuse.
set -euo pipefail

command -v jq >/dev/null 2>&1 || { echo "codeql-gate: jq is required" >&2; exit 2; }
[ "$#" -gt 0 ] || { echo "usage: codeql-gate.sh <sarif-file>..." >&2; exit 2; }

blocking=0; total=0
for f in "$@"; do
  [ -s "$f" ] || { echo "codeql-gate: $f is missing or empty; no analysis is not a pass" >&2; exit 2; }
  jq -e '.runs | type == "array"' "$f" >/dev/null 2>&1 \
    || { echo "codeql-gate: $f is not SARIF (no .runs array)" >&2; exit 2; }
  # One line per unsuppressed result: <level><TAB><workflow-command annotation>.
  rows="$(jq -r '
    def esc:  gsub("%"; "%25") | gsub("\r"; "%0D") | gsub("\n"; "%0A") | gsub("\t"; " ");
    def escp: esc | gsub(":"; "%3A") | gsub(","; "%2C");
    .runs[]
    | ([ (.tool.driver.rules // [])[], ((.tool.extensions // [])[] | (.rules // [])[]) ]
       | map({key: .id, value: (.defaultConfiguration.level // "warning")})
       | from_entries) as $levels
    | (.results // [])[]
    | select((.suppressions // []) | length == 0)
    | (.ruleId // .rule.id // "unknown-rule") as $rule
    | (.level // $levels[$rule] // "warning") as $level
    | (.locations[0].physicalLocation // {}) as $loc
    | $level + "\t"
      + (if $level == "error" or $level == "warning" then "error" else "notice" end)
      + " file=" + (($loc.artifactLocation.uri // "unknown") | escp)
      + ",line=" + (($loc.region.startLine // 1) | tostring)
      + ",title=" + ("CodeQL " + $rule + " (" + $level + ")" | escp)
      + "::" + ((.message.text // "") | esc)' "$f")"
  [ -n "$rows" ] || continue
  while IFS=$'\t' read -r level annotation; do
    total=$((total + 1))
    case "$level" in error|warning) blocking=$((blocking + 1)) ;; esac
    printf '::%s\n' "$annotation"
  done <<<"$rows"
done

if [ "$blocking" -gt 0 ]; then
  echo "RESULT: FAIL -- $blocking blocking result(s) of $total in $# SARIF file(s)"
  exit 1
fi
echo "RESULT: PASS -- no blocking result ($total non-blocking) in $# SARIF file(s)"
