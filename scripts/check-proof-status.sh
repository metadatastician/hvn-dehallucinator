#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# check-proof-status.sh [ledger-file [repo-root]]
#
# The ledger in docs/status/PROOF-STATUS.adoc must describe the tree it ships
# in. The ledger is the table introduced by a `[#ledger,...]` block attribute;
# each row is one line `| ID | Claim | Status | Artefact`.
#
#   * every row has exactly four cells and a status in
#     PROVEN | TESTED | ASSUMED | DESIGNED | OPEN;
#   * a row that is not OPEN names at least one repo path in backticks in its
#     Artefact cell, and every backticked repo path there exists;
#     `path#fragment` additionally requires the fixed string `fragment` to
#     occur in that file (a lemma name, a test label);
#   * no rsr-template text remains in the file.
#
# OPEN rows may name planned paths that do not exist yet. A backticked token
# is a repo path when it contains a `/` and only path characters before any
# `#`; lemma names (`Core.from-to`), commands, and sibling references at a pin
# (anything containing `@`) are not checked here.
#
# Exit: 0 = consistent; 1 = at least one violation (each printed); 2 = misuse.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FILE="${1:-$here/docs/status/PROOF-STATUS.adoc}"
ROOT="${2:-$here}"
[ -f "$FILE" ] || { echo "check-proof-status: no such file: $FILE" >&2; exit 2; }
[ -d "$ROOT" ] || { echo "check-proof-status: no such root: $ROOT" >&2; exit 2; }

fails=0
bad() { echo "FAIL: $*"; fails=$((fails + 1)); }

trim() { local s="$1"; s="${s#"${s%%[![:space:]]*}"}"; printf '%s' "${s%"${s##*[![:space:]]}"}"; }

# --- template residue ----------------------------------------------------------
if grep -nE 'rsr-template-repo/docs/status|No proofs completed yet|HARVARD_DEHALLUCINATOR|Initial proof status tracking' "$FILE"; then
  bad "template text remains in $FILE (lines above)"
fi

# --- ledger rows ----------------------------------------------------------------
# Rows between the `|===` that follows `[#ledger` and the next `|===`; the
# first row is the header.
rows="$(awk '
  /^\[#ledger/            { armed = 1; next }
  armed && /^\|===[[:space:]]*$/ { if (inside) exit; inside = 1; next }
  inside && /^\|/         { if (!header) { header = 1; next } print }
' "$FILE")"

if [ -z "$rows" ]; then
  bad "no ledger rows: expected a [#ledger,...] table with a header row and at least one row"
fi

n=0
while IFS= read -r line; do
  [ -z "$line" ] && continue
  n=$((n + 1))
  IFS='|' read -r -a cell <<<"$line"
  # A leading `|` makes cell[0] empty; four cells means five fields.
  if [ "${#cell[@]}" -ne 5 ]; then
    bad "row $n has $(( ${#cell[@]} - 1 )) cells, expected 4: $line"
    continue
  fi
  id="$(trim "${cell[1]}")"
  status="$(trim "${cell[3]}")"
  artefact="${cell[4]}"
  case "$status" in
    PROVEN|TESTED|ASSUMED|DESIGNED|OPEN) ;;
    *) bad "$id: status '$status' is not one of PROVEN TESTED ASSUMED DESIGNED OPEN"; continue ;;
  esac
  [ "$status" = OPEN ] && continue

  named=0
  while IFS= read -r tok; do
    [ -z "$tok" ] && continue
    tok="${tok#\`}"; tok="${tok%\`}"
    case "$tok" in *@*) continue ;; esac
    path="${tok%%#*}"
    [[ "$path" == */* && "$path" =~ ^[A-Za-z0-9._/-]+$ ]] || continue
    named=$((named + 1))
    if [ ! -e "$ROOT/$path" ]; then
      bad "$id ($status): names $path, which is not in the tree"
      continue
    fi
    if [[ "$tok" == *"#"* ]]; then
      frag="${tok#*#}"
      if ! grep -qF -- "$frag" "$ROOT/$path"; then
        bad "$id ($status): $path does not contain '$frag'"
      fi
    fi
  done < <(grep -o '`[^`]*`' <<<"$artefact" || true)

  if [ "$named" -eq 0 ]; then
    bad "$id ($status): names no artefact in the tree; a status other than OPEN needs one"
  fi
done <<<"$rows"

if [ "$fails" -gt 0 ]; then
  echo "RESULT: FAIL ($fails violation(s)) in $FILE"
  exit 1
fi
echo "RESULT: PASS -- $n ledger row(s); every non-OPEN row names artefacts present in the tree"
