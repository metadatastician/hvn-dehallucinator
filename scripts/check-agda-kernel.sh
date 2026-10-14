#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# check-agda-kernel.sh [reject-dir]
#
# The Agda kernel gate (--safe --without-K --no-libraries --ignore-interfaces
# --double-check):
#
#   1. fetch the pinned siblings (scripts/fetch-siblings.sh);
#   2. the positive set: every module in verification/proofs/agda/MANIFEST,
#      via scripts/check-proofs.sh agda, which also fails on any .agda file
#      there that the MANIFEST does not list;
#   3. every module in the reject directory (default tests/reject) must be
#      REFUSED, with a type-checking error at its own declaration. A missing
#      import, an unsolved meta or a parse error is a broken fixture, not a
#      rejection, and fails the gate (the residual-evidence-types rule).
#
# Positive set first: a broken checkout must not turn into passing rejections.
# Exit 0 only when all three hold.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
# Agda aborts when it must print non-ASCII names under a non-UTF-8 locale.
export LC_ALL=C.UTF-8 LANG=C.UTF-8
prover="${AGDA:-agda}"
reject_dir="${1:-tests/reject}"

command -v "$prover" >/dev/null 2>&1 || {
  echo "FAIL: '$prover' not found on PATH. The kernel gate cannot be skipped." >&2
  exit 1
}

bash scripts/fetch-siblings.sh
bash scripts/check-proofs.sh agda

includes=(-i verification/proofs/agda)
for d in _build/dependencies/*/src; do [ -d "$d" ] && includes+=(-i "$d"); done
flags=(--safe --without-K --no-libraries --ignore-interfaces --double-check)

echo
echo "=== expected rejections ($reject_dir) ==="
shopt -s nullglob
rejects=("$reject_dir"/*.agda)
shopt -u nullglob
if (( ${#rejects[@]} == 0 )); then
  echo "FAIL: no expected-rejection modules under $reject_dir" >&2
  exit 1
fi
logs=_build/check-logs
mkdir -p "$logs"
for file in "${rejects[@]}"; do
  name="$(basename -- "$file" .agda)"
  log="$logs/$name.log"
  if "$prover" "${flags[@]}" "${includes[@]}" -i "$reject_dir" "$file" >"$log" 2>&1; then
    cat "$log"
    echo "FAIL: invalid proof accepted: $name" >&2
    exit 1
  fi
  if ! grep -Eq "/$name\.agda:[0-9]+,[0-9]+" "$log" ||
     ! grep -q 'when checking that' "$log" ||
     grep -Eq 'Not in scope|Failed to find|Unsolved|Parse error' "$log"; then
    cat "$log"
    echo "FAIL: unexpected failure while checking $name (not a type error at its declaration)" >&2
    exit 1
  fi
  echo "  PASS: refused $name at $(grep -Eo "/$name\.agda:[0-9]+,[0-9-]+" "$log" | head -1 | sed 's#^/##')"
done
echo "RESULT: PASS -- kernel modules check; all ${#rejects[@]} expected rejection(s) refused"
