#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# Negative controls for scripts/check-proof-status.sh: a gate that cannot fail
# is not a gate, so each way a ledger can disagree with the tree is fed to it
# and must be refused. The positive controls are a well-formed fixture and the
# repository's own docs/status/PROOF-STATUS.adoc.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CHECK="$REPO_ROOT/scripts/check-proof-status.sh"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

mkdir -p "$WORK/root/a"
printf 'alpha-lemma : something\n' > "$WORK/root/a/b.agda"

ledger() { # ledger <name> <row>...
  local f="$WORK/$1.adoc"; shift
  { echo '= Fixture'; echo; echo '[#ledger,cols="1,3,1,3",options="header"]'; echo '|==='
    echo '| ID | Claim | Status | Artefact'; printf '%s\n' "$@"; echo '|==='; } > "$f"
  printf '%s' "$f"
}

pass=0; fail=0
expect() { # expect <name> <want-exit> <file> [root]
  local name="$1" want="$2" file="$3" root="${4:-$WORK/root}" out rc
  out="$(bash "$CHECK" "$file" "$root" 2>&1)"; rc=$?
  if [ "$rc" = "$want" ]; then printf '  PASS  %s (exit %s)\n' "$name" "$rc"; pass=$((pass+1))
  else printf '  FAIL  %s: want exit %s, got %s\n%s\n' "$name" "$want" "$rc" "$out"; fail=$((fail+1)); fi
}

echo "== positive controls =="
expect "well-formed ledger, OPEN row may name a planned path" 0 \
  "$(ledger ok '| X-1 | holds | PROVEN | `a/b.agda#alpha-lemma`' '| X-2 | later | OPEN | planned `x/y.agda`')"
expect "the repository's own PROOF-STATUS.adoc" 0 "$REPO_ROOT/docs/status/PROOF-STATUS.adoc" "$REPO_ROOT"

echo "== negative controls (each must be refused) =="
expect "non-OPEN row names a missing file"       1 "$(ledger missing '| X-1 | holds | TESTED | `a/nope.sh`')"
expect "non-OPEN row names a missing fragment"   1 "$(ledger frag '| X-1 | holds | PROVEN | `a/b.agda#beta-lemma`')"
expect "status outside the five"                 1 "$(ledger status '| X-1 | holds | PROVED | `a/b.agda`')"
expect "non-OPEN row names no repo path"         1 "$(ledger nopath '| X-1 | holds | TESTED | a lemma called `Core.from-to`')"
expect "row with three cells"                    1 "$(ledger cells '| X-1 | holds | `a/b.agda`')"
printf '= Fixture\n\nNo ledger here.\n' > "$WORK/noledger.adoc"
expect "no ledger table"                         1 "$WORK/noledger.adoc"
f="$(ledger tmpl '| X-1 | holds | PROVEN | `a/b.agda`')"; echo '| — | No proofs completed yet | — | — | — | —' >> "$f"
expect "template text remains"                   1 "$f"
expect "missing ledger file is misuse"           2 "$WORK/absent.adoc"

printf '\n%s\n' "PASS=$pass FAIL=$fail"
[ "$fail" -eq 0 ] || exit 1
