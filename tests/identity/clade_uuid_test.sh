#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# The repository identity in .machine_readable/descriptiles/CLADE.a2ml must be
# what scripts/derive-clade-uuid.sh derives from the forge path the file
# itself records (ESTATE-UUID-V8 profile C). A repository that moves owner or
# name and keeps its old uuid fails here: that is how this repository carried
# the template's identity, and then a hyperpolymath-derived one, after it moved.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
DERIVE="$REPO_ROOT/scripts/derive-clade-uuid.sh"
CLADE="$REPO_ROOT/.machine_readable/descriptiles/CLADE.a2ml"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

pass=0; fail=0
# chk <name> <got> <want> - compare <got> against <want> for the test labelled
# <name>; prints a PASS line, or a FAIL line with both values, and increments
# the $pass or $fail counter accordingly. No output is returned; results
# accumulate in $pass/$fail for the summary line at the end of the script.
chk() { # chk <name> <got> <want>
  if [ "$2" = "$3" ]; then printf '  PASS  %s\n' "$1"; pass=$((pass+1))
  else printf '  FAIL  %s\n        want=[%s]\n        got =[%s]\n' "$1" "$3" "$2"; fail=$((fail+1)); fi
}

# uuid and forge path recorded in a CLADE file.
field() { sed -n "s/^$2 *= *\"\\([^\"]*\\)\".*/\\1/p" "$1" | head -1; }
# drift <clade-file> -> "ok" or a description of the mismatch - reads the
# uuid and github fields from <clade-file>, re-derives the uuid from the
# recorded forge path via $DERIVE, and echoes "ok" if they agree or else a
# message naming the recorded and derived uuids and the path used.
drift() { # drift <clade-file> -> "ok" or a description of the mismatch
  local u g d
  u="$(field "$1" uuid)"; g="$(field "$1" github)"
  d="$(sh "$DERIVE" "github.com/$g")"
  if [ "$u" = "$d" ]; then echo ok; else echo "recorded $u, derived $d from github.com/$g"; fi
}

echo "== derivation =="
# Known answer, cross-checked on 2026-10-14 against an independent SHA-256
# (openssl dgst -sha256 of "gv-clade-index:github.com/metadatastician/hvn-dehallucinator"
# begins b48d084cbaa50415f9683b98b3f69a71; byte 6 0x04 -> 0x84, byte 8 0xf9 -> 0xb9).
chk "known answer for this repository" \
  "$(sh "$DERIVE" github.com/metadatastician/hvn-dehallucinator)" "b48d084c-baa5-8415-b968-3b98b3f69a71"
u="$(sh "$DERIVE" github.com/metadatastician/hvn-dehallucinator)"
chk "version nibble is 8" "$(printf '%s' "$u" | cut -d- -f3 | cut -c1)" "8"
case "$(printf '%s' "$u" | cut -d- -f4 | cut -c1)" in 8|9|a|b) v=10 ;; *) v=other ;; esac
chk "variant is 10 (8, 9, a or b)" "$v" "10"
chk "deterministic" "$(sh "$DERIVE" github.com/metadatastician/hvn-dehallucinator)" "$u"

echo "== negative controls =="
sh "$DERIVE" github.com/x/y a:b >/dev/null 2>&1
chk "a domain containing ':' is refused (exit 2)" "$?" "2"
old="$(sh "$DERIVE" github.com/hyperpolymath/harvard-dehallucinator)"
[ "$old" != "$u" ]; chk "a different forge path gives a different uuid" "$?" "0"
sed -e 's#^github = ".*"#github = "hyperpolymath/harvard-dehallucinator"#' "$CLADE" > "$WORK/moved.a2ml"
[ "$(drift "$WORK/moved.a2ml")" != ok ]; chk "drift check catches a stale forge path" "$?" "0"

echo "== CLADE.a2ml =="
chk "CLADE.a2ml uuid derives from its own forge path" "$(drift "$CLADE")" "ok"

printf '\n%s\n' "PASS=$pass FAIL=$fail"
[ "$fail" -eq 0 ] || exit 1
