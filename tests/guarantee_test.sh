#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# Regression suite for THE GUARANTEE: `completed` and `status` are only ever
# derived from engine/verify_register.sh run on the target bound at the
# baseline, and no caller-supplied argument can choose what is measured or
# reach the string COMPLETE.
#
# The original engine took `remaining` as a parameter and wrote COMPLETE on the
# agent's say-so. On 2026-08-23 it recorded 16/16 COMPLETE 1h27m before the
# first file of the migration was ported. These tests exist so that cannot
# silently return.
#
# Portable: operates entirely on a scratch copy via $HARVARD_ROOT and mktemp,
# so it never touches the repo's own state/state.txt.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
command -v runghc >/dev/null 2>&1 || {
    echo "FAIL: runghc not found. The engine cannot be exercised, so its" >&2
    echo "      guarantee cannot be verified. Install GHC (runghc, and the" >&2
    echo "      process/directory/filepath boot packages) before this gate." >&2
    exit 1
}

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# Scratch checkout: engine + state only.
mkdir -p "$WORK/root/engine" "$WORK/root/state"
cp "$REPO_ROOT/engine/Engine.hs" "$REPO_ROOT/engine/verify_register.sh" "$WORK/root/engine/"
chmod +x "$WORK/root/engine/verify_register.sh"
export HARVARD_ROOT="$WORK/root"
ENGINE="runghc $WORK/root/engine/Engine.hs"

# Fixtures: one tree with surviving ReScript, one without.
mkdir -p "$WORK/dirty/src" "$WORK/clean/src"
printf 'let x = 1\n' > "$WORK/dirty/src/A.res"
printf 'let y = 2\n' > "$WORK/dirty/src/B.res"
printf '{}\n'        > "$WORK/dirty/rescript.json"
printf 'module A;\n' > "$WORK/clean/src/A.affine"
DIRTY="$(cd "$WORK/dirty" && pwd -P)"

pass=0; fail=0
chk() { # chk <name> <got> <want>
    if [ "$2" = "$3" ]; then printf '  PASS  %s\n' "$1"; pass=$((pass+1))
    else printf '  FAIL  %s\n        want=[%s]\n        got =[%s]\n' "$1" "$3" "$2"; fail=$((fail+1)); fi
}
field() { sed -n "$1p" "$WORK/root/state/state.txt"; }
snapshot() { tr '\n' '/' < "$WORK/root/state/state.txt"; }

echo "== verifier (on the bound target) =="
$ENGINE init-from "$WORK/dirty" >/dev/null 2>&1
chk "counts .res/.resi/rescript.json" "$($ENGINE verify 2>&1)" "3"
$ENGINE init-from "$WORK/clean" >/dev/null 2>&1
chk "counts zero on a clean tree"     "$($ENGINE verify 2>&1)" "0"

echo "== baseline binds the target =="
$ENGINE init 30 "$WORK/dirty" >/dev/null 2>&1
chk "init sets RUNNING and binds the target" "$(snapshot)" "30/0/0/RUNNING/$DIRTY/"
$ENGINE init-from "$WORK/dirty" >/dev/null 2>&1
chk "init-from MEASURES total"     "$(field 1)" "3"
chk "init-from binds the target"   "$(field 5)" "$DIRTY"

echo "== THE GUARANTEE =="
$ENGINE init 30 "$WORK/dirty" >/dev/null 2>&1
$ENGINE update >/dev/null 2>&1
chk "non-zero target cannot write COMPLETE" "$(field 4)" "RUNNING"
chk "progress derived from the count"       "$(field 2)" "27"
chk "update charges an attempt"             "$(field 3)" "1"

# The original attack: assert progress as an argument. `update 0` used to mean
# "zero remaining, mark COMPLETE". The second: name an empty directory, so the
# verifier counts nothing (found 2026-11-09). `update` now takes no argument at
# all; both are usage errors that change nothing, not even the attempt count.
before="$(snapshot)"
$ENGINE update 0 >/dev/null 2>&1
chk "caller cannot assert a number (exit 2)"         "$?" "2"
$ENGINE update "$WORK/clean" >/dev/null 2>&1
chk "caller cannot choose the measured directory (exit 2)" "$?" "2"
$ENGINE verify "$WORK/clean" >/dev/null 2>&1
chk "verify measures only the bound target (exit 2)" "$?" "2"
chk "status unchanged by the attempt"                "$(snapshot)" "$before"

# COMPLETE comes only from the bound target measuring zero: do the work.
rm -f "$WORK/dirty/src/A.res" "$WORK/dirty/src/B.res" "$WORK/dirty/rescript.json"
$ENGINE update >/dev/null 2>&1
chk "COMPLETE only via a MEASURED zero"      "$(field 4)" "COMPLETE"

printf 'let z = 3\n' > "$WORK/dirty/src/C.res"
$ENGINE update >/dev/null 2>&1
chk "regresses out of COMPLETE"              "$(field 4)" "RUNNING"

out="$($ENGINE init-from "$WORK/clean" 2>&1)"
chk "a re-bind is announced"                 "$(printf '%s' "$out" | grep -c 'target re-bound')" "1"
printf 'garbage\n' > "$WORK/root/state/state.txt"
out="$($ENGINE init-from "$WORK/clean" 2>&1)"
chk "replacing an unreadable state is announced"      "$(printf '%s' "$out" | grep -c 'replacing a state file that does not parse')" "1"

echo "== circuit breaker =="
$ENGINE init 1 "$WORK/dirty" >/dev/null 2>&1
for _ in 1 2 3 4 5 6; do $ENGINE attempt >/dev/null 2>&1; done
chk "attempts accumulate to budget" "$(field 3)" "6"
$ENGINE attempt >/dev/null 2>&1
chk "trips past total+5 (exit 3)"   "$?" "3"
chk "EMERGENCY_STOP written"        "$(field 4)" "EMERGENCY_STOP"
$ENGINE update >/dev/null 2>&1
chk "stopped state is terminal (exit 1)" "$?" "1"
chk "stays stopped"                      "$(field 4)" "EMERGENCY_STOP"

echo "== robustness =="
printf 'not-a-number\n0\n0\nRUNNING\n%s\n' "$DIRTY" > "$WORK/root/state/state.txt"
out="$($ENGINE status 2>&1)"; rc=$?
chk "malformed state exits 1, no crash" "$rc" "1"
chk "names the offending field"         "$(printf '%s' "$out" | grep -c totalItems)" "1"
printf '3\n0\n0\nPAUSED\n%s\n' "$DIRTY" > "$WORK/root/state/state.txt"
$ENGINE status >/dev/null 2>&1
chk "an unknown status is refused (exit 1)"  "$?" "1"
printf '3\n5\n0\nRUNNING\n%s\n' "$DIRTY" > "$WORK/root/state/state.txt"
$ENGINE status >/dev/null 2>&1
chk "completed > total is refused (exit 1)"  "$?" "1"
printf '3\n0\n0\nRUNNING\n' > "$WORK/root/state/state.txt"
$ENGINE status >/dev/null 2>&1
chk "a 4-line state without a target is refused (exit 1)" "$?" "1"
$ENGINE init -5 "$WORK/dirty" >/dev/null 2>&1
chk "a negative baseline is refused (exit 1)" "$?" "1"
$ENGINE init 9223372036854775807 "$WORK/dirty" >/dev/null 2>&1
chk "a baseline above the bound is refused (exit 1)" "$?" "1"
$ENGINE init 3 "$WORK/nowhere" >/dev/null 2>&1
chk "a missing target cannot be bound (exit 1)" "$?" "1"

$ENGINE init 5 "$WORK/dirty" >/dev/null 2>&1
a="$(cd / && $ENGINE status 2>&1)"
b="$(cd "$WORK/root/engine" && runghc Engine.hs status 2>&1)"
chk "cwd-independent" "$a" "$b"

printf '\n%s\n' "PASS=$pass FAIL=$fail"
[ "$fail" -eq 0 ] || exit 1
