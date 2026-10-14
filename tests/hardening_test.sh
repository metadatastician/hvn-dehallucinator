#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# The hardening suite: everything the engine does to stay correct when its
# surroundings are not (commit f48ad55, "F7 - hardening"). tests/guarantee_test.sh
# covers THE GUARANTEE; this suite covers the ways the engine could otherwise
# crash, guess, or report success it did not obtain:
#
#   locating   the root is found from HARVARD_ROOT or by climbing, never cwd-relative
#   parsing    a malformed state file is refused with the field named, never crashes
#   writing    writes are atomic and the state file stays four lines
#   arguments  bad command lines are refused with the documented exit codes
#   verifier   a verifier that misbehaves is never read as a count
#   read-only  verify and status never write
#   breaker    EMERGENCY_STOP refuses work until a deliberate init
#   pruning    verify_register.sh prunes vendored trees and nothing else
#
# Runs on scratch copies via $HARVARD_ROOT, like tests/guarantee_test.sh.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
command -v runghc >/dev/null 2>&1 || {
    echo "FAIL: runghc not found; the engine cannot be exercised." >&2
    exit 1
}

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

checkout() { # checkout <dir>: a scratch root with the real engine and verifier
    mkdir -p "$1/engine" "$1/state"
    cp "$REPO_ROOT/engine/Engine.hs" "$REPO_ROOT/engine/verify_register.sh" "$1/engine/"
    chmod +x "$1/engine/verify_register.sh"
}
checkout "$WORK/root"
export HARVARD_ROOT="$WORK/root"
ENGINE="runghc $WORK/root/engine/Engine.hs"
STATE="$WORK/root/state/state.txt"
mkdir -p "$WORK/clean/src" "$WORK/empty" "$WORK/nowhere"

pass=0; fail=0
chk() { # chk <name> <got> <want>
    if [ "$2" = "$3" ]; then printf '  PASS  %s\n' "$1"; pass=$((pass+1))
    else printf '  FAIL  %s\n        want=[%s]\n        got =[%s]\n' "$1" "$3" "$2"; fail=$((fail+1)); fi
}
has() { grep -cF -- "$2" <<<"$1"; }

echo "== locating =="
out="$(HARVARD_ROOT="$WORK/empty" $ENGINE status 2>&1)"; rc=$?
chk "HARVARD_ROOT at a non-checkout is refused (exit 1)" "$rc" "1"
chk "  ... and the variable is named"                    "$(has "$out" "HARVARD_ROOT is not")" "1"
$ENGINE init 7 >/dev/null 2>&1
out="$(cd "$WORK/root/state" && env -u HARVARD_ROOT runghc "$WORK/root/engine/Engine.hs" status 2>&1)"
chk "root found by climbing from a subdirectory"         "$out" "RUNNING  0/7 (attempts 0)"
out="$(cd "$WORK/nowhere" && env -u HARVARD_ROOT runghc "$WORK/root/engine/Engine.hs" status 2>&1)"; rc=$?
chk "no root above the working directory: exit 1"        "$rc" "1"

echo "== parsing =="
rm -f "$STATE"
out="$($ENGINE status 2>&1)"; rc=$?
chk "missing state file: exit 1"                         "$rc" "1"
chk "  ... and says to run init"                         "$(has "$out" "no state file")" "1"
printf '7\n0\n0\n' > "$STATE"
chk "three lines: names the expected four"              "$(has "$($ENGINE status 2>&1)" "expected 4 lines")" "1"
printf '7\nx\n0\nRUNNING\n' > "$STATE"
chk "non-integer completed is named"                     "$(has "$($ENGINE status 2>&1)" "completed: not an integer")" "1"
printf '7\n0\n1.5\nRUNNING\n' > "$STATE"
chk "non-integer attempts is named"                      "$(has "$($ENGINE status 2>&1)" "attempts: not an integer")" "1"
printf '7\n0\n0\n   \n' > "$STATE"
chk "blank status is refused"                            "$(has "$($ENGINE status 2>&1)" "status: empty")" "1"
printf '  7 \n 0\n0  \n RUNNING \n' > "$STATE"
chk "padded fields are trimmed, not refused"             "$($ENGINE status 2>&1)" "RUNNING  0/7 (attempts 0)"

echo "== writing =="
$ENGINE init 5 >/dev/null 2>&1
chk "no temporary file is left behind"                   "$(ls "$WORK/root/state")" "state.txt"
$ENGINE update "$WORK/clean" >/dev/null 2>&1
chk "the state file stays four lines"                    "$(wc -l < "$STATE" | tr -d ' ')" "4"

echo "== arguments =="
$ENGINE init -1 >/dev/null 2>&1;      chk "init with a negative total: exit 1"   "$?" "1"
$ENGINE init twelve >/dev/null 2>&1;  chk "init with a non-number: exit 1"       "$?" "1"
$ENGINE frobnicate >/dev/null 2>&1;   chk "unknown command: usage, exit 2"       "$?" "2"
$ENGINE >/dev/null 2>&1;              chk "no command: usage, exit 2"            "$?" "2"

echo "== verifier =="
checkout "$WORK/liar"; printf '#!/usr/bin/env bash\necho lots\n' > "$WORK/liar/engine/verify_register.sh"
HARVARD_ROOT="$WORK/liar" runghc "$WORK/liar/engine/Engine.hs" init 3 >/dev/null 2>&1
out="$(HARVARD_ROOT="$WORK/liar" runghc "$WORK/liar/engine/Engine.hs" update "$WORK/clean" 2>&1)"; rc=$?
chk "a verifier that prints no integer: exit 4"          "$rc" "4"
chk "  ... the attempt is charged, nothing derived"      "$(tr '\n' '/' < "$WORK/liar/state/state.txt")" "3/0/1/RUNNING/"
checkout "$WORK/crash"; printf '#!/usr/bin/env bash\necho 0\nexit 3\n' > "$WORK/crash/engine/verify_register.sh"
HARVARD_ROOT="$WORK/crash" runghc "$WORK/crash/engine/Engine.hs" init 3 >/dev/null 2>&1
out="$(HARVARD_ROOT="$WORK/crash" runghc "$WORK/crash/engine/Engine.hs" update "$WORK/clean" 2>&1)"; rc=$?
chk "a verifier that prints 0 but exits non-zero: exit 4, not COMPLETE" "$rc/$(sed -n 4p "$WORK/crash/state/state.txt")" "4/RUNNING"
before="$(cat "$STATE")"
$ENGINE init-from "$WORK/absent" >/dev/null 2>&1; rc=$?
chk "init-from an unmeasurable target: exit 1, state untouched" "$rc/$(cat "$STATE")" "1/$before"

echo "== read-only =="
before="$(cat "$STATE")"
$ENGINE verify "$WORK/clean" >/dev/null 2>&1; $ENGINE status >/dev/null 2>&1
chk "verify and status never write"                      "$(cat "$STATE")" "$before"

echo "== breaker =="
printf '1\n0\n7\nEMERGENCY_STOP\n' > "$STATE"
$ENGINE attempt >/dev/null 2>&1;      chk "EMERGENCY_STOP refuses attempt: exit 1" "$?" "1"
$ENGINE init 4 >/dev/null 2>&1
chk "init is the deliberate reset"                       "$(tr '\n' '/' < "$STATE")" "4/0/0/RUNNING/"

echo "== pruning =="
mkdir -p "$WORK/tree/node_modules/x" "$WORK/tree/.git/y" "$WORK/tree/repos/proven" "$WORK/tree/src/proven"
touch "$WORK/tree/node_modules/x/A.res" "$WORK/tree/.git/y/B.res" "$WORK/tree/repos/proven/C.res" "$WORK/tree/src/proven/D.res"
chk "vendored trees pruned, first-party src/proven counted" "$($ENGINE verify "$WORK/tree" 2>&1)" "1"

printf '\n%s\n' "PASS=$pass FAIL=$fail"
[ "$fail" -eq 0 ] || exit 1
