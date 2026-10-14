#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# The blind-spot witness, and the 2026-08-23/24 Incident replayed at its
# literal numbers.
#
# state/state.txt was written 16 / 16 / 0 / COMPLETE by hand at 19:22:46 on
# 2026-08-23 and never measured; the first measurement (init-from, 2026-08-25)
# counted 15,272 surviving ReScript artefacts. Replayed against today's engine:
#
#   * regress: `update` on a 15,272-file tree must write RUNNING with nothing
#     completed (16/0/1, Fibre.incident-regresses) and print the witness:
#     recorded remaining 0, measured remaining 15272, claim COMPLETE;
#   * refuse: the original attack, `update 0`, must exit 4, demote the recorded
#     COMPLETE that no measurement confirms (16/16/1/RUNNING), and print the
#     no-case block instead of a bare error;
#   * controls: when record and measurement agree on COMPLETE, or the record
#     does not claim COMPLETE, no witness is printed.
#
# Runs on a scratch copy via $HARVARD_ROOT, like tests/guarantee_test.sh.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
command -v runghc >/dev/null 2>&1 || {
    echo "FAIL: runghc not found; the witness cannot be exercised." >&2
    exit 1
}

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

mkdir -p "$WORK/root/engine" "$WORK/root/state"
cp "$REPO_ROOT/engine/Engine.hs" "$REPO_ROOT/engine/verify_register.sh" "$WORK/root/engine/"
chmod +x "$WORK/root/engine/verify_register.sh"
export HARVARD_ROOT="$WORK/root"
ENGINE="runghc $WORK/root/engine/Engine.hs"
STATE="$WORK/root/state/state.txt"

# The Incident's estate: 15,272 surviving artefacts.
mkdir -p "$WORK/estate/src" "$WORK/clean/src" "$WORK/dirty/src"
seq -f "$WORK/estate/src/M%g.res" 1 15272 | xargs touch
printf 'module A;\n' > "$WORK/clean/src/A.affine"
printf 'let x = 1\n' > "$WORK/dirty/src/A.res"

incident() { printf '16\n16\n0\nCOMPLETE\n' > "$STATE"; }

pass=0; fail=0
chk() { # chk <name> <got> <want>
    if [ "$2" = "$3" ]; then printf '  PASS  %s\n' "$1"; pass=$((pass+1))
    else printf '  FAIL  %s\n        want=[%s]\n        got =[%s]\n' "$1" "$3" "$2"; fail=$((fail+1)); fi
}
has() { grep -cF -- "$2" <<<"$1"; } # has <text> <fixed-string> -> count

echo "== the Incident's estate =="
chk "verifier counts the 15,272 survivors" "$($ENGINE verify "$WORK/estate" 2>&1)" "15272"

echo "== regress: the Incident replayed =="
incident
out="$($ENGINE update "$WORK/estate" 2>&1)"; rc=$?
chk "update succeeds (exit 0)"                 "$rc" "0"
chk "state becomes 16/0/1/RUNNING (Fibre.incident-regresses)" "$(tr '\n' '/' < "$STATE")" "16/0/1/RUNNING/"
chk "witness block printed"                    "$(has "$out" "WITNESS regress: the recorded state does not identify COMPLETE")" "1"
chk "claim named"                              "$(has "$out" "  claim:    COMPLETE (remaining 0)")" "1"
chk "recorded reading: remaining 0"            "$(has "$out" "  recorded: remaining 0  (state 16/16, attempts 0, status COMPLETE)")" "1"
chk "measured reading: remaining 15272"        "$(has "$out" "  measured: remaining 15272  (engine/verify_register.sh $WORK/estate)")" "1"
chk "re-check command given"                   "$(has "$out" "Re-check: Engine verify $WORK/estate")" "1"
chk "cites Fibre.asserted-not-identified"      "$(has "$out" "Proof: Fibre.asserted-not-identified, Fibre.regress-refutes")" "1"
chk "state file stays four lines"              "$(wc -l < "$STATE" | tr -d ' ')" "4"

echo "== refuse: the original attack, update 0 =="
incident
out="$($ENGINE update 0 2>&1)"; rc=$?
chk "refused (exit 4)"                         "$rc" "4"
chk "no-case block printed"                    "$(has "$out" "WITNESS refuse: no measured case, so COMPLETE cannot be derived")" "1"
chk "measured: none, with the reason"          "$(has "$out" "  measured: none (target directory does not exist: 0)")" "1"
chk "says the recorded COMPLETE is demoted"    "$(has "$out" "The recorded COMPLETE is demoted to RUNNING: no measurement confirms it.")" "1"
chk "status line reports the demotion"         "$(has "$out" "status demoted from COMPLETE to RUNNING.")" "1"
chk "cites Fibre.complete-needs-case"          "$(has "$out" "Proof: Fibre.complete-needs-case")" "1"
chk "attempt charged, COMPLETE demoted (Fibre.incident-refused)" "$(tr '\n' '/' < "$STATE")" "16/16/1/RUNNING/"

echo "== controls: no blind spot, no witness =="
incident
out="$($ENGINE update "$WORK/clean" 2>&1)"
chk "record and measurement agree on COMPLETE" "$(has "$out" "WITNESS")" "0"
chk "  ... and COMPLETE stands"                "$(sed -n 4p "$STATE")" "COMPLETE"
printf '30\n0\n0\nRUNNING\n' > "$STATE"
out="$($ENGINE update "$WORK/dirty" 2>&1)"
chk "record does not claim COMPLETE"           "$(has "$out" "WITNESS")" "0"
out="$($ENGINE update "$WORK/clean" 2>&1)"
chk "RUNNING to a measured COMPLETE"           "$(has "$out" "WITNESS")" "0"
printf '30\n0\n0\nRUNNING\n' > "$STATE"
out="$($ENGINE update "$WORK/nowhere" 2>&1)"
chk "refuse on a RUNNING record omits the COMPLETE note" "$(has "$out" "The recorded COMPLETE")" "0"
chk "  ... and leaves RUNNING as it was"       "$(tr '\n' '/' < "$STATE")" "30/0/1/RUNNING/"

printf '\n%s\n' "PASS=$pass FAIL=$fail"
[ "$fail" -eq 0 ] || exit 1
