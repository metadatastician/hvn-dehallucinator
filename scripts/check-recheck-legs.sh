#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# check-recheck-legs.sh [rocq-file] [lean-file]
#
# The recheck legs of standards PROOF-POLICY section 2 for the Haruspex theory
# theorems (verification/proofs/agda/Haruspex.agda, HaruspexExplorer.agda):
#
#   1. Rocq: coqc compiles verification/proofs/coq/Haruspex.v, and every
#      `Print Assumptions` in it reports "Closed under the global context".
#      Any axiom, admitted lemma or parameter shows up there and fails the leg.
#   2. Lean: lean compiles verification/proofs/lean4/Haruspex.lean, and every
#      `#print axioms` in it reports "does not depend on any axioms". sorry
#      (sorryAx), Classical.choice, propext and Quot.sound all fail the leg.
#   3. Each file prints the assumptions of every theorem the correspondence
#      record names (docs/status/RECHECK-CORRESPONDENCE.adoc). A theorem missing
#      from the printed set fails the leg, so a deleted print cannot hide one.
#
# The number of reports must equal the number of print commands: a compile that
# stops early, or is killed, prints fewer and fails. Exit 0 only when both legs
# pass. The arguments exist for the negative controls
# (tests/proofs/recheck_legs_test.sh).
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
rocq_file="${1:-verification/proofs/coq/Haruspex.v}"
lean_file="${2:-verification/proofs/lean4/Haruspex.lean}"
coqc="${COQC:-coqc}"
lean="${LEAN:-lean}"

fail() { echo "FAIL: $*" >&2; exit 1; }

# The theorems the correspondence record names, by their names in each prover.
required=(holdsAll_sound holdsAll_complete candidate_mem mem_candidate
  entailed_sound refuted_sound refuted_refutes unresolved_sound inconsistent_sound
  entailed_complete identified_sound unidentified_sound unidentified_refutes
  no_candidate_sound identified_complete actual_sound listing_complete_sound
  sound_given sound_given_query haruspex
  to_finite from_finite candidates_match presence_match identity_match outputs_match)

command -v "$coqc" >/dev/null 2>&1 || fail "'$coqc' not found. The Rocq leg cannot be skipped."
command -v "$lean" >/dev/null 2>&1 || fail "'$lean' not found. The Lean leg cannot be skipped."
[ -f "$rocq_file" ] || fail "no such file: $rocq_file"
[ -f "$lean_file" ] || fail "no such file: $lean_file"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

covers() { # covers <file> <print-regex-prefix> <leg>
  local name
  for name in "${required[@]}"; do
    grep -Eq "^$2([A-Za-z_.]*\\.)?$name\\.?\$" "$1" || fail "$3: no assumption report for '$name'"
  done
}

echo "=== Rocq leg: $rocq_file ($("$coqc" --version | head -1)) ==="
cp -- "$rocq_file" "$work/Leg.v"
if ! (cd "$work" && "$coqc" Leg.v) >"$work/rocq.log" 2>&1; then
  cat "$work/rocq.log"; fail "Rocq leg: coqc failed"
fi
prints="$(grep -c '^Print Assumptions ' "$rocq_file" || true)"
closed="$(grep -c '^Closed under the global context$' "$work/rocq.log" || true)"
if grep -Eq '^(Axioms|Opaque constants|Section Variables):' "$work/rocq.log"; then
  cat "$work/rocq.log"; fail "Rocq leg: a theorem rests on an assumption"
fi
[ "$prints" -gt 0 ] || fail "Rocq leg: no Print Assumptions in $rocq_file"
[ "$closed" = "$prints" ] || { cat "$work/rocq.log"; fail "Rocq leg: $closed of $prints reports are closed"; }
covers "$rocq_file" 'Print Assumptions ' "Rocq leg"
echo "  PASS: compiles; $closed of $prints theorems closed under the global context"

echo "=== Lean leg: $lean_file ($("$lean" --version | head -1)) ==="
if ! "$lean" "$lean_file" >"$work/lean.log" 2>&1; then
  grep -v 'does not depend on any axioms' "$work/lean.log" | head -40; fail "Lean leg: lean failed"
fi
prints="$(grep -c '^#print axioms ' "$lean_file" || true)"
clean="$(grep -c "' does not depend on any axioms$" "$work/lean.log" || true)"
if grep -q 'depends on axioms' "$work/lean.log"; then
  grep 'depends on axioms' "$work/lean.log"; fail "Lean leg: a theorem rests on an axiom"
fi
[ "$prints" -gt 0 ] || fail "Lean leg: no #print axioms in $lean_file"
[ "$clean" = "$prints" ] || { cat "$work/lean.log"; fail "Lean leg: $clean of $prints reports are axiom-free"; }
covers "$lean_file" '#print axioms ' "Lean leg"
echo "  PASS: compiles; $clean of $prints theorems depend on no axioms"

echo "RESULT: PASS -- Rocq and Lean legs compile with no axioms; every recorded theorem is reported"
