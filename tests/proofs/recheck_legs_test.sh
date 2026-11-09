#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# Negative controls for scripts/check-recheck-legs.sh. The gate claims a leg
# passes only when it compiles, every printed theorem is free of axioms, and
# every theorem the correspondence record names is printed. Small fixtures stand
# in for the real files (the Lean leg takes minutes): a clean pair the gate must
# pass, then one defect at a time, each of which it must fail.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
GATE="$REPO_ROOT/scripts/check-recheck-legs.sh"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

names=(holdsAll_sound holdsAll_complete candidate_mem mem_candidate
  entailed_sound refuted_sound refuted_refutes unresolved_sound inconsistent_sound
  entailed_complete identified_sound unidentified_sound unidentified_refutes
  no_candidate_sound identified_complete actual_sound listing_complete_sound
  sound_given sound_given_query haruspex
  to_finite from_finite candidates_match presence_match identity_match outputs_match)

rocq() { # rocq <file> [skip-name] [extra]
  { for n in "${names[@]}"; do
      [ "$n" = "${2:-}" ] && continue
      printf 'Lemma %s : True. Proof. exact I. Qed.\nPrint Assumptions %s.\n' "$n" "$n"
    done; printf '%s\n' "${3:-}"; } > "$1"
}
lean() { # lean <file> [skip-name] [extra]
  { echo 'namespace Fixture'
    for n in "${names[@]}"; do
      [ "$n" = "${2:-}" ] && continue
      printf 'theorem %s : True := trivial\n' "$n"
    done
    printf '%s\n' "${3:-}"
    echo 'end Fixture'
    for n in "${names[@]}"; do
      [ "$n" = "${2:-}" ] && continue
      printf '#print axioms Fixture.%s\n' "$n"
    done; } > "$1"
}

pass=0; fail=0
expect() { # expect <name> <want-exit> <want-text> <rocq> <lean>
  local name="$1" want="$2" text="$3" out rc
  out="$(bash "$GATE" "$4" "$5" 2>&1)"; rc=$?
  if [ "$rc" = "$want" ] && grep -qF -- "$text" <<<"$out"; then
    printf '  PASS  %s (exit %s)\n' "$name" "$rc"; pass=$((pass+1))
  else
    printf '  FAIL  %s: want exit %s and "%s", got exit %s\n%s\n' "$name" "$want" "$text" "$rc" "$out"; fail=$((fail+1))
  fi
}

rocq "$WORK/ok.v"; lean "$WORK/ok.lean"
echo "== positive control =="
expect "clean fixtures pass" 0 "RESULT: PASS" "$WORK/ok.v" "$WORK/ok.lean"

echo "== negative controls (each must fail the gate) =="
rocq "$WORK/axiom.v" holdsAll_sound \
  'Axiom cheat : False. Lemma holdsAll_sound : False. Proof. exact cheat. Qed. Print Assumptions holdsAll_sound.'
expect "a Rocq theorem resting on an axiom" 1 "rests on an assumption" "$WORK/axiom.v" "$WORK/ok.lean"

rocq "$WORK/admitted.v" sound_given \
  'Lemma sound_given : False. Proof. Admitted. Print Assumptions sound_given.'
expect "an admitted Rocq theorem" 1 "rests on an assumption" "$WORK/admitted.v" "$WORK/ok.lean"

rocq "$WORK/missing.v" outputs_match
expect "a Rocq theorem the record names is not printed" 1 "no assumption report for 'outputs_match'" "$WORK/missing.v" "$WORK/ok.lean"

rocq "$WORK/broken.v" "" 'Lemma broken : False. Proof. exact I. Qed.'
expect "a Rocq file that does not compile" 1 "Rocq leg: coqc failed" "$WORK/broken.v" "$WORK/ok.lean"

lean "$WORK/sorry.lean" holdsAll_sound 'theorem holdsAll_sound : False := sorry'
echo '#print axioms Fixture.holdsAll_sound' >> "$WORK/sorry.lean"
expect "a Lean theorem left as sorry" 1 "rests on an axiom" "$WORK/ok.v" "$WORK/sorry.lean"

lean "$WORK/classical.lean" sound_given 'theorem sound_given (p : Prop) : p ∨ ¬p := Classical.em p'
echo '#print axioms Fixture.sound_given' >> "$WORK/classical.lean"
expect "a Lean theorem using Classical.choice" 1 "rests on an axiom" "$WORK/ok.v" "$WORK/classical.lean"

lean "$WORK/missing.lean" candidates_match
expect "a Lean theorem the record names is not printed" 1 "no assumption report for 'candidates_match'" "$WORK/ok.v" "$WORK/missing.lean"

lean "$WORK/broken.lean" "" 'theorem broken : False := trivial'
expect "a Lean file that does not compile" 1 "Lean leg: lean failed" "$WORK/ok.v" "$WORK/broken.lean"

printf '\n%s\n' "PASS=$pass FAIL=$fail"
[ "$fail" -eq 0 ] || exit 1
