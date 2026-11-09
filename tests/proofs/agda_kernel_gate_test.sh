#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# Negative controls for scripts/check-agda-kernel.sh. The gate claims that an
# expected-rejection fixture passes only when Agda refuses it with a type error
# at its own declaration. Each way that claim could be vacuous is fed to it:
# a fixture Agda accepts, a fixture that fails for a scope error instead of a
# type error, and an empty fixture set. The positive control is tests/reject.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
GATE="$REPO_ROOT/scripts/check-agda-kernel.sh"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

fixture() { # fixture <dir> <Module> <body>
  mkdir -p "$WORK/$1"
  { echo '{-# OPTIONS --safe --without-K #-}'; echo "module $2 where"
    echo 'open import ResidualEvidence.Prelude'; echo 'open import Fibre'; echo "$3"; } > "$WORK/$1/$2.agda"
}

pass=0; fail=0
expect() { # expect <name> <want-exit> <want-text> [reject-dir]
  local name="$1" want="$2" text="$3" out rc
  shift 3
  out="$(bash "$GATE" "$@" 2>&1)"; rc=$?
  if [ "$rc" = "$want" ] && grep -qF -- "$text" <<<"$out"; then
    printf '  PASS  %s (exit %s)\n' "$name" "$rc"; pass=$((pass+1))
  else
    printf '  FAIL  %s: want exit %s and "%s", got exit %s\n%s\n' "$name" "$want" "$text" "$rc" "$out"; fail=$((fail+1))
  fi
}

echo "== positive control =="
expect "tests/reject: the Incident is refused" 0 "refused AssertedComplete"

echo "== negative controls (each must fail the gate) =="
fixture accepted Accepted 'ok : update incident incident-measured ≡ task 16 0 1 running
ok = refl'
expect "a fixture Agda accepts" 1 "invalid proof accepted: Accepted" "$WORK/accepted"

fixture scope Scope 'bad : Disagreeing-typo
bad = incident-witness'
expect "a fixture refused for a scope error, not a type error" 1 "unexpected failure while checking Scope" "$WORK/scope"

# A genuine refusal, but not where the fixture says its counterexample is:
# the first clause is refused (1 is not 0), the marker is on the second.
fixture offmark Offmark 'open import Agda.Builtin.Nat using (Nat)
bad : (n : Nat) → n ≡ 0
bad (suc n) = refl
bad zero    = refl   -- refused here'
expect "a fixture refused away from its marked line" 1 "not at its marked line" "$WORK/offmark"

fixture nomark Nomark 'bad : incident-measured ≡ 0
bad = refl'
expect "a fixture with no marked line" 1 "must mark exactly one line" "$WORK/nomark"

mkdir -p "$WORK/empty"
expect "an empty fixture set" 1 "no expected-rejection modules" "$WORK/empty"

printf '\n%s\n' "PASS=$pass FAIL=$fail"
[ "$fail" -eq 0 ] || exit 1
