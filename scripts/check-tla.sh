#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# check-tla.sh — the TLA+ gate for the engine model (HD-1, re-derived 2026-10-14).
#
#   1. TLC (tla2tools.jar) is fetched at a pinned release into _build/tools and
#      its SHA-256 checked; a mismatch deletes the jar and fails, never runs it;
#   2. Engine.cfg — the engine as it is — must model-check with no error:
#      TypeOK, Guarantee, Budget and CompletedBounded as invariants,
#      CompleteOnlyFromZeroCount and StopTerminal as properties;
#   3. Original.cfg — the same model plus the root-commit engine's
#      caller-asserted `update <remaining>` — must FAIL with Guarantee
#      violated. That is the Incident as a counterexample, and the negative
#      control: a gate whose model cannot fail is not checking anything.
#
# Needs java and curl (or a jar already in _build/tools). Exit 0 only when
# both hold.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
ROOT="$PWD"

TLA_VERSION=v1.8.0
TLA_SHA256=0f56d6a813368c48008dfbecb23a73ab43a4a5e1bf09f026782a674aa9d4b3c9
jar="_build/tools/tla2tools-$TLA_VERSION.jar"
spec_dir=verification/proofs/tlaplus

command -v java >/dev/null 2>&1 || { echo "FAIL: java not found; the TLA+ gate cannot be skipped." >&2; exit 1; }

if [ ! -f "$jar" ]; then
  mkdir -p _build/tools
  curl -sSfL --retry 3 -o "$jar.part" \
    "https://github.com/tlaplus/tlaplus/releases/download/$TLA_VERSION/tla2tools.jar"
  mv "$jar.part" "$jar"
fi
if ! echo "$TLA_SHA256  $jar" | sha256sum -c --status -; then
  rm -f "$jar"
  echo "FAIL: $jar does not match the pinned SHA-256; removed, not run." >&2
  exit 1
fi
echo "tla2tools $TLA_VERSION @ sha256:$TLA_SHA256"

meta="$(mktemp -d)"
trap 'rm -rf "$meta"' EXIT
tlc() { # tlc <config> <log>; prints TLC's exit code
  set +e
  (cd "$spec_dir" && java -XX:+UseParallelGC -cp "$ROOT/$jar" tlc2.TLC \
     -config "$1" -workers 1 -noGenerateSpecTE -metadir "$meta/$1" Engine.tla) >"$2" 2>&1
  echo $?
  set -e
}

echo
echo "=== Engine.cfg: the engine as it is ==="
log="$meta/engine.log"; rc="$(tlc Engine.cfg "$log")"
grep -E 'states generated|depth of the complete' "$log" | sed 's/^/  /'
if [ "$rc" -ne 0 ] || ! grep -q 'Model checking completed. No error has been found.' "$log"; then
  cat "$log"
  echo "FAIL: TLC found an error in the engine model (exit $rc)" >&2
  exit 1
fi
echo "  PASS: no error found"

echo
echo "=== Original.cfg: the root-commit engine (negative control) ==="
log="$meta/original.log"; rc="$(tlc Original.cfg "$log")"
if [ "$rc" -eq 0 ] || ! grep -q 'Invariant Guarantee is violated' "$log"; then
  cat "$log"
  echo "FAIL: the original engine was not refuted; the model cannot tell the engines apart" >&2
  exit 1
fi
sed -n '/The behavior up to this point is:/,/^$/p;/UpdateAsserted/,/^$/p' "$log" | sed 's/^/  /' | head -24
echo "  PASS: Guarantee violated, as it must be"
echo
echo "RESULT: PASS -- engine model checked; original engine refuted"
