#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# difftest.sh -- HD-F-E: the models agree with engine/Engine.hs.
#
# 1. Run the real engine over thousands of command sequences, a verifier stub
#    standing in for the world (tests/difftest/engine_traces.sh).
# 2. Agda: generate one `refl` lemma per trace saying EngineCore.step, run along
#    the same commands, yields exactly what the engine did (state and exit code);
#    the proof kernel must accept all of them.
# 3. TLA+: TLC replays every trace against Engine.tla's own actions
#    (tests/difftest/TraceCheck.tla); every trace must be replayed to its end.
# 4. Negative controls: the check must FAIL on (a) a corrupted observation,
#    (b) an engine whose breaker slack is 6, (c) an engine that keeps COMPLETE
#    when the verifier fails. A comparison that cannot fail proves nothing.
#
# This ties the models to the engine on the traces tried, not for all inputs:
# HD-F-E is TESTED, not PROVEN. DIFF_RANDOM=<n> sets the random traces (300).
set -uo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL=C.UTF-8 LANG=C.UTF-8
D=tests/difftest
W="$(mktemp -d)"; trap 'rm -rf "$W"' EXIT
pass=0; fail=0
ok()  { printf '  PASS  %s\n' "$1"; pass=$((pass + 1)); }
bad() { printf '  FAIL  %s\n' "$1"; fail=$((fail + 1)); }

for tool in ghc agda java; do
  command -v "$tool" >/dev/null 2>&1 || { echo "FAIL: $tool not found; the differential test cannot be skipped." >&2; exit 1; }
done
bash scripts/fetch-siblings.sh >/dev/null || { echo "FAIL: fetch-siblings" >&2; exit 1; }
bash scripts/check-tla.sh >/dev/null || { echo "FAIL: scripts/check-tla.sh (it also fetches the pinned TLC jar)" >&2; exit 1; }
JAR="_build/tools/tla2tools-$(awk -F= '/^TLA_VERSION=/{print $2}' scripts/check-tla.sh).jar"

agda_check() { # agda_check <traces> -> 0: kernel accepts every lemma; 1: a lemma refused; 2: broken
  bash "$D/to_agda.sh" "$1" "$W/Diff.agda" || return 2
  local inc=(-i verification/proofs/agda -i "$W")
  for d in _build/dependencies/*/src; do [ -d "$d" ] && inc+=(-i "$d"); done
  agda "${inc[@]}" --safe --without-K --no-libraries --ignore-interfaces "$W/Diff.agda" >"$W/agda.log" 2>&1 && return 0
  grep -q " != " "$W/agda.log" && return 1   # a lemma refused: model and engine differ
  return 2                                      # anything else is a broken check, not a refusal
}

tla_check() { # tla_check <traces> -> 0: every trace replayed; 1: some not; 3: TLC itself failed
  local t="$W/tla"; rm -rf "$t"; mkdir -p "$t"
  bash "$D/to_tla.sh" "$1" "$t" || return 2
  cp verification/proofs/tlaplus/Engine.tla "$D/TraceCheck.tla" "$D/TraceCheck.cfg" "$t/"
  ( cd "$t" && java -XX:+UseParallelGC -cp "$OLDPWD/$JAR" tlc2.TLC -config TraceCheck.cfg \
      -workers 2 -metadir "$t/m" -dump "$t/dump" -deadlock TraceCheck.tla >"$t/tlc.log" 2>&1 )
  grep -q 'Model checking completed. No error has been found.' "$t/tlc.log" || return 3
  # a trace is replayed iff some state has tid = k and ptr = its length
  awk 'NR==FNR { len[$1] = $2; next }
       /^State / { if (tid != "" && ptr == len[tid]) seen[tid] = 1; tid = ""; ptr = "" }
       /\/\\ tid =/ { tid = $NF } /\/\\ ptr =/ { ptr = $NF }
       END { if (tid != "" && ptr == len[tid]) seen[tid] = 1
             for (k in len) if (!(k in seen)) { print k; miss++ }
             exit (miss > 0) }' "$t/lens.txt" "$t/dump.dump" >"$t/missing.txt"
}

echo "== real engine -> traces =="
bash "$D/engine_traces.sh" engine/Engine.hs "$W/traces.txt" || { echo "FAIL: engine_traces" >&2; exit 1; }
n="$(wc -l < "$W/traces.txt")"

echo "== the models accept what the engine did ($n traces) =="
agda_check "$W/traces.txt" && ok "EngineCore.step reproduces every trace (state and exit code)" \
  || { bad "EngineCore.step disagrees with the engine"; head -20 "$W/agda.log"; }
tla_check "$W/traces.txt" && ok "Engine.tla replays every trace to its end" \
  || { bad "Engine.tla cannot replay every trace"; head -5 "$W/tla/missing.txt" 2>/dev/null; tail -5 "$W/tla/tlc.log"; }

echo "== negative controls (each must be REFUSED) =="
# (a) one observation corrupted: `completed` at the last step of trace 7 is off by one
awk -F'|' 'NR == 7 { n = split($2, r, ";"); split(r[n], f, ","); f[3] += 1
                     r[n] = f[1] "," f[2] "," f[3] "," f[4] "," f[5]
                     s = r[1]; for (i = 2; i <= n; i++) s = s ";" r[i]; print $1 "|" s; next }
           { print }' "$W/traces.txt" > "$W/corrupt.txt"
refused() { [ "$1" -eq 1 ]; }  # only a genuine refusal counts; rc 2/3 is a broken check
agda_check "$W/corrupt.txt"; refused $? && ok "Agda refuses a corrupted observation" || { bad "Agda did not refuse a corrupted observation"; head -5 "$W/agda.log"; }
tla_check "$W/corrupt.txt"; refused $? && [ "$(cat "$W/tla/missing.txt")" = 7 ] \
  && ok "TLC refuses a corrupted observation, and exactly that trace (7)" || bad "TLC did not refuse exactly the corrupted trace"

mutant() { # mutant <name> <sed-expression>: engine drift must be caught by both models
  sed "$2" engine/Engine.hs > "$W/Mutant.hs"
  cmp -s engine/Engine.hs "$W/Mutant.hs" && { bad "mutant '$1' changed nothing (stale sed)"; return; }
  DIFF_RANDOM=40 bash "$D/engine_traces.sh" "$W/Mutant.hs" "$W/m.txt" 2>/dev/null || { bad "mutant '$1' did not build"; return; }
  agda_check "$W/m.txt"; refused $? && ok "Agda refuses mutant '$1'" || bad "Agda did not refuse mutant '$1'"
  tla_check "$W/m.txt"; refused $? && ok "TLC refuses mutant '$1' ($(wc -l < "$W/tla/missing.txt") traces not replayable)" || bad "TLC did not refuse mutant '$1'"
}
mutant "breaker slack 6"          's/^attemptSlack = 5/attemptSlack = 6/'
mutant "keeps COMPLETE on failed verifier" 's/st2 = if unconfirmed then st1 { status = statusRunning } else st1/st2 = st1/'

printf '\nPASS=%s FAIL=%s\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
