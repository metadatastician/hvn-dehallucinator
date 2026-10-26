#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# engine_traces.sh <engine.hs> <out-file>
#
# Runs the REAL engine (compiled from <engine.hs>) over command sequences and
# records what it did. Every trace starts with `init 2`; then:
#   * all sequences of three tokens from the alphabet below (exhaustive);
#   * the same, but with a first token that sets the baseline to 1 or 3
#     (i1 i3 f1 f3), so that every baseline 0..3 is tried;
#   * hand-written traces: the breaker at each baseline, regression, refusal,
#     demotion and recovery;
#   * DIFF_RANDOM (default 300) seeded pseudo-random sequences of 14 tokens.
#
# Tokens:  i<n> init n | f<n> init-from, verifier counts n | ff init-from,
#          verifier fails | at attempt | u<n> update, verifier counts n |
#          uf update, verifier fails | v<n> verify, verifier counts n | st status
#
# Output, one line per trace:  tok tok ...|exit,total,completed,attempts,STATUS;...
# The verifier is a stub that prints the count in $HARVARD_ROOT/world, or exits 1
# when the file says `fail`: the harness, not the engine, controls the world.
set -euo pipefail
src="$1"; out="$2"
work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
mkdir -p "$work/root/engine" "$work/root/state" "$work/target" "$work/o"
cp "$src" "$work/root/engine/Engine.hs"
cat > "$work/root/engine/verify_register.sh" <<'V'
#!/usr/bin/env bash
w="$(cat "$HARVARD_ROOT/world")"
[ "$w" = fail ] && { echo "stub verifier: told to fail" >&2; exit 1; }
echo "$w"
V
chmod +x "$work/root/engine/verify_register.sh"
ghc -O0 -v0 -outputdir "$work/o" -o "$work/Engine" "$work/root/engine/Engine.hs"
export HARVARD_ROOT="$work/root"
root="$work/root"; T="$work/target"; E="$work/Engine"

ALPHABET=(i2 i0 f0 f2 ff at u0 u1 u2 u3 uf v1 st)
WEIGHTED=(i2 i0 i1 i3 f0 f2 f1 f3 ff at at at at at u0 u0 u1 u2 u3 uf uf v1 st)

run_token() { # run_token <token>; prints the exit code
  local t="$1" rc=0
  case "$t" in
    i[0-9]*) timeout 20 "$E" init "${t#i}" >/dev/null 2>&1 || rc=$? ;;
    f[0-9]*) echo "${t#f}" > "$root/world"; timeout 20 "$E" init-from "$T" >/dev/null 2>&1 || rc=$? ;;
    ff)      echo fail     > "$root/world"; timeout 20 "$E" init-from "$T" >/dev/null 2>&1 || rc=$? ;;
    at)      timeout 20 "$E" attempt >/dev/null 2>&1 || rc=$? ;;
    u[0-9]*) echo "${t#u}" > "$root/world"; timeout 20 "$E" update "$T" >/dev/null 2>&1 || rc=$? ;;
    uf)      echo fail     > "$root/world"; timeout 20 "$E" update "$T" >/dev/null 2>&1 || rc=$? ;;
    v[0-9]*) echo "${t#v}" > "$root/world"; timeout 20 "$E" verify "$T" >/dev/null 2>&1 || rc=$? ;;
    st)      timeout 20 "$E" status >/dev/null 2>&1 || rc=$? ;;
    *) echo "engine_traces: unknown token $t" >&2; exit 2 ;;
  esac
  echo "$rc"
}

trace() { # trace <token>...; appends one line to $out
  local toks=("i2" "$@") obs="" rc L
  rm -f "$root/state/state.txt"
  for t in "${toks[@]}"; do
    rc="$(run_token "$t")"
    mapfile -t L < "$root/state/state.txt"
    obs+="$rc,${L[0]},${L[1]},${L[2]},${L[3]};"
  done
  echo "${toks[*]}|${obs%;}" >> "$out"
}

: > "$out"
# 1. exhaustive, three tokens
for a in "${ALPHABET[@]}"; do for b in "${ALPHABET[@]}"; do for c in "${ALPHABET[@]}"; do
  trace "$a" "$b" "$c"
done; done; done
# 1b. exhaustive, three tokens, the first setting the baseline to 1 or 3
for a in i1 i3 f1 f3; do for b in "${ALPHABET[@]}"; do for c in "${ALPHABET[@]}"; do
  trace "$a" "$b" "$c"
done; done; done
# 2. hand-written: the breaker, regression, refusal, demotion and recovery
trace at at at at at at at at at at
trace i0 at at at at at at at at
trace u0 at at at at at at at at u0 i2 at u0
trace u0 u2 uf u0 uf at
trace f2 u0 uf uf u1 u0 at st v1
trace i0 u0 u0 u0 u0 u0 u0 u0 u0
# the breaker at baselines 1 and 3 (it trips on attempt total + 6)
trace i1 at at at at at at at at
trace f1 at at at at at at at at
trace i3 at at at at at at at at at at
trace f3 u1 at at at at at at at at at at i3 at
# 3. seeded pseudo-random
seed=20261026; n="${DIFF_RANDOM:-300}"
for ((k = 0; k < n; k++)); do
  toks=()
  for ((j = 0; j < 14; j++)); do
    seed=$(( (seed * 1103515245 + 12345) % 2147483648 ))
    toks+=("${WEIGHTED[$(( (seed >> 8) % ${#WEIGHTED[@]} ))]}")
  done
  trace "${toks[@]}"
done
echo "engine_traces: $(wc -l < "$out") traces from $src" >&2
