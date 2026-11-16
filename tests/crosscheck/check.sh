#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# check.sh: the mechanical cross-check behind docs/status/RECHECK-CORRESPONDENCE.adoc.
#
# Each prover's kernel computes the explorer table and must equal one shared
# literal, tests/crosscheck/explorer-table.txt. For each of the 546
# configurations, in `allConfigs` order, the table holds the presence verdict,
# the identity status and every candidate world:
#
#   Agda  residual-evidence-types' own Finite.Checker (presence, identity,
#         enumerate, allConfigs), at the pin in scripts/fetch-siblings.sh,
#         by `refl` under the kernel flags;
#   Rocq  the restatement in verification/proofs/coq/Haruspex.v, by vm_compute;
#   Lean  the restatement in verification/proofs/lean4/Haruspex.lean, by kernel
#         reduction (`decide +kernel`), one declaration per residual.
#
# The restatements cannot drift from the original without failing here. Each
# leg also proves, in its own kernel, that Haruspex decides what its checker
# decides (candidates_match, presence_match, identity_match, outputs_match).
# So the three Haruspex checkers agree on all 546 configurations. This covers
# the finite checker's definitions only. The general Check statements are
# compared in the correspondence record.
#
# Negative controls: the same three checks run against a copy of the table with
# one verdict changed, and each must fail. Exit 0 only when every leg passes and
# every control fails.
set -uo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."
export LC_ALL=C.UTF-8 LANG=C.UTF-8
agda="${AGDA:-agda}"; coqc="${COQC:-coqc}"; lean="${LEAN:-lean}"
table=tests/crosscheck/explorer-table.txt
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
for t in "$agda" "$coqc" "$lean"; do
  command -v "$t" >/dev/null 2>&1 || { echo "FAIL: '$t' not found. The cross-check cannot be skipped." >&2; exit 1; }
done
bash scripts/fetch-siblings.sh >/dev/null || { echo "FAIL: could not fetch the pinned siblings" >&2; exit 1; }
ret=_build/dependencies/residual-evidence-types/src

agda_leg() { # agda_leg <table> <dir>
  mkdir -p "$2"
  { cat <<'EOF'
{-# OPTIONS --safe --without-K --cubical-compatible #-}
module CrossCheck where
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import ResidualEvidence.Prelude using (_×_; _,_)
open import ResidualEvidence.Finite.Row
  using (Verdict; entailed; refuted; unresolved; inconsistent;
         IdStatus; identified; unidentified; no-candidate)
open import ResidualEvidence.Finite.Checker
  using (Config; World; enumerate; presence; identity; allConfigs; map)
EOF
    bash tests/crosscheck/render.sh agda "$1"
    cat <<'EOF'
row : Config → Verdict × IdStatus × List World
row cfg = presence cfg , identity cfg , enumerate cfg

matches : map row allConfigs ≡ table
matches = refl
EOF
  } > "$2/CrossCheck.agda"
  "$agda" --safe --without-K --cubical-compatible --no-libraries --ignore-interfaces \
    -i "$2" -i "$ret" "$2/CrossCheck.agda" > "$2/agda.log" 2>&1
}

rocq_leg() { # rocq_leg <table> <dir>
  mkdir -p "$2"
  { cat verification/proofs/coq/Haruspex.v
    bash tests/crosscheck/render.sh rocq "$1"
    cat <<'EOF'
Definition row (cfg : Config) : Verdict * IdStatus * list World :=
  (presenceC cfg, identityC cfg, enumerate cfg).
Lemma table_matches : map row allConfigs = table.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions table_matches.
EOF
  } > "$2/CrossCheck.v"
  (cd "$2" && "$coqc" CrossCheck.v > rocq.log 2>&1) &&
    [ "$(tail -1 "$2/rocq.log")" = "Closed under the global context" ]
}

lean_leg() { # lean_leg <table> <dir>
  mkdir -p "$2"
  local src=verification/proofs/lean4/Haruspex.lean end i r
  local rs=("negsuc 5" "negsuc 4" "negsuc 3" "negsuc 2" "negsuc 1" "negsuc 0" "pos 0" "pos 1" "pos 2" "pos 3" "pos 4" "pos 5" "pos 6")
  end="$(grep -n '^end Haruspex$' "$src" | cut -d: -f1)"
  { head -n $((end - 1)) "$src"
    echo 'def rowL (cfg : Config) : Verdict × IdStatus × List World := (presenceC cfg, identityC cfg, enumerate cfg)'
    bash tests/crosscheck/render.sh lean "$1"
    for i in "${!rs[@]}"; do
      echo "theorem table_matches_$i : mapL rowL (configsFor (.${rs[$i]})) = tableChunk$i := by decide +kernel"
    done
    echo 'end Haruspex'
    for i in "${!rs[@]}"; do echo "#print axioms Haruspex.table_matches_$i"; done
  } > "$2/CrossCheck.lean"
  (cd "$2" && "$lean" CrossCheck.lean > lean.log 2>&1) &&
    [ "$(grep -c "does not depend on any axioms" "$2/lean.log")" = "${#rs[@]}" ] &&
    ! grep -q "depends on axioms" "$2/lean.log"
}

pass=0; fail=0
want() { # want <name> <pass|fail> <command...>
  local name="$1" expect="$2"; shift 2
  if "$@"; then got=pass; else got=fail; fi
  if [ "$got" = "$expect" ]; then printf '  PASS  %s\n' "$name"; pass=$((pass+1))
  else printf '  FAIL  %s: expected the check to %s\n' "$name" "$expect"; fail=$((fail+1)); fi
}

echo "== each kernel computes the explorer table ($(grep -vc '^#' "$table") configurations) =="
want "Agda: residual-evidence-types' Finite.Checker equals the table" pass agda_leg "$table" "$work/agda"
want "Rocq: the restated checker equals the table, no axioms" pass rocq_leg "$table" "$work/rocq"
want "Lean: the restated checker equals the table, no axioms" pass lean_leg "$table" "$work/lean"

# Negative control: one verdict changed, in the first row.
sed '0,/^[^#].*| entailed /s/| entailed /| refuted /' "$table" > "$work/mutant.txt"
cmp -s "$table" "$work/mutant.txt" && { echo "FAIL: the mutant table is unchanged" >&2; exit 1; }
echo "== negative controls: one verdict changed (each must be refused) =="
want "Agda refuses the changed table" fail agda_leg "$work/mutant.txt" "$work/agda-m"
want "Rocq refuses the changed table" fail rocq_leg "$work/mutant.txt" "$work/rocq-m"
want "Lean refuses the changed table" fail lean_leg "$work/mutant.txt" "$work/lean-m"

printf '\n%s\n' "PASS=$pass FAIL=$fail"
[ "$fail" -eq 0 ]
