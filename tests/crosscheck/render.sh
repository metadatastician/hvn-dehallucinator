#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# render.sh <agda|rocq|lean> [table]
#
# Renders the explorer table (default tests/crosscheck/explorer-table.txt) as a
# literal in one prover's syntax: one row per configuration, in table order,
# each row (verdict, id-status, candidate worlds). For Lean the rows are grouped
# by residual, 42 to a group, one definition per group. The rendering is
# syntax only: integers, constructor names, pairs and lists. It computes nothing.
set -euo pipefail
prover="$1"
table="${2:-$(dirname -- "${BASH_SOURCE[0]}")/explorer-table.txt}"
case "$prover" in agda|rocq|lean) ;; *) echo "usage: render.sh <agda|rocq|lean> [table]" >&2; exit 2 ;; esac

grep -v '^#' "$table" | awk -v P="$prover" '
function zint(v) {
  if (P == "agda") return (v < 0) ? "(negsuc " (-v - 1) ")" : "(pos " v ")"
  if (P == "rocq") return (v < 0) ? "(negsuc " (-v - 1) ")" : "(pos " v ")"
  return (v < 0) ? "(.negsuc " (-v - 1) ")" : "(.pos " v ")"
}
function verdict(s) { return (P == "lean") ? "." s : s }
function ids(s) {
  if (P == "rocq" && s == "no-candidate") s = "no_candidate"
  if (P == "lean") { if (s == "no-candidate") s = "no_candidate"; return "." s }
  return s
}
function worlds(str,   n, a, i, p, out, sep) {
  n = split(str, a, " ")
  if (P == "agda") {
    out = ""
    for (i = 1; i <= n; i++) { split(a[i], p, ","); out = out "(" zint(p[1]) " , " zint(p[2]) ") ∷ " }
    return "(" out "[])"
  }
  sep = (P == "rocq") ? "; " : ", "
  out = ""
  for (i = 1; i <= n; i++) { split(a[i], p, ","); out = out (i > 1 ? sep : "") "(" zint(p[1]) ", " zint(p[2]) ")" }
  return "[" out "]"
}
{
  split($0, f, "|")
  split(f[2], vi, " ")
  w = f[3]; gsub(/^ +| +$/, "", w)
  if (P == "agda") row = "(" verdict(vi[1]) " , " ids(vi[2]) " , " worlds(w) ")"
  else             row = "(" verdict(vi[1]) ", " ids(vi[2]) ", " worlds(w) ")"
  rows[NR] = row
}
END {
  if (P == "agda") {
    print "table : List (Verdict × IdStatus × List World)"
    print "table ="
    for (i = 1; i <= NR; i++) print "  " rows[i] " ∷"
    print "  []"
  } else if (P == "rocq") {
    print "Definition table : list (Verdict * IdStatus * list World) := ["
    for (i = 1; i <= NR; i++) print "  " rows[i] (i < NR ? ";" : "")
    print "]."
  } else {
    if (NR % 42 != 0) { print "render.sh: expected 42 rows per residual, got " NR > "/dev/stderr"; exit 1 }
    for (g = 0; g < NR / 42; g++) {
      print "def tableChunk" g " : List (Verdict × IdStatus × List World) := ["
      for (i = 1; i <= 42; i++) print "  " rows[g * 42 + i] (i < 42 ? "," : "")
      print "]"
    }
  }
}'
