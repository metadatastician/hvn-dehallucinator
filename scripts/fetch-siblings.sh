#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# Fetch the sibling proof repositories this repository consumes into
# _build/dependencies with plain git, each at a recorded commit (the pattern of
# residual-evidence-types' own scripts/fetch-siblings.sh). A checkout that does
# not resolve to the pinned commit is a failure, never a fallback to whatever
# the remote currently serves. Definitions are consumed from the pinned
# checkout, never re-declared here.
#
# Re-pin deliberately, one commit per pin, and record the pin in the header of
# every module that imports the sibling.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
deps=_build/dependencies

fetch() {
  local name=$1 repo=$2 sha=$3 dir
  dir=$deps/$name
  if [[ "$(git -C "$dir" rev-parse HEAD 2>/dev/null || true)" == "$sha" ]]; then
    echo "$name @ $sha (already present)"
    return
  fi
  if [[ ! -d "$dir/.git" ]]; then
    git init -q "$dir"
    git -C "$dir" remote add origin "https://github.com/$repo.git"
  fi
  git -C "$dir" fetch -q --depth 1 origin "$sha"
  git -C "$dir" checkout -q --detach FETCH_HEAD
  test "$(git -C "$dir" rev-parse HEAD)" = "$sha"
  echo "$name @ $sha"
}

mkdir -p "$deps"
# Evidence-refined fibres, empty cases, constructive refutation (2026-10-12).
fetch residual-evidence-types hyperpolymath/residual-evidence-types 97244f5cb63bd6697caff261b187b62e9788b692
