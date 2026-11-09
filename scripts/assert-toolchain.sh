#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# assert-toolchain.sh <tool>...   tool in: agda | ghc | java
#
# The proof toolchains are installed from the Ubuntu 24.04 archive, not from
# the repository's Guix manifest: guix.scm is the template's and carries none
# of them. That is a deviation under standards PROOF-POLICY section 6, recorded
# in docs/status/PROOF-STATUS.adoc. The policy requires the run to assert the
# version it got and fail on a mismatch; this script is that assertion.
#
#   agda  package agda-bin at exactly 2.6.3-1build1, and /usr/bin/agda at the
#         recorded SHA-256 (the noble build, the one the MANIFEST was
#         ground-truthed with);
#   ghc   package ghc at exactly 9.4.7-3, and /usr/bin/ghc-9.4.7 at its SHA-256;
#   java  package openjdk-21-jre-headless (any security build) and a Java 21
#         runtime at $JAVA (default java). Its digest is printed, not pinned:
#         the archive ships security rebuilds every few weeks.
#
# A move of any pin is a reviewed change to this file and to the ledger.
set -euo pipefail

fail() { echo "FAIL: $*" >&2; exit 1; }

want_pkg() { # want_pkg <package> <version or "any">
  local got
  got="$(dpkg-query -W -f='${Version}' "$1" 2>/dev/null)" || fail "package $1 is not installed"
  [ "$2" = any ] || [ "$got" = "$2" ] || fail "package $1 is $got, pinned $2"
  echo "  $1 $got"
}

want_sha() { # want_sha <file> <sha256>
  local got
  [ -f "$1" ] || fail "$1 not found"
  got="$(sha256sum "$1" | cut -d' ' -f1)"
  [ "$got" = "$2" ] || fail "$1 has sha256 $got, pinned $2"
  echo "  $1 sha256:$got"
}

[ "$#" -gt 0 ] || fail "usage: assert-toolchain.sh agda|ghc|java ..."
for tool in "$@"; do
  echo "== $tool"
  case "$tool" in
    agda)
      want_pkg agda-bin 2.6.3-1build1
      want_sha /usr/bin/agda 852806142a15951f667df303c73cfce5f4123218ce6e1f1b29acaddc242af00d
      [ "$(agda --version)" = "Agda version 2.6.3" ] || fail "agda --version is not 'Agda version 2.6.3'"
      ;;
    ghc)
      want_pkg ghc 9.4.7-3
      want_sha /usr/bin/ghc-9.4.7 00d84327aa4d93ce55a576e75ad9306f216156dd213537b5a88b23500569a83e
      ;;
    java)
      want_pkg openjdk-21-jre-headless any
      java="${JAVA:-java}"
      major="$("$java" -version 2>&1 | sed -n 's/.*version "\([0-9]*\).*/\1/p' | head -1)"
      [ "$major" = 21 ] || fail "$java is Java $major, pinned 21"
      bin="$(readlink -f "$(command -v "$java")")"
      echo "  $bin Java $major sha256:$(sha256sum "$bin" | cut -d' ' -f1) (printed, not pinned)"
      ;;
    *) fail "unknown tool: $tool" ;;
  esac
done
echo "RESULT: PASS -- toolchain as pinned"
