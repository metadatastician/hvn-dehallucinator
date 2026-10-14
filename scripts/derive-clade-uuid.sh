#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# derive-clade-uuid.sh <forge-path> [domain]
#
# A repository identity under ESTATE-UUID-V8 profile C (hyperpolymath/standards
# docs/decisions/ADR-008-uuid-v8-estate-standard.adoc): the first 16 bytes of
# SHA-256( domain ":" name ), version nibble set to 8, variant bits set to 10.
# The name is the forge path the repository lives at TODAY, for example
#
#     derive-clade-uuid.sh github.com/metadatastician/hvn-dehallucinator
#
# and the domain defaults to `gv-clade-index`, the registry that owns
# repository identity. Same input, same uuid: anyone can recompute it, and a
# repository that moves must re-derive. tests/identity/clade_uuid_test.sh
# checks that .machine_readable/descriptiles/CLADE.a2ml agrees with this.
set -eu

name="${1:?usage: derive-clade-uuid.sh <forge-path> [domain]}"
domain="${2:-gv-clade-index}"
case "$domain" in
  *:*) echo "derive-clade-uuid: domain must not contain ':' (ADR-008 profile C)" >&2; exit 2 ;;
  '')  echo "derive-clade-uuid: empty domain" >&2; exit 2 ;;
esac

hex=$(printf '%s:%s' "$domain" "$name" | sha256sum | cut -c1-32)

# Byte 6 is hex characters 13-14: its high nibble becomes the version, 8.
# Byte 8 is hex characters 17-18: its top two bits become the variant, 10.
b6=$(printf '8%s' "$(printf '%s' "$hex" | cut -c14)")
b8=$(printf '%02x' $(( (0x$(printf '%s' "$hex" | cut -c17-18) & 0x3f) | 0x80 )))

printf '%s-%s-%s%s-%s%s-%s\n' \
  "$(printf '%s' "$hex" | cut -c1-8)" \
  "$(printf '%s' "$hex" | cut -c9-12)" \
  "$b6" "$(printf '%s' "$hex" | cut -c15-16)" \
  "$b8" "$(printf '%s' "$hex" | cut -c19-20)" \
  "$(printf '%s' "$hex" | cut -c21-32)"
