#!/usr/bin/env bash
# audit-helpers.sh — grep helpers for the Lean recurring-pattern audit (Tier1/Tier2).
#
# These only surface CANDIDATES. What is forbidden is the entity (a duplicate
# statement / a zero-reference decorative declaration), not the name; the final
# judgement is made by reading statements (audit_gate.py and the lean-audit-tier*
# subagents). This script does the cheap first-pass extraction only.
#
# usage:
#   scripts/audit-helpers.sh dead-decls        # zero-reference theorem/lemma candidates
#   scripts/audit-helpers.sh oversize [N]      # files over N lines (default 700)
#   scripts/audit-helpers.sh suffix-hints      # name hints for hunting duplicates
set -euo pipefail

ROOT="${LEAN_SRC_ROOT:-LatticeSystem}"
SUFFIX_HINTS='_structural|_legacy|_alt|_mirror|_doubled|_factored|_twin|_copy|_old|_aux2|_aux3|_variant|_tmp'

cmd="${1:-help}"; shift || true

case "$cmd" in
  dead-decls)
    # Zero-reference = a theorem/lemma name that appears only at its declaration.
    # A first-pass decorative-decl candidate; exclude capstones / @[simp] / tests
    # via the allowlist when judging.
    grep -rEoh '\b(theorem|lemma)[[:space:]]+[A-Za-z0-9_]+' "$ROOT" '--include=*.lean' \
      | awk '{print $2}' | sort -u \
      | while read -r name; do
          n=$(grep -rEw "$name" "$ROOT" '--include=*.lean' | wc -l | tr -d ' ')
          # The declaration line is always one occurrence; total <=1 means zero-ref.
          [ "$n" -le 1 ] && echo "$name"
        done
    ;;
  oversize)
    N="${1:-700}"
    find "$ROOT" -name '*.lean' -exec wc -l {} + \
      | awk -v n="$N" '$2!="total" && $1>n {print $1"\t"$2}' | sort -rn
    ;;
  suffix-hints)
    # NOTE: not a blocking criterion; only an entry point for hunting duplicate statements.
    grep -rEnoh "\b(theorem|lemma|def)[[:space:]]+[A-Za-z0-9_]*($SUFFIX_HINTS)[A-Za-z0-9_]*" \
      "$ROOT" '--include=*.lean' | sort -u
    ;;
  *)
    sed -n '1,15p' "$0"
    ;;
esac
