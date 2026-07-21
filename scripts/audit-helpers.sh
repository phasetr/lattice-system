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
#   scripts/audit-helpers.sh undocumented-dead [FILE|-]  # of those, the ones the
#                                              # docs do not record ('-' = stdin)
#   scripts/audit-helpers.sh oversize [N]      # files over N lines (default 700)
#   scripts/audit-helpers.sh suffix-hints      # name hints for hunting duplicates
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

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
          # `if` rather than `[ ... ] && echo`: as the body's last command the
          # latter exits 1 for every referenced name, which under `set -e` aborts
          # the loop at the first one and silently truncates the list.
          if [ "$n" -le 1 ]; then echo "$name"; fi
        done
    ;;
  undocumented-dead)
    # Zero-reference AND not written up in docs/index.md / tex/proof-guide.tex.
    # The docs record whole families in a compressed notation, so the match must
    # expand it (scripts/audit/docs_names.py); an exact grep mis-reports
    # `spinOneRot{1,2,3}_zero` and friends as undocumented.
    # With FILE ('-' = stdin) it filters a precomputed list ("… name" per line);
    # with no argument it recomputes dead-decls (slow). The source is an explicit
    # argument, never a tty test, so this behaves the same under CI/automation.
    SRC="${1:-}"
    if [ -n "$SRC" ]; then
      python3 "$HERE/audit/docs_names.py" --filter "$SRC"
    else
      "$0" dead-decls | python3 "$HERE/audit/docs_names.py" --filter -
    fi
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
