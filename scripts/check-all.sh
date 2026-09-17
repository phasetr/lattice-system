#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}

"$ROOT/scripts/check-tree.sh" "$ROOT"
"$ROOT/scripts/check-registry.sh" "$ROOT"
"$ROOT/scripts/check-census.sh" "$ROOT"
"$ROOT/scripts/check-policy.sh" "$ROOT"
{ IFS= read -r _; IFS= read -r phase; } < "$ROOT/registry/phase.tsv"
if [[ "$phase" == vocabulary || $(awk 'END { print NR }' "$ROOT/registry/modules.tsv") -gt 1 ]]; then
  "$ROOT/scripts/check-vocabulary.sh" "$ROOT"
fi
"$ROOT/scripts/test-checkers.sh" "$ROOT"
"$ROOT/scripts/check-base-diff.sh" "$ROOT" "${BASE_REF:-HEAD^}"

echo "check-all: ok"
