#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}

# Checks of the actual current corpus, distinct from checker mutation fixtures.
for gate in tree schema sources order lifecycle registry census source-items policy; do
  "$ROOT/scripts/check-$gate.sh" "$ROOT"
done
{ IFS= read -r _; IFS= read -r phase; } < "$ROOT/registry/phase.tsv"
if [[ "$phase" == vocabulary || $(awk 'END { print NR }' "$ROOT/registry/modules.tsv") -gt 1 ]]; then
  "$ROOT/scripts/check-vocabulary.sh" "$ROOT"
fi
"$ROOT/scripts/check-skeleton.sh" "$ROOT"
python3 "$ROOT/scripts/generate-public-docs.py" --test --root "$ROOT"
python3 "$ROOT/scripts/generate-public-docs.py" --check --root "$ROOT"
echo "check-current: ok"
