#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}

python3 "$ROOT/scripts/test-check-selected.py"
"$ROOT/scripts/check-current.sh" "$ROOT"
"$ROOT/scripts/test-checkers.sh" "$ROOT"
"$ROOT/scripts/test-skeleton-semantic.sh" "$ROOT"
"$ROOT/scripts/test-claim-corrections-runtime.sh" "$ROOT"
"$ROOT/scripts/test-content-amendments-runtime.sh" "$ROOT"
"$ROOT/scripts/test-base-diff-ci-runtime.sh" "$ROOT"
"$ROOT/scripts/check-base-diff-ci.sh" "$ROOT" "${BASE_REF:-HEAD^}"

echo "check-all: ok"
