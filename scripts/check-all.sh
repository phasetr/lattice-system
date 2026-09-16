#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}

"$ROOT/scripts/check-tree.sh" "$ROOT"
"$ROOT/scripts/check-registry.sh" "$ROOT"
"$ROOT/scripts/check-policy.sh" "$ROOT"
"$ROOT/scripts/test-checkers.sh" "$ROOT"
"$ROOT/scripts/check-base-diff.sh" "$ROOT" "${BASE_REF:-HEAD^}"

echo "check-all: ok"
