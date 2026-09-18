#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
TMP=$(mktemp -d "$ROOT/fixtures/.vocabulary-registry.XXXXXX")
trap 'rm -rf "$TMP"' EXIT
cp -R "$ROOT/fixtures/registry-vocabulary-good" "$TMP/good"

expect_fail() {
  local label=$1 diagnostic=$2
  shift 2
  local output
  if output=$("$@" 2>&1); then echo "test-vocabulary-registry: expected failure: $label" >&2; exit 1; fi
  [[ "$output" == *"$diagnostic"* ]] || { echo "test-vocabulary-registry: wrong diagnostic: $label" >&2; echo "$output" >&2; exit 1; }
}
mutate() { awk -F '\t' -v OFS='\t' "$3" "$1" > "$2"; }
variant() { cp -R "$TMP/good" "$TMP/$1"; }

"$ROOT/scripts/check-registry.sh" "$TMP/good" >/dev/null

variant uncovered
mutate "$TMP/good/registry/claim-vocabulary-review.tsv" "$TMP/uncovered/registry/claim-vocabulary-review.tsv" 'NR!=3 {print}'
expect_fail uncovered "active claim lacks exactly one vocabulary review" "$ROOT/scripts/check-registry.sh" "$TMP/uncovered"

variant unused
printf '%s\n' $'VO-TASAKI2020-0002\tLatticeSystem.Fixture.Unused\tLatticeSystem.Fixture\tabbrev\tprimary\tNONE\tbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\tcccccccccccccccccccccccccccccccccccccccc\tlinear_algebra\tnone' >> "$TMP/unused/registry/vocabulary.tsv"
expect_fail unused "unused vocabulary declaration" "$ROOT/scripts/check-registry.sh" "$TMP/unused"

variant bad-import
mutate "$TMP/good/registry/imports.tsv" "$TMP/bad-import/registry/imports.tsv" 'NR==3 {$3="Lean.Meta"} {print}'
expect_fail bad-import "unauthorized external import" "$ROOT/scripts/check-registry.sh" "$TMP/bad-import"

variant slices
printf '%s\n' $'SL-TASAKI2020-0001\t1\tCL-TASAKI2020-0001' $'SL-TASAKI2020-0002\t1\tCL-TASAKI2020-0002' >> "$TMP/slices/registry/slices.tsv"
expect_fail slices "vocabulary requires header-only slices.tsv" "$ROOT/scripts/check-registry.sh" "$TMP/slices"
"$ROOT/scripts/check-census.sh" --fixture "$TMP/slices" 2 2 1 >/dev/null

variant census-bad
mutate "$TMP/good/registry/pages.tsv" "$TMP/census-bad/registry/pages.tsv" 'NR==2 {$8="pending"} {print}'
expect_fail census-regression "page census is not exact" "$ROOT/scripts/check-census.sh" --fixture "$TMP/census-bad" 2 2 1

echo "test-vocabulary-registry: ok"
