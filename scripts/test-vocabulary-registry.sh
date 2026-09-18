#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-system-tests.vocabulary-registry.XXXXXX")
trap 'rm -rf "$TMP"' EXIT
export LATTICE_TEST_ROOT=$TMP
mkdir -p "$TMP/good"
cp -R "$ROOT/registry" "$TMP/good/registry"
mutate_review_ref() {
  local file=$1
  awk -F '\t' -v OFS='\t' 'NR==1 {print; next} {$3="VOCABULARY-FIXTURE"; print}' "$file" > "$file.tmp"
  mv "$file.tmp" "$file"
}
mutate_review_ref "$TMP/good/registry/claim-vocabulary-review.tsv"

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
mutate "$TMP/good/registry/claim-vocabulary-review.tsv" "$TMP/uncovered/registry/claim-vocabulary-review.tsv" 'NR!=2 {print}'
expect_fail uncovered "active claim lacks exactly one vocabulary review" "$ROOT/scripts/check-registry.sh" "$TMP/uncovered"

variant unused
mutate "$TMP/good/registry/vocabulary.tsv" "$TMP/unused/registry/vocabulary.tsv" 'NR==1 {print; print "VO-LS-00001\tLatticeSystem.Vocabulary.Unused\tLatticeSystem.Vocabulary.Quantum\tabbrev\tprimary\tNONE\tbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\tcccccccccccccccccccccccccccccccccccccccc\tlinear_algebra\tnone"; next} {print}'
expect_fail unused "unused vocabulary declaration" "$ROOT/scripts/check-registry.sh" "$TMP/unused"

variant bad-import
mutate "$TMP/good/registry/imports.tsv" "$TMP/bad-import/registry/imports.tsv" 'NR==2 {$3="Lean.Meta"} {print}'
expect_fail bad-import "unauthorized external import" "$ROOT/scripts/check-registry.sh" "$TMP/bad-import"

variant slices
printf '%s\n' $'SL-TASAKI2020-0001\t1\tCL-TASAKI2020-0001' $'SL-TASAKI2020-0002\t1\tCL-TASAKI2020-0002' >> "$TMP/slices/registry/slices.tsv"
expect_fail slices "vocabulary requires header-only slices.tsv" "$ROOT/scripts/check-registry.sh" "$TMP/slices"
"$ROOT/scripts/check-census.sh" --fixture "$TMP/slices" >/dev/null

variant census-bad
mutate "$TMP/good/registry/pages.tsv" "$TMP/census-bad/registry/pages.tsv" 'NR==2 {$8="pending"} {print}'
expect_fail census-regression "page census is not exact" "$ROOT/scripts/check-census.sh" --fixture "$TMP/census-bad" 2 2 1

echo "test-vocabulary-registry: ok"
