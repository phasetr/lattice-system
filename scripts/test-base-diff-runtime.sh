#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
PROJECT_ROOT=$(cd "$PROJECT_ROOT" && pwd)
TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-system-tests.base-diff.XXXXXX")
trap 'rm -rf "$TMP"' EXIT
export LATTICE_TEST_ROOT=$TMP

CHECK_REGISTRY="$PROJECT_ROOT/scripts/check-registry.sh"
CHECK_BASE_DIFF="$PROJECT_ROOT/scripts/check-base-diff.sh"
CASES="$TMP/base-diff"
mkdir -p "$CASES" "$TMP/production"
cp -R "$PROJECT_ROOT/registry" "$TMP/production/registry"

baseline_digest() {
  find "$TMP/production/registry" -type f -print0 | LC_ALL=C sort -z |
    xargs -0 shasum | shasum | awk '{print $1}'
}
BASELINE_DIGEST=$(baseline_digest)

expect_pass() {
  local label=$1
  shift
  local output
  if ! output=$("$@" 2>&1); then
    echo "test-base-diff-runtime: expected pass: $label" >&2
    echo "$output" >&2
    exit 1
  fi
}

expect_fail() {
  local label=$1
  shift
  local diagnostic= output
  if [[ ${1:-} == --diagnostic ]]; then
    [[ $# -ge 3 ]] || {
      echo "test-base-diff-runtime: missing diagnostic or command: $label" >&2
      exit 1
    }
    diagnostic=$2
    shift 2
  fi
  if output=$("$@" 2>&1); then
    echo "test-base-diff-runtime: expected failure: $label" >&2
    exit 1
  fi
  if [[ -n "$diagnostic" && "$output" != *"$diagnostic"* ]]; then
    echo "test-base-diff-runtime: wrong failure diagnostic: $label" >&2
    echo "$output" >&2
    exit 1
  fi
}

clone_production() {
  local target=$1
  mkdir -p "$target"
  cp -R "$TMP/production/registry" "$target/registry"
}

clone_case() {
  local source=$1 target=$2
  mkdir -p "$target"
  cp -R "$source/registry" "$target/registry"
}

rewrite() {
  local file=$1 program=$2
  awk -F '\t' -v OFS='\t' "$program" "$file" > "$file.tmp"
  mv "$file.tmp" "$file"
}

BASE="$CASES/base"
GOOD="$CASES/good"
clone_production "$BASE"
# Give the frozen baseline one concrete claim OID so later drift cannot be
# mistaken for the separately tested PENDING-to-fixed transition.
rewrite "$BASE/registry/claims.tsv" \
  'NR==2 {$9="1111111111111111111111111111111111111111"} {print}'
clone_case "$BASE" "$GOOD"

clone_case "$BASE" "$CASES/deletion"
rewrite "$CASES/deletion/registry/pages.tsv" 'NR!=2 {print}'

clone_case "$BASE" "$CASES/drift"
rewrite "$CASES/drift/registry/pages.tsv" 'NR==2 {$6=$6 "-drift"} {print}'

clone_case "$BASE" "$CASES/regression"
printf '%s\n' phase census > "$CASES/regression/registry/phase.tsv.tmp"
mv "$CASES/regression/registry/phase.tsv.tmp" "$CASES/regression/registry/phase.tsv"

# A valid dedicated supersession uses a census-era legacy baseline, before
# vocabulary-review and source-item edges exist. This isolates the transition
# contract from later registries whose old rows are independently immutable.
SUPER_BASE="$CASES/supersession-base"
SUPER_GOOD="$CASES/supersession-good"
clone_production "$SUPER_BASE"
rm -f \
  "$SUPER_BASE/registry/tracks.tsv" \
  "$SUPER_BASE/registry/sources.tsv" \
  "$SUPER_BASE/registry/source-invariants.tsv" \
  "$SUPER_BASE/registry/source-progress.tsv" \
  "$SUPER_BASE/registry/source-items.tsv" \
  "$SUPER_BASE/registry/item-claims.tsv"
mkdir -p "$SUPER_BASE/references"
printf '%s\n' \
  $'source_id\tlocal_ref_key\tedition\tpdf_oid\ttext_oid\tcoverage\tnotes' \
  $'TASAKI2020\truntime.pdf\t2020.ed1\t1111111111111111111111111111111111111111\t2222222222222222222222222222222222222222\tfrozen\truntime' \
  > "$SUPER_BASE/references/tasaki-2020.tsv.tmp"
mv "$SUPER_BASE/references/tasaki-2020.tsv.tmp" "$SUPER_BASE/references/tasaki-2020.tsv"
printf '%s\n' phase census > "$SUPER_BASE/registry/phase.tsv.tmp"
mv "$SUPER_BASE/registry/phase.tsv.tmp" "$SUPER_BASE/registry/phase.tsv"
rewrite "$SUPER_BASE/registry/claim-vocabulary-review.tsv" 'NR==1 {print}'
clone_case "$SUPER_BASE" "$SUPER_GOOD"
mkdir -p "$SUPER_GOOD/references"
cp -R "$SUPER_BASE/references/." "$SUPER_GOOD/references/"
OLD_CLAIM=$(awk -F '\t' 'END {print $1}' "$SUPER_GOOD/registry/claims.tsv")
NEW_CLAIM=CL-TASAKI2020-9999
awk -F '\t' -v OFS='\t' -v old="$OLD_CLAIM" -v new="$NEW_CLAIM" '
  $1==old {
    source=$2; page=$4
    split($3, orderPart, ".")
    nextOrder=orderPart[1] "." sprintf("%04d", orderPart[2] + 1)
    $12="true"; $13=new; $14="runtime-supersession"; $15="RUNTIME-REVIEW"
  }
  { print }
  END {
    print new,source,nextOrder,page,"runtime successor", "assertion", "lemma",
      "Runtime successor claim.","PENDING","NONE","NONE","false","NONE","NONE","NONE"
  }
' "$SUPER_GOOD/registry/claims.tsv" > "$SUPER_GOOD/registry/claims.tsv.tmp"
mv "$SUPER_GOOD/registry/claims.tsv.tmp" "$SUPER_GOOD/registry/claims.tsv"

clone_case "$SUPER_GOOD" "$CASES/supersession-bad"
mkdir -p "$CASES/supersession-bad/references"
cp -R "$SUPER_GOOD/references/." "$CASES/supersession-bad/references/"
rewrite "$CASES/supersession-bad/registry/claims.tsv" \
  '$1=="'"$OLD_CLAIM"'" {$14="NONE"} {print}'

CLAIM_OID_BASE="$CASES/claim-oid-base"
CLAIM_OID_GOOD="$CASES/claim-oid-good"
clone_production "$CLAIM_OID_BASE"
clone_case "$CLAIM_OID_BASE" "$CLAIM_OID_GOOD"
rewrite "$CLAIM_OID_GOOD/registry/claims.tsv" \
  'NR==2 {$9="1111111111111111111111111111111111111111"} {print}'
clone_case "$CLAIM_OID_BASE" "$CASES/claim-oid-bad"
rewrite "$CASES/claim-oid-bad/registry/claims.tsv" 'NR==2 {$9="invalid"} {print}'
clone_case "$BASE" "$CASES/claim-oid-freeze-bad"
rewrite "$CASES/claim-oid-freeze-bad/registry/claims.tsv" \
  'NR==2 {$9="2222222222222222222222222222222222222222"} {print}'

LIFECYCLE_BASE="$CASES/lifecycle-base"
LIFECYCLE_GOOD="$CASES/lifecycle-good"
clone_production "$LIFECYCLE_BASE"
clone_case "$LIFECYCLE_BASE" "$LIFECYCLE_GOOD"
clone_case "$LIFECYCLE_BASE" "$CASES/lifecycle-partial-oid"
rewrite "$CASES/lifecycle-partial-oid/registry/sources.tsv" 'NR==2 {$15=""} {print}'
clone_case "$LIFECYCLE_BASE" "$CASES/lifecycle-bad-edition"
rewrite "$CASES/lifecycle-bad-edition/registry/sources.tsv" 'NR==2 {$9="changed.edition"} {print}'
clone_case "$LIFECYCLE_BASE" "$CASES/registry-post-edition-pending"
rewrite "$CASES/registry-post-edition-pending/registry/sources.tsv" 'NR==2 {$9="pending"} {print}'
clone_case "$LIFECYCLE_BASE" "$CASES/registry-source-mixed-width"
rewrite "$CASES/registry-source-mixed-width/registry/sources.tsv" \
  'NR==2 {$16="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"} {print}'
clone_case "$BASE" "$CASES/lifecycle-regress"
rewrite "$CASES/lifecycle-regress/registry/sources.tsv" 'NR==2 {$17="pass2"} {print}'
clone_case "$LIFECYCLE_GOOD" "$CASES/lifecycle-edition-drift"
rewrite "$CASES/lifecycle-edition-drift/registry/sources.tsv" 'NR==2 {$9="other.edition"} {print}'
clone_case "$LIFECYCLE_GOOD" "$CASES/lifecycle-oid-drift"
rewrite "$CASES/lifecycle-oid-drift/registry/sources.tsv" \
  'NR==2 {$15="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"} {print}'

VOCABULARY_BASE="$CASES/vocabulary-base"
VOCABULARY_GOOD="$CASES/vocabulary-good"
clone_production "$VOCABULARY_BASE"
clone_case "$VOCABULARY_BASE" "$VOCABULARY_GOOD"
clone_case "$VOCABULARY_GOOD" "$CASES/vocabulary-type-regression"
rewrite "$CASES/vocabulary-type-regression/registry/vocabulary.tsv" \
  'NR==2 {$7="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"} {print}'
clone_case "$VOCABULARY_GOOD" "$CASES/vocabulary-regression"
rewrite "$CASES/vocabulary-regression/registry/vocabulary.tsv" \
  'NR==2 {$8="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"} {print}'

TOKEN_MIGRATION_BASE="$CASES/review-token-migration-base"
clone_production "$TOKEN_MIGRATION_BASE"
rewrite "$TOKEN_MIGRATION_BASE/registry/claim-vocabulary-review.tsv" \
  'NR>1 {$3="R3-INDEPENDENT-REVIEW-P0"} {print}'
rewrite "$TOKEN_MIGRATION_BASE/registry/source-progress.tsv" \
  'NR>1 {$3="R3-INDEPENDENT-REVIEW-P0"} {print}'

clone_production "$CASES/review-ref-arbitrary"
rewrite "$CASES/review-ref-arbitrary/registry/claim-vocabulary-review.tsv" \
  'NR==2 {$3="ARBITRARY-REVIEW-REF"} {print}'

expect_pass base-snapshot-registry "$CHECK_REGISTRY" "$BASE"
expect_pass good-snapshot-registry "$CHECK_REGISTRY" "$GOOD"
expect_pass supersession-snapshot-registry "$CHECK_REGISTRY" "$SUPER_GOOD"
expect_pass claim-oid-base-snapshot-registry "$CHECK_REGISTRY" "$CLAIM_OID_BASE"
expect_pass claim-oid-good-snapshot-registry "$CHECK_REGISTRY" "$CLAIM_OID_GOOD"
expect_pass lifecycle-base-snapshot-registry "$CHECK_REGISTRY" "$LIFECYCLE_BASE"
expect_pass lifecycle-good-snapshot-registry "$CHECK_REGISTRY" "$LIFECYCLE_GOOD"
expect_pass vocabulary-base-snapshot-registry "$CHECK_REGISTRY" "$VOCABULARY_BASE"
expect_pass vocabulary-good-snapshot-registry "$CHECK_REGISTRY" "$VOCABULARY_GOOD"
expect_pass vocabulary-type-regression-snapshot-registry \
  "$CHECK_REGISTRY" "$CASES/vocabulary-type-regression"

expect_pass base-good "$CHECK_BASE_DIFF" --fixture-dirs "$BASE" "$GOOD"
expect_fail base-deletion "$CHECK_BASE_DIFF" --fixture-dirs "$BASE" "$CASES/deletion"
expect_fail base-drift "$CHECK_BASE_DIFF" --fixture-dirs "$BASE" "$CASES/drift"
expect_fail base-regression "$CHECK_BASE_DIFF" --fixture-dirs "$BASE" "$CASES/regression"
expect_fail supersession-default-reject \
  "$CHECK_BASE_DIFF" --fixture-dirs "$SUPER_BASE" "$SUPER_GOOD"
expect_pass supersession-dedicated-accept \
  "$CHECK_BASE_DIFF" --allow-supersession --fixture-dirs "$SUPER_BASE" "$SUPER_GOOD"
expect_fail supersession-dedicated-reject \
  "$CHECK_BASE_DIFF" --allow-supersession --fixture-dirs "$SUPER_BASE" "$CASES/supersession-bad"
expect_pass claim-oid-transition \
  "$CHECK_BASE_DIFF" --fixture-dirs "$CLAIM_OID_BASE" "$CLAIM_OID_GOOD"
expect_fail claim-oid-invalid \
  "$CHECK_BASE_DIFF" --fixture-dirs "$CLAIM_OID_BASE" "$CASES/claim-oid-bad"
expect_fail claim-oid-frozen \
  "$CHECK_BASE_DIFF" --fixture-dirs "$BASE" "$CASES/claim-oid-freeze-bad"
expect_pass reference-lifecycle \
  "$CHECK_BASE_DIFF" --fixture-dirs "$LIFECYCLE_BASE" "$LIFECYCLE_GOOD"
expect_fail reference-partial-oid \
  "$CHECK_BASE_DIFF" --fixture-dirs "$LIFECYCLE_BASE" "$CASES/lifecycle-partial-oid"
expect_fail reference-bad-edition \
  "$CHECK_BASE_DIFF" --fixture-dirs "$LIFECYCLE_BASE" "$CASES/lifecycle-bad-edition"
expect_fail reference-pending-edition \
  "$CHECK_BASE_DIFF" --fixture-dirs "$LIFECYCLE_BASE" "$CASES/registry-post-edition-pending"
expect_fail reference-mixed-oid-width \
  "$CHECK_BASE_DIFF" --fixture-dirs "$LIFECYCLE_BASE" "$CASES/registry-source-mixed-width"
expect_fail reference-coverage-regress \
  "$CHECK_BASE_DIFF" --fixture-dirs "$BASE" "$CASES/lifecycle-regress"
expect_fail reference-edition-frozen \
  "$CHECK_BASE_DIFF" --fixture-dirs "$LIFECYCLE_GOOD" "$CASES/lifecycle-edition-drift"
expect_fail reference-oid-frozen \
  "$CHECK_BASE_DIFF" --fixture-dirs "$LIFECYCLE_GOOD" "$CASES/lifecycle-oid-drift"
expect_pass vocabulary-type-freeze \
  "$CHECK_BASE_DIFF" --fixture-dirs "$VOCABULARY_BASE" "$VOCABULARY_GOOD"
expect_fail vocabulary-type-only-drift --diagnostic "vocabulary type OID regressed" \
  "$CHECK_BASE_DIFF" --fixture-dirs "$VOCABULARY_GOOD" "$CASES/vocabulary-type-regression"
expect_fail vocabulary-declaration-only-drift --diagnostic "vocabulary declaration OID regressed" \
  "$CHECK_BASE_DIFF" --fixture-dirs "$VOCABULARY_GOOD" "$CASES/vocabulary-regression"

expect_pass review-token-migration-positive \
  "$CHECK_BASE_DIFF" --fixture-dirs "$TOKEN_MIGRATION_BASE" "$TMP/production"
expect_fail review-ref-arbitrary-reject --diagnostic "vocabulary review" \
  "$CHECK_BASE_DIFF" --fixture-dirs "$TMP/production" "$CASES/review-ref-arbitrary"

expect_fail invalid-base-ref \
  "$CHECK_BASE_DIFF" "$PROJECT_ROOT" refs/heads/runtime-base-ref-that-does-not-exist

[[ $(baseline_digest) == "$BASELINE_DIGEST" ]] || {
  echo "test-base-diff-runtime: immutable production baseline changed" >&2
  exit 1
}

echo "test-base-diff-runtime: ok"
