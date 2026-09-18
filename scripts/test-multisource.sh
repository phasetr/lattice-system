#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-system-tests.multisource.XXXXXX")
trap 'rm -rf "$TMP"' EXIT
export LATTICE_TEST_ROOT=$TMP
BASE="$TMP/base"
mkdir -p "$BASE/registry"

write_headers() {
  local reg=$1
  printf '%s\n' 'slice_id	position	claim_id' > "$reg/slices.tsv"
  printf '%s\n' 'claim_id	role	target_claim_id	rationale' > "$reg/dependencies.tsv"
  printf '%s\n' 'claim_id	statement_decl	proof_decl	module	statement_oid	nonvacuity_decl' > "$reg/bindings.tsv"
  printf '%s\n' 'axiom_id	declaration	module	category	source_locator	rationale	reopen_condition' > "$reg/axioms.tsv"
  printf '%s\n' 'claim_id	axiom_id' > "$reg/claim-axioms.tsv"
  printf '%s\n' 'claim_id	basis	review_ref' > "$reg/claim-vocabulary-review.tsv"
  printf '%s\n' 'vocabulary_id	declaration	module	declaration_kind	origin	parent_vocabulary_id	type_oid	declaration_oid	design_role	finiteness_scope' > "$reg/vocabulary.tsv"
  printf '%s\n' 'claim_id	vocabulary_id' > "$reg/claim-vocabulary.tsv"
  printf '%s\n' 'module	source_path	role' > "$reg/modules.tsv"
  printf '%s\n' 'module	position	imported_module	is_exported	is_meta	import_all' > "$reg/imports.tsv"
  printf '%s\n' $'event_id\tevent_position\tsource_id\tbase_commit\treview_ref' > "$reg/correction-events.tsv"
  printf '%s\n' $'review_id\tevent_id\treview_position\tclaim_id\treview_scope\toutcome\tstatus\trationale\treview_ref' > "$reg/claim-normalization-reviews.tsv"
  printf '%s\n' $'correction_id\tevent_id\tcorrection_position\treview_id\tclaim_id\taction\told_disposition\told_subkind\tnew_disposition\tnew_subkind' > "$reg/claim-corrections.tsv"
  printf '%s\n' $'successor_edge_id\tevent_id\tcorrection_id\tpredecessor_claim_id\tsuccessor_position\trelation\tsuccessor_claim_id' > "$reg/claim-successors.tsv"
}

printf '%s\n' 'phase' 'census' > "$BASE/registry/phase.tsv"
printf '%s\n' \
  $'track_id\tposition\ttitle\tpublic_slug' \
  $'TR-A\t1\tTrack A\ttrack-a' \
  $'TR-B\t2\tTrack B\ttrack-b' > "$BASE/registry/tracks.tsv"
printf '%s\n' \
  $'source_id\ttrack_id\tsource_position\tsource_kind\tcitation_key\ttitle\tauthors\tyear\tedition\tidentifier_kind\tidentifier\tpublic_url\tpublic_slug\tlocal_ref_key\tpdf_oid\ttext_oid\tcoverage' \
  $'SRA\tTR-A\t1\tpaper\tSRA\tSource A\tAuthor A\t2025\tv1\tnone\tNONE\tNONE\tsource-a\tSourceA\taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\tbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\treconciled' \
  $'SRB\tTR-B\t1\tpaper\tSRB\tSource B\tAuthor B\t2026\tv1\tnone\tNONE\tNONE\tsource-b\tSourceB\tcccccccccccccccccccccccccccccccccccccccc\tdddddddddddddddddddddddddddddddddddddddd\treconciled' > "$BASE/registry/sources.tsv"
printf '%s\n' \
  $'source_id\tlifecycle\treview_ref' \
  $'SRA\tcensus_reconciled\tREVIEW-A' \
  $'SRB\tcensus_reconciled\tREVIEW-B' > "$BASE/registry/source-progress.tsv"
printf '%s\n' \
  $'page_id\tsource_id\torder_key\tprinted_page\tpdf_page\tsection\tpage_kind\tpass1\tpass2\tsource_oid' \
  $'PG-SRA-0001\tSRA\t000001\t1\t1\t1\tcontent\tcomplete\tcomplete\taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa' \
  $'PG-SRB-0001\tSRB\t000001\t1\t1\t1\tcontent\tcomplete\tcomplete\tcccccccccccccccccccccccccccccccccccccccc' > "$BASE/registry/pages.tsv"
printf '%s\n' \
  $'claim_id\tsource_id\torder_key\tpage_id\tlocator\tdisposition\tsubkind\tnormalized_content\tcontent_oid\texclusion_rationale\texclusion_review_ref\ttombstone\tsuperseded_by\ttombstone_rationale\ttombstone_review_ref' \
  $'CL-SRA-0001\tSRA\t000001.0001\tPG-SRA-0001\tPDF p. 1; paragraph 1\tassertion\tunnumbered_obligation\tClaim A\taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE' \
  $'CL-SRB-0001\tSRB\t000001.0001\tPG-SRB-0001\tPDF p. 1; paragraph 1\tassertion\tunnumbered_obligation\tClaim B\tcccccccccccccccccccccccccccccccccccccccc\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE' > "$BASE/registry/claims.tsv"
printf '%s\n' \
  $'item_id\tsource_id\torder_key\tpage_id\titem_kind\tsource_label\ttitle\tlocator\tpublic_group\tpublic_slug\treview_ref' \
  $'IT-SRA-0001\tSRA\t000001.0001\tPG-SRA-0001\tunlabeled\tNONE\tNONE\tPDF p. 1; paragraph 1\tChapter 01\tchapter-01\tREVIEW-A' \
  $'IT-SRB-0001\tSRB\t000001.0001\tPG-SRB-0001\tunlabeled\tNONE\tNONE\tPDF p. 1; paragraph 1\tChapter 01\tchapter-01\tREVIEW-B' > "$BASE/registry/source-items.tsv"
printf '%s\n' \
  $'item_id\tposition\tclaim_id' \
  $'IT-SRA-0001\t1\tCL-SRA-0001' \
  $'IT-SRB-0001\t1\tCL-SRB-0001' > "$BASE/registry/item-claims.tsv"
write_headers "$BASE/registry"

oid_a=$(LC_ALL=C awk -F '\t' 'FNR>1 && $2=="SRA" { print }' "$BASE/registry/pages.tsv" "$BASE/registry/claims.tsv" | git hash-object --stdin)
oid_b=$(LC_ALL=C awk -F '\t' 'FNR>1 && $2=="SRB" { print }' "$BASE/registry/pages.tsv" "$BASE/registry/claims.tsv" | git hash-object --stdin)
printf '%s\n' \
  $'source_id\tphysical_page_count\tactive_claim_count\tformalization_target_count\tequation_pair_count\tno_claim_page_count\tcensus_oid\treview_ref' \
  "SRA"$'\t1\t1\t1\t0\t0\t'"$oid_a"$'\tREVIEW-A' \
  "SRB"$'\t1\t1\t1\t0\t0\t'"$oid_b"$'\tREVIEW-B' > "$BASE/registry/source-invariants.tsv"

expect_fail() {
  local label=$1 diagnostic=$2
  shift 2
  local output
  if output=$("$@" 2>&1); then
    echo "test-multisource: expected failure: $label" >&2
    exit 1
  fi
  [[ "$output" == *"$diagnostic"* ]] || { echo "test-multisource: wrong diagnostic: $label" >&2; echo "$output" >&2; exit 1; }
}

mutate() {
  local source=$1 target=$2 awk_program=$3
  awk -F '\t' -v OFS='\t' "$awk_program" "$source" > "$target"
}

"$ROOT/scripts/check-registry.sh" "$BASE" >/dev/null
"$ROOT/scripts/check-census.sh" --fixture "$BASE" >/dev/null
"$ROOT/scripts/check-source-items.sh" "$BASE" >/dev/null

cp -R "$BASE" "$TMP/unpadded-chapter"
mutate "$BASE/registry/source-items.tsv" "$TMP/unpadded-chapter/registry/source-items.tsv" 'NR==2 {$9="Chapter 1";$10="chapter-1"} {print}'
expect_fail unpadded-chapter "numeric chapter group is not zero-padded" "$ROOT/scripts/check-source-items.sh" "$TMP/unpadded-chapter"

cp -R "$BASE" "$TMP/id-mismatch"
mutate "$BASE/registry/pages.tsv" "$TMP/id-mismatch/registry/pages.tsv" 'NR==2 {$1="PG-SRB-0002"} {print}'
expect_fail id-source-mismatch "page ID/source mismatch" "$ROOT/scripts/check-order.sh" "$TMP/id-mismatch"

cp -R "$BASE" "$TMP/count"
mutate "$BASE/registry/source-invariants.tsv" "$TMP/count/registry/source-invariants.tsv" 'NR==2 {$3=2} {print}'
expect_fail per-source-count "claim census invariant failed for SRA" "$ROOT/scripts/check-census.sh" --fixture "$TMP/count"

cp -R "$BASE" "$TMP/order"
mutate "$BASE/registry/sources.tsv" "$TMP/order/registry/sources.tsv" 'NR==3 {$3=2} {print}'
expect_fail per-source-order "source positions are not contiguous" "$ROOT/scripts/check-sources.sh" "$TMP/order"

cp -R "$BASE" "$TMP/lifecycle"
mutate "$BASE/registry/source-progress.tsv" "$TMP/lifecycle/registry/source-progress.tsv" 'NR==2 {$2="vocabulary_reviewed"} {print}'
expect_fail lifecycle-mismatch "source lifecycle exceeds checker capability SRA" "$ROOT/scripts/check-lifecycle.sh" "$TMP/lifecycle"

cp -R "$BASE" "$TMP/mixed-census"
printf '%s\n' 'phase' 'vocabulary' > "$TMP/mixed-census/registry/phase.tsv"
mutate "$BASE/registry/sources.tsv" "$TMP/mixed-census/registry/sources.tsv" 'NR==2 {$17="frozen"} {print}'
mutate "$BASE/registry/source-progress.tsv" "$TMP/mixed-census/registry/source-progress.tsv" 'NR==2 {$2="vocabulary_reviewed"} {print}'
printf '%s\n' $'claim_id\tbasis\treview_ref' $'CL-SRA-0001\tmathlib_only\tREVIEW-A' > "$TMP/mixed-census/registry/claim-vocabulary-review.tsv"
"$ROOT/scripts/check-registry.sh" "$TMP/mixed-census" >/dev/null
"$ROOT/scripts/check-census.sh" --fixture "$TMP/mixed-census" >/dev/null

cp -R "$TMP/mixed-census" "$TMP/mixed-registered"
mutate "$TMP/mixed-census/registry/sources.tsv" "$TMP/mixed-registered/registry/sources.tsv" 'NR==3 {$15="";$16="";$17="pending"} {print}'
mutate "$TMP/mixed-census/registry/source-progress.tsv" "$TMP/mixed-registered/registry/source-progress.tsv" 'NR==3 {$2="registered"} {print}'
mutate "$TMP/mixed-census/registry/source-invariants.tsv" "$TMP/mixed-registered/registry/source-invariants.tsv" 'NR!=3 {print}'
mutate "$TMP/mixed-census/registry/pages.tsv" "$TMP/mixed-registered/registry/pages.tsv" 'NR==1 || $2!="SRB" {print}'
mutate "$TMP/mixed-census/registry/claims.tsv" "$TMP/mixed-registered/registry/claims.tsv" 'NR==1 || $2!="SRB" {print}'
mutate "$TMP/mixed-census/registry/source-items.tsv" "$TMP/mixed-registered/registry/source-items.tsv" 'NR==1 || $2!="SRB" {print}'
mutate "$TMP/mixed-census/registry/item-claims.tsv" "$TMP/mixed-registered/registry/item-claims.tsv" 'NR==1 || $1!="IT-SRB-0001" {print}'
"$ROOT/scripts/check-registry.sh" "$TMP/mixed-registered" >/dev/null
"$ROOT/scripts/check-census.sh" --fixture "$TMP/mixed-registered" >/dev/null
"$ROOT/scripts/check-source-items.sh" "$TMP/mixed-registered" >/dev/null

cp -R "$BASE" "$TMP/dependency-good"
printf '%s\n' $'CL-SRB-0001\trequires\tCL-SRA-0001\tCROSS-TRACK-REVIEW' >> "$TMP/dependency-good/registry/dependencies.tsv"
"$ROOT/scripts/check-order.sh" "$TMP/dependency-good" >/dev/null

cp -R "$BASE" "$TMP/dependency-required-by"
printf '%s\n' $'CL-SRB-0001\trequired_by\tCL-SRA-0001\tNONE' >> "$TMP/dependency-required-by/registry/dependencies.tsv"
expect_fail required-by-rationale "required_by needs review rationale" "$ROOT/scripts/check-order.sh" "$TMP/dependency-required-by"

cp -R "$BASE" "$TMP/dependency-cross-track-rationale"
printf '%s\n' $'CL-SRB-0001\trequires\tCL-SRA-0001\tNONE' >> "$TMP/dependency-cross-track-rationale/registry/dependencies.tsv"
expect_fail cross-track-rationale "cross-track dependency needs review rationale" "$ROOT/scripts/check-order.sh" "$TMP/dependency-cross-track-rationale"

cp -R "$BASE" "$TMP/dependency"
printf '%s\n' $'CL-SRA-0001\trequires\tCL-SRB-0001\tCROSS-SOURCE-NEGATIVE' >> "$TMP/dependency/registry/dependencies.tsv"
expect_fail cross-source-dependency "dependency target is not earlier in global source order" "$ROOT/scripts/check-order.sh" "$TMP/dependency"

# Exercise every frozen through-vocabulary base-diff gate with a multi-source current tree.
# These rows need not satisfy the census phase policy: they are a compact pair
# of base/current snapshots used only by the anti-regression checker.
DIFF_BASE="$TMP/diff-base"
cp -R "$BASE" "$DIFF_BASE"
printf '%s\n' $'SL-SRA-0001\t1\tCL-SRA-0001' >> "$DIFF_BASE/registry/slices.tsv"
printf '%s\n' $'CL-SRA-0001\tFixture.statement\tNONE\tFixture.Module\taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\tNONE' >> "$DIFF_BASE/registry/bindings.tsv"
printf '%s\n' $'VO-LS-0001\tFixture.term\tFixture.Module\tdefinition\tprimary\tNONE\taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\tbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\tgraph_core\tnone' >> "$DIFF_BASE/registry/vocabulary.tsv"
cp -R "$DIFF_BASE" "$TMP/diff-good"
"$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$DIFF_BASE" "$TMP/diff-good" >/dev/null

cp -R "$DIFF_BASE" "$TMP/diff-vocabulary-type"
mutate "$DIFF_BASE/registry/vocabulary.tsv" "$TMP/diff-vocabulary-type/registry/vocabulary.tsv" 'NR==2 {$7="cccccccccccccccccccccccccccccccccccccccc"} {print}'
expect_fail base-vocabulary-type "vocabulary type OID regressed" "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$DIFF_BASE" "$TMP/diff-vocabulary-type"

cp -R "$DIFF_BASE" "$TMP/diff-vocabulary-declaration"
mutate "$DIFF_BASE/registry/vocabulary.tsv" "$TMP/diff-vocabulary-declaration/registry/vocabulary.tsv" 'NR==2 {$8="cccccccccccccccccccccccccccccccccccccccc"} {print}'
expect_fail base-vocabulary-declaration "vocabulary declaration OID regressed" "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$DIFF_BASE" "$TMP/diff-vocabulary-declaration"

cp -R "$DIFF_BASE" "$TMP/diff-slice-position"
mutate "$DIFF_BASE/registry/slices.tsv" "$TMP/diff-slice-position/registry/slices.tsv" 'NR==2 {$2=2} {print}'
expect_fail base-slice-position "slice position changed" "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$DIFF_BASE" "$TMP/diff-slice-position"

cp -R "$DIFF_BASE" "$TMP/diff-slice-deletion"
printf '%s\n' $'slice_id\tposition\tclaim_id' > "$TMP/diff-slice-deletion/registry/slices.tsv"
expect_fail base-slice-deletion "slice membership disappeared" "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$DIFF_BASE" "$TMP/diff-slice-deletion"

cp -R "$DIFF_BASE" "$TMP/diff-phase-base"
mutate "$DIFF_BASE/registry/phase.tsv" "$TMP/diff-phase-base/registry/phase.tsv" 'NR==2 {$1="vocabulary"} {print}'
expect_fail base-phase "phase regression: vocabulary -> census" "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$TMP/diff-phase-base" "$TMP/diff-good"

cp -R "$DIFF_BASE" "$TMP/diff-page-pass"
mutate "$DIFF_BASE/registry/pages.tsv" "$TMP/diff-page-pass/registry/pages.tsv" 'NR==2 {$8="pending"} {print}'
expect_fail base-page-pass "page OID or census pass regressed" "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$DIFF_BASE" "$TMP/diff-page-pass"

cp -R "$DIFF_BASE" "$TMP/diff-page-oid"
mutate "$DIFF_BASE/registry/pages.tsv" "$TMP/diff-page-oid/registry/pages.tsv" 'NR==2 {$10="eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"} {print}'
expect_fail base-page-oid "page OID or census pass regressed" "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$DIFF_BASE" "$TMP/diff-page-oid"

cp -R "$DIFF_BASE" "$TMP/diff-claim-oid"
mutate "$DIFF_BASE/registry/claims.tsv" "$TMP/diff-claim-oid/registry/claims.tsv" 'NR==2 {$9="eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"} {print}'
expect_fail base-claim-oid "claim OID or tombstone regressed" "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$DIFF_BASE" "$TMP/diff-claim-oid"

cp -R "$DIFF_BASE" "$TMP/diff-binding"
printf '%s\n' $'claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_oid\tnonvacuity_decl' > "$TMP/diff-binding/registry/bindings.tsv"
expect_fail base-binding "binding disappeared or identity drifted" "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$DIFF_BASE" "$TMP/diff-binding"

cp -R "$DIFF_BASE" "$TMP/diff-tombstone-base"
mutate "$DIFF_BASE/registry/claims.tsv" "$TMP/diff-tombstone-base/registry/claims.tsv" 'NR==2 {$12="true";$13="CL-SRB-0001";$14="RETIRED";$15="REVIEW"} {print}'
expect_fail base-tombstone-reversal "claim OID or tombstone regressed" "$ROOT/scripts/check-base-diff.sh" --allow-supersession --fixture-dirs "$TMP/diff-tombstone-base" "$TMP/diff-good"

cp -R "$DIFF_BASE" "$TMP/diff-supersession"
mutate "$DIFF_BASE/registry/claims.tsv" "$TMP/diff-supersession/registry/claims.tsv" 'NR==2 {$12="true";$13="CL-SRB-0001";$14="RETIRED";$15="REVIEW"} {print}'
expect_fail base-supersession "invalid dedicated supersession transition" "$ROOT/scripts/check-base-diff.sh" --allow-supersession --fixture-dirs "$DIFF_BASE" "$TMP/diff-supersession"

echo "test-multisource: ok"
