#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
PROJECT_ROOT=$(cd "$PROJECT_ROOT" && pwd)
TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-system-tests.claim-corrections.XXXXXX")
trap 'rm -rf "$TMP"' EXIT
export LATTICE_TEST_ROOT=$TMP

CHECK_CORRECTIONS=${CHECK_CORRECTIONS:-"$PROJECT_ROOT/scripts/check-claim-corrections.sh"}
GENERATE_PUBLIC_DOCS=${GENERATE_PUBLIC_DOCS:-"$PROJECT_ROOT/scripts/generate-public-docs.py"}
EVENT_ID=RUNTIME-CORRECTION-EVENT-2
BASE_COMMIT=c6fb1ec6046626e14dd9a65f396a66386fcb9b7b
REVIEW_REF=CORPUS-NORMALIZATION-TASAKI2020-2026-REVIEW
BASE="$TMP/base"
CASES="$TMP/cases"
mkdir -p "$BASE" "$CASES"
cp -R "$PROJECT_ROOT/registry" "$BASE/registry"

baseline_digest() {
  find "$BASE/registry" -type f -print0 | LC_ALL=C sort -z |
    xargs -0 shasum | shasum | awk '{print $1}'
}
BASELINE_DIGEST=$(baseline_digest)

expect_pass() {
  local label=$1
  shift
  local output
  if ! output=$("$@" 2>&1); then
    echo "test-claim-corrections-runtime: expected pass: $label" >&2
    echo "$output" >&2
    exit 1
  fi
}

expect_fail() {
  local label=$1 diagnostic=$2
  shift 2
  local output
  if output=$("$@" 2>&1); then
    echo "test-claim-corrections-runtime: expected failure: $label" >&2
    exit 1
  fi
  if [[ "$output" != *"$diagnostic"* ]]; then
    echo "test-claim-corrections-runtime: wrong failure diagnostic: $label" >&2
    echo "$output" >&2
    exit 1
  fi
}

expect_registered_content() {
  local label=$1 claim_id=$2 expected=$3 actual
  actual=$(awk -F '\t' -v id="$claim_id" '$1==id {print $8; exit}' \
    "$BASE/registry/claims.tsv")
  if [[ "$actual" != "$expected" ]]; then
    echo "test-claim-corrections-runtime: registered content mismatch: $label" >&2
    exit 1
  fi
}

expect_registered_content af-axis-labels CL-TASAKI2020-3436 \
  'In the reported ground-state phase diagram of Hamiltonian (8.3.4), the Haldane phase is surrounded by the large-D, AF2, and AF3 phases, and the spins in AF2 and AF3 point in the 2-direction and the 3-direction, respectively.'
expect_registered_content decorated-lattice-source-notation CL-TASAKI2020-3447 \
  'Define the decorated hypercubic lattice by Λ := E ∪ (I × {1, 2}).'

clone_base() {
  local target=$1
  mkdir -p "$target"
  cp -R "$BASE/registry" "$target/registry"
}

clone_case() {
  local source=$1 target=$2
  mkdir -p "$target"
  cp -R "$source/registry" "$target/registry"
}

clone_commit_registry() {
  local commit=$1 target=$2 path
  mkdir -p "$target/registry"
  while IFS= read -r path; do
    git -C "$PROJECT_ROOT" show "$commit:$path" > "$target/$path"
  done < <(git -C "$PROJECT_ROOT" ls-tree -r --name-only "$commit" registry)
}

rewrite() {
  local file=$1 program=$2
  awk -F '\t' -v OFS='\t' "$program" "$file" > "$file.tmp"
  mv "$file.tmp" "$file"
}

prepare_event() {
  local target=$1
  clone_base "$target"
  printf '%s\n' "$EVENT_ID"$'\t2\tTASAKI2020\t'"$BASE_COMMIT"$'\t'"$REVIEW_REF" >> "$target/registry/correction-events.tsv"
}

append_correction() {
  local target=$1 row=$2
  printf '%s\n' "$row" >> "$target/registry/claim-corrections.tsv"
}

append_review() {
  local target=$1 row=$2
  printf '%s\n' "$row" >> "$target/registry/claim-normalization-reviews.tsv"
}

refresh_invariants() {
  local target=$1 source=${2:-TASAKI2020} active targets equations empty census_oid
  active=$(awk -F '\t' -v source="$source" \
    'FNR>1 && $2==source && $12=="false" {n++} END {print n+0}' \
    "$target/registry/claims.tsv")
  targets=$(awk -F '\t' -v source="$source" \
    'FNR>1 && $2==source && $12=="false" && $6!="out_of_scope" {n++} END {print n+0}' \
    "$target/registry/claims.tsv")
  equations=$(awk -F '\t' -v source="$source" \
    'FNR>1 && $2==source && $12=="false" && $7=="equation" {n++} END {print n+0}' \
    "$target/registry/claims.tsv")
  empty=$(awk -F '\t' -v source="$source" '
    NR==FNR {if (FNR>1 && $2==source) page[$1]=1; next}
    FNR>1 && $2==source && $12=="false" {used[$4]=1}
    END {for (id in page) if (!(id in used)) n++; print n+0}
  ' "$target/registry/pages.tsv" "$target/registry/claims.tsv")
  census_oid=$(LC_ALL=C awk -F '\t' -v source="$source" \
    'FNR>1 && $2==source {print}' \
    "$target/registry/pages.tsv" "$target/registry/claims.tsv" | git hash-object --stdin)
  awk -F '\t' -v OFS='\t' -v active="$active" -v targets="$targets" \
    -v equations="$equations" -v empty="$empty" -v census_oid="$census_oid" \
    -v source="$source" '
    FNR==1 {
      print "source_id","physical_page_count","active_claim_count", \
        "formalization_target_count","equation_pair_count", \
        "no_claim_page_count","census_oid","review_ref"
      next
    }
    $1==source {
      review=(NF==8 ? $8 : $7)
      print $1,$2,active,targets,equations,empty,census_oid,review
      next
    }
    NF==8 {print; next}
    {
      review=(NF==8 ? $8 : $7)
      print $1,$2,$3,$3,$4,$5,$6,review
    }
  ' "$target/registry/source-invariants.tsv" > "$target/registry/source-invariants.tsv.tmp"
  mv "$target/registry/source-invariants.tsv.tmp" "$target/registry/source-invariants.tsv"
}

add_source_b() {
  local target=$1
  printf '%s\n' \
    $'SRB\tTR-TASAKI\t2\tpaper\tSRB2026\tRuntime Source B\tRuntime Author\t2026\tv1\tnone\tNONE\tNONE\tsource-b\truntime-source-b.pdf\taaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\tbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\tfrozen' \
    >> "$target/registry/sources.tsv"
  printf '%s\n' $'SRB\tvocabulary_reviewed\tRUNTIME-SOURCE-B-REVIEW' \
    >> "$target/registry/source-progress.tsv"
  printf '%s\n' \
    $'PG-SRB-0001\tSRB\t000001\t1\t1\t1\tcontent\tcomplete\tcomplete\tcccccccccccccccccccccccccccccccccccccccc' \
    >> "$target/registry/pages.tsv"
  printf '%s\n' \
    $'CL-SRB-0001\tSRB\t000001.0001\tPG-SRB-0001\tPDF p. 1; paragraph 1\tassertion\ttheorem\tRuntime source B assertion.\tPENDING\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE' \
    >> "$target/registry/claims.tsv"
  printf '%s\n' \
    $'IT-SRB-0001\tSRB\t000001.0001\tPG-SRB-0001\ttheorem\tTheorem B\tRuntime theorem B\tPDF p. 1; Theorem B\tRuntime Source B\truntime-source-b\tRUNTIME-SOURCE-B-REVIEW' \
    >> "$target/registry/source-items.tsv"
  printf '%s\n' $'IT-SRB-0001\t1\tCL-SRB-0001' \
    >> "$target/registry/item-claims.tsv"
  printf '%s\n' $'CL-SRB-0001\tmathlib_only\tRUNTIME-SOURCE-B-REVIEW' \
    >> "$target/registry/claim-vocabulary-review.tsv"
  printf '%s\n' \
    $'SRB\t1\t1\t1\t0\t0\t0000000000000000000000000000000000000000\tRUNTIME-SOURCE-B-REVIEW' \
    >> "$target/registry/source-invariants.tsv"
  refresh_invariants "$target" SRB
}

prepare_event_from() {
  local base=$1 target=$2 source=$3
  clone_case "$base" "$target"
  printf '%s\n' \
    "$EVENT_ID"$'\t2\t'"$source"$'\t'"$BASE_COMMIT"$'\t'"$REVIEW_REF" \
    >> "$target/registry/correction-events.tsv"
}

add_event1_source_item() {
  local target=$1
  if awk -F '\t' '$1=="IT-TASAKI2020-3037" {found=1} END {exit !found}' \
    "$target/registry/source-items.tsv"; then
    return
  fi
  printf '%s\n' \
    $'item_addition_id\tevent_id\tcorrection_id\taddition_position\titem_id\treview_ref' \
    $'IA-TASAKI2020-0001\tCORPUS-NORMALIZATION-TASAKI2020-2026\tCC-TASAKI2020-0012\t1\tIT-TASAKI2020-3037\tCORPUS-NORMALIZATION-INDEPENDENT-REVIEW' \
    > "$target/registry/source-item-additions.tsv"
  awk -F '\t' -v OFS='\t' '
    {print}
    $1=="IT-TASAKI2020-1537" {
      print "IT-TASAKI2020-3037","TASAKI2020","000301.0003.0001", \
        "PG-TASAKI2020-0301","unlabeled","NONE","NONE", \
        "PDF p. 301; print p. 289; §8.4; paragraph 6", \
        "Chapter 08","chapter-08","PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1"
    }
  ' "$target/registry/source-items.tsv" > "$target/registry/source-items.tsv.tmp"
  mv "$target/registry/source-items.tsv.tmp" "$target/registry/source-items.tsv"
  awk -F '\t' -v OFS='\t' '
    $1=="IT-TASAKI2020-1539" && ($3=="CL-TASAKI2020-3442" || $3=="CL-TASAKI2020-3443") {next}
    {print}
    $1=="IT-TASAKI2020-1537" {
      print "IT-TASAKI2020-3037",1,"CL-TASAKI2020-3442"
      print "IT-TASAKI2020-3037",2,"CL-TASAKI2020-3443"
    }
  ' "$target/registry/item-claims.tsv" > "$target/registry/item-claims.tsv.tmp"
  mv "$target/registry/item-claims.tsv.tmp" "$target/registry/item-claims.tsv"
}

check_item_public_contract() {
  local base=$1 current=$2 item_count chapter_count relation_count
  "$CHECK_CORRECTIONS" --fixture-dirs "$base" "$current" || return
  python3 "$GENERATE_PUBLIC_DOCS" --write --root "$current" \
    >/dev/null || return
  item_count=$(awk 'END {print NR-1}' "$current/registry/source-items.tsv")
  chapter_count=$(awk -F '\t' 'FNR>1 && $9=="Chapter 08" {n++} END {print n+0}' \
    "$current/registry/source-items.tsv")
  relation_count=$(awk 'END {print NR-1}' "$current/registry/item-claims.tsv")
  [[ "$item_count" == 3037 && "$chapter_count" == 363 && "$relation_count" == 3190 ]]
  awk -F '\t' '$1=="IT-TASAKI2020-3036" {found=1} END {exit !found}' \
    "$current/registry/source-items.tsv"
  awk -F '\t' '$1=="IT-TASAKI2020-3037" {found=1} END {exit !found}' \
    "$current/registry/source-items.tsv"
  grep -Fq 'Reviewed source items: 3037' \
    "$current/docs/generated/sources/tasaki-2020.md"
  grep -Fq 'IT-TASAKI2020-3037' \
    "$current/docs/generated/groups/tasaki-2020/chapter-08.md"
}

make_reclassify() {
  local target=$1
  prepare_event "$target"
  rewrite "$target/registry/claims.tsv" \
    '$1=="CL-TASAKI2020-0001" {$6="definition";$7="definition"} {print}'
  rewrite "$target/registry/claim-vocabulary-review.tsv" \
    '$1=="CL-TASAKI2020-0001" {$3="'"$REVIEW_REF"'"} {print}'
  append_review "$target" \
    "NR-RUNTIME-0001"$'\t'"$EVENT_ID"$'\t1\tCL-TASAKI2020-0001\texact_statement_readiness\treclassify\tclosed\twrong-source-kind\t'"$REVIEW_REF"
  append_correction "$target" \
    "CC-RUNTIME-0001"$'\t'"$EVENT_ID"$'\t1\tNR-RUNTIME-0001\tCL-TASAKI2020-0001\treclassify\tnotation\tnotation\tdefinition\tdefinition'
  refresh_invariants "$target"
}

make_unchanged() {
  local target=$1
  prepare_event "$target"
  append_review "$target" \
    "NR-RUNTIME-UNCHANGED"$'\t'"$EVENT_ID"$'\t1\tCL-TASAKI2020-0001\texact_statement_readiness\tunchanged\tclosed\texact-statement-ready\t'"$REVIEW_REF"
}

make_out_of_scope() {
  local target=$1
  prepare_event "$target"
  rewrite "$target/registry/claims.tsv" \
    '$1=="CL-TASAKI2020-0002" {$6="out_of_scope";$10="not-a-formalizable-claim";$11="'"$REVIEW_REF"'"} {print}'
  rewrite "$target/registry/claim-vocabulary-review.tsv" \
    '$1!="CL-TASAKI2020-0002" {print}'
  append_review "$target" \
    "NR-RUNTIME-0002"$'\t'"$EVENT_ID"$'\t1\tCL-TASAKI2020-0002\texact_statement_readiness\texclude_nonclaim\tclosed\tnot-a-formalizable-claim\t'"$REVIEW_REF"
  append_correction "$target" \
    "CC-RUNTIME-0002"$'\t'"$EVENT_ID"$'\t1\tNR-RUNTIME-0002\tCL-TASAKI2020-0002\texclude_nonclaim\tnotation\tnotation\tout_of_scope\tnotation'
  refresh_invariants "$target"
}

make_split() {
  local target=$1
  local content1='For Problem 11.4.1.a, assume the stated local decay estimate.'
  local content2='The estimate applies whenever the lattice distance exceeds one.'
  local oid1 oid2
  oid1=$(printf '%s' "$content1" | git hash-object --stdin)
  oid2=$(printf '%s' "$content2" | git hash-object --stdin)
  prepare_event "$target"
  awk -F '\t' -v OFS='\t' -v review="$REVIEW_REF" -v oid1="$oid1" -v oid2="$oid2" '
    $1=="CL-TASAKI2020-3256" {
      $12="true"; $13="CL-TASAKI2020-9001"; $14="compound-claim"; $15=review
      print
      print "CL-TASAKI2020-9001","TASAKI2020","000528.0005", \
        "PG-TASAKI2020-0528", \
        "PDF p. 528; print p. 519; NONE; paragraph 7; correction split atom 1/2", \
        "hypothesis","hypothesis", \
        "For Problem 11.4.1.a, assume the stated local decay estimate.", \
        oid1,"NONE","NONE","false","NONE","NONE","NONE"
      print "CL-TASAKI2020-9002","TASAKI2020","000528.0006", \
        "PG-TASAKI2020-0528", \
        "PDF p. 528; print p. 519; NONE; paragraph 7; correction split atom 2/2", \
        "hypothesis","hypothesis", \
        "The estimate applies whenever the lattice distance exceeds one.", \
        oid2,"NONE","NONE","false","NONE","NONE","NONE"
      next
    }
    {print}
  ' "$target/registry/claims.tsv" > "$target/registry/claims.tsv.tmp"
  mv "$target/registry/claims.tsv.tmp" "$target/registry/claims.tsv"
  awk -F '\t' -v OFS='\t' '
    {print}
    $1=="IT-TASAKI2020-3034" && $3=="CL-TASAKI2020-3256" {
      print $1,2,"CL-TASAKI2020-9001"
      print $1,3,"CL-TASAKI2020-9002"
    }
  ' "$target/registry/item-claims.tsv" > "$target/registry/item-claims.tsv.tmp"
  mv "$target/registry/item-claims.tsv.tmp" "$target/registry/item-claims.tsv"
  rewrite "$target/registry/claim-vocabulary-review.tsv" \
    '$1!="CL-TASAKI2020-3256" {print}'
  printf '%s\n' \
    "CL-TASAKI2020-9001"$'\tmathlib_only\t'"$REVIEW_REF" \
    "CL-TASAKI2020-9002"$'\tmathlib_only\t'"$REVIEW_REF" \
    >> "$target/registry/claim-vocabulary-review.tsv"
  append_review "$target" \
    "NR-RUNTIME-0003"$'\t'"$EVENT_ID"$'\t1\tCL-TASAKI2020-3256\texact_statement_readiness\tsplit\tclosed\tcompound-claim\t'"$REVIEW_REF"
  append_correction "$target" \
    "CC-RUNTIME-0003"$'\t'"$EVENT_ID"$'\t1\tNR-RUNTIME-0003\tCL-TASAKI2020-3256\tsplit\thypothesis\thypothesis\thypothesis\thypothesis'
  printf '%s\n' \
    "SE-RUNTIME-0001"$'\t'"$EVENT_ID"$'\tCC-RUNTIME-0003\tCL-TASAKI2020-3256\t1\tnew_successor\tCL-TASAKI2020-9001' \
    "SE-RUNTIME-0002"$'\t'"$EVENT_ID"$'\tCC-RUNTIME-0003\tCL-TASAKI2020-3256\t2\tnew_successor\tCL-TASAKI2020-9002' \
    >> "$target/registry/claim-successors.tsv"
  refresh_invariants "$target"
}

replace_second_successor_with_existing() {
  local target=$1 successor=$2
  rewrite "$target/registry/claim-successors.tsv" \
    '$1=="SE-RUNTIME-0002" {$6="existing_duplicate";$7="'"$successor"'"} {print}'
  rewrite "$target/registry/claims.tsv" '$1!="CL-TASAKI2020-9002" {print}'
  rewrite "$target/registry/item-claims.tsv" '$3!="CL-TASAKI2020-9002" {print}'
  rewrite "$target/registry/claim-vocabulary-review.tsv" \
    '$1!="CL-TASAKI2020-9002" {print}'
  refresh_invariants "$target"
}

RECLASSIFY="$CASES/reclassify"
OUT_OF_SCOPE="$CASES/out-of-scope"
SPLIT="$CASES/split"
UNCHANGED="$CASES/unchanged"
make_reclassify "$RECLASSIFY"
make_out_of_scope "$OUT_OF_SCOPE"
make_split "$SPLIT"
make_unchanged "$UNCHANGED"

ITEM_EVENT1_BASE="$CASES/item-event1-base"
ITEM_EVENT1_CURRENT="$CASES/item-event1-current"
clone_commit_registry "$BASE_COMMIT" "$ITEM_EVENT1_BASE"
clone_base "$ITEM_EVENT1_CURRENT"
add_event1_source_item "$ITEM_EVENT1_CURRENT"

# Positive transition coverage comes first deliberately.  Before the dedicated
# checker exists, this is the measured TDD Red failure rather than a false
# success caused by every negative command failing with "command not found".
expect_pass event1-source-item-contract check_item_public_contract \
  "$ITEM_EVENT1_BASE" "$ITEM_EVENT1_CURRENT"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/item-missing-ledger"
rewrite "$CASES/item-missing-ledger/registry/source-item-additions.tsv" 'FNR==1 {print}'
expect_fail item-missing-ledger "unmanifested source item addition" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/item-missing-ledger"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/item-existing-reregistration"
printf '%s\n' \
  $'IA-TASAKI2020-0099\tCORPUS-NORMALIZATION-TASAKI2020-2026\tCC-TASAKI2020-0012\t2\tIT-TASAKI2020-1539\tCORPUS-NORMALIZATION-INDEPENDENT-REVIEW' \
  >> "$CASES/item-existing-reregistration/registry/source-item-additions.tsv"
expect_fail item-existing-reregistration "source item addition reuses a frozen item ID" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/item-existing-reregistration"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/item-correction-mismatch"
rewrite "$CASES/item-correction-mismatch/registry/source-item-additions.tsv" \
  '$1=="IA-TASAKI2020-0001" {$3="CC-TASAKI2020-0011"} {print}'
expect_fail item-correction-mismatch "source item addition event or correction mismatch" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/item-correction-mismatch"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/item-event-mismatch"
rewrite "$CASES/item-event-mismatch/registry/source-item-additions.tsv" \
  '$1=="IA-TASAKI2020-0001" {$2="CORPUS-NORMALIZATION-TASAKI2020-2027"} {print}'
expect_fail item-event-mismatch "source item addition event or correction mismatch" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/item-event-mismatch"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/new-item-old-claim"
rewrite "$CASES/new-item-old-claim/registry/item-claims.tsv" \
  '$1=="IT-TASAKI2020-3037" && $2==1 {$3="CL-TASAKI2020-1522"} {print}'
expect_fail new-item-old-claim "new source item contains a frozen predecessor claim" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/new-item-old-claim"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/new-item-existing-duplicate"
rewrite "$CASES/new-item-existing-duplicate/registry/item-claims.tsv" \
  '$1=="IT-TASAKI2020-3037" && $2==1 {$3="CL-TASAKI2020-0349"} {print}'
expect_fail new-item-existing-duplicate \
  "new source item contains an existing-duplicate successor" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/new-item-existing-duplicate"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/new-item-different-correction"
rewrite "$CASES/new-item-different-correction/registry/item-claims.tsv" \
  '$1=="IT-TASAKI2020-3037" && $2==1 {$3="CL-TASAKI2020-3430"} {print}'
expect_fail new-item-different-correction \
  "new source item contains a successor from a different correction" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/new-item-different-correction"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/source-item-successor-duplicate"
printf '%s\n' \
  $'IA-TASAKI2020-0098\tCORPUS-NORMALIZATION-TASAKI2020-2026\tCC-TASAKI2020-0012\t2\tIT-TASAKI2020-3038\tCORPUS-NORMALIZATION-INDEPENDENT-REVIEW' \
  >> "$CASES/source-item-successor-duplicate/registry/source-item-additions.tsv"
awk -F '\t' -v OFS='\t' '
  {print}
  $1=="IT-TASAKI2020-3037" {
    print "IT-TASAKI2020-3038","TASAKI2020","000301.0003.0002", \
      "PG-TASAKI2020-0301","unlabeled","NONE","NONE", \
      "PDF p. 301; print p. 289; §8.4; paragraph 6 duplicate", \
      "Chapter 08","chapter-08","PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1"
  }
' "$CASES/source-item-successor-duplicate/registry/source-items.tsv" \
  > "$CASES/source-item-successor-duplicate/registry/source-items.tsv.tmp"
mv "$CASES/source-item-successor-duplicate/registry/source-items.tsv.tmp" \
  "$CASES/source-item-successor-duplicate/registry/source-items.tsv"
printf '%s\n' $'IT-TASAKI2020-3038\t1\tCL-TASAKI2020-3442' \
  >> "$CASES/source-item-successor-duplicate/registry/item-claims.tsv"
expect_fail source-item-successor-duplicate \
  "correction successor occurs in more than one source item" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/source-item-successor-duplicate"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/fig-item-keeps-successors"
printf '%s\n' \
  $'IT-TASAKI2020-1539\t2\tCL-TASAKI2020-3442' \
  $'IT-TASAKI2020-1539\t3\tCL-TASAKI2020-3443' \
  >> "$CASES/fig-item-keeps-successors/registry/item-claims.tsv"
expect_fail fig-item-keeps-successors \
  "correction successor occurs in more than one source item" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/fig-item-keeps-successors"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/historical-item-edited"
rewrite "$CASES/historical-item-edited/registry/source-items.tsv" \
  '$1=="IT-TASAKI2020-1539" {$8=$8 "; drift"} {print}'
expect_fail historical-item-edited "historical source item drift" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/historical-item-edited"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/historical-item-deleted"
rewrite "$CASES/historical-item-deleted/registry/source-items.tsv" \
  '$1!="IT-TASAKI2020-1539" {print}'
expect_fail historical-item-deleted "historical source item drift" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/historical-item-deleted"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/historical-relation-moved"
rewrite "$CASES/historical-relation-moved/registry/item-claims.tsv" \
  '$1=="IT-TASAKI2020-1539" && $3=="CL-TASAKI2020-1523" {$1="IT-TASAKI2020-3037";$2=3} {print}'
expect_fail historical-relation-moved "historical source item relation drift" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/historical-relation-moved"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/item-nested-key-malformed"
rewrite "$CASES/item-nested-key-malformed/registry/source-items.tsv" \
  '$1=="IT-TASAKI2020-3037" {$3="000301.3.0001"} {print}'
expect_fail item-nested-key-malformed "bad nested source item order key" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/item-nested-key-malformed"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/item-nested-key-inverted"
rewrite "$CASES/item-nested-key-inverted/registry/source-items.tsv" \
  '$1=="IT-TASAKI2020-3037" {$3="000301.0005.0001"} {print}'
expect_fail item-nested-key-inverted "source items are not in global source order" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/item-nested-key-inverted"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/ordinary-unauthorized-item-add"
rewrite "$CASES/ordinary-unauthorized-item-add/registry/source-item-additions.tsv" \
  'FNR==1 {print}'
expect_fail ordinary-unauthorized-item-add "unmanifested source item addition" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" \
  "$CASES/ordinary-unauthorized-item-add"

EVENT2=CORPUS-NORMALIZATION-TASAKI2020-2027
EVENT2_REVIEW=CORPUS-NORMALIZATION-TASAKI2020-2027-REVIEW
EVENT2_CURRENT="$CASES/historical-event2-new-item"
clone_case "$ITEM_EVENT1_CURRENT" "$EVENT2_CURRENT"
printf '%s\n' \
  "$EVENT2"$'\t2\tTASAKI2020\tdddddddddddddddddddddddddddddddddddddddd\t'"$EVENT2_REVIEW" \
  >> "$EVENT2_CURRENT/registry/correction-events.tsv"
printf '%s\n' \
  "NR-TASAKI2020-2027-0001"$'\t'"$EVENT2"$'\t1\tCL-TASAKI2020-3256\texact_statement_readiness\tsplit\tclosed\tcompound-claim\t'"$EVENT2_REVIEW" \
  >> "$EVENT2_CURRENT/registry/claim-normalization-reviews.tsv"
printf '%s\n' \
  "CC-TASAKI2020-2027-0001"$'\t'"$EVENT2"$'\t1\tNR-TASAKI2020-2027-0001\tCL-TASAKI2020-3256\tsplit\thypothesis\thypothesis\thypothesis\thypothesis' \
  >> "$EVENT2_CURRENT/registry/claim-corrections.tsv"
event2_content='For Problem 11.4.1.a, assume the stated local decay estimate.'
event2_oid=$(printf '%s' "$event2_content" | git hash-object --stdin)
awk -F '\t' -v OFS='\t' -v review="$EVENT2_REVIEW" -v oid="$event2_oid" '
  $1=="CL-TASAKI2020-3256" {
    $12="true";$13="CL-TASAKI2020-9003";$14="compound-claim";$15=review
    print
    print "CL-TASAKI2020-9003","TASAKI2020","000528.0004.0001", \
      "PG-TASAKI2020-0528", \
      "PDF p. 528; print p. 519; paragraph 7; event 2 successor", \
      "hypothesis","hypothesis", \
      "For Problem 11.4.1.a, assume the stated local decay estimate.", \
      oid,"NONE","NONE","false","NONE","NONE","NONE"
    next
  }
  {print}
' "$EVENT2_CURRENT/registry/claims.tsv" > "$EVENT2_CURRENT/registry/claims.tsv.tmp"
mv "$EVENT2_CURRENT/registry/claims.tsv.tmp" "$EVENT2_CURRENT/registry/claims.tsv"
printf '%s\n' \
  "SE-TASAKI2020-2027-0001"$'\t'"$EVENT2"$'\tCC-TASAKI2020-2027-0001\tCL-TASAKI2020-3256\t1\tnew_successor\tCL-TASAKI2020-9003' \
  >> "$EVENT2_CURRENT/registry/claim-successors.tsv"
rewrite "$EVENT2_CURRENT/registry/claim-vocabulary-review.tsv" \
  '$1!="CL-TASAKI2020-3256" {print}'
printf '%s\n' \
  "CL-TASAKI2020-9003"$'\tmathlib_only\t'"$EVENT2_REVIEW" \
  >> "$EVENT2_CURRENT/registry/claim-vocabulary-review.tsv"
printf '%s\n' \
  "IA-TASAKI2020-0002"$'\t'"$EVENT2"$'\tCC-TASAKI2020-2027-0001\t1\tIT-TASAKI2020-3038\t'"$EVENT2_REVIEW" \
  >> "$EVENT2_CURRENT/registry/source-item-additions.tsv"
awk -F '\t' -v OFS='\t' '
  {print}
  $1=="IT-TASAKI2020-3034" {
    print "IT-TASAKI2020-3038","TASAKI2020","000528.0004.0001", \
      "PG-TASAKI2020-0528","unlabeled","NONE","NONE", \
      "PDF p. 528; print p. 519; paragraph 7; event 2 successor", \
      "Solutions","solutions","PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1"
  }
' "$EVENT2_CURRENT/registry/source-items.tsv" > "$EVENT2_CURRENT/registry/source-items.tsv.tmp"
mv "$EVENT2_CURRENT/registry/source-items.tsv.tmp" \
  "$EVENT2_CURRENT/registry/source-items.tsv"
awk -F '\t' -v OFS='\t' '
  {print}
  $1=="IT-TASAKI2020-3034" {print "IT-TASAKI2020-3038",1,"CL-TASAKI2020-9003"}
' "$EVENT2_CURRENT/registry/item-claims.tsv" > "$EVENT2_CURRENT/registry/item-claims.tsv.tmp"
mv "$EVENT2_CURRENT/registry/item-claims.tsv.tmp" \
  "$EVENT2_CURRENT/registry/item-claims.tsv"
refresh_invariants "$EVENT2_CURRENT"
expect_pass historical-event2-new-item "$CHECK_CORRECTIONS" --fixture-dirs \
  "$ITEM_EVENT1_CURRENT" "$EVENT2_CURRENT"

expect_pass minimal-reclassify "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$RECLASSIFY"
expect_pass minimal-out-of-scope "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$OUT_OF_SCOPE"
expect_pass minimal-split "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$SPLIT"
expect_pass minimal-unchanged-review "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$UNCHANGED"

# The event source owns every review, correction, predecessor, successor, and
# invariant transition.  A token-shaped but unknown source must not silently
# inherit the first source-invariant row.
clone_case "$RECLASSIFY" "$CASES/event-source-bogus"
rewrite "$CASES/event-source-bogus/registry/correction-events.tsv" \
  '$1=="'"$EVENT_ID"'" {$3="BOGUS"} {print}'
expect_fail event-source-bogus "correction event source mismatch" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/event-source-bogus"

clone_case "$UNCHANGED" "$CASES/unchanged-unknown-claim"
rewrite "$CASES/unchanged-unknown-claim/registry/claim-normalization-reviews.tsv" \
  '$1=="NR-RUNTIME-UNCHANGED" {$4="CL-TASAKI2020-9999"} {print}'
expect_fail unchanged-unknown-claim "normalization review targets an unknown claim" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/unchanged-unknown-claim"

clone_case "$SPLIT" "$CASES/existing-duplicate-tombstone"
replace_second_successor_with_existing \
  "$CASES/existing-duplicate-tombstone" CL-TASAKI2020-0287
expect_fail existing-duplicate-tombstone "existing duplicate successor is not active" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/existing-duplicate-tombstone"

clone_case "$SPLIT" "$CASES/existing-duplicate-out-of-scope"
replace_second_successor_with_existing \
  "$CASES/existing-duplicate-out-of-scope" CL-TASAKI2020-2947
expect_fail existing-duplicate-out-of-scope \
  "existing duplicate successor is not a formalization target" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/existing-duplicate-out-of-scope"

MULTI_BASE="$CASES/multi-source-base"
clone_base "$MULTI_BASE"
add_source_b "$MULTI_BASE"

clone_case "$SPLIT" "$CASES/existing-duplicate-different-source"
add_source_b "$CASES/existing-duplicate-different-source"
replace_second_successor_with_existing \
  "$CASES/existing-duplicate-different-source" CL-SRB-0001
expect_fail existing-duplicate-different-source "correction successor source mismatch" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$MULTI_BASE" \
  "$CASES/existing-duplicate-different-source"

prepare_event_from "$MULTI_BASE" "$CASES/multi-source-selected-second" SRB
append_review "$CASES/multi-source-selected-second" \
  "NR-RUNTIME-SRB-UNCHANGED"$'\t'"$EVENT_ID"$'\t1\tCL-SRB-0001\texact_statement_readiness\tunchanged\tclosed\texact-statement-ready\t'"$REVIEW_REF"
expect_pass multi-source-selected-invariant-second \
  "$CHECK_CORRECTIONS" --fixture-dirs "$MULTI_BASE" \
  "$CASES/multi-source-selected-second"

clone_case "$CASES/multi-source-selected-second" \
  "$CASES/multi-source-selected-second-stale"
rewrite "$CASES/multi-source-selected-second-stale/registry/source-invariants.tsv" \
  '$1=="SRB" {$3=$3+1} {print}'
expect_fail multi-source-selected-invariant-stale "census invariant count is stale" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$MULTI_BASE" \
  "$CASES/multi-source-selected-second-stale"

prepare_event_from "$MULTI_BASE" "$CASES/review-source-mismatch" TASAKI2020
append_review "$CASES/review-source-mismatch" \
  "NR-RUNTIME-SRB-MISMATCH"$'\t'"$EVENT_ID"$'\t1\tCL-SRB-0001\texact_statement_readiness\tunchanged\tclosed\texact-statement-ready\t'"$REVIEW_REF"
expect_fail review-source-mismatch "normalization review source mismatch" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$MULTI_BASE" \
  "$CASES/review-source-mismatch"

prepare_event_from "$MULTI_BASE" "$CASES/correction-predecessor-source-mismatch" \
  TASAKI2020
rewrite "$CASES/correction-predecessor-source-mismatch/registry/claims.tsv" \
  '$1=="CL-SRB-0001" {$6="definition";$7="definition"} {print}'
rewrite "$CASES/correction-predecessor-source-mismatch/registry/claim-vocabulary-review.tsv" \
  '$1=="CL-SRB-0001" {$3="'"$REVIEW_REF"'"} {print}'
append_review "$CASES/correction-predecessor-source-mismatch" \
  "NR-RUNTIME-SRB-RECLASSIFY"$'\t'"$EVENT_ID"$'\t1\tCL-SRB-0001\texact_statement_readiness\treclassify\tclosed\twrong-source-kind\t'"$REVIEW_REF"
append_correction "$CASES/correction-predecessor-source-mismatch" \
  "CC-RUNTIME-SRB-RECLASSIFY"$'\t'"$EVENT_ID"$'\t1\tNR-RUNTIME-SRB-RECLASSIFY\tCL-SRB-0001\treclassify\tassertion\ttheorem\tdefinition\tdefinition'
refresh_invariants "$CASES/correction-predecessor-source-mismatch" SRB
expect_fail correction-predecessor-source-mismatch \
  "correction predecessor source mismatch" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$MULTI_BASE" \
  "$CASES/correction-predecessor-source-mismatch"

clone_case "$SPLIT" "$CASES/new-successor-source-mismatch"
add_source_b "$CASES/new-successor-source-mismatch"
rewrite "$CASES/new-successor-source-mismatch/registry/claims.tsv" \
  '$1=="CL-TASAKI2020-9002" {$2="SRB";$4="PG-SRB-0001";$3="000002.0001"} {print}'
refresh_invariants "$CASES/new-successor-source-mismatch"
refresh_invariants "$CASES/new-successor-source-mismatch" SRB
expect_fail new-successor-source-mismatch "new successor source mismatch" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$MULTI_BASE" \
  "$CASES/new-successor-source-mismatch"

clone_case "$RECLASSIFY" "$CASES/event-position-gap"
rewrite "$CASES/event-position-gap/registry/correction-events.tsv" \
  '$1=="'"$EVENT_ID"'" {$2=3} {print}'
expect_fail event-position-gap "invalid correction event ledger" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/event-position-gap"

clone_case "$RECLASSIFY" "$CASES/review-position-gap"
rewrite "$CASES/review-position-gap/registry/claim-normalization-reviews.tsv" \
  '$1=="NR-RUNTIME-0001" {$3=2} {print}'
expect_fail review-position-gap "invalid claim normalization review ledger" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/review-position-gap"

clone_case "$RECLASSIFY" "$CASES/correction-position-gap"
rewrite "$CASES/correction-position-gap/registry/claim-corrections.tsv" \
  '$1=="CC-RUNTIME-0001" {$3=2} {print}'
expect_fail correction-position-gap "invalid claim correction ledger" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/correction-position-gap"

clone_case "$RECLASSIFY" "$CASES/correction-review-owner"
rewrite "$CASES/correction-review-owner/registry/claim-corrections.tsv" \
  '$1=="CC-RUNTIME-0001" {$4="NR-TASAKI2020-0001"} {print}'
expect_fail correction-review-owner "invalid claim correction ledger" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/correction-review-owner"

clone_case "$SPLIT" "$CASES/successor-correction-owner"
rewrite "$CASES/successor-correction-owner/registry/claim-successors.tsv" \
  '$1=="SE-RUNTIME-0001" {$3="CC-TASAKI2020-0001"} {print}'
expect_fail successor-correction-owner "successor provenance has no split correction" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/successor-correction-owner"

# A split is a decomposition, so at least one edge must introduce a genuinely
# new atomic claim.  Pointing only at pre-existing claims is not a split.
clone_case "$SPLIT" "$CASES/split-existing-only"
rewrite "$CASES/split-existing-only/registry/claims.tsv" '
  $1=="CL-TASAKI2020-3256" {$13="CL-TASAKI2020-0001"}
  $1!="CL-TASAKI2020-9001" && $1!="CL-TASAKI2020-9002" {print}
'
rewrite "$CASES/split-existing-only/registry/claim-successors.tsv" '
  $1=="SE-RUNTIME-0001" {$6="existing_duplicate";$7="CL-TASAKI2020-0001"}
  $1=="SE-RUNTIME-0002" {$6="existing_duplicate";$7="CL-TASAKI2020-0002"}
  {print}
'
rewrite "$CASES/split-existing-only/registry/item-claims.tsv" \
  '$3!="CL-TASAKI2020-9001" && $3!="CL-TASAKI2020-9002" {print}'
rewrite "$CASES/split-existing-only/registry/claim-vocabulary-review.tsv" \
  '$1!="CL-TASAKI2020-9001" && $1!="CL-TASAKI2020-9002" {print}'
refresh_invariants "$CASES/split-existing-only"
expect_fail split-existing-only "split requires a new successor" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/split-existing-only"

clone_case "$RECLASSIFY" "$CASES/missing-event-review"
rewrite "$CASES/missing-event-review/registry/correction-events.tsv" '$1!="'"$EVENT_ID"'" {print}'
expect_fail missing-event-review "correction event is not reviewed" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/missing-event-review"

clone_case "$RECLASSIFY" "$CASES/missing-ledger"
rewrite "$CASES/missing-ledger/registry/claim-corrections.tsv" '$2!="'"$EVENT_ID"'" {print}'
expect_fail disposition-without-ledger "invalid claim correction ledger" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/missing-ledger"

clone_case "$RECLASSIFY" "$CASES/unmanifested-drift"
rewrite "$CASES/unmanifested-drift/registry/claims.tsv" \
  '$1=="CL-TASAKI2020-0003" {$8=$8 " Unreviewed drift."} {print}'
refresh_invariants "$CASES/unmanifested-drift"
expect_fail unmanifested-claim-drift "unmanifested claim drift" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/unmanifested-drift"

clone_case "$SPLIT" "$CASES/split-provenance-missing"
rewrite "$CASES/split-provenance-missing/registry/claim-successors.tsv" '$2!="'"$EVENT_ID"'" {print}'
expect_fail split-provenance-missing "split successor provenance is incomplete" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/split-provenance-missing"

clone_case "$SPLIT" "$CASES/split-duplicate-position"
rewrite "$CASES/split-duplicate-position/registry/claim-successors.tsv" \
  '$1=="SE-RUNTIME-0002" {$5=1} {print}'
expect_fail split-duplicate-position "duplicate or noncontiguous successor position" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/split-duplicate-position"

clone_case "$SPLIT" "$CASES/split-missing-successor"
rewrite "$CASES/split-missing-successor/registry/claim-successors.tsv" \
  '$1=="SE-RUNTIME-0002" {$7="CL-TASAKI2020-9999"} {print}'
rewrite "$CASES/split-missing-successor/registry/claims.tsv" \
  '$1!="CL-TASAKI2020-9002" {print}'
rewrite "$CASES/split-missing-successor/registry/item-claims.tsv" \
  '$3!="CL-TASAKI2020-9002" {print}'
rewrite "$CASES/split-missing-successor/registry/claim-vocabulary-review.tsv" \
  '$1!="CL-TASAKI2020-9002" {print}'
refresh_invariants "$CASES/split-missing-successor"
expect_fail split-missing-successor "unknown correction successor" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/split-missing-successor"

clone_case "$SPLIT" "$CASES/split-id-reuse"
rewrite "$CASES/split-id-reuse/registry/claim-successors.tsv" \
  '$1=="SE-RUNTIME-0002" {$7="CL-TASAKI2020-0001"} {print}'
rewrite "$CASES/split-id-reuse/registry/claims.tsv" \
  '$1!="CL-TASAKI2020-9002" {print}'
rewrite "$CASES/split-id-reuse/registry/item-claims.tsv" \
  '$3!="CL-TASAKI2020-9002" {print}'
rewrite "$CASES/split-id-reuse/registry/claim-vocabulary-review.tsv" \
  '$1!="CL-TASAKI2020-9002" {print}'
refresh_invariants "$CASES/split-id-reuse"
expect_fail split-id-reuse "new successor reuses a frozen claim ID" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/split-id-reuse"

clone_case "$SPLIT" "$CASES/tombstone-review-remains"
printf '%s\n' \
  "CL-TASAKI2020-3256"$'\tmathlib_only\t'"$REVIEW_REF" \
  >> "$CASES/tombstone-review-remains/registry/claim-vocabulary-review.tsv"
expect_fail tombstone-review-remains "excluded predecessor retains vocabulary review" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/tombstone-review-remains"

clone_case "$SPLIT" "$CASES/tombstone-use-remains"
printf '%s\n' $'CL-TASAKI2020-3256\tVO-TASAKI2020-0001' \
  >> "$CASES/tombstone-use-remains/registry/claim-vocabulary.tsv"
expect_fail tombstone-use-remains "excluded predecessor retains vocabulary use" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/tombstone-use-remains"

clone_case "$SPLIT" "$CASES/successor-item-missing"
rewrite "$CASES/successor-item-missing/registry/item-claims.tsv" \
  '$3!="CL-TASAKI2020-9002" {print}'
expect_fail successor-item-missing "active successor lacks the predecessor item" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/successor-item-missing"

clone_case "$SPLIT" "$CASES/successor-item-duplicate"
printf '%s\n' $'IT-TASAKI2020-3034\t4\tCL-TASAKI2020-9001' \
  >> "$CASES/successor-item-duplicate/registry/item-claims.tsv"
expect_fail successor-item-duplicate "active successor has duplicate item provenance" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/successor-item-duplicate"

clone_case "$RECLASSIFY" "$CASES/unrelated-row"
rewrite "$CASES/unrelated-row/registry/source-items.tsv" \
  '$1=="IT-TASAKI2020-0003" {$7="Unreviewed title drift"} {print}'
expect_fail unrelated-frozen-row "unrelated frozen registry drift" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/unrelated-row"

clone_case "$RECLASSIFY" "$CASES/unrelated-oid"
rewrite "$CASES/unrelated-oid/registry/claims.tsv" \
  '$1=="CL-TASAKI2020-0003" {$9="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"} {print}'
refresh_invariants "$CASES/unrelated-oid"
expect_fail unrelated-frozen-oid "unmanifested claim drift" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/unrelated-oid"

clone_case "$RECLASSIFY" "$CASES/unrelated-locator"
rewrite "$CASES/unrelated-locator/registry/claims.tsv" \
  '$1=="CL-TASAKI2020-0003" {$5=$5 "; drift"} {print}'
refresh_invariants "$CASES/unrelated-locator"
expect_fail unrelated-frozen-locator "unmanifested claim drift" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/unrelated-locator"

clone_case "$RECLASSIFY" "$CASES/unrelated-order"
rewrite "$CASES/unrelated-order/registry/claims.tsv" \
  '$1=="CL-TASAKI2020-0003" {$3="000015.0099"} {print}'
refresh_invariants "$CASES/unrelated-order"
expect_fail unrelated-frozen-order "unmanifested claim drift" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/unrelated-order"

clone_case "$OUT_OF_SCOPE" "$CASES/stale-count"
rewrite "$CASES/stale-count/registry/source-invariants.tsv" \
  'FNR==2 {$4=3172} {print}'
expect_fail stale-formalization-target-count "formalization target count is stale" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/stale-count"

clone_case "$RECLASSIFY" "$CASES/stale-oid"
rewrite "$CASES/stale-oid/registry/source-invariants.tsv" \
  'FNR==2 {$7="0000000000000000000000000000000000000000"} {print}'
expect_fail stale-census-oid "census OID is stale" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/stale-oid"

clone_case "$RECLASSIFY" "$CASES/final-counts-without-final-corpus"
rewrite "$CASES/final-counts-without-final-corpus/registry/source-invariants.tsv" \
  'FNR==2 {$3=$3+1;$4=$4+1} {print}'
expect_fail final-counts-are-derived "census invariant count is stale" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/final-counts-without-final-corpus"

clone_case "$SPLIT" "$CASES/contentless-true"
rewrite "$CASES/contentless-true/registry/claims.tsv" \
  '$1=="CL-TASAKI2020-9002" {$8="True."} {print}'
refresh_invariants "$CASES/contentless-true"
expect_fail contentless-true "contentless correction surrogate" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/contentless-true"

clone_case "$SPLIT" "$CASES/successor-oid-pending"
rewrite "$CASES/successor-oid-pending/registry/claims.tsv" \
  '$1=="CL-TASAKI2020-9002" {$9="PENDING"} {print}'
refresh_invariants "$CASES/successor-oid-pending"
expect_fail successor-oid-pending "new correction successor lacks a frozen content OID" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/successor-oid-pending"

clone_case "$SPLIT" "$CASES/successor-oid-stale"
rewrite "$CASES/successor-oid-stale/registry/claims.tsv" \
  '$1=="CL-TASAKI2020-9002" {$9="0000000000000000000000000000000000000000"} {print}'
refresh_invariants "$CASES/successor-oid-stale"
expect_fail successor-oid-stale "new correction successor content OID is stale" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/successor-oid-stale"

clone_case "$RECLASSIFY" "$CASES/axiom-artifact"
printf '%s\n' \
  $'AX-PROJECT-9001\tLatticeSystem.Axioms.ContentlessPredicate.correctionAxiom\tLatticeSystem.Axioms.ContentlessPredicate\tcontentless_predicate\tTASAKI2020\tcorrection-surrogate\treplace-with-source-content' \
  >> "$CASES/axiom-artifact/registry/axioms.tsv"
printf '%s\n' $'CL-TASAKI2020-0001\tAX-PROJECT-9001' \
  >> "$CASES/axiom-artifact/registry/claim-axioms.tsv"
expect_fail axiom-artifact "correction event introduces an axiom artifact" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/axiom-artifact"

clone_case "$RECLASSIFY" "$CASES/r4-artifact"
printf '%s\n' \
  $'CL-TASAKI2020-0001\tLatticeSystem.Claims.TASAKI2020.statement0001\tLatticeSystem.Claims.TASAKI2020.claim0001\tLatticeSystem.Claims.TASAKI2020.Front\tPENDING\tNONE' \
  >> "$CASES/r4-artifact/registry/bindings.tsv"
expect_fail r4-artifact "correction event introduces an R4 artifact" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/r4-artifact"

[[ $(baseline_digest) == "$BASELINE_DIGEST" ]] || {
  echo "test-claim-corrections-runtime: immutable runtime base changed" >&2
  exit 1
}
[[ -z $(git -C "$PROJECT_ROOT" ls-files 'fixtures/**') ]] || {
  echo "test-claim-corrections-runtime: tracked fixtures are forbidden" >&2
  exit 1
}

echo "test-claim-corrections-runtime: ok"
