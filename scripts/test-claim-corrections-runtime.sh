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
EVENT1_COMMIT=cf4a289e7c766554c8821e167eddac2c3e291c2a
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
PASS_COUNT=0
REJECT_COUNT=0

expect_pass() {
  local label=$1
  shift
  local output
  if ! output=$("$@" 2>&1); then
    echo "test-claim-corrections-runtime: expected pass: $label" >&2
    echo "$output" >&2
    exit 1
  fi
  PASS_COUNT=$((PASS_COUNT + 1))
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
  if [[ "$label" == adapter-old-populated-* ]]; then
    printf '%s\n' "$output"
  fi
  REJECT_COUNT=$((REJECT_COUNT + 1))
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

adapt_empty_r4_schemas() {
  local target=$1 name path expected
  # Historical source-data fixtures need current infrastructure headers. Never
  # reinterpret populated artifact rows or rewrite a current-schema table.
  for name in bindings.tsv axioms.tsv claim-context.tsv statement-modules.tsv statement-imports.tsv; do
    path="$target/registry/$name"
    expected=$(head -n 1 "$PROJECT_ROOT/registry/$name")
    if [[ ! -f "$path" ]]; then
      printf '%s\n' "$expected" > "$path"
    elif [[ $(head -n 1 "$path") != "$expected" ]]; then
      [[ $(awk 'END {print NR}' "$path") -eq 1 ]] || {
        echo "test-claim-corrections-runtime: cannot migrate populated historical R4 fixture: $name" >&2
        return 1
      }
      printf '%s\n' "$expected" > "$path"
    fi
  done
}

clone_commit_registry() {
  local commit=$1 target=$2 path
  mkdir -p "$target/registry"
  while IFS= read -r path; do
    git -C "$PROJECT_ROOT" show "$commit:$path" > "$target/$path"
  done < <(git -C "$PROJECT_ROOT" ls-tree -r --name-only "$commit" registry)
  if [[ ! -f "$target/registry/claim-content-amendments.tsv" ]]; then
    printf '%s\n' $'amendment_id\tevent_id\tcorrection_id\tclaim_id\told_content_oid\tnew_content_oid\tpage_source_oid\treview_ref' > "$target/registry/claim-content-amendments.tsv"
  fi
  adapt_empty_r4_schemas "$target"
}

rewrite() {
  local file=$1 program=$2
  awk -F '\t' -v OFS='\t' "$program" "$file" > "$file.tmp"
  mv "$file.tmp" "$file"
}

prepare_event() {
  local target=$1 position
  clone_base "$target"
  position=$(awk 'END {print NR}' "$target/registry/correction-events.tsv")
  printf '%s\n' "$EVENT_ID"$'\t'"$position"$'\tTASAKI2020\t'"$BASE_COMMIT"$'\t'"$REVIEW_REF" >> "$target/registry/correction-events.tsv"
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
  local base=$1 target=$2 source=$3 position
  clone_case "$base" "$target"
  position=$(awk 'END {print NR}' "$target/registry/correction-events.tsv")
  printf '%s\n' \
    "$EVENT_ID"$'\t'"$position"$'\t'"$source"$'\t'"$BASE_COMMIT"$'\t'"$REVIEW_REF" \
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
clone_commit_registry "$EVENT1_COMMIT" "$ITEM_EVENT1_CURRENT"
add_event1_source_item "$ITEM_EVENT1_CURRENT"

# Positive transition coverage comes first deliberately.  Before the dedicated
# checker exists, this is the measured TDD Red failure rather than a false
# success caused by every negative command failing with "command not found".
expect_pass event1-source-item-contract check_item_public_contract \
  "$ITEM_EVENT1_BASE" "$ITEM_EVENT1_CURRENT"

# Check the adapter itself independently of source-event rejection. Its normal
# historical input is empty; a current-schema table may already carry rows.
check_empty_r4_headers() {
  local target=$1 name
  for name in bindings.tsv axioms.tsv claim-context.tsv statement-modules.tsv statement-imports.tsv; do
    [[ $(head -n 1 "$target/registry/$name") == $(head -n 1 "$PROJECT_ROOT/registry/$name") ]] || return 1
    [[ $(awk 'END {print NR}' "$target/registry/$name") -eq 1 ]] || return 1
  done
}
expect_pass adapter-historical-empty-headers check_empty_r4_headers "$ITEM_EVENT1_CURRENT"

ADAPTER_POPULATED="$CASES/adapter-current-populated"
clone_base "$ADAPTER_POPULATED"
printf '%s\n' $'CL-TASAKI2020-0001\tLatticeSystem.Claims.Front.statement0001\tNONE\tLatticeSystem.Claims.Front\tdefinition\tnotation_relation\tPENDING\tPENDING\tdefinitional\tNONE\tNONE\tNONE\tNONE\tNONE\tRUNTIME-REVIEW' >> "$ADAPTER_POPULATED/registry/bindings.tsv"
printf '%s\n' $'AX-PROJECT-9001\tLatticeSystem.Axioms.State.fixture\tLatticeSystem.Axioms.State\tstate\tfixture\tfixture\tremove\tPENDING' >> "$ADAPTER_POPULATED/registry/axioms.tsv"
printf '%s\n' $'CL-TASAKI2020-0002\t1\tCL-TASAKI2020-0001\tterm_reference\tinherited\tRUNTIME-REVIEW' >> "$ADAPTER_POPULATED/registry/claim-context.tsv"
printf '%s\n' $'LatticeSystem.Claims.Front\tLatticeSystem/Claims/Front.lean\tleaf' >> "$ADAPTER_POPULATED/registry/statement-modules.tsv"
printf '%s\n' $'LatticeSystem.Claims.Front\t1\tMathlib\ttrue\tfalse\tfalse' >> "$ADAPTER_POPULATED/registry/statement-imports.tsv"
check_adapter_preserves_current() {
  local target=$1 before after
  before=$(find "$target/registry" -type f -print0 | LC_ALL=C sort -z | xargs -0 shasum | shasum)
  adapt_empty_r4_schemas "$target" || return
  after=$(find "$target/registry" -type f -print0 | LC_ALL=C sort -z | xargs -0 shasum | shasum)
  [[ "$before" == "$after" ]]
}
expect_pass adapter-current-populated-preserved check_adapter_preserves_current "$ADAPTER_POPULATED"
for name in bindings.tsv axioms.tsv; do
  target="$CASES/adapter-old-populated-${name%.tsv}"
  clone_base "$target"
  git -C "$PROJECT_ROOT" show "$BASE_COMMIT:registry/$name" > "$target/registry/$name"
  printf '%s\n' $'historical\tpopulated\tartifact\trow\tmust\tremain\tunchanged' >> "$target/registry/$name"
  expect_fail "adapter-old-populated-$name" "cannot migrate populated historical R4 fixture: $name" \
    adapt_empty_r4_schemas "$target"
done

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/item-addition-id-duplicate"
printf '%s\n' \
  $'IA-TASAKI2020-0001\tCORPUS-NORMALIZATION-TASAKI2020-2026\tCC-TASAKI2020-0012\t2\tIT-TASAKI2020-3038\tCORPUS-NORMALIZATION-INDEPENDENT-REVIEW' \
  >> "$CASES/item-addition-id-duplicate/registry/source-item-additions.tsv"
awk -F '\t' -v OFS='\t' '
  {print}
  $1=="IT-TASAKI2020-3037" {
    print "IT-TASAKI2020-3038","TASAKI2020","000301.0003.0002", \
      "PG-TASAKI2020-0301","unlabeled","NONE","NONE", \
      "PDF p. 301; print p. 289; §8.4; paragraph 6 duplicate ID", \
      "Chapter 08","chapter-08","PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1"
  }
' "$CASES/item-addition-id-duplicate/registry/source-items.tsv" \
  > "$CASES/item-addition-id-duplicate/registry/source-items.tsv.tmp"
mv "$CASES/item-addition-id-duplicate/registry/source-items.tsv.tmp" \
  "$CASES/item-addition-id-duplicate/registry/source-items.tsv"
rewrite "$CASES/item-addition-id-duplicate/registry/item-claims.tsv" '
  $1=="IT-TASAKI2020-3037" && $3=="CL-TASAKI2020-3443" {
    print "IT-TASAKI2020-3038",1,$3
    next
  }
  {print}
'
expect_fail item-addition-id-duplicate "duplicate source item addition ID" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/item-addition-id-duplicate"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/item-double-manifest"
printf '%s\n' \
  $'IA-TASAKI2020-0099\tCORPUS-NORMALIZATION-TASAKI2020-2026\tCC-TASAKI2020-0012\t2\tIT-TASAKI2020-3037\tCORPUS-NORMALIZATION-INDEPENDENT-REVIEW' \
  >> "$CASES/item-double-manifest/registry/source-item-additions.tsv"
expect_fail item-double-manifest "source item is manifested more than once" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/item-double-manifest"

clone_case "$ITEM_EVENT1_CURRENT" "$CASES/item-addition-id-invalid"
rewrite "$CASES/item-addition-id-invalid/registry/source-item-additions.tsv" \
  '$1=="IA-TASAKI2020-0001" {$1="IA-bad"} {print}'
expect_fail item-addition-id-invalid "bad source item addition ID" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_BASE" \
  "$CASES/item-addition-id-invalid"

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
  "$CHECK_CORRECTIONS" --fixture-dirs "$ITEM_EVENT1_CURRENT" \
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
  '$1=="'"$EVENT_ID"'" {$2=$2+1} {print}'
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
expect_fail successor-correction-owner "successor provenance has no split or duplicate retirement correction" \
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
  'FNR==2 {$4=$4+1} {print}'
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
  $'AX-PROJECT-9001\tLatticeSystem.Axioms.ContentlessPredicate.correctionAxiom\tLatticeSystem.Axioms.ContentlessPredicate\tcontentless_predicate\tTASAKI2020\tcorrection-surrogate\treplace-with-source-content\tPENDING' \
  >> "$CASES/axiom-artifact/registry/axioms.tsv"
printf '%s\n' $'CL-TASAKI2020-0001\tAX-PROJECT-9001' \
  >> "$CASES/axiom-artifact/registry/claim-axioms.tsv"
expect_fail axiom-artifact "correction event introduces an axiom artifact" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/axiom-artifact"

clone_case "$RECLASSIFY" "$CASES/r4-artifact"
printf '%s\n' \
  $'CL-TASAKI2020-0001\tLatticeSystem.Claims.Front.statement0001\tLatticeSystem.Claims.Front.claim0001\tLatticeSystem.Claims.Front\tdefinition\tproof_proposition\tPENDING\tPENDING\tproof_stub\ttheorem\tPENDING\tNONE\tNONE\tNONE\tCORRECTION-FIXTURE-REVIEW' \
  >> "$CASES/r4-artifact/registry/bindings.tsv"
expect_fail r4-artifact "correction event introduces an R4 artifact" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/r4-artifact"

# A fresh successor has one creation owner, even across split corrections.
# A map that only remembers the last owner would silently accept this case.
clone_case "$SPLIT" "$CASES/split-two-creation-owners"
rewrite "$CASES/split-two-creation-owners/registry/claims.tsv" \
  '$1=="CL-TASAKI2020-0001" {$12="true";$13="CL-TASAKI2020-9001";$14="compound-claim";$15="'"$REVIEW_REF"'"} {print}'
rewrite "$CASES/split-two-creation-owners/registry/claim-vocabulary-review.tsv" \
  '$1!="CL-TASAKI2020-0001" {print}'
append_review "$CASES/split-two-creation-owners" \
  "NR-RUNTIME-TWO-OWNERS"$'\t'"$EVENT_ID"$'\t2\tCL-TASAKI2020-0001\texact_statement_readiness\tsplit\tclosed\tcompound-claim\t'"$REVIEW_REF"
append_correction "$CASES/split-two-creation-owners" \
  "CC-RUNTIME-TWO-OWNERS"$'\t'"$EVENT_ID"$'\t2\tNR-RUNTIME-TWO-OWNERS\tCL-TASAKI2020-0001\tsplit\tnotation\tnotation\tnotation\tnotation'
printf '%s\n' \
  "SE-RUNTIME-TWO-OWNERS"$'\t'"$EVENT_ID"$'\tCC-RUNTIME-TWO-OWNERS\tCL-TASAKI2020-0001\t1\tnew_successor\tCL-TASAKI2020-9001' \
  >> "$CASES/split-two-creation-owners/registry/claim-successors.tsv"
refresh_invariants "$CASES/split-two-creation-owners"
expect_fail split-two-creation-owners "split successor provenance is incomplete" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/split-two-creation-owners"

# Every R4 table is guarded, not only bindings.
clone_case "$RECLASSIFY" "$CASES/r4-artifact-claim-context"
printf '%s\n' $'CL-TASAKI2020-0002\t1\tCL-TASAKI2020-0001\tassumption\tsame_item\tCORRECTION-FIXTURE-REVIEW' \
  >> "$CASES/r4-artifact-claim-context/registry/claim-context.tsv"
expect_fail r4-artifact-claim-context "correction event introduces an R4 artifact" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/r4-artifact-claim-context"

clone_case "$RECLASSIFY" "$CASES/r4-artifact-statement-modules"
printf '%s\n' $'LatticeSystem.Claims.Front\tLatticeSystem/Claims/Front.lean\tleaf' \
  >> "$CASES/r4-artifact-statement-modules/registry/statement-modules.tsv"
expect_fail r4-artifact-statement-modules "correction event introduces an R4 artifact" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/r4-artifact-statement-modules"

clone_case "$RECLASSIFY" "$CASES/r4-artifact-statement-imports"
printf '%s\n' $'LatticeSystem.Claims.Front\t1\tMathlib\ttrue\tfalse\tfalse' \
  >> "$CASES/r4-artifact-statement-imports/registry/statement-imports.tsv"
expect_fail r4-artifact-statement-imports "correction event introduces an R4 artifact" \
  "$CHECK_CORRECTIONS" --fixture-dirs "$BASE" "$CASES/r4-artifact-statement-imports"

# Keep the new protocol cases synthetic: no source assertion is introduced by
# these fixtures, and the production-derived baseline above remains untouched.
python3 - "$PROJECT_ROOT" "$TMP" <<'PY'
import csv
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

project, temporary = map(Path, sys.argv[1:])
retirement_root = temporary / 'duplicate-retirement'
retirement_root.mkdir()
passed = rejected = 0
source = 'SRD'
predecessor = 'CL-SRD-0001'
canonical = 'CL-SRD-0002'
other = 'CL-SRD-0003'
event = 'RUNTIME-DUPLICATE-RETIREMENT'
review = event + '-REVIEW'
correction = 'CC-RUNTIME-DUPLICATE-0001'

def table(root, name):
    with (root / 'registry' / name).open(newline='', encoding='utf-8') as stream:
        return list(csv.reader(stream, delimiter='\t', quoting=csv.QUOTE_NONE))

def write(root, name, rows):
    with (root / 'registry' / name).open('w', newline='', encoding='utf-8') as stream:
        csv.writer(stream, delimiter='\t', lineterminator='\n',
                   quoting=csv.QUOTE_NONE, quotechar=None).writerows(rows)

def append(root, name, row):
    write(root, name, table(root, name) + [row])

def record(root, name, identifier):
    return next(row for row in table(root, name)[1:] if row[0] == identifier)

def mutate(root, name, identifier, column, value):
    rows = table(root, name)
    for row in rows[1:]:
        if row[0] == identifier:
            row[column] = value
    write(root, name, rows)

def remove(root, name, identifier):
    rows = table(root, name)
    write(root, name, rows[:1] + [r for r in rows[1:] if r[0] != identifier])

def clone(before, name):
    after = retirement_root / name
    after.mkdir()
    shutil.copytree(before / 'registry', after / 'registry')
    return after

def require(condition, message):
    if not condition:
        raise SystemExit('test-claim-corrections-runtime: duplicate oracle: ' + message)

def blob(text):
    return subprocess.check_output(['git', 'hash-object', '--stdin'],
                                   input=text.encode('utf-8'), cwd=project).decode().strip()

def refresh(root):
    pages, claims = table(root, 'pages.tsv')[1:], table(root, 'claims.tsv')[1:]
    rows = table(root, 'source-invariants.tsv')
    for row in rows[1:]:
        active = [r for r in claims if r[1] == row[0] and r[11] == 'false']
        row[2:7] = [str(len(active)), str(sum(r[5] != 'out_of_scope' for r in active)),
                    str(sum(r[6] == 'equation' for r in active)),
                    str(sum(p[1] == row[0] and p[0] not in {r[3] for r in active} for p in pages)),
                    blob(''.join('\t'.join(r) + '\n' for r in pages + claims if r[1] == row[0]))]
    write(root, 'source-invariants.tsv', rows)

def expect(label, expected, command, diagnostic=''):
    global passed, rejected
    result = subprocess.run(list(map(str, command)), text=True, capture_output=True)
    output = result.stdout + result.stderr
    require((result.returncode == 0) == expected and diagnostic in output,
            label + ' (completed ' + str(passed) + ' positive, ' + str(rejected) +
            ' rejection cases)\n' + output)
    if expected:
        passed += 1
    else:
        rejected += 1
    return output

checker = project / 'scripts/check-claim-corrections.sh'
base_checker = project / 'scripts/check-base-diff.sh'
selector = project / 'scripts/check-base-diff-ci.sh'

def transition(label, before, after, expected=True, diagnostic='', both=False):
    expect(label + '-dedicated', expected,
           [checker, '--fixture-dirs', before, after], diagnostic)
    if both:
        expect(label + '-base', expected,
               [base_checker, '--correction-event', event, '--fixture-dirs', before, after], diagnostic)

def static(label, root):
    expect(label + '-registry', True, [project / 'scripts/check-registry.sh', root],
           'check-registry: ok')
    expect(label + '-items', True, [project / 'scripts/check-source-items.sh', root],
           'check-source-items: ok')

base = clone(project, 'base')
append(base, 'sources.tsv', [source, 'TR-TASAKI', '2', 'paper', 'SRD2026',
       'Runtime duplicate protocol', 'Runtime Author', '2026', 'v1', 'none',
       'NONE', 'NONE', 'runtime-duplicate', 'runtime-duplicate.pdf', 'a'*40, 'b'*40, 'frozen'])
append(base, 'source-progress.tsv', [source, 'vocabulary_reviewed', 'RUNTIME-DUPLICATE-BASE-REVIEW'])
append(base, 'pages.tsv', ['PG-SRD-0001', source, '000001', '1', '1', '1',
                         'content', 'complete', 'complete', 'c'*40])
for position, claim in enumerate((predecessor, canonical, other), 1):
    order = '000001.' + format(position, '04d')
    content = 'Synthetic duplicate protocol private content ' + str(position) + '.'
    append(base, 'claims.tsv', [claim, source, order, 'PG-SRD-0001',
           'PDF p. 1; Equation (R.' + str(position) + ')', 'assertion', 'equation',
           content, blob(content), 'NONE', 'NONE', 'false', 'NONE', 'NONE', 'NONE'])
    item = 'IT-SRD-' + format(position, '04d')
    append(base, 'source-items.tsv', [item, source, order, 'PG-SRD-0001', 'equation',
           'Equation (R.' + str(position) + ')', 'NONE', 'PDF p. 1; Equation (R.' + str(position) + ')',
           'Ungrouped', 'ungrouped', 'PUBLIC-DOCS-SOURCE-ITEM-REVIEW-V1'])
    append(base, 'item-claims.tsv', [item, '1', claim])
    append(base, 'claim-vocabulary-review.tsv', [claim, 'mathlib_only', review])
append(base, 'source-invariants.tsv', [source, '1', '3', '3', '3', '0', '0'*40,
                                    'RUNTIME-DUPLICATE-BASE-REVIEW'])
refresh(base)

def retirement(before, name, base_commit=None):
    after = clone(before, name)
    events = table(after, 'correction-events.tsv')
    append(after, 'correction-events.tsv', [event, str(len(events)), source,
           base_commit or subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project).decode().strip(), review])
    append(after, 'claim-normalization-reviews.tsv', ['NR-RUNTIME-DUPLICATE-0001', event, '1',
           predecessor, 'exact_statement_readiness', 'retire_duplicate', 'closed',
           'same-source-atomic-assertion', review])
    old = record(before, 'claims.tsv', predecessor)
    append(after, 'claim-corrections.tsv', [correction, event, '1', 'NR-RUNTIME-DUPLICATE-0001',
           predecessor, 'retire_duplicate', old[5], old[6], old[5], old[6]])
    append(after, 'claim-successors.tsv', ['SE-RUNTIME-DUPLICATE-0001', event, correction,
           predecessor, '1', 'existing_duplicate', canonical])
    for col, value in enumerate(['true', canonical, 'same-source-atomic-assertion', review], 11):
        mutate(after, 'claims.tsv', predecessor, col, value)
    remove(after, 'claim-vocabulary-review.tsv', predecessor)
    mutate(after, 'source-invariants.tsv', source, 7, review)
    refresh(after)
    return after

valid = retirement(base, 'valid')
static('duplicate-base', base)
static('duplicate-current', valid)
transition('duplicate-valid', base, valid, both=True)

history = ('correction-events.tsv', 'claim-normalization-reviews.tsv', 'claim-corrections.tsv',
           'claim-successors.tsv', 'source-item-additions.tsv', 'claim-content-amendments.tsv')

def preserved(before, after):
    require(record(before, 'claims.tsv', predecessor)[:11] ==
            record(after, 'claims.tsv', predecessor)[:11], 'predecessor columns 1--11')
    require(record(before, 'claims.tsv', canonical) == record(after, 'claims.tsv', canonical),
            'canonical whole row')
    for name in ('source-items.tsv', 'item-claims.tsv', 'vocabulary.tsv', 'modules.tsv', 'imports.tsv'):
        require((before / 'registry' / name).read_bytes() == (after / 'registry' / name).read_bytes(), name)
    for name in ('claim-vocabulary-review.tsv', 'claim-vocabulary.tsv'):
        require([r for r in table(before, name)[1:] if r[0] == canonical] ==
                [r for r in table(after, name)[1:] if r[0] == canonical], 'canonical ' + name)
    for name in history:
        require((after / 'registry' / name).read_bytes().startswith(
                (before / 'registry' / name).read_bytes()), 'prefix ' + name)
    old, new = record(before, 'source-invariants.tsv', source), record(after, 'source-invariants.tsv', source)
    equation_loss = int(record(before, 'claims.tsv', predecessor)[6] == 'equation')
    require([int(new[i]) - int(old[i]) for i in (2, 3, 4)] == [-1, -1, -equation_loss],
            'counts follow the actual predecessor subkind')
    require(new[7] == review, 'selected invariant review')

preserved(base, valid)
non_equation_base = clone(base, 'non-equation-base')
mutate(non_equation_base, 'claims.tsv', predecessor, 6, 'theorem')
refresh(non_equation_base)
non_equation = retirement(non_equation_base, 'non-equation-current')
static('non-equation-current', non_equation)
transition('non-equation-counts', non_equation_base, non_equation, both=True)
preserved(non_equation_base, non_equation)

# The canonical may use existing project vocabulary; the real production users
# remain present, so none of these controls can fail merely from orphaning it.
vocabulary_ids = [r[0] for r in table(base, 'vocabulary.tsv')[1:]]
require(len(vocabulary_ids) >= 2, 'two existing vocabulary declarations required')
project_base = clone(base, 'project-canonical-base')
mutate(project_base, 'claim-vocabulary-review.tsv', canonical, 1, 'project_vocabulary')
append(project_base, 'claim-vocabulary.tsv', [canonical, vocabulary_ids[0]])
project_valid = retirement(project_base, 'project-canonical-valid')
static('project-canonical-base', project_base)
static('project-canonical-current', project_valid)
transition('project-canonical-valid', project_base, project_valid, both=True)
preserved(project_base, project_valid)

# Check the existing declared vocabulary through its actual environment entrypoint
# once. Every other fixture uses these exact frozen declaration/module/import bytes.
for module in table(base, 'modules.tsv')[1:]:
    destination = base / module[1]
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(project / module[1], destination)
expect('duplicate-existing-vocabulary-environment', True,
       [project / 'scripts/check-vocabulary.sh', '--fixture', base], 'check-vocabulary: ok')

def negative(label, change, diagnostic, before=base, initial=valid, both=False):
    after = clone(initial, label)
    change(after)
    refresh(after)
    transition(label, before, after, False, diagnostic, both)
    return after

# N01/N02: a valid project-vocabulary predecessor reaches the explicit narrow
# basis guard; malformed basis/use combinations separately exercise each guard.
project_predecessor = clone(project_base, 'project-predecessor-base')
mutate(project_predecessor, 'claim-vocabulary-review.tsv', predecessor, 1, 'project_vocabulary')
append(project_predecessor, 'claim-vocabulary.tsv', [predecessor, vocabulary_ids[0]])
static('project-predecessor-base', project_predecessor)
project_predecessor_current = retirement(project_predecessor, 'project-predecessor-current')
remove(project_predecessor_current, 'claim-vocabulary.tsv', predecessor)
static('project-predecessor-current', project_predecessor_current)
transition('project-predecessor-rejected', project_predecessor, project_predecessor_current,
           False, 'duplicate retirement requires exactly one base mathlib_only review', True)
for label, change, diagnostic in [
    ('missing-base-review', lambda r: remove(r, 'claim-vocabulary-review.tsv', predecessor),
     'duplicate retirement requires exactly one base mathlib_only review'),
    ('duplicate-base-review', lambda r: append(r, 'claim-vocabulary-review.tsv',
         record(r, 'claim-vocabulary-review.tsv', predecessor)),
     'duplicate retirement requires exactly one base mathlib_only review'),
    ('forged-base-use', lambda r: append(r, 'claim-vocabulary.tsv', [predecessor, vocabulary_ids[0]]),
     'duplicate retirement predecessor has vocabulary uses')]:
    before = clone(base, label + '-base')
    change(before)
    after = retirement(before, label + '-current')
    transition(label, before, after, False, diagnostic)
negative('current-predecessor-use', lambda r: append(r, 'claim-vocabulary.tsv',
         [predecessor, vocabulary_ids[0]]), 'duplicate retirement predecessor has vocabulary uses')

# N03: base identity, activity and source. Unknown/fresh targets fail the actual
# existing predecessor/review guards; tombstoned/excluded targets reach eligibility.
for label, change, diagnostic in [
    ('unknown-predecessor', lambda r: remove(r, 'claims.tsv', predecessor), 'correction predecessor source mismatch'),
    ('excluded-predecessor', lambda r: mutate(r, 'claims.tsv', predecessor, 5, 'out_of_scope'),
     'duplicate retirement requires a frozen active formal predecessor'),
    ('tombstoned-predecessor', lambda r: mutate(r, 'claims.tsv', predecessor, 11, 'true'),
     'duplicate retirement requires a frozen active formal predecessor'),
    ('wrong-source-predecessor', lambda r: mutate(r, 'claims.tsv', predecessor, 1, 'TASAKI2020'),
     'correction predecessor source mismatch')]:
    before = clone(base, label + '-base')
    change(before)
    refresh(before)
    transition(label, before, valid, False, diagnostic)
fresh = clone(valid, 'fresh-predecessor')
mutate(fresh, 'claim-corrections.tsv', correction, 4, 'CL-SRD-9999')
mutate(fresh, 'claim-normalization-reviews.tsv', 'NR-RUNTIME-DUPLICATE-0001', 3, 'CL-SRD-9999')
mutate(fresh, 'claim-successors.tsv', 'SE-RUNTIME-DUPLICATE-0001', 3, 'CL-SRD-9999')
fresh_row = record(fresh, 'claims.tsv', predecessor)[:]
fresh_row[0], fresh_row[2] = 'CL-SRD-9999', '000001.0004'
append(fresh, 'claims.tsv', fresh_row)
refresh(fresh)
transition('fresh-predecessor', base, fresh, False, 'correction predecessor source mismatch')

# N04: each forbidden field is changed independently, with derived invariants
# repaired. Source/identity fields may be rejected by their earlier exact guards.
for column, value, diagnostic in [
    (0, 'CL-SRD-9999', 'normalization review targets an unknown claim'),
    (1, 'TASAKI2020', 'duplicate retirement requires a frozen active formal predecessor'),
    (2, '000001.0001.0001', 'unmanifested claim drift'),
    (3, 'PG-SRD-9999', 'unmanifested claim drift'),
    (4, 'PDF p. 1; altered locator', 'unmanifested claim drift'),
    (5, 'definition', 'unmanifested claim drift'),
    (6, 'definition', 'unmanifested claim drift'),
    (7, 'Altered synthetic content.', 'unmanifested claim drift'),
    (8, 'PENDING', 'unmanifested claim drift'),
    (9, 'forged-exclusion', 'unmanifested claim drift'),
    (10, 'FORGED-REVIEW', 'unmanifested claim drift')]:
    def frozen_change(root, c=column, v=value):
        mutate(root, 'claims.tsv', predecessor, c, v)
        if c in (5, 6):
            mutate(root, 'claim-corrections.tsv', correction, c + 3, v)
    negative('frozen-predecessor-column-' + str(column + 1), frozen_change, diagnostic)
for column, value, diagnostic in [
    (11, 'false', 'invalid duplicate retirement transition'),
    (12, other, 'tombstone does not name its first successor'),
    (13, 'forged-rationale', 'invalid duplicate retirement transition'),
    (14, 'FORGED-REVIEW', 'invalid duplicate retirement transition')]:
    negative('retirement-field-' + str(column + 1),
             lambda r, c=column, v=value: mutate(r, 'claims.tsv', predecessor, c, v), diagnostic)
pending_base = clone(base, 'pending-base')
mutate(pending_base, 'claims.tsv', predecessor, 8, 'PENDING')
refresh(pending_base)
pending_current = retirement(pending_base, 'pending-current')
static('pending-current', pending_current)
transition('pending-oid-preserved', pending_base, pending_current, both=True)
require(record(pending_current, 'claims.tsv', predecessor)[8] == 'PENDING', 'pending OID retained')

# N05/N06: edge shape and canonical selection do not weaken split semantics.
edge = 'SE-RUNTIME-DUPLICATE-0001'
for label, change in [
    ('zero-successors', lambda r: remove(r, 'claim-successors.tsv', edge)),
    ('two-successors', lambda r: append(r, 'claim-successors.tsv',
         ['SE-RUNTIME-DUPLICATE-0002', event, correction, predecessor, '2', 'existing_duplicate', other])),
    ('wrong-position', lambda r: mutate(r, 'claim-successors.tsv', edge, 4, '2')),
    ('new-successor-relation', lambda r: mutate(r, 'claim-successors.tsv', edge, 5, 'new_successor')),
    ('wrong-successor-owner', lambda r: mutate(r, 'claim-successors.tsv', edge, 2, 'CC-UNKNOWN-0001')),
    ('wrong-edge-predecessor', lambda r: mutate(r, 'claim-successors.tsv', edge, 3, other)),
    ('self-successor', lambda r: mutate(r, 'claim-successors.tsv', edge, 6, predecessor))]:
    negative(label, change, 'duplicate retirement requires one existing successor at position 1')
for label, change in [
    ('unknown-canonical', lambda r: mutate(r, 'claim-successors.tsv', edge, 6, 'CL-SRD-9999')),
    ('fresh-canonical', lambda r: remove(r, 'claims.tsv', canonical)),
    ('cross-source-canonical', lambda r: mutate(r, 'claims.tsv', canonical, 1, 'TASAKI2020')),
    ('excluded-canonical', lambda r: mutate(r, 'claims.tsv', canonical, 5, 'out_of_scope')),
    ('tombstoned-canonical', lambda r: mutate(r, 'claims.tsv', canonical, 11, 'true'))]:
    negative(label, change, 'duplicate retirement canonical is not a frozen same-source active formal target')
for label, column, value in [('base-excluded', 5, 'out_of_scope'), ('base-tombstoned', 11, 'true'),
                             ('base-cross-source', 1, 'TASAKI2020')]:
    before = clone(base, label + '-canonical')
    mutate(before, 'claims.tsv', canonical, column, value)
    refresh(before)
    transition(label, before, valid, False,
               'duplicate retirement canonical is not a frozen same-source active formal target')
fresh_canonical_base = clone(base, 'absent-base-canonical')
remove(fresh_canonical_base, 'claims.tsv', canonical)
refresh(fresh_canonical_base)
transition('canonical-must-exist-in-base', fresh_canonical_base, valid, False,
           'duplicate retirement canonical is not a frozen same-source active formal target')

def add_canonical_owner(root, action='reclassify', content=None):
    old = record(root, 'claims.tsv', canonical)
    append(root, 'claim-normalization-reviews.tsv', ['NR-RUNTIME-DUPLICATE-0002', event, '2', canonical,
           'exact_statement_readiness', action, 'closed', 'canonical-owner-control', review])
    append(root, 'claim-corrections.tsv', ['CC-RUNTIME-DUPLICATE-0002', event, '2',
           'NR-RUNTIME-DUPLICATE-0002', canonical, action, old[5], old[6], old[5], old[6]])
    if content is not None:
        append(root, 'claim-content-amendments.tsv', ['CA-RUNTIME-DUPLICATE-0001', event,
               'CC-RUNTIME-DUPLICATE-0002', canonical, blob(old[7]), blob(content), 'c'*40, review])
        mutate(root, 'claims.tsv', canonical, 7, content)
        mutate(root, 'claims.tsv', canonical, 8, blob(content))

# N07: real amendment provenance is valid before testing same-event canonical
# whole-row drift. N08 attacks bypass the generic "unrelated" vocabulary filter.
same_event_amendment = clone(valid, 'same-event-canonical-amendment')
add_canonical_owner(same_event_amendment, 'amend_content', 'Synthetic corrected canonical content.')
refresh(same_event_amendment)
static('same-event-amendment', same_event_amendment)
expect('same-event-canonical-amendment-provenance', True,
       ['python3', project / 'scripts/check-content-amendments.py', '--transition', base,
        same_event_amendment, event], 'check-content-amendments: ok')
transition('same-event-canonical-amendment', base, same_event_amendment,
           False, 'existing duplicate successor drift', True)
negative('canonical-review-drift', lambda r: mutate(r, 'claim-vocabulary-review.tsv', canonical, 2,
         'OTHER-REVIEW'), 'duplicate retirement canonical vocabulary review drift')
negative('canonical-use-drift', lambda r: append(r, 'claim-vocabulary.tsv',
         [canonical, vocabulary_ids[1]]), 'duplicate retirement canonical vocabulary use drift',
         project_base, project_valid)
negative('canonical-use-removed', lambda r: remove(r, 'claim-vocabulary.tsv', canonical),
         'duplicate retirement canonical vocabulary use drift', project_base, project_valid)
owner_review_base = clone(base, 'owner-review-base')
mutate(owner_review_base, 'claim-vocabulary-review.tsv', canonical, 2, 'EARLIER-CANONICAL-REVIEW')
owner_review = retirement(owner_review_base, 'owner-review-current')
add_canonical_owner(owner_review)
mutate(owner_review, 'claim-vocabulary-review.tsv', canonical, 2, review)
static('owner-review-base', owner_review_base)
static('owner-review-current', owner_review)
transition('same-event-owner-review-drift', owner_review_base, owner_review,
           False, 'duplicate retirement canonical vocabulary review drift', True)
owner_use = clone(project_valid, 'owner-use-current')
add_canonical_owner(owner_use)
append(owner_use, 'claim-vocabulary.tsv', [canonical, vocabulary_ids[1]])
static('owner-use-current', owner_use)
transition('same-event-owner-use-drift', project_base, owner_use,
           False, 'duplicate retirement canonical vocabulary use drift', True)

# N09/N10: no new creator privilege and no rewriting item history.
negative('retained-predecessor-review', lambda r: append(r, 'claim-vocabulary-review.tsv',
         [predecessor, 'mathlib_only', review]), 'excluded predecessor retains vocabulary review')
negative('retirement-owned-amendment', lambda r: append(r, 'claim-content-amendments.tsv',
         ['CA-RUNTIME-DUPLICATE-0001', event, correction, predecessor, 'd'*40, 'e'*40, 'c'*40, review]),
         'duplicate retirement cannot own source items or content amendments')
negative('retirement-owned-item', lambda r: append(r, 'source-item-additions.tsv',
         ['IA-RUNTIME-DUPLICATE-0001', event, correction, '1', 'IT-SRD-9999', review]),
         'duplicate retirement cannot own source items or content amendments')
new_claim = record(base, 'claims.tsv', other)[:]
new_claim[0], new_claim[2] = 'CL-SRD-0004', '000001.0004'
negative('unowned-fresh-claim', lambda r: append(r, 'claims.tsv', new_claim),
         'split successor provenance is incomplete')
for identifier in ('IT-SRD-0001', 'IT-SRD-0002'):
    negative('edited-item-' + identifier, lambda r, i=identifier: mutate(r, 'source-items.tsv', i, 6,
             'Altered item title'), 'historical source item drift' if identifier.endswith('0001') else
             'unrelated frozen registry drift')
    negative('deleted-item-' + identifier, lambda r, i=identifier: remove(r, 'source-items.tsv', i),
             'historical source item drift' if identifier.endswith('0001') else 'unrelated frozen registry drift')
    negative('deleted-relation-' + identifier, lambda r, i=identifier: remove(r, 'item-claims.tsv', i),
             'historical source item relation drift' if identifier.endswith('0001') else 'unrelated item-claim drift')
extra_member = clone(valid, 'canonical-in-predecessor-item')
append(extra_member, 'item-claims.tsv', ['IT-SRD-0001', '2', canonical])
transition('canonical-in-predecessor-item', base, extra_member, False, 'unrelated item-claim drift')
expect('canonical-unique-item', False, [project / 'scripts/check-source-items.sh', extra_member],
       'claim occurs in more than one item')

# N11: eligibility sees relations already present in the base, using the actual
# current schemas in both trees. These fixtures intentionally describe an
# ineligible R4 state, rather than a newly injected row caught by artifact drift.
binding = [other, 'LatticeSystem.Claims.Runtime.statement', 'LatticeSystem.Claims.Runtime.proof',
           'LatticeSystem.Claims.Runtime', 'definition', 'proof_proposition', 'PENDING', 'PENDING',
           'proof_stub', 'theorem', 'PENDING', 'NONE', 'NONE', 'NONE', 'RUNTIME-BINDING-REVIEW']
for label, name, row, diagnostic in [
    ('source-bindings', 'bindings.tsv', binding, 'duplicate retirement source already has bindings'),
    ('slice', 'slices.tsv', ['SL-RUNTIME-0001', '1', predecessor],
     'duplicate retirement predecessor has skeleton or axiom relations'),
    ('dependency-owner', 'dependencies.tsv', [predecessor, 'requires', 'CL-TASAKI2020-0001', 'NONE'],
     'duplicate retirement predecessor has skeleton or axiom relations'),
    ('dependency-target', 'dependencies.tsv', [other, 'requires', predecessor, 'NONE'],
     'duplicate retirement predecessor has skeleton or axiom relations'),
    ('axiom', 'claim-axioms.tsv', [predecessor, 'AX-RUNTIME-0001'],
     'duplicate retirement predecessor has skeleton or axiom relations'),
    ('context-owner', 'claim-context.tsv', [predecessor, '1', 'CL-TASAKI2020-0001', 'term_reference', 'inherited', review],
     'duplicate retirement predecessor has skeleton or axiom relations'),
    ('context-setup', 'claim-context.tsv', [other, '1', predecessor, 'assumption', 'inherited', review],
     'duplicate retirement predecessor has skeleton or axiom relations')]:
    before = clone(base, 'existing-' + label + '-base')
    if label == 'context-setup':
        mutate(before, 'claims.tsv', predecessor, 5, 'definition')
        mutate(before, 'claims.tsv', predecessor, 6, 'definition')
        refresh(before)
    append(before, name, row)
    after = retirement(before, 'existing-' + label + '-current')
    transition('existing-' + label, before, after, False, diagnostic)
for lifecycle in ('skeleton_frozen', 'proof_active', 'complete'):
    before = clone(base, lifecycle + '-base')
    mutate(before, 'source-progress.tsv', source, 1, lifecycle)
    after = retirement(before, lifecycle + '-current')
    transition(lifecycle, before, after, False, 'duplicate retirement requires a pre-R4 source')
negative('current-lifecycle', lambda r: mutate(r, 'source-progress.tsv', source, 1, 'skeleton_frozen'),
         'duplicate retirement requires a pre-R4 source')

# N12: event/review/correction closed ownership and exact classification pairs.
for label, name, identifier, column, value, diagnostic in [
    ('open-review', 'claim-normalization-reviews.tsv', 'NR-RUNTIME-DUPLICATE-0001', 6, 'open',
     'invalid claim normalization review ledger'),
    ('mismatched-review', 'claim-normalization-reviews.tsv', 'NR-RUNTIME-DUPLICATE-0001', 8, 'OTHER-REVIEW',
     'invalid claim normalization review ledger'),
    ('wrong-review-owner', 'claim-corrections.tsv', correction, 3, 'NR-UNKNOWN-0001',
     'invalid claim correction ledger'),
    ('none-old-disposition', 'claim-corrections.tsv', correction, 6, 'NONE',
     'NONE old classification requires add_omitted_claim'),
    ('none-old-subkind', 'claim-corrections.tsv', correction, 7, 'NONE',
     'NONE old classification requires add_omitted_claim'),
    ('mismatched-old-pair', 'claim-corrections.tsv', correction, 7, 'lemma',
     'correction ledger does not match claim transition'),
    ('mismatched-new-pair', 'claim-corrections.tsv', correction, 9, 'lemma',
     'correction ledger does not match claim transition')]:
    negative(label, lambda r, n=name, i=identifier, c=column, v=value: mutate(r, n, i, c, v), diagnostic)
for name, identifier, diagnostic in [
    ('claim-normalization-reviews.tsv', 'NR-RUNTIME-DUPLICATE-0001', 'invalid claim normalization review ledger'),
    ('claim-corrections.tsv', correction, 'invalid claim correction ledger')]:
    negative('duplicate-' + name, lambda r, n=name, i=identifier: append(r, n, record(r, n, i)), diagnostic)

# N14/N15: ledger history, unrelated inputs and every derived census field.
for name in history:
    rows = table(base, name)
    require(len(rows) > 2, 'historical rows required for prefix controls: ' + name)
    for mode in ('value', 'order'):
        def historical_change(root, n=name, m=mode):
            rows = table(root, n)
            if m == 'value':
                rows[1][-1] += '-FORGED'
            else:
                rows[1], rows[2] = rows[2], rows[1]
                if n == 'correction-events.tsv':
                    rows[1][1], rows[2][1] = '1', '2'
            write(root, n, rows)
        diagnostic = ('unmanifested source item addition' if name == 'source-item-additions.tsv' and
                      mode == 'value' else 'historical correction ledger drift')
        negative('history-' + name + '-' + mode, historical_change, diagnostic)
for label, name, identifier, column, value in [
    ('page-fingerprint', 'pages.tsv', 'PG-SRD-0001', 9, 'd'*40),
    ('source-fingerprint', 'sources.tsv', source, 14, 'd'*40),
    ('vocabulary', 'vocabulary.tsv', vocabulary_ids[0], 7, 'd'*40),
    ('module', 'modules.tsv', table(base, 'modules.tsv')[1][0], 1, 'Altered.lean'),
    ('import', 'imports.tsv', table(base, 'imports.tsv')[1][0], 2, 'Mathlib.Altered'),
    ('phase', 'phase.tsv', 'vocabulary', 0, 'skeleton'),
    ('unrelated-source', 'sources.tsv', 'TASAKI2020', 5, 'Altered title')]:
    negative('unrelated-' + label, lambda r, n=name, i=identifier, c=column, v=value: mutate(r, n, i, c, v),
             'unrelated frozen registry drift')
for label, name, row, diagnostic in [
    ('r4-injection', 'statement-modules.tsv', ['LatticeSystem.Claims.Runtime', 'LatticeSystem/Claims/Runtime.lean', 'leaf'],
     'correction event introduces an R4 artifact'),
    ('axiom-injection', 'axioms.tsv', ['AX-RUNTIME-0001', 'LatticeSystem.Axioms.State.runtime',
     'LatticeSystem.Axioms.State', 'state', 'Runtime source', 'runtime-reason', 'runtime-reopen', 'a'*40],
     'correction event introduces an axiom artifact')]:
    negative(label, lambda r, n=name, x=row: append(r, n, x), diagnostic)
for column, diagnostic in [(2, 'census invariant count is stale'), (3, 'formalization target count is stale'),
                           (4, 'census invariant count is stale'), (5, 'census invariant count is stale'),
                           (6, 'census OID is stale'),
                           (7, 'duplicate retirement lacks its event invariant review')]:
    after = clone(valid, 'stale-invariant-' + str(column))
    old = record(after, 'source-invariants.tsv', source)[column]
    value = str(int(old) + 1) if column < 6 else ('d'*40 if column == 6 else 'RUNTIME-DUPLICATE-BASE-REVIEW')
    mutate(after, 'source-invariants.tsv', source, column, value)
    transition('stale-invariant-' + str(column), base, after, False, diagnostic, True)

# P06: real generated output retains both items, original equation provenance
# and the canonical link, while keeping source text and correction evidence private.
public = clone(valid, 'public')
generator = project / 'scripts/generate-public-docs.py'
expect('duplicate-public-write', True, ['python3', generator, '--write', '--root', public])
expect('duplicate-public-no-drift', True, ['python3', generator, '--check', '--root', public])
catalog = json.loads((public / 'docs/generated/catalog.json').read_text())
items = {r['item_id']: r for r in catalog['items']}
require(items['IT-SRD-0001']['claims'][0]['claim_id'] == predecessor and
        items['IT-SRD-0001']['claims'][0]['successor_claim'] == canonical and
        items['IT-SRD-0002']['claims'][0]['claim_id'] == canonical and
        items['IT-SRD-0002']['source_label'] == 'Equation (R.2)', 'public original provenance and successor')
public_text = '\n'.join(p.read_text() for p in (public / 'docs').rglob('*') if p.is_file())
for token in [event, review, correction, 'CA-RUNTIME-DUPLICATE', '.self-local', str(temporary)] + [
        row[column] for row in table(base, 'claims.tsv')[1:] if row[1] == source for column in (7, 8)]:
    require(token not in public_text, 'private output token: ' + token)

def content_event(before, name, event_id, base_commit):
    after = clone(before, name)
    ref = event_id + '-REVIEW'
    old = record(before, 'claims.tsv', canonical)
    content = 'Synthetic canonical revision for ' + event_id + '.'
    append(after, 'correction-events.tsv', [event_id, str(len(table(after, 'correction-events.tsv'))),
           source, base_commit, ref])
    append(after, 'claim-normalization-reviews.tsv', ['NR-' + event_id + '-0001', event_id, '1',
           canonical, 'exact_statement_readiness', 'amend_content', 'closed', 'runtime-repair', ref])
    append(after, 'claim-corrections.tsv', ['CC-' + event_id + '-0001', event_id, '1',
           'NR-' + event_id + '-0001', canonical, 'amend_content', old[5], old[6], old[5], old[6]])
    append(after, 'claim-content-amendments.tsv', ['CA-' + event_id + '-0001', event_id,
           'CC-' + event_id + '-0001', canonical, blob(old[7]), blob(content), 'c'*40, ref])
    mutate(after, 'claims.tsv', canonical, 7, content)
    mutate(after, 'claims.tsv', canonical, 8, blob(content))
    mutate(after, 'claim-vocabulary-review.tsv', canonical, 2, ref)
    mutate(after, 'source-invariants.tsv', source, 7, ref)
    refresh(after)
    return after

# P03/P04/P05 and N13: actual Git merge-base selector, actual base checker,
# actual correction helper, with no stand-in at any layer of the chain.
require('CHECK_BASE_DIFF' not in os.environ, 'selector must use real base checker')
repo = retirement_root / 'git-chain'
repo.mkdir()
def git(*args):
    return subprocess.check_output(['git', '-C', str(repo), *args], stderr=subprocess.STDOUT).decode().strip()
def install(root):
    shutil.copytree(root / 'registry', repo / 'registry', dirs_exist_ok=True)
def commit(message):
    git('add', 'registry')
    git('commit', '--allow-empty', '-qm', message)
    return git('rev-parse', 'HEAD')
git('init', '-q')
git('config', 'user.name', 'phasetr')
git('config', 'user.email', 'phasetr@gmail.com')
install(base)
initial_sha = commit('Synthetic registry base')
repair = content_event(base, 'earlier-canonical-repair', 'RUNTIME-EARLIER-REPAIR', initial_sha)
install(repair)
expect('selector-earlier-canonical-repair', True, [selector, repo, initial_sha], 'check-base-diff-ci: ok')
repair_sha = commit('Synthetic accepted canonical repair')
retired = retirement(repair, 'after-earlier-repair', repair_sha)
static('after-earlier-repair', retired)
install(retired)
output = expect('selector-retirement-real', True, [selector, repo, repair_sha], 'check-base-diff-ci: ok')
require('check-base-diff: ok' in output, 'real selector delegates actual base checker')
mutate(repo, 'correction-events.tsv', event, 3, initial_sha)
expect('selector-wrong-base', False, [selector, repo, repair_sha],
       'new correction event base commit does not match the actual merge base')
install(retired)
expect('selector-two-new-events', False, [selector, repo, initial_sha],
       'multiple new correction events require an explicit CI policy change')
retirement_sha = commit('Synthetic accepted retirement')
ordinary_sha = commit('Synthetic ordinary successor')
output = expect('selector-historical-ordinary', True, [selector, repo, retirement_sha], 'check-base-diff: ok')
require('check-base-diff-ci: ok' not in output, 'historical event takes ordinary branch')
for name in history:
    require((repo / 'registry' / name).read_bytes() == (retired / 'registry' / name).read_bytes(),
            'ordinary ledger unchanged: ' + name)
mutate(repo, 'claims.tsv', predecessor, 11, 'false')
expect('selector-historical-reopening', False, [selector, repo, retirement_sha],
       'identity/order/locator/content/exclusion/supersession')
install(retired)
expect('ordinary-unowned-retirement', False,
       [base_checker, '--fixture-dirs', repair, retired],
       'claim-vocabulary-review.tsv stable-ID deletion')
later = content_event(retired, 'later-canonical-repair', 'RUNTIME-LATER-REPAIR', ordinary_sha)
static('later-canonical-repair', later)
expect('later-canonical-content-helper', True,
       ['python3', project / 'scripts/check-content-amendments.py', '--transition', retired, later,
        'RUNTIME-LATER-REPAIR'], 'check-content-amendments: ok')
expect('later-canonical-dedicated', True, [checker, '--fixture-dirs', retired, later],
       'check-claim-corrections: ok')
expect('later-canonical-base', True,
       [base_checker, '--correction-event', 'RUNTIME-LATER-REPAIR', '--fixture-dirs', retired, later],
       'check-base-diff: ok')
install(later)
expect('selector-later-canonical-repair', True, [selector, repo, ordinary_sha], 'check-base-diff-ci: ok')
print('test-claim-corrections-runtime: duplicate cases (' + str(passed) +
      ' positive, ' + str(rejected) + ' rejection cases)')
PY

[[ $(baseline_digest) == "$BASELINE_DIGEST" ]] || {
  echo "test-claim-corrections-runtime: immutable runtime base changed" >&2
  exit 1
}
[[ -z $(git -C "$PROJECT_ROOT" ls-files 'fixtures/**') ]] || {
  echo "test-claim-corrections-runtime: tracked fixtures are forbidden" >&2
  exit 1
}

echo "test-claim-corrections-runtime: ok ($PASS_COUNT positive, $REJECT_COUNT rejection cases)"
