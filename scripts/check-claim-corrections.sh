#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=$(cd -P "$SCRIPT_DIR/.." && pwd)
fail() { echo "check-claim-corrections: $*" >&2; exit 1; }

MODE=fixture
PRODUCTION=0
EVENT=
TMP=
if [[ ${1:-} == --fixture-dirs ]]; then
  [[ $# -eq 3 ]] || fail "usage: check-claim-corrections.sh --fixture-dirs BASE CURRENT"
  BASE=$(cd "$2" && pwd) || fail "invalid fixture base"
  CURRENT=$(cd "$3" && pwd) || fail "invalid fixture current"
  [[ -n ${LATTICE_TEST_ROOT:-} ]] || fail "fixture mode requires LATTICE_TEST_ROOT"
  TEST_ROOT=$(cd "$LATTICE_TEST_ROOT" && pwd) || fail "invalid LATTICE_TEST_ROOT"
  case "$BASE/" in "$TEST_ROOT/"*) ;; *) fail "fixture base must be below LATTICE_TEST_ROOT" ;; esac
  case "$CURRENT/" in "$TEST_ROOT/"*) ;; *) fail "fixture current must be below LATTICE_TEST_ROOT" ;; esac
elif [[ ${1:-} == --correction-event ]]; then
  [[ $# -eq 4 ]] || fail "usage: check-claim-corrections.sh --correction-event EVENT ROOT BASE_COMMIT"
  EVENT=$2
  CURRENT=$(cd "$3" && pwd) || fail "invalid repository root"
  BASE_COMMIT=$4
  [[ $(git -C "$CURRENT" rev-parse --show-toplevel 2>/dev/null) == "$CURRENT" ]] ||
    fail "ROOT must be the repository top"
  git -C "$CURRENT" cat-file -e "$BASE_COMMIT:registry/claims.tsv" 2>/dev/null ||
    fail "base commit lacks the claim registry"
  TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-claim-corrections.XXXXXX")
  trap 'rm -rf "$TMP"' EXIT HUP INT TERM
  mkdir -p "$TMP/registry"
  while IFS= read -r path; do
    git -C "$CURRENT" show "$BASE_COMMIT:$path" > "$TMP/$path"
  done < <(git -C "$CURRENT" ls-tree -r --name-only "$BASE_COMMIT" registry)
  BASE=$TMP
  PRODUCTION=1
else
  fail "explicit --fixture-dirs or --correction-event mode is required"
fi

BASE_REG=$BASE/registry
CURRENT_REG=$CURRENT/registry
for file in claims.tsv item-claims.tsv claim-vocabulary-review.tsv claim-vocabulary.tsv \
  source-invariants.tsv bindings.tsv axioms.tsv claim-axioms.tsv; do
  [[ -f "$BASE_REG/$file" && -f "$CURRENT_REG/$file" ]] || fail "missing registry/$file"
done
for file in correction-events.tsv claim-corrections.tsv claim-successors.tsv; do
  [[ -f "$CURRENT_REG/$file" ]] || fail "missing registry/$file"
done

[[ $(head -n 1 "$CURRENT_REG/correction-events.tsv") == $'event_id\tsource_id\tbase_commit\treview_ref' ]] ||
  fail "bad correction-events.tsv header"
[[ $(head -n 1 "$CURRENT_REG/claim-corrections.tsv") == $'correction_id\tevent_id\tclaim_id\taction\told_disposition\told_subkind\tnew_disposition\tnew_subkind\trationale\treview_ref' ]] ||
  fail "bad claim-corrections.tsv header"
[[ $(head -n 1 "$CURRENT_REG/claim-successors.tsv") == $'predecessor_claim_id\tposition\trelation\tsuccessor_claim_id' ]] ||
  fail "bad claim-successors.tsv header"

if [[ -z "$EVENT" ]]; then
  EVENT=$(awk -F '\t' 'FNR==2 {print $1}' "$CURRENT_REG/correction-events.tsv")
fi
[[ -n "$EVENT" ]] || fail "correction event is not reviewed"
awk -F '\t' -v event="$EVENT" '
  function token(s) { return s ~ "^[A-Za-z0-9][A-Za-z0-9._:/#@+-]*$" }
  FNR==1 { next }
  $1==event { found++; if (!token($2) || $3 !~ /^[0-9a-f]{40}$/ || !token($4)) bad=1 }
  END { exit !(found==1 && !bad) }
' "$CURRENT_REG/correction-events.tsv" || fail "correction event is not reviewed"
if [[ "$PRODUCTION" -eq 1 ]]; then
  recorded_base=$(awk -F '\t' -v event="$EVENT" 'FNR>1 && $1==event {print $3}' "$CURRENT_REG/correction-events.tsv")
  [[ "$recorded_base" == "$BASE_COMMIT" ]] || fail "correction event base commit mismatch"
  event_review=$(awk -F '\t' -v event="$EVENT" 'FNR>1 && $1==event {print $4}' "$CURRENT_REG/correction-events.tsv")
  awk -F '\t' -v event="$EVENT" -v review="$event_review" '
    FNR>1 && $2==event && $10!=review {bad=1}
    END {exit bad}
  ' "$CURRENT_REG/claim-corrections.tsv" || fail "correction review does not match its event"
fi

if ! cmp -s "$BASE_REG/axioms.tsv" "$CURRENT_REG/axioms.tsv" ||
   ! cmp -s "$BASE_REG/claim-axioms.tsv" "$CURRENT_REG/claim-axioms.tsv"; then
  fail "correction event introduces an axiom artifact"
fi
if ! cmp -s "$BASE_REG/bindings.tsv" "$CURRENT_REG/bindings.tsv"; then
  fail "correction event introduces an R4 artifact"
fi

for path in "$BASE_REG"/*.tsv; do
  file=${path##*/}
  case "$file" in
    claims.tsv|item-claims.tsv|claim-vocabulary-review.tsv|claim-vocabulary.tsv|source-invariants.tsv|correction-events.tsv|claim-corrections.tsv|claim-successors.tsv|bindings.tsv|axioms.tsv|claim-axioms.tsv) continue ;;
  esac
  [[ -f "$CURRENT_REG/$file" ]] || fail "unrelated frozen registry drift"
  cmp -s "$path" "$CURRENT_REG/$file" || fail "unrelated frozen registry drift"
done

awk -F '\t' -v event="$EVENT" '
  function token(s) { return s ~ "^[A-Za-z0-9][A-Za-z0-9._:/#@+-]*$" }
  FNR==1 { next }
  $2!=event { bad("correction belongs to another event") }
  $1=="" || seenId[$1]++ { bad("duplicate correction ID") }
  seenClaim[$3]++ { bad("claim has multiple correction actions") }
  $4 !~ /^(reclassify|exclude_nonclaim|exclude_duplicate|split)$/ { bad("bad correction action") }
  !token($9) || !token($10) { bad("correction row is not independently reviewed") }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$CURRENT_REG/claim-corrections.tsv" || fail "invalid claim correction ledger"

awk -F '\t' -v production="$PRODUCTION" '
  FILENAME==ARGV[1] {
    if (FNR>1) {
      old[$1]=$0; oldKnown[$1]=1; oldDisp[$1]=$6; oldSub[$1]=$7
      oldSource[$1]=$2; oldPage[$1]=$4; oldContent[$1]=$8; oldOid[$1]=$9
    }
    next
  }
  FILENAME==ARGV[2] {
    if (FNR>1) {
      current[$1]=$0; currentKnown[$1]=1; newDisp[$1]=$6; newSub[$1]=$7
      newSource[$1]=$2; newOrder[$1]=$3; newPage[$1]=$4; newLocator[$1]=$5
      newContent[$1]=$8; newOid[$1]=$9; exclusion[$1]=$10; exclusionReview[$1]=$11
      tomb[$1]=$12; superseded[$1]=$13; tombReason[$1]=$14; tombReview[$1]=$15
    }
    next
  }
  FILENAME==ARGV[3] {
    if (FNR>1) {
      action[$3]=$4; correction[$3]=1; ledgerOldDisp[$3]=$5; ledgerOldSub[$3]=$6
      ledgerNewDisp[$3]=$7; ledgerNewSub[$3]=$8; rationale[$3]=$9; review[$3]=$10
    }
    next
  }
  END {
    for (id in oldKnown) {
      if (!(id in currentKnown)) bad("unmanifested claim drift")
      if (!(id in correction)) {
        if (old[id]!=current[id]) bad("unmanifested claim drift")
        continue
      }
      if (ledgerOldDisp[id]!=oldDisp[id] || ledgerOldSub[id]!=oldSub[id] ||
          ledgerNewDisp[id]!=newDisp[id] || ledgerNewSub[id]!=newSub[id]) bad("correction ledger does not match claim transition")
      n=split(old[id],a,"\t"); split(current[id],b,"\t")
      if (action[id]=="reclassify") {
        for (i=1;i<=n;i++) if (i!=6 && i!=7 && a[i]!=b[i]) bad("unmanifested claim drift")
        if (tomb[id]!="false" || exclusion[id]!="NONE" || exclusionReview[id]!="NONE") bad("invalid reclassify transition")
      } else if (action[id]=="exclude_nonclaim") {
        for (i=1;i<=n;i++) if (i!=6 && i!=10 && i!=11 && a[i]!=b[i]) bad("unmanifested claim drift")
        if (newDisp[id]!="out_of_scope" || tomb[id]!="false" || exclusion[id]!=rationale[id] || exclusionReview[id]!=review[id]) bad("invalid nonclaim exclusion")
      } else {
        for (i=1;i<=n;i++) if (i<12 && a[i]!=b[i]) bad("unmanifested claim drift")
        if (tomb[id]!="true" || superseded[id]=="NONE" || tombReason[id]!=rationale[id] || tombReview[id]!=review[id]) bad("invalid tombstone transition")
      }
    }
    for (id in correction) if (!(id in oldKnown)) bad("correction targets an unknown frozen claim")
    for (id in currentKnown) if (!(id in oldKnown)) {
      added[id]=1
      if (newContent[id] ~ /^[[:space:]]*(True|False)[.]?[[:space:]]*$/ || newContent[id]=="") bad("contentless correction surrogate")
      if (production && newOid[id] !~ /^[0-9a-f]{40}$/) bad("new correction successor lacks a frozen content OID")
      if (tomb[id]!="false" || exclusion[id]!="NONE" || exclusionReview[id]!="NONE") bad("new correction successor is not active")
    }
    exit failed
  }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
' "$BASE_REG/claims.tsv" "$CURRENT_REG/claims.tsv" "$CURRENT_REG/claim-corrections.tsv" ||
  fail "unmanifested claim drift"

awk -F '\t' '
  FILENAME==ARGV[1] { if (FNR>1) old[$1]=1; next }
  FILENAME==ARGV[2] { if (FNR>1) { current[$1]=1; tomb[$1]=$12; superseded[$1]=$13 } next }
  FILENAME==ARGV[3] { if (FNR>1) action[$3]=$4; next }
  FNR==1 { next }
  {
    pred=$1; pos=$2+0; rel=$3; succ=$4
    if (!(pred in action) || action[pred] !~ /^(split|exclude_duplicate)$/) bad("successor provenance has no tombstone correction")
    if ($2 !~ /^[1-9][0-9]*$/ || pos!=++count[pred] || seen[pred SUBSEP pos]++) bad("duplicate or noncontiguous successor position")
    if (rel !~ /^(new_successor|existing_duplicate)$/) bad("bad successor relation")
    if (!(succ in current)) bad("unknown correction successor")
    if (rel=="new_successor" && (succ in old)) bad("new successor reuses a frozen claim ID")
    if (rel=="existing_duplicate" && !(succ in old)) bad("existing duplicate is not frozen")
    if (seenSucc[pred SUBSEP succ]++) bad("duplicate correction successor")
    if (pos==1) first[pred]=succ
    successor[succ]=rel; predecessor[succ]=pred
  }
  END {
    for (pred in action) if (action[pred] ~ /^(split|exclude_duplicate)$/ && count[pred]==0) bad("split successor provenance is incomplete")
    for (id in current) if (!(id in old) && successor[id]!="new_successor") bad("split successor provenance is incomplete")
    for (pred in first) {
      if (tomb[pred]!="true") bad("successor predecessor is not tombstoned")
      if (superseded[pred]!=first[pred]) bad("tombstone does not name its first successor")
    }
    exit failed
  }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
' "$BASE_REG/claims.tsv" "$CURRENT_REG/claims.tsv" "$CURRENT_REG/claim-corrections.tsv" "$CURRENT_REG/claim-successors.tsv" ||
  fail "split successor provenance is incomplete"

if [[ "$PRODUCTION" -eq 1 ]]; then
  while IFS= read -r id; do
    content=$(awk -F '\t' -v id="$id" '$1==id {print $8; exit}' "$CURRENT_REG/claims.tsv")
    recorded=$(awk -F '\t' -v id="$id" '$1==id {print $9; exit}' "$CURRENT_REG/claims.tsv")
    computed=$(printf '%s' "$content" | git hash-object --stdin)
    [[ "$recorded" == "$computed" ]] || fail "new correction successor content OID is stale"
  done < <(awk -F '\t' 'FNR>1 && $3=="new_successor" {print $4}' "$CURRENT_REG/claim-successors.tsv")
fi

awk -F '\t' '
  FILENAME==ARGV[1] { if (FNR>1) affected[$3]=1; next }
  FILENAME==ARGV[2] { if (FNR>1 && $3=="new_successor") affected[$4]=1; next }
  FILENAME==ARGV[3] { if (FNR>1 && !($1 in affected)) old[$1]=$0; next }
  FILENAME==ARGV[4] { if (FNR>1 && !($1 in affected)) current[$1]=$0; next }
  END {
    for (id in old) if (current[id]!=old[id]) bad=1
    for (id in current) if (!(id in old)) bad=1
    exit bad
  }
' "$CURRENT_REG/claim-corrections.tsv" "$CURRENT_REG/claim-successors.tsv" \
  "$BASE_REG/claim-vocabulary-review.tsv" "$CURRENT_REG/claim-vocabulary-review.tsv" ||
  fail "unrelated vocabulary review drift"

awk -F '\t' '
  FILENAME==ARGV[1] { if (FNR>1) affected[$3]=1; next }
  FILENAME==ARGV[2] { if (FNR>1 && $3=="new_successor") affected[$4]=1; next }
  FILENAME==ARGV[3] { if (FNR>1 && !($1 in affected)) old[$0]=1; next }
  FILENAME==ARGV[4] { if (FNR>1 && !($1 in affected)) current[$0]=1; next }
  END {
    for (row in old) if (!(row in current)) bad=1
    for (row in current) if (!(row in old)) bad=1
    exit bad
  }
' "$CURRENT_REG/claim-corrections.tsv" "$CURRENT_REG/claim-successors.tsv" \
  "$BASE_REG/claim-vocabulary.tsv" "$CURRENT_REG/claim-vocabulary.tsv" ||
  fail "unrelated vocabulary use drift"

awk -F '\t' '
  FILENAME==ARGV[1] { if (FNR>1) base[$0]=1; next }
  FILENAME==ARGV[2] { if (FNR>1 && $3=="new_successor") added[$4]=1; next }
  FNR==1 { next }
  { current[$0]=1; if (!($0 in base) && !($3 in added)) bad=1 }
  END { for (row in base) if (!(row in current)) bad=1; exit bad }
' "$BASE_REG/item-claims.tsv" "$CURRENT_REG/claim-successors.tsv" "$CURRENT_REG/item-claims.tsv" ||
  fail "unrelated item-claim drift"

awk -F '\t' '
  FILENAME==ARGV[1] { if (FNR>1) baseClaim[$1]=1; next }
  FILENAME==ARGV[2] { if (FNR>1) { action[$3]=$4; review[$3]=$10 } next }
  FILENAME==ARGV[3] { if (FNR>1 && $3=="new_successor") { pred[$4]=$1; added[$4]=1 } next }
  FILENAME==ARGV[4] { if (FNR>1) { currentClaim[$1]=1; tomb[$1]=$12; disp[$1]=$6 } next }
  FILENAME==ARGV[5] { if (FNR>1) { item[$3]=$1; itemUse[$3]++; pos[$3]=$2 } next }
  FILENAME==ARGV[6] { if (FNR>1) { basis[$1]=$2; reviewRef[$1]=$3; reviewUse[$1]++ } next }
  FILENAME==ARGV[7] { if (FNR>1) vocabUse[$1]++ ; next }
  END {
    for (id in action) {
      if (action[id]=="reclassify") {
        if (reviewUse[id]!=1 || reviewRef[id]!=review[id]) bad("reclassified claim lacks correction vocabulary review")
      } else if (action[id] ~ /^(exclude_nonclaim|exclude_duplicate|split)$/) {
        if (reviewUse[id]) bad("excluded predecessor retains vocabulary review")
        if (vocabUse[id]) bad("excluded predecessor retains vocabulary use")
      }
    }
    for (id in added) {
      if (!(id in currentClaim)) continue
      if (itemUse[id]==0) bad("active successor lacks the predecessor item")
      if (itemUse[id]>1) bad("active successor has duplicate item provenance")
      if (item[id]!=item[pred[id]]) bad("active successor lacks the predecessor item")
      if (reviewUse[id]!=1) bad("active successor lacks vocabulary review")
    }
    exit failed
  }
  function bad(s) { print s > "/dev/stderr"; failed=1 }
' "$BASE_REG/claims.tsv" "$CURRENT_REG/claim-corrections.tsv" "$CURRENT_REG/claim-successors.tsv" \
  "$CURRENT_REG/claims.tsv" "$CURRENT_REG/item-claims.tsv" "$CURRENT_REG/claim-vocabulary-review.tsv" \
  "$CURRENT_REG/claim-vocabulary.tsv" || fail "correction relation propagation failed"

IFS=$'\t' read -r source pages recorded_active recorded_targets recorded_equations recorded_empty recorded_oid recorded_review < <(
  awk -F '\t' 'FNR==2 {print}' "$CURRENT_REG/source-invariants.tsv"
)
[[ $(head -n 1 "$CURRENT_REG/source-invariants.tsv") == $'source_id\tphysical_page_count\tactive_claim_count\tformalization_target_count\tequation_pair_count\tno_claim_page_count\tcensus_oid\treview_ref' ]] ||
  fail "bad source-invariants.tsv header"
actual_active=$(awk -F '\t' -v source="$source" 'FNR>1 && $2==source && $12=="false" {n++} END{print n+0}' "$CURRENT_REG/claims.tsv")
actual_targets=$(awk -F '\t' -v source="$source" 'FNR>1 && $2==source && $12=="false" && $6!="out_of_scope" {n++} END{print n+0}' "$CURRENT_REG/claims.tsv")
actual_equations=$(awk -F '\t' -v source="$source" 'FNR>1 && $2==source && $12=="false" && $7=="equation" {n++} END{print n+0}' "$CURRENT_REG/claims.tsv")
actual_empty=$(awk -F '\t' -v source="$source" '
  NR==FNR { if (FNR>1 && $2==source) page[$1]=1; next }
  FNR>1 && $2==source && $12=="false" { used[$4]=1 }
  END { for (id in page) if (!(id in used)) n++; print n+0 }
' "$CURRENT_REG/pages.tsv" "$CURRENT_REG/claims.tsv")
if [[ "$recorded_active" != "$actual_active" || "$recorded_equations" != "$actual_equations" || "$recorded_empty" != "$actual_empty" ]]; then
  fail "census invariant count is stale"
fi
[[ "$recorded_targets" == "$actual_targets" ]] || fail "formalization target count is stale"
actual_oid=$(LC_ALL=C awk -F '\t' -v source="$source" 'FNR>1 && $2==source {print}' \
  "$CURRENT_REG/pages.tsv" "$CURRENT_REG/claims.tsv" | git hash-object --stdin)
[[ "$recorded_oid" == "$actual_oid" ]] || fail "census OID is stale"

echo "check-claim-corrections: ok"
