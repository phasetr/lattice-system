#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=$(cd "$SCRIPT_DIR/.." && pwd)
fail() { echo "check-base-diff: $*" >&2; exit 1; }

ALLOW_SUPERSESSION=0
if [[ ${1:-} == "--allow-supersession" ]]; then
  ALLOW_SUPERSESSION=1
  shift
fi

if [[ ${1:-} == "--fixture-dirs" ]]; then
  [[ $# -eq 3 ]] || fail "usage: check-base-diff.sh --fixture-dirs BASE CURRENT"
  BASE_DIR=$(cd "$2" && pwd) || fail "invalid fixture base directory"
  CURRENT_DIR=$(cd "$3" && pwd) || fail "invalid fixture current directory"
  case "$BASE_DIR/" in "$PROJECT_ROOT/fixtures/"*) ;; *) fail "fixture base must be below fixtures/" ;; esac
  case "$CURRENT_DIR/" in "$PROJECT_ROOT/fixtures/"*) ;; *) fail "fixture current must be below fixtures/" ;; esac
  [[ "$BASE_DIR" != "$PROJECT_ROOT" && "$CURRENT_DIR" != "$PROJECT_ROOT" ]] || fail "production root cannot use fixture mode"
  BASE_MODE=directory
else
  ROOT=${1:-$PROJECT_ROOT}
  ROOT=$(cd "$ROOT" && pwd) || fail "invalid repository root"
  [[ $(git -C "$ROOT" rev-parse --show-toplevel 2>/dev/null) == "$ROOT" ]] || fail "ROOT must be the repository top"
  BASE_REF=${2:-HEAD^}
  BASE_TIP=$(git -C "$ROOT" rev-parse --verify "$BASE_REF^{commit}" 2>/dev/null) || fail "invalid or unfetched base ref: $BASE_REF"
  BASE_COMMIT=$(git -C "$ROOT" merge-base HEAD "$BASE_TIP" 2>/dev/null) || fail "base ref has no merge base: $BASE_REF"
  git -C "$ROOT" merge-base --is-ancestor "$BASE_COMMIT" HEAD || fail "computed base is not an ancestor of HEAD"
  git -C "$ROOT" merge-base --is-ancestor "$BASE_COMMIT" "$BASE_TIP" || fail "computed base is not an ancestor of base ref"
  if ! git -C "$ROOT" cat-file -e "$BASE_COMMIT:registry/claims.tsv" 2>/dev/null; then
    echo "check-base-diff: bootstrap skip (verified ancestor has no registry/claims.tsv)"
    exit 0
  fi
  BASE_MODE=git
  CURRENT_DIR=$ROOT
fi

base_file() {
  local path=$1
  if ! base_exists "$path"; then
    case "$path" in
      registry/claim-vocabulary-review.tsv) printf '%s\n' $'claim_id\tbasis\treview_ref'; return ;;
      registry/vocabulary.tsv) printf '%s\n' $'vocabulary_id\tdeclaration\tmodule\tdeclaration_kind\torigin\tparent_vocabulary_id\ttype_oid\tdeclaration_oid\tdesign_role\tfiniteness_scope'; return ;;
      registry/claim-vocabulary.tsv) printf '%s\n' $'claim_id\tvocabulary_id'; return ;;
      registry/modules.tsv) printf '%s\n' $'module\tsource_path\trole'; return ;;
      registry/imports.tsv) printf '%s\n' $'module\tposition\timported_module\tis_exported\tis_meta\timport_all'; return ;;
      *) fail "base missing $path" ;;
    esac
  fi
  if [[ "$BASE_MODE" == directory ]]; then
    awk '{ print }' "$BASE_DIR/$path"
  else
    git -C "$ROOT" show "$BASE_COMMIT:$path"
  fi
}
base_exists() {
  local path=$1
  if [[ "$BASE_MODE" == directory ]]; then [[ -f "$BASE_DIR/$path" ]]; else git -C "$ROOT" cat-file -e "$BASE_COMMIT:$path" 2>/dev/null; fi
}

for path in registry/phase.tsv registry/pages.tsv registry/claims.tsv registry/slices.tsv registry/dependencies.tsv registry/bindings.tsv registry/axioms.tsv registry/claim-axioms.tsv references/tasaki-2020.tsv; do
  base_exists "$path" || fail "base missing $path"
  [[ -f "$CURRENT_DIR/$path" ]] || fail "current missing $path"
done
for path in registry/claim-vocabulary-review.tsv registry/vocabulary.tsv registry/claim-vocabulary.tsv registry/modules.tsv registry/imports.tsv; do
  [[ -f "$CURRENT_DIR/$path" ]] || fail "current missing $path"
done

detect_deleted_id() {
  local path=$1
  awk -F '\t' '
    NR == FNR { if (FNR > 1) old[$1]=1; next }
    FNR > 1 { current[$1]=1 }
    END { for (id in old) if (!(id in current)) { print "deleted stable ID " id > "/dev/stderr"; bad=1 } exit bad }
  ' <(base_file "$path") "$CURRENT_DIR/$path" || fail "$path stable-ID deletion"
}
compare_columns() {
  local path=$1 columns=$2 label=$3
  awk -F '\t' -v columns="$columns" -v label="$label" '
    function projection(  n,a,i,out) { n=split(columns,a,","); out=""; for (i=1;i<=n;i++) out=out SUBSEP $(a[i]); return out }
    NR == FNR { if (FNR > 1) old[$1]=projection(); next }
    FNR > 1 && ($1 in old) && old[$1] != projection() { print label " changed for " $1 > "/dev/stderr"; bad=1 }
    END { exit bad }
  ' <(base_file "$path") "$CURRENT_DIR/$path" || fail "$path $label regression"
}
require_old_rows() {
  local path=$1 label=$2
  awk -v label="$label" '
    NR == FNR { if (FNR > 1) old[$0]=1; next }
    FNR > 1 { current[$0]=1 }
    END { for (row in old) if (!(row in current)) { print label " disappeared or drifted" > "/dev/stderr"; bad=1 } exit bad }
  ' <(base_file "$path") "$CURRENT_DIR/$path" || fail "$path $label regression"
}

for path in registry/pages.tsv registry/claims.tsv registry/axioms.tsv registry/claim-vocabulary-review.tsv registry/vocabulary.tsv registry/modules.tsv references/tasaki-2020.tsv; do detect_deleted_id "$path"; done
compare_columns registry/pages.tsv '2,3,4,5,6,7' 'identity/order/locator'
if [[ "$ALLOW_SUPERSESSION" -eq 1 ]]; then
  compare_columns registry/claims.tsv '2,3,4,5,6,7,8,10,11' 'identity/order/locator/content/exclusion'
else
  compare_columns registry/claims.tsv '2,3,4,5,6,7,8,10,11,12,13,14,15' 'identity/order/locator/content/exclusion/supersession'
fi
compare_columns registry/axioms.tsv '2,3,4,5,6,7' 'identity/locator/declaration'
compare_columns registry/claim-vocabulary-review.tsv '2,3' 'vocabulary review'
compare_columns registry/vocabulary.tsv '2,3,4,5,6,9,10' 'declaration/module/kind/origin/parent/design/finiteness'
compare_columns registry/modules.tsv '2,3' 'source path/role'
compare_columns references/tasaki-2020.tsv '2' 'source identity'
require_old_rows registry/dependencies.tsv dependency
require_old_rows registry/claim-axioms.tsv claim-axiom
require_old_rows registry/claim-vocabulary.tsv claim-vocabulary
require_old_rows registry/imports.tsv import

awk -F '\t' '
  function validOid(s) { return s ~ /^[0-9a-f]+$/ && (length(s)==40 || length(s)==64) }
  NR == FNR { if (FNR > 1) oid[$1]=$7; next }
  FNR > 1 && ($1 in oid) {
    if (oid[$1]=="PENDING") { if ($7!="PENDING" && !validOid($7)) bad=1 }
    else if (!validOid(oid[$1]) || $7!=oid[$1]) bad=1
  }
  END { if (bad) print "vocabulary type OID regressed" > "/dev/stderr"; exit bad }
' <(base_file registry/vocabulary.tsv) "$CURRENT_DIR/registry/vocabulary.tsv" || fail "vocabulary type regression"

awk -F '\t' '
  function validOid(s) { return s ~ /^[0-9a-f]+$/ && (length(s)==40 || length(s)==64) }
  NR == FNR { if (FNR > 1) oid[$1]=$8; next }
  FNR > 1 && ($1 in oid) {
    if (oid[$1]=="PENDING") { if ($8!="PENDING" && !validOid($8)) bad=1 }
    else if (!validOid(oid[$1]) || $8!=oid[$1]) bad=1
  }
  END { if (bad) print "vocabulary declaration OID regressed" > "/dev/stderr"; exit bad }
' <(base_file registry/vocabulary.tsv) "$CURRENT_DIR/registry/vocabulary.tsv" || fail "vocabulary declaration regression"

awk -F '\t' '
  NR == FNR { if (FNR > 1) old[$1 SUBSEP $3]=$2; next }
  FNR > 1 { key=$1 SUBSEP $3; seen[key]=1; if ((key in old) && $2 != old[key]) { print "slice position changed" > "/dev/stderr"; bad=1 } }
  END { for (key in old) if (!(key in seen)) { print "slice membership disappeared" > "/dev/stderr"; bad=1 } exit bad }
' <(base_file registry/slices.tsv) "$CURRENT_DIR/registry/slices.tsv" || fail "slice regression"

phase_rank() { case "$1" in bootstrap) echo 1;; census) echo 2;; vocabulary) echo 3;; skeleton) echo 4;; proof) echo 5;; *) echo 0;; esac; }
{ IFS= read -r _; IFS= read -r base_phase; } < <(base_file registry/phase.tsv)
{ IFS= read -r _; IFS= read -r current_phase; } < "$CURRENT_DIR/registry/phase.tsv"
[[ $(phase_rank "$current_phase") -ge $(phase_rank "$base_phase") ]] || fail "phase regression: $base_phase -> $current_phase"

awk -F '\t' '
  function rank(s) { return s=="pending" ? 1 : s=="disputed" ? 2 : s=="complete" ? 3 : 0 }
  NR == FNR { if (FNR > 1) { oid[$1]=$10; p1[$1]=rank($8); p2[$1]=rank($9) } next }
  FNR > 1 && ($1 in oid) { if (oid[$1] != "PENDING" && $10 != oid[$1]) bad=1; if (rank($8)<p1[$1] || rank($9)<p2[$1]) bad=1 }
  END { if (bad) print "page OID or census pass regressed" > "/dev/stderr"; exit bad }
' <(base_file registry/pages.tsv) "$CURRENT_DIR/registry/pages.tsv" || fail "page state regression"

awk -F '\t' '
  function validOid(s) { return s ~ /^[0-9a-f]+$/ && (length(s)==40 || length(s)==64) }
  NR == FNR { if (FNR > 1) { oldOid[$1]=$9; tombstone[$1]=$12 } next }
  FNR > 1 && ($1 in oldOid) {
    if (oldOid[$1] == "PENDING") { if ($9 != "PENDING" && !validOid($9)) bad=1 }
    else if (!validOid(oldOid[$1]) || $9 != oldOid[$1]) bad=1
    if (tombstone[$1]=="true" && $12!="true") bad=1
  }
  END { if (bad) print "claim OID or tombstone regressed" > "/dev/stderr"; exit bad }
' <(base_file registry/claims.tsv) "$CURRENT_DIR/registry/claims.tsv" || fail "claim state regression"

if [[ "$ALLOW_SUPERSESSION" -eq 1 ]]; then
  awk -F '\t' '
    function token(s) { return s ~ /^[A-Za-z0-9][A-Za-z0-9._:\/#@+-]*$/ }
    NR == FNR { if (FNR > 1) { baseKnown[$1]=1; oldC[$1]=$9; oldT[$1]=$12; oldS[$1]=$13; oldR[$1]=$14; oldV[$1]=$15 } next }
    FNR > 1 { currentKnown[$1]=1; newC[$1]=$9; newT[$1]=$12; newS[$1]=$13; newR[$1]=$14; newV[$1]=$15 }
    END {
      for (id in oldT) {
        unchanged=(oldT[id]==newT[id] && oldS[id]==newS[id] && oldR[id]==newR[id] && oldV[id]==newV[id])
        transition=(oldC[id]==newC[id] && oldT[id]=="false" && oldS[id]=="NONE" && oldR[id]=="NONE" && oldV[id]=="NONE" && newT[id]=="true" && newS[id]!="NONE" && newS[id]!=id && newR[id]!="" && newR[id]!="NONE" && token(newR[id]) && newV[id]!="" && newV[id]!="NONE" && token(newV[id]) && (newS[id] in currentKnown) && !(newS[id] in baseKnown))
        if (!unchanged && !transition) bad=1
      }
      if (bad) print "invalid dedicated supersession transition" > "/dev/stderr"
      exit bad
    }
  ' <(base_file registry/claims.tsv) "$CURRENT_DIR/registry/claims.tsv" || fail "supersession transition regression"
fi

awk -F '\t' '
  function fixed(s) { return s!="" && s!="NONE" }
  NR == FNR { if (FNR > 1) { statement[$1]=$2; proof[$1]=$3; module[$1]=$4; oid[$1]=$5; nonvac[$1]=$6 } next }
  FNR > 1 { seen[$1]=1; if (($1 in statement) && (statement[$1]!=$2 || module[$1]!=$4 || (oid[$1]!="PENDING" && oid[$1]!=$5) || (fixed(proof[$1]) && proof[$1]!=$3) || (fixed(nonvac[$1]) && nonvac[$1]!=$6))) bad=1 }
  END { for (id in statement) if (!(id in seen)) bad=1; if (bad) print "binding disappeared or identity drifted" > "/dev/stderr"; exit bad }
' <(base_file registry/bindings.tsv) "$CURRENT_DIR/registry/bindings.tsv" || fail "binding regression"

awk -F '\t' '
  function validOid(s) { return s ~ /^[0-9a-f]+$/ && (length(s)==40 || length(s)==64) }
  function edition(s, lower) { lower=tolower(s); return s ~ /^[A-Za-z0-9][A-Za-z0-9._+-]*$/ && lower!="unspecified" && lower!="pending" && lower!="unknown" && lower!="none" }
  function rank(s) { return s=="pending"?1:s=="pass1"?2:s=="pass2"?3:s=="reconciled"?4:s=="frozen"?5:0 }
  NR == FNR { if (FNR > 1) { oldEdition[$1]=$3; pdf[$1]=$4; text[$1]=$5; coverage[$1]=rank($6) } next }
  FNR > 1 && ($1 in pdf) {
    if (oldEdition[$1]=="unspecified") { if ($3!="unspecified" && !edition($3)) bad=1 }
    else if (!edition(oldEdition[$1]) || $3!=oldEdition[$1]) bad=1
    if (pdf[$1]=="" && text[$1]=="") { if (!(($4=="" && $5=="") || (validOid($4) && validOid($5) && length($4)==length($5)))) bad=1 }
    else if (!(validOid(pdf[$1]) && validOid(text[$1]) && length(pdf[$1])==length(text[$1]) && $4==pdf[$1] && $5==text[$1])) bad=1
    if (rank($6)==0 || coverage[$1]==0 || rank($6)<coverage[$1]) bad=1
  }
  END { if (bad) print "reference fingerprint or coverage regressed" > "/dev/stderr"; exit bad }
' <(base_file references/tasaki-2020.tsv) "$CURRENT_DIR/references/tasaki-2020.tsv" || fail "reference regression"

echo "check-base-diff: ok"
