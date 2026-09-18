#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR=${BASH_SOURCE[0]%/*}; [[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=$(cd -P "$SCRIPT_DIR/.." && pwd)
fail(){ echo "check-claim-corrections: $*" >&2; exit 1; }

PRODUCTION=0; EVENT=; TMP=
if [[ ${1:-} == --fixture-dirs ]]; then
  [[ $# -eq 3 ]] || fail "usage: check-claim-corrections.sh --fixture-dirs BASE CURRENT"
  BASE=$(cd "$2" && pwd); CURRENT=$(cd "$3" && pwd)
  [[ -n ${LATTICE_TEST_ROOT:-} ]] || fail "fixture mode requires LATTICE_TEST_ROOT"
  TEST_ROOT=$(cd "$LATTICE_TEST_ROOT" && pwd)
  case "$BASE/" in "$TEST_ROOT/"*) ;; *) fail "fixture base must be below LATTICE_TEST_ROOT";; esac
  case "$CURRENT/" in "$TEST_ROOT/"*) ;; *) fail "fixture current must be below LATTICE_TEST_ROOT";; esac
elif [[ ${1:-} == --correction-event ]]; then
  [[ $# -eq 4 ]] || fail "usage: check-claim-corrections.sh --correction-event EVENT ROOT BASE_COMMIT"
  EVENT=$2; CURRENT=$(cd "$3" && pwd); BASE_COMMIT=$4; PRODUCTION=1
  [[ $(git -C "$CURRENT" rev-parse --show-toplevel 2>/dev/null) == "$CURRENT" ]] || fail "ROOT must be the repository top"
  git -C "$CURRENT" cat-file -e "$BASE_COMMIT:registry/claims.tsv" 2>/dev/null || fail "base commit lacks the claim registry"
  TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-claim-corrections.XXXXXX"); trap 'rm -rf "$TMP"' EXIT HUP INT TERM
  mkdir -p "$TMP/registry"
  while IFS= read -r path; do git -C "$CURRENT" show "$BASE_COMMIT:$path" > "$TMP/$path"; done < <(git -C "$CURRENT" ls-tree -r --name-only "$BASE_COMMIT" registry)
  BASE=$TMP
else fail "explicit --fixture-dirs or --correction-event mode is required"
fi
BASE_REG=$BASE/registry; CURRENT_REG=$CURRENT/registry
for f in claims.tsv item-claims.tsv claim-vocabulary-review.tsv claim-vocabulary.tsv source-invariants.tsv bindings.tsv axioms.tsv claim-axioms.tsv pages.tsv; do
  [[ -f "$BASE_REG/$f" && -f "$CURRENT_REG/$f" ]] || fail "missing registry/$f"
done
for f in correction-events.tsv claim-normalization-reviews.tsv claim-corrections.tsv claim-successors.tsv; do [[ -f "$CURRENT_REG/$f" ]] || fail "missing registry/$f"; done
[[ $(head -1 "$CURRENT_REG/correction-events.tsv") == $'event_id\tevent_position\tsource_id\tbase_commit\treview_ref' ]] || fail "bad correction-events.tsv header"
[[ $(head -1 "$CURRENT_REG/claim-normalization-reviews.tsv") == $'review_id\tevent_id\treview_position\tclaim_id\treview_scope\toutcome\tstatus\trationale\treview_ref' ]] || fail "bad claim-normalization-reviews.tsv header"
[[ $(head -1 "$CURRENT_REG/claim-corrections.tsv") == $'correction_id\tevent_id\tcorrection_position\treview_id\tclaim_id\taction\told_disposition\told_subkind\tnew_disposition\tnew_subkind' ]] || fail "bad claim-corrections.tsv header"
[[ $(head -1 "$CURRENT_REG/claim-successors.tsv") == $'successor_edge_id\tevent_id\tcorrection_id\tpredecessor_claim_id\tsuccessor_position\trelation\tsuccessor_claim_id' ]] || fail "bad claim-successors.tsv header"

awk -F '\t' 'function t(s){return s~/^[A-Za-z0-9][A-Za-z0-9._:#@+-]*$/} FNR>1&&(NF!=5||!t($1)||$2!=FNR-1||seen[$1]++||!t($3)||$4!~/^[0-9a-f]{40}$/||!t($5)){b=1} END{exit b}' "$CURRENT_REG/correction-events.tsv" || fail "invalid correction event ledger"
if [[ -z "$EVENT" ]]; then
  if [[ -f "$BASE_REG/correction-events.tsv" ]]; then
    EVENT=$(awk -F '\t' 'NR==FNR{if(FNR>1)o[$1]=1;next}FNR>1&&!($1 in o){print $1}' "$BASE_REG/correction-events.tsv" "$CURRENT_REG/correction-events.tsv")
  else EVENT=$(awk -F '\t' 'FNR==2{print $1}' "$CURRENT_REG/correction-events.tsv"); fi
  [[ $(printf '%s\n' "$EVENT" | awk 'NF{n++}END{print n+0}') -eq 1 ]] || fail "correction event is not reviewed"
fi
awk -F '\t' -v e="$EVENT" 'FNR>1&&$1==e{n++}END{exit n!=1}' "$CURRENT_REG/correction-events.tsv" || fail "correction event is not reviewed"
RECORDED_BASE=$(awk -F '\t' -v e="$EVENT" 'FNR>1&&$1==e{print $4}' "$CURRENT_REG/correction-events.tsv")
EVENT_REVIEW=$(awk -F '\t' -v e="$EVENT" 'FNR>1&&$1==e{print $5}' "$CURRENT_REG/correction-events.tsv")
[[ $PRODUCTION -eq 0 || "$RECORDED_BASE" == "$BASE_COMMIT" ]] || fail "correction event base commit mismatch"

freeze(){ local f=$1 ec=$2; [[ -f "$BASE_REG/$f" ]] || return 0; awk -F '\t' -v e="$EVENT" -v ec="$ec" 'NR==FNR{if(FNR>1){o[$1]=$0;k[$1]=1}next}FNR>1{s[$1]++;if($1 in k){if($0!=o[$1])b=1}else if(ec==0?$1!=e:$ec!=e)b=1}END{for(i in k)if(s[i]!=1)b=1;exit b}' "$BASE_REG/$f" "$CURRENT_REG/$f" || fail "historical correction ledger drift"; }
freeze correction-events.tsv 0; freeze claim-normalization-reviews.tsv 2; freeze claim-corrections.tsv 2; freeze claim-successors.tsv 2

awk -F '\t' 'function t(s){return s~/^[A-Za-z0-9][A-Za-z0-9._:#@+-]*$/} FILENAME==ARGV[1]{if(FNR>1){e[$1]=1;r[$1]=$5}next}FNR>1{if(NF!=9||seen[$1]++||!($2 in e)||$3!=++p[$2]||sc[$2 SUBSEP $4]++||$5!="exact_statement_readiness"||$6!~/^(unchanged|reclassify|exclude_nonclaim|split)$/||$7!="closed"||!t($8)||$9!=r[$2])b=1}END{exit b}' "$CURRENT_REG/correction-events.tsv" "$CURRENT_REG/claim-normalization-reviews.tsv" || fail "invalid claim normalization review ledger"
awk -F '\t' 'FILENAME==ARGV[1]{if(FNR>1)e[$1]=1;next}FILENAME==ARGV[2]{if(FNR>1){r[$1]=1;re[$1]=$2;rc[$1]=$4;ro[$1]=$6}next}FNR>1{if(NF!=10||seen[$1]++||!($2 in e)||$3!=++p[$2]||!($4 in r)||re[$4]!=$2||rc[$4]!=$5||$6!~/^(reclassify|exclude_nonclaim|split)$/||ro[$4]!=$6||sr[$4]++||sc[$2 SUBSEP $5]++)b=1}END{for(i in r){if(ro[i]=="unchanged"&&sr[i])b=1;if(ro[i]!="unchanged"&&sr[i]!=1)b=1}exit b}' "$CURRENT_REG/correction-events.tsv" "$CURRENT_REG/claim-normalization-reviews.tsv" "$CURRENT_REG/claim-corrections.tsv" || fail "invalid claim correction ledger"

cmp -s "$BASE_REG/axioms.tsv" "$CURRENT_REG/axioms.tsv" && cmp -s "$BASE_REG/claim-axioms.tsv" "$CURRENT_REG/claim-axioms.tsv" || fail "correction event introduces an axiom artifact"
cmp -s "$BASE_REG/bindings.tsv" "$CURRENT_REG/bindings.tsv" || fail "correction event introduces an R4 artifact"
for p in "$BASE_REG"/*.tsv; do f=${p##*/}; case "$f" in claims.tsv|item-claims.tsv|claim-vocabulary-review.tsv|claim-vocabulary.tsv|source-invariants.tsv|correction-events.tsv|claim-normalization-reviews.tsv|claim-corrections.tsv|claim-successors.tsv|bindings.tsv|axioms.tsv|claim-axioms.tsv)continue;;esac; [[ -f "$CURRENT_REG/$f" ]]&&cmp -s "$p" "$CURRENT_REG/$f" || fail "unrelated frozen registry drift"; done

awk -F '\t' -v e="$EVENT" '
 FILENAME==ARGV[1]{if(FNR>1&&$2==e){rat[$4]=$8;ref[$4]=$9;out[$4]=$6}next}
 FILENAME==ARGV[2]{if(FNR>1){old[$1]=$0;ok[$1]=1;od[$1]=$6;os[$1]=$7}next}
 FILENAME==ARGV[3]{if(FNR>1){cur[$1]=$0;ck[$1]=1;nd[$1]=$6;ns[$1]=$7;ct[$1]=$8;oid[$1]=$9;ex[$1]=$10;xr[$1]=$11;tm[$1]=$12;su[$1]=$13;tr[$1]=$14;tv[$1]=$15}next}
 FILENAME==ARGV[4]{if(FNR>1&&$2==e){a[$5]=$6;c[$5]=1;lod[$5]=$7;los[$5]=$8;lnd[$5]=$9;lns[$5]=$10;rid[$5]=$4}next}
 END{
  for(id in ok){if(!(id in ck))bad("unmanifested claim drift");if(!(id in c)){if(old[id]!=cur[id])bad("unmanifested claim drift");continue} if(out[id]!=a[id])bad("correction lacks owning review");if(lod[id]!=od[id]||los[id]!=os[id]||lnd[id]!=nd[id]||lns[id]!=ns[id])bad("correction ledger does not match claim transition");n=split(old[id],x,"\t");split(cur[id],y,"\t");if(a[id]=="reclassify"){for(i=1;i<=n;i++)if(i!=6&&i!=7&&x[i]!=y[i])bad("unmanifested claim drift");if(tm[id]!="false"||ex[id]!="NONE"||xr[id]!="NONE")bad("invalid reclassify transition")}else if(a[id]=="exclude_nonclaim"){for(i=1;i<=n;i++)if(i!=6&&i!=10&&i!=11&&x[i]!=y[i])bad("unmanifested claim drift");if(nd[id]!="out_of_scope"||ns[id]!=os[id]||tm[id]!="false"||ex[id]!=rat[id]||xr[id]!=ref[id])bad("invalid nonclaim exclusion")}else{for(i=1;i<=n;i++)if(i<12&&x[i]!=y[i])bad("unmanifested claim drift");if(nd[id]!=od[id]||ns[id]!=os[id]||tm[id]!="true"||su[id]=="NONE"||tr[id]!=rat[id]||tv[id]!=ref[id])bad("invalid split transition")}}
  for(id in c)if(!(id in ok))bad("correction targets an unknown frozen claim");for(id in ck)if(!(id in ok)){if(ct[id]~/^[[:space:]]*(True|False)[.]?[[:space:]]*$/||ct[id]=="")bad("contentless correction surrogate");if(oid[id]!~/^[0-9a-f]{40}$/)bad("new correction successor lacks a frozen content OID");if(tm[id]!="false"||ex[id]!="NONE"||xr[id]!="NONE")bad("new correction successor is not active")};exit failed}
 function bad(s){print s>"/dev/stderr";failed=1}
' "$CURRENT_REG/claim-normalization-reviews.tsv" "$BASE_REG/claims.tsv" "$CURRENT_REG/claims.tsv" "$CURRENT_REG/claim-corrections.tsv" || fail "unmanifested claim drift"

awk -F '\t' -v e="$EVENT" '
 FILENAME==ARGV[1]{if(FNR>1)o[$1]=1;next}FILENAME==ARGV[2]{if(FNR>1){c[$1]=1;t[$1]=$12;s[$1]=$13}next}FILENAME==ARGV[3]{if(FNR>1&&$2==e){co[$1]=1;a[$1]=$6;p[$1]=$5}next}FNR==1{next}$2==e{if(NF!=7||se[$1]++||!($3 in co)||p[$3]!=$4||a[$3]!="split")bad("successor provenance has no split correction");z=$5+0;if($5!~/^[1-9][0-9]*$/||z!=++n[$3]||sp[$3 SUBSEP z]++)bad("duplicate or noncontiguous successor position");if($6!~/^(new_successor|existing_duplicate)$/)bad("bad successor relation");if(!($7 in c))bad("unknown correction successor");if($6=="new_successor"&&($7 in o))bad("new successor reuses a frozen claim ID");if($6=="existing_duplicate"&&!($7 in o))bad("existing duplicate is not frozen");if(ss[$3 SUBSEP $7]++)bad("duplicate correction successor");if(z==1)first[$4]=$7;if($6=="new_successor")nn[$3]++;succ[$7]=$6}END{for(x in co)if(a[x]=="split"&&(n[x]==0||nn[x]==0))bad(n[x]==0?"split successor provenance is incomplete":"split requires a new successor");for(x in c)if(!(x in o)&&succ[x]!="new_successor")bad("split successor provenance is incomplete");for(x in first){if(t[x]!="true")bad("successor predecessor is not tombstoned");if(s[x]!=first[x])bad("tombstone does not name its first successor")};exit failed}function bad(s){print s>"/dev/stderr";failed=1}
' "$BASE_REG/claims.tsv" "$CURRENT_REG/claims.tsv" "$CURRENT_REG/claim-corrections.tsv" "$CURRENT_REG/claim-successors.tsv" || fail "split successor provenance is incomplete"

while IFS= read -r id; do content=$(awk -F '\t' -v id="$id" '$1==id{print $8;exit}' "$CURRENT_REG/claims.tsv"); recorded=$(awk -F '\t' -v id="$id" '$1==id{print $9;exit}' "$CURRENT_REG/claims.tsv"); [[ "$recorded" == "$(printf '%s' "$content"|git hash-object --stdin)" ]] || fail "new correction successor content OID is stale"; done < <(awk -F '\t' -v e="$EVENT" 'FNR>1&&$2==e&&$6=="new_successor"{print $7}' "$CURRENT_REG/claim-successors.tsv")

awk -F '\t' -v e="$EVENT" 'FILENAME==ARGV[1]{if(FNR>1&&$2==e)x[$5]=1;next}FILENAME==ARGV[2]{if(FNR>1&&$2==e&&$6=="new_successor")x[$7]=1;next}FILENAME==ARGV[3]{if(FNR>1&&!($1 in x))o[$1]=$0;next}FILENAME==ARGV[4]{if(FNR>1&&!($1 in x))c[$1]=$0;next}END{for(i in o)if(c[i]!=o[i])b=1;for(i in c)if(!(i in o))b=1;exit b}' "$CURRENT_REG/claim-corrections.tsv" "$CURRENT_REG/claim-successors.tsv" "$BASE_REG/claim-vocabulary-review.tsv" "$CURRENT_REG/claim-vocabulary-review.tsv" || fail "unrelated vocabulary review drift"
awk -F '\t' -v e="$EVENT" 'FILENAME==ARGV[1]{if(FNR>1&&$2==e)x[$5]=1;next}FILENAME==ARGV[2]{if(FNR>1&&$2==e&&$6=="new_successor")x[$7]=1;next}FILENAME==ARGV[3]{if(FNR>1&&!($1 in x))o[$0]=1;next}FILENAME==ARGV[4]{if(FNR>1&&!($1 in x))c[$0]=1;next}END{for(i in o)if(!(i in c))b=1;for(i in c)if(!(i in o))b=1;exit b}' "$CURRENT_REG/claim-corrections.tsv" "$CURRENT_REG/claim-successors.tsv" "$BASE_REG/claim-vocabulary.tsv" "$CURRENT_REG/claim-vocabulary.tsv" || fail "unrelated vocabulary use drift"
awk -F '\t' -v e="$EVENT" 'FILENAME==ARGV[1]{if(FNR>1)o[$0]=1;next}FILENAME==ARGV[2]{if(FNR>1&&$2==e&&$6=="new_successor")a[$7]=1;next}FNR>1{c[$0]=1;if(!($0 in o)&&!($3 in a))b=1}END{for(i in o)if(!(i in c))b=1;exit b}' "$BASE_REG/item-claims.tsv" "$CURRENT_REG/claim-successors.tsv" "$CURRENT_REG/item-claims.tsv" || fail "unrelated item-claim drift"
awk -F '\t' -v e="$EVENT" 'FILENAME==ARGV[1]{if(FNR>1&&$2==e){a[$5]=$6;r[$5]=$4}next}FILENAME==ARGV[2]{if(FNR>1)rr[$1]=$9;next}FILENAME==ARGV[3]{if(FNR>1&&$2==e&&$6=="new_successor"){p[$7]=$4;ad[$7]=1}next}FILENAME==ARGV[4]{if(FNR>1)c[$1]=1;next}FILENAME==ARGV[5]{if(FNR>1){it[$3]=$1;iu[$3]++}next}FILENAME==ARGV[6]{if(FNR>1){vr[$1]=$3;vu[$1]++}next}FILENAME==ARGV[7]{if(FNR>1)vv[$1]++;next}END{for(i in a)if(a[i]=="reclassify"){if(vu[i]!=1||vr[i]!=rr[r[i]])bad("reclassified claim lacks correction vocabulary review")}else{if(vu[i])bad("excluded predecessor retains vocabulary review");if(vv[i])bad("excluded predecessor retains vocabulary use")}for(i in ad){if(!(i in c))continue;if(iu[i]==0)bad("active successor lacks the predecessor item");if(iu[i]>1)bad("active successor has duplicate item provenance");if(it[i]!=it[p[i]])bad("active successor lacks the predecessor item");if(vu[i]!=1)bad("active successor lacks vocabulary review")};exit failed}function bad(s){print s>"/dev/stderr";failed=1}' "$CURRENT_REG/claim-corrections.tsv" "$CURRENT_REG/claim-normalization-reviews.tsv" "$CURRENT_REG/claim-successors.tsv" "$CURRENT_REG/claims.tsv" "$CURRENT_REG/item-claims.tsv" "$CURRENT_REG/claim-vocabulary-review.tsv" "$CURRENT_REG/claim-vocabulary.tsv" || fail "correction relation propagation failed"

IFS=$'\t' read -r source pages ra rt re rem ro rr < <(awk -F '\t' 'FNR==2{print}' "$CURRENT_REG/source-invariants.tsv")
[[ $(head -1 "$CURRENT_REG/source-invariants.tsv") == $'source_id\tphysical_page_count\tactive_claim_count\tformalization_target_count\tequation_pair_count\tno_claim_page_count\tcensus_oid\treview_ref' ]] || fail "bad source-invariants.tsv header"
aa=$(awk -F '\t' -v s="$source" 'FNR>1&&$2==s&&$12=="false"{n++}END{print n+0}' "$CURRENT_REG/claims.tsv"); at=$(awk -F '\t' -v s="$source" 'FNR>1&&$2==s&&$12=="false"&&$6!="out_of_scope"{n++}END{print n+0}' "$CURRENT_REG/claims.tsv"); ae=$(awk -F '\t' -v s="$source" 'FNR>1&&$2==s&&$12=="false"&&$7=="equation"{n++}END{print n+0}' "$CURRENT_REG/claims.tsv"); am=$(awk -F '\t' -v s="$source" 'NR==FNR{if(FNR>1&&$2==s)p[$1]=1;next}FNR>1&&$2==s&&$12=="false"{u[$4]=1}END{for(i in p)if(!(i in u))n++;print n+0}' "$CURRENT_REG/pages.tsv" "$CURRENT_REG/claims.tsv")
[[ "$ra" == "$aa" && "$re" == "$ae" && "$rem" == "$am" ]] || fail "census invariant count is stale"
[[ "$rt" == "$at" ]] || fail "formalization target count is stale"
ao=$(LC_ALL=C awk -F '\t' -v s="$source" 'FNR>1&&$2==s{print}' "$CURRENT_REG/pages.tsv" "$CURRENT_REG/claims.tsv"|git hash-object --stdin); [[ "$ro" == "$ao" ]] || fail "census OID is stale"
echo "check-claim-corrections: ok"
