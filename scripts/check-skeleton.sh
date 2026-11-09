#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=$(cd -P "$SCRIPT_DIR/.." && pwd)
fail() { echo "check-skeleton: $*" >&2; exit 1; }

FIXTURE=0
if [[ ${1:-} == --fixture ]]; then
  FIXTURE=1
  [[ $# -eq 2 ]] || fail "usage: check-skeleton.sh --fixture ROOT"
  ROOT=$2
else
  [[ $# -le 1 ]] || fail "usage: check-skeleton.sh [ROOT]"
  ROOT=${1:-$PROJECT_ROOT}
fi
ROOT=$(cd "$ROOT" && pwd) || fail "invalid root"
# The semantic checker is the tool under test in the mutation suite, so an
# alternate copy is accepted only for an explicit, repository-external fixture.
CHECKER_ROOT=$PROJECT_ROOT
if [[ $FIXTURE -eq 1 ]]; then
  [[ -n "${LATTICE_TEST_ROOT:-}" ]] || fail "fixture mode requires LATTICE_TEST_ROOT"
  TEST_ROOT=$(cd "$LATTICE_TEST_ROOT" && pwd) || fail "invalid LATTICE_TEST_ROOT"
  case "$TEST_ROOT" in "$PROJECT_ROOT"|"$PROJECT_ROOT"/*) fail "LATTICE_TEST_ROOT must be repository-external" ;; esac
  [[ "$TEST_ROOT" != / ]] || fail "LATTICE_TEST_ROOT must not contain the repository"
  case "$PROJECT_ROOT" in "$TEST_ROOT"|"$TEST_ROOT"/*) fail "LATTICE_TEST_ROOT must not contain the repository" ;; esac
  case "$ROOT/" in "$TEST_ROOT/"*) ;; *) fail "fixture root must be below LATTICE_TEST_ROOT" ;; esac
  if [[ -n "${LATTICE_SKELETON_CHECKER_DIR:-}" ]]; then
    CHECKER_ROOT=$(cd "$LATTICE_SKELETON_CHECKER_DIR" && pwd) || fail "invalid LATTICE_SKELETON_CHECKER_DIR"
    case "$CHECKER_ROOT/" in "$TEST_ROOT/"*) ;; *) fail "fixture checker must be below LATTICE_TEST_ROOT" ;; esac
  fi
else
  [[ $(git -C "$ROOT" rev-parse --show-toplevel 2>/dev/null) == "$ROOT" ]] ||
    fail "ROOT must be repository top; fixture mode is explicit"
  [[ -z "${LATTICE_SKELETON_CHECKER_DIR:-}" ]] || fail "production run cannot substitute the semantic checker"
fi

REG=$ROOT/registry
for table in phase sources source-progress claims item-claims bindings dependencies claim-context axioms claim-axioms vocabulary claim-vocabulary claim-vocabulary-review modules imports statement-modules statement-imports; do
  [[ -f "$REG/$table.tsv" ]] || fail "missing registry/$table.tsv"
done
[[ $(head -n 1 "$REG/bindings.tsv") == $'claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_kind\tstatement_shape\tstatement_type_oid\tstatement_value_oid\timplementation_status\tproof_kind\tproof_type_oid\tproof_value_oid\tnonvacuity_decl\tnonvacuity_oid\treview_ref' ]] || fail "bad bindings.tsv header"
[[ $(head -n 1 "$REG/axioms.tsv") == $'axiom_id\tdeclaration\tmodule\tcategory\tsource_locator\trationale\treopen_condition\taxiom_type_oid' ]] || fail "bad axioms.tsv header"

[[ $(awk 'END{print NR}' "$REG/phase.tsv") -eq 2 ]] || fail "phase.tsv must have exactly one data row"
{ IFS= read -r _; IFS= read -r PHASE; } < "$REG/phase.tsv"

statement_rows=$(awk 'END{print NR-1}' "$REG/statement-modules.tsv")
binding_rows=$(awk 'END{print NR-1}' "$REG/bindings.tsv")
if [[ $statement_rows -eq 0 && $binding_rows -eq 0 ]]; then
  case "$PHASE" in
    skeleton|proof) fail "$PHASE capability requires a registered skeleton" ;;
  esac
  echo "check-skeleton: ok (contract only; no production skeleton)"
  exit 0
fi
[[ $statement_rows -gt 0 && $binding_rows -gt 0 ]] ||
  fail "statement modules and bindings must be introduced together"

# A source freezes only when every formalization target is bound exactly once
# and nothing else is. Earlier lifecycles may coexist and stage a strict subset.
awk -F '\t' '
  FILENAME==ARGV[1] {if(FNR>1)complete[$1]=($2~/^(skeleton_frozen|proof_active|complete)$/);next}
  FILENAME==ARGV[2] {if(FNR>1){source[$1]=$2;target[$1]=($12=="false"&&$6!="out_of_scope");if(target[$1])targets[$2]++}next}
  FILENAME==ARGV[3] {if(FNR>1){bound[$1]++;if($1 in source)bindings[source[$1]]++}next}
  END{
    for(c in source)if(complete[source[c]]&&target[c]&&!(c in bound))bad("skeleton source lacks a binding " c)
    for(c in bound)if(bound[c]!=1)bad("duplicate binding " c)
    for(s in complete)if(complete[s]&&bindings[s]+0!=targets[s]+0)bad("binding count does not match formalization targets in " s)
    exit failed
  }
  function bad(s){print s > "/dev/stderr";failed=1}
' "$REG/source-progress.tsv" "$REG/claims.tsv" "$REG/bindings.tsv" ||
  fail "source skeleton coverage failed"

TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-skeleton.XXXXXX")
cleanup() { rm -rf "$TMP"; }
trap cleanup EXIT HUP INT TERM
LEAN=$(elan which lean)
BASE_LEAN_PATH=$(cd "$PROJECT_ROOT" && lake env printenv LEAN_PATH)
export LEAN_PATH="$TMP:$BASE_LEAN_PATH"
mkdir -p "$TMP/Checker"
"$LEAN" --root="$CHECKER_ROOT" "$CHECKER_ROOT/Checker/Semantic.lean" -o "$TMP/Checker/Semantic.olean" >/dev/null ||
  fail "failed to compile shared semantic checker"
"$LEAN" --root="$CHECKER_ROOT" "$CHECKER_ROOT/Checker/Skeleton.lean" -o "$TMP/Checker/Skeleton.olean" >/dev/null ||
  fail "failed to compile skeleton semantic checker"

awk -F '\t' 'FNR>1{print $1 "\t" $2 "\t" $3}' "$REG/modules.tsv" "$REG/statement-modules.tsv" > "$TMP/modules.tsv"
awk -F '\t' 'FNR>1{print $0}' "$REG/imports.tsv" "$REG/statement-imports.tsv" > "$TMP/imports.tsv"
cut -f1 "$TMP/modules.tsv" > "$TMP/modules.list"
awk -F '\t' 'FNR>1{print $1}' "$REG/statement-modules.tsv" > "$TMP/statement-modules.list"
: > "$TMP/compiled.list"
remaining=$(awk 'END{print NR}' "$TMP/modules.tsv")
while [[ $remaining -gt 0 ]]; do
  progressed=0
  while IFS=$'\t' read -r module source_path role extra; do
    [[ -z "${extra:-}" && -n "$module" && -n "$source_path" ]] || fail "malformed module row"
    grep -Fqx "$module" "$TMP/compiled.list" && continue
    [[ "$module" =~ ^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$ ]] || fail "unsafe module name"
    [[ "$source_path" != /* && "$source_path" != *..* && "$source_path" == *.lean ]] || fail "unsafe source path"
    [[ -f "$ROOT/$source_path" ]] || fail "missing source path $source_path"
    blocked=0
    while IFS= read -r dep; do
      [[ -n "$dep" ]] || continue
      if grep -Fqx "$dep" "$TMP/modules.list" && ! grep -Fqx "$dep" "$TMP/compiled.list"; then blocked=1; break; fi
    done < <(awk -F '\t' -v m="$module" '$1==m{print $3}' "$TMP/imports.tsv")
    [[ $blocked -eq 0 ]] || continue
    output="$TMP/${module//./\/}.olean"
    mkdir -p "${output%/*}"
    "$LEAN" -DwarningAsError=true --root="$ROOT" "$ROOT/$source_path" -o "$output" >/dev/null ||
      fail "failed to elaborate registered module $module"
    printf '%s\n' "$module" >> "$TMP/compiled.list"
    remaining=$((remaining-1)); progressed=1
  done < "$TMP/modules.tsv"
  [[ $progressed -eq 1 ]] || fail "registered module import graph is cyclic or incomplete"
done

# Lean's module mode can expose imported theorems as axiomInfo without their
# proofs. Use the same non-module import mode required by `#print axioms` so
# transitive kernel proofs are available; do not mistake hidden theorems for
# unregistered axioms or omit their real axiom dependencies.
{
  while IFS= read -r module; do printf 'import %s\n' "$module"; done < "$TMP/modules.list"
  echo 'import Checker.Skeleton'
  printf '\n#skeleton_dump "%s" "%s" "%s" "%s"\n' "$TMP/statement-modules.list" "$TMP/environment.tsv" "$ROOT" "$REG/statement-modules.tsv"
} > "$TMP/SkeletonRun.lean"
"$LEAN" --root="$TMP" "$TMP/SkeletonRun.lean" -o "$TMP/SkeletonRun.olean" >/dev/null ||
  fail "skeleton environment inspection failed"

mkdir -p "$TMP/types" "$TMP/values"
awk -F '\t' -v td="$TMP/types" -v vd="$TMP/values" '$1=="D"{
  n++;print n "\t" $2 "\t" $3 "\t" $4 "\t" $5 "\t" $6 "\t" $7 "\t" $8 "\t" $9 "\t" $10 "\t" $11 "\t" $12 "\t" $13 "\t" $14 "\t" $15 "\t" $16 "\t" $17
  printf "%s",$18 > (td "/" n);printf "%s",$19 > (vd "/" n)
}' "$TMP/environment.tsv" > "$TMP/declaration-index.tsv"
: > "$TMP/actual.tsv"
while IFS= read -r index; do
  type_oid=$(git -C "$PROJECT_ROOT" hash-object "$TMP/types/$index")
  value_oid=$(git -C "$PROJECT_ROOT" hash-object "$TMP/values/$index")
  printf '%s\t%s\t%s\n' "$index" "$type_oid" "$value_oid" >> "$TMP/declaration-oids.tsv"
done < <(cut -f1 "$TMP/declaration-index.tsv")
awk -F '\t' 'BEGIN{OFS="\t"}NR==FNR{toid[$1]=$2;void[$1]=$3;next}{print $2,$3,$4,toid[$1],void[$1],$5,$6,$7,$8,$9,$10,$11,$12,$13,$14,$15,$16,$17}' \
  "$TMP/declaration-oids.tsv" "$TMP/declaration-index.tsv" > "$TMP/actual.tsv"
# Registry OIDs are authored from this environment, so the computed table is
# exported on request. The export is write-only and changes no decision below.
if [[ -n "${LATTICE_SKELETON_ACTUAL_OUT:-}" ]]; then
  cp "$TMP/actual.tsv" "$LATTICE_SKELETON_ACTUAL_OUT" || fail "cannot export the actual declaration table"
fi

awk -F '\t' 'BEGIN{OFS="\t"}NR>1{
  print $4,$2,$5,$7,$8,"statement",$1,$6
  if($3!="NONE")print $4,$3,$10,$11,$12,"proof",$1,$6
  if($13!="NONE")print $4,$13,"theorem",$14,"NONE","nonvacuity",$1,$6
}' "$REG/bindings.tsv" > "$TMP/expected.tsv"
# An axiom carries no kernel value, so only its frozen type OID is comparable.
awk -F '\t' 'BEGIN{OFS="\t"}NR>1{print $3,$2,"axiom",$8,"NONE","axiom",$1,"axiom"}' "$REG/axioms.tsv" >> "$TMP/expected.tsv"

awk -F '\t' '
  NR==FNR{key=$1 SUBSEP $2;if(seen[key]++)bad("duplicate registered declaration " $2);kind[key]=$3;toid[key]=$4;void[key]=$5;role[key]=$6;next}
  {key=$1 SUBSEP $2;actual[key]=1;if(!(key in role)){bad("extra declaration " $2);next}
   if(kind[key]!=$3)bad("wrong declaration kind " $2 " expected=" kind[key] " actual=" $3 " row=" $0)
   if(toid[key]!="PENDING"&&toid[key]!=$4)bad("wrong type OID " $2)
   if(void[key]!="NONE"&&void[key]!="PENDING"&&void[key]!=$5)bad("wrong value OID " $2)}
  END{for(k in role)if(!(k in actual))bad("missing or wrong-module declaration " k);exit failed}
  function bad(s){print s > "/dev/stderr";failed=1}
' "$TMP/expected.tsv" "$TMP/actual.tsv" || fail "declaration registry/environment mismatch"

# Column 6 is `Meta.isProp` of the declaration type and column 15 is
# `Meta.isProp` of its value. A primary statement carries the proposition as its
# value, so only column 15 can witness a `proof_proposition` shape. Column 18
# names the declaration type when it is exactly a constant, which is how a proof
# obligation is pinned to its bound statement rather than to a weakening of it.
awk -F '\t' '
  FILENAME==ARGV[1]{if(FNR>1){statement[$2]=$1;shape[$2]=$6;if($3!="NONE"){proof[$3]=$1;target[$3]=$2;unresolved[$3]=($12=="NONE")};if($13!="NONE"){nonvac[$13]=$1;witnessed[$13]=$2}}next}
  {
    d=$2;direct=$7+0;trans=$8
    if(d in statement){
      if(direct||trans=="true")bad("primary statement depends on sorryAx " d)
      if($14=="true")bad("literal True primary statement " d)
      if(shape[d]=="proof_proposition"&&$15!="true")bad("proof proposition is not Prop-valued " d)
    }else if(d in proof){
      if($6!="true")bad("proof declaration is not Prop-valued " d)
      if($18!=target[d])bad("proof type is not exactly the bound primary statement " d " expected=" target[d] " actual=" $18)
      if(unresolved[d]&&(direct!=1||trans!="true"))bad(direct==0&&trans=="true"?"hidden or transitive-only sorryAx " d:"proof stub needs exactly one direct sorryAx " d)
      if(!unresolved[d]&&(direct||trans=="true"))bad("completed proof depends on sorryAx " d)
    }else if(d in nonvac){
      if(direct||trans=="true")bad("nonvacuity declaration depends on sorryAx " d)
      if($16=="true")bad("nonvacuity declaration concludes True " d)
      if($17=="true")bad("nonvacuity declaration follows from its own hypotheses " d)
      n=split($9,a,",");found=0;for(i=1;i<=n;i++)if(a[i]==witnessed[d])found=1
      if(!found)bad("nonvacuity declaration does not reference its bound statement " d)
    }
    else if(direct||trans=="true")bad("unregistered sorryAx declaration " d)
  }
  END{exit failed} function bad(s){print s > "/dev/stderr";failed=1}
' "$REG/bindings.tsv" "$TMP/actual.tsv" || fail "primary/proof-hole bijection failed"

# Every project constant a primary statement uses must be registered vocabulary
# or another claim statement. References to other claim statements must in turn
# be admitted by the reviewed context or dependency registry. Claim rows are in
# global source order, so row order is the order key; a `required_by` edge is
# the reviewed exception that deliberately pulls a later claim forward.
# Assumption context edges must occur in a binder domain/antecedent, which for a
# definitional binding lives in the declaration type rather than in its value.
awk -F '\t' '
  function root(s,  cut){cut=index(s,".");return cut?substr(s,1,cut-1):s}
  FILENAME==ARGV[1]{if(FNR>1)sequence[$1]=++claims;next}
  FILENAME==ARGV[2]{if(FNR>1){claimOf[$2]=$1;registered[$2]=1}next}
  FILENAME==ARGV[3]{if(FNR>1)registered[$2]=1;next}
  FILENAME==ARGV[4]{if(FNR>1){context[$1 SUBSEP $3]=$4;admitted[$1 SUBSEP $3]=1}next}
  FILENAME==ARGV[5]{if(FNR>1){if($2=="required_by"){admitted[$3 SUBSEP $1]=1;forward[$3 SUBSEP $1]=1}else admitted[$1 SUBSEP $3]=1}next}
  FILENAME==ARGV[6]||FILENAME==ARGV[7]{if(FNR>1)project[root($1)]=1;next}
  {
    if($2 in claimOf){
      owner=claimOf[$2]
      n=split($9 "," $10,a,",")
      for(i=1;i<=n;i++){
        if(a[i]=="")continue
        if(a[i] in claimOf&&claimOf[a[i]]!=owner)actual[owner SUBSEP claimOf[a[i]]]=1
        if((root(a[i]) in project)&&a[i]!=$2&&!(a[i] in registered))bad("primary statement uses an unregistered project constant " a[i])
      }
      n=split($12 "," $13,g,",")
      for(i=1;i<=n;i++)if(g[i] in claimOf)guard[owner SUBSEP claimOf[g[i]]]=1
    }
  }
  END{
    for(k in context){if(!(k in actual))bad("registered context is absent from statement " k);if(context[k]=="assumption"&&!(k in guard))bad("assumption context is not a binder or antecedent " k)}
    for(k in actual){
      split(k,edge,SUBSEP)
      if(!(k in admitted))bad("actual setup reference lacks claim-context or dependency " k)
      else if(k in forward){if(sequence[edge[2]]<=sequence[edge[1]])bad("required_by reference does not pull a later claim forward " k)}
      else if(sequence[edge[2]]>=sequence[edge[1]])bad("statement references a claim that is not earlier " k)
    }
    exit failed
  }
  function bad(s){print s > "/dev/stderr";failed=1}
' "$REG/claims.tsv" "$REG/bindings.tsv" "$REG/vocabulary.tsv" "$REG/claim-context.tsv" \
  "$REG/dependencies.tsv" "$REG/modules.tsv" "$REG/statement-modules.tsv" "$TMP/actual.tsv" ||
  fail "claim-context semantic mismatch"

# A globally registered vocabulary declaration is usable only under this
# primary claim's reviewed admission. This is a necessary direct-use check,
# not a reverse equality with all planned R3 links or future proof dependencies.
awk -F '\t' '
  FILENAME==ARGV[1]{if(FNR>1)vocabulary[$2]=$1;next}
  FILENAME==ARGV[2]{if(FNR>1)owner[$2]=$1;next}
  FILENAME==ARGV[3]{if(FNR>1)admitted[$1 SUBSEP $2]=1;next}
  FILENAME==ARGV[4]{if(FNR>1)basis[$1]=$2;next}
  $2 in owner {
    claim=owner[$2]
    n=split($9 "," $10,constants,",")
    for(i=1;i<=n;i++)if(constants[i] in vocabulary){
      id=vocabulary[constants[i]]
      if(basis[claim]!="project_vocabulary")
        bad("primary project vocabulary contradicts claim review basis " claim " " id)
      else if(!(claim SUBSEP id in admitted))
        bad("primary vocabulary use lacks claim-vocabulary admission " claim " " id)
    }
  }
  END{exit failed} function bad(s){print s > "/dev/stderr";failed=1}
' "$REG/vocabulary.tsv" "$REG/bindings.tsv" "$REG/claim-vocabulary.tsv" \
  "$REG/claim-vocabulary-review.tsv" "$TMP/actual.tsv" || fail "claim vocabulary admission mismatch"

awk -F '\t' '
  FILENAME==ARGV[1]{if(FNR>1){owner[$2]=$1;if($3!="NONE")owner[$3]=$1;if($13!="NONE")owner[$13]=$1}next}
  FILENAME==ARGV[2]{if(FNR>1){axiom[$2]=$1;used[$1]=0}next}
  FILENAME==ARGV[3]{if(FNR>1)expected[$1 SUBSEP $2]=1;next}
  {
    if($2 in owner){
      n=split($11,names,",")
      for(i=1;i<=n;i++){
        name=names[i]
        if(name in axiom){actual[owner[$2] SUBSEP axiom[name]]=1;used[axiom[name]]=1}
        else if(name!="" && name!="propext" && name!="Classical.choice" &&
                name!="Quot.sound" && name!="sorryAx")
          bad("unregistered nonstandard axiom " name " used by " $2)
      }
    }
  }
  END{for(k in expected)if(!(k in actual))bad("approved claim axiom is not used");for(k in actual)if(!(k in expected))bad("unapproved claim axiom is used");for(id in used)if(!used[id])bad("registered axiom is unused " id);exit failed}
  function bad(s){print s > "/dev/stderr";failed=1}
' "$REG/bindings.tsv" "$REG/axioms.tsv" "$REG/claim-axioms.tsv" "$TMP/actual.tsv" || fail "claim axiom contract failed"

awk -F '\t' 'NR>1{print $0}' "$REG/statement-imports.tsv" | LC_ALL=C sort > "$TMP/expected-imports.tsv"
awk -F '\t' '$1=="I"&&$4!="Init"{p[$2]++;print $2 "\t" p[$2] "\t" $4 "\t" $5 "\t" $6 "\t" $7}' "$TMP/environment.tsv" | LC_ALL=C sort > "$TMP/actual-imports.tsv"
if ! cmp -s "$TMP/expected-imports.tsv" "$TMP/actual-imports.tsv"; then
  echo "registered statement imports:" >&2
  cat "$TMP/expected-imports.tsv" >&2
  echo "elaborated statement imports:" >&2
  cat "$TMP/actual-imports.tsv" >&2
  fail "statement import registry/environment mismatch"
fi

awk -F '\t' '
  FILENAME==ARGV[1]{if(FNR>1){all[$1]=1;if($3=="root")root=$1}next}
  FILENAME==ARGV[2]{if(FNR>1){all[$1]=1;stmt[$1]=1;if($3=="leaf")leaf[$1]=1;else{umbrella=$1;umbrellas++}}next}
  FILENAME==ARGV[3]||FILENAME==ARGV[4]{if(FNR>1&&$3 in all)reach[$1 SUBSEP $3]=1}
  END{for(m in all)reach[m SUBSEP m]=1;for(k in all)for(i in all)for(j in all)if(reach[i SUBSEP k]&&reach[k SUBSEP j])reach[i SUBSEP j]=1
    if(umbrellas!=1)bad("skeleton needs exactly one umbrella");for(m in leaf)if(!reach[umbrella SUBSEP m])bad("umbrella misses " m);for(m in stmt)if(root!=""&&reach[root SUBSEP m])bad("production root reaches " m);exit failed}
  function bad(s){print s > "/dev/stderr";failed=1}
' "$REG/modules.tsv" "$REG/statement-modules.tsv" "$REG/imports.tsv" "$REG/statement-imports.tsv" || fail "skeleton import isolation failed"

awk -F '\t' '
  FILENAME==ARGV[1]{if(FNR>1&&$9=="proof_stub"&&$12=="NONE")expected[$4 SUBSEP $3]=1;next}
  $1=="W" {
    key=$2 SUBSEP $3
    if($4!="declaration"||$3=="NONE")bad("unscoped warningAsError suppression in " $2)
    else if(!(key in expected))bad("warningAsError exception is not a registered unresolved proof " $3)
    else seen[key]++
  }
  END{for(key in expected)if(seen[key]!=1)bad("unresolved proof needs exactly one declaration-local warningAsError exception " key);exit failed}
  function bad(s){print s > "/dev/stderr";failed=1}
' "$REG/bindings.tsv" "$TMP/environment.tsv" || fail "warning exception ownership failed"

if [[ $FIXTURE -eq 0 ]]; then
  awk -F '\t' 'NR>1&&$3=="umbrella"{if($1!="LatticeSystem.Skeleton")exit 1;found=1}END{exit !found}' "$REG/statement-modules.tsv" ||
    fail "production skeleton umbrella must be LatticeSystem.Skeleton"
  grep -Eq '^defaultTargets = \["LatticeSystem"\]$' "$ROOT/lakefile.toml" || fail "skeleton must remain nondefault"
  (cd "$ROOT" && lake build +LatticeSystem.Skeleton >/dev/null) || fail "nondefault Lake skeleton target failed"
fi
echo "check-skeleton: ok"
