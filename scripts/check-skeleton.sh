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
if [[ $FIXTURE -eq 1 ]]; then
  [[ -n "${LATTICE_TEST_ROOT:-}" ]] || fail "fixture mode requires LATTICE_TEST_ROOT"
  TEST_ROOT=$(cd "$LATTICE_TEST_ROOT" && pwd) || fail "invalid LATTICE_TEST_ROOT"
  case "$TEST_ROOT" in "$PROJECT_ROOT"|"$PROJECT_ROOT"/*) fail "LATTICE_TEST_ROOT must be repository-external" ;; esac
  [[ "$TEST_ROOT" != / ]] || fail "LATTICE_TEST_ROOT must not contain the repository"
  case "$PROJECT_ROOT" in "$TEST_ROOT"|"$TEST_ROOT"/*) fail "LATTICE_TEST_ROOT must not contain the repository" ;; esac
  case "$ROOT/" in "$TEST_ROOT/"*) ;; *) fail "fixture root must be below LATTICE_TEST_ROOT" ;; esac
else
  [[ $(git -C "$ROOT" rev-parse --show-toplevel 2>/dev/null) == "$ROOT" ]] ||
    fail "ROOT must be repository top; fixture mode is explicit"
fi

REG=$ROOT/registry
for table in phase sources source-progress claims item-claims bindings dependencies claim-context axioms claim-axioms modules imports statement-modules statement-imports; do
  [[ -f "$REG/$table.tsv" ]] || fail "missing registry/$table.tsv"
done
[[ $(head -n 1 "$REG/bindings.tsv") == $'claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_kind\tstatement_shape\tstatement_type_oid\tstatement_value_oid\timplementation_status\tproof_kind\tproof_type_oid\tproof_value_oid\tnonvacuity_decl\tnonvacuity_oid\treview_ref' ]] || fail "bad bindings.tsv header"

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
"$LEAN" --root="$PROJECT_ROOT" "$PROJECT_ROOT/Checker/Semantic.lean" -o "$TMP/Checker/Semantic.olean" >/dev/null ||
  fail "failed to compile shared semantic checker"
"$LEAN" --root="$PROJECT_ROOT" "$PROJECT_ROOT/Checker/Skeleton.lean" -o "$TMP/Checker/Skeleton.olean" >/dev/null ||
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

# A plain `public import` re-exports a theorem as `axiomInfo`, so its proof term
# and its direct `sorryAx` occurrences are invisible. `import all` restores the
# kernel values; Lean rejects the combined `public import all` spelling.
{
  echo module
  while IFS= read -r module; do printf 'public import %s\n' "$module"; done < "$TMP/modules.list"
  while IFS= read -r module; do printf 'import all %s\n' "$module"; done < "$TMP/modules.list"
  echo 'public meta import Checker.Skeleton'
  printf '\n#skeleton_dump "%s" "%s"\n' "$TMP/statement-modules.list" "$TMP/environment.tsv"
} > "$TMP/SkeletonRun.lean"
"$LEAN" --root="$TMP" "$TMP/SkeletonRun.lean" -o "$TMP/SkeletonRun.olean" >/dev/null ||
  fail "skeleton environment inspection failed"

mkdir -p "$TMP/types" "$TMP/values"
awk -F '\t' -v td="$TMP/types" -v vd="$TMP/values" '$1=="D"{
  n++;print n "\t" $2 "\t" $3 "\t" $4 "\t" $5 "\t" $6 "\t" $7 "\t" $8 "\t" $9 "\t" $10 "\t" $11 "\t" $12 "\t" $13 "\t" $14 "\t" $15
  printf "%s",$16 > (td "/" n);printf "%s",$17 > (vd "/" n)
}' "$TMP/environment.tsv" > "$TMP/declaration-index.tsv"
: > "$TMP/actual.tsv"
while IFS= read -r index; do
  type_oid=$(git -C "$PROJECT_ROOT" hash-object "$TMP/types/$index")
  value_oid=$(git -C "$PROJECT_ROOT" hash-object "$TMP/values/$index")
  printf '%s\t%s\t%s\n' "$index" "$type_oid" "$value_oid" >> "$TMP/declaration-oids.tsv"
done < <(cut -f1 "$TMP/declaration-index.tsv")
awk -F '\t' 'BEGIN{OFS="\t"}NR==FNR{toid[$1]=$2;void[$1]=$3;next}{print $2,$3,$4,toid[$1],void[$1],$5,$6,$7,$8,$9,$10,$11,$12,$13,$14,$15}' \
  "$TMP/declaration-oids.tsv" "$TMP/declaration-index.tsv" > "$TMP/actual.tsv"

awk -F '\t' 'BEGIN{OFS="\t"}NR>1{
  print $4,$2,$5,$7,$8,"statement",$1,$6
  if($3!="NONE")print $4,$3,$10,$11,$12,"proof",$1,$6
  if($13!="NONE")print $4,$13,"theorem",$14,"NONE","nonvacuity",$1,$6
}' "$REG/bindings.tsv" > "$TMP/expected.tsv"
awk -F '\t' 'BEGIN{OFS="\t"}NR>1{print $3,$2,"axiom","ANY","ANY","axiom",$1,"axiom"}' "$REG/axioms.tsv" >> "$TMP/expected.tsv"

awk -F '\t' '
  NR==FNR{key=$1 SUBSEP $2;if(seen[key]++)bad("duplicate registered declaration " $2);kind[key]=$3;toid[key]=$4;void[key]=$5;role[key]=$6;next}
  {key=$1 SUBSEP $2;actual[key]=1;if(!(key in role)){bad("extra declaration " $2);next}
   if(kind[key]!=$3)bad("wrong declaration kind " $2 " expected=" kind[key] " actual=" $3 " row=" $0)
   if(toid[key]!="ANY"&&toid[key]!="PENDING"&&toid[key]!=$4)bad("wrong type OID " $2)
   if(void[key]!="ANY"&&void[key]!="NONE"&&void[key]!="PENDING"&&void[key]!=$5)bad("wrong value OID " $2)}
  END{for(k in role)if(!(k in actual))bad("missing or wrong-module declaration " k);exit failed}
  function bad(s){print s > "/dev/stderr";failed=1}
' "$TMP/expected.tsv" "$TMP/actual.tsv" || fail "declaration registry/environment mismatch"

# Column 6 is `Meta.isProp` of the declaration type and column 14 is
# `Meta.isProp` of its value. A primary statement carries the proposition as its
# value, so only column 14 can witness a `proof_proposition` shape.
awk -F '\t' '
  FILENAME==ARGV[1]{if(FNR>1){statement[$2]=$1;shape[$2]=$6;if($3!="NONE"){proof[$3]=$1;target[$3]=$2;unresolved[$3]=($12=="NONE")};if($13!="NONE")nonvac[$13]=$1}next}
  {
    d=$2;direct=$7+0;trans=$8
    if(d in statement){
      if(direct||trans=="true")bad("primary statement depends on sorryAx " d)
      if($13=="true")bad("literal True primary statement " d)
      if(shape[d]=="proof_proposition"&&$14!="true")bad("proof proposition is not Prop-valued " d)
    }else if(d in proof){
      if($6!="true")bad("proof declaration is not Prop-valued " d)
      n=split($9,a,",");found=0;for(i=1;i<=n;i++)if(a[i]==target[d])found=1
      if(!found)bad("proof type does not reference bound primary " d)
      if(unresolved[d]&&(direct!=1||trans!="true"))bad(direct==0&&trans=="true"?"hidden or transitive-only sorryAx " d:"proof stub needs exactly one direct sorryAx " d)
      if(!unresolved[d]&&(direct||trans=="true"))bad("completed proof depends on sorryAx " d)
    }else if(d in nonvac){
      if(direct||trans=="true")bad("nonvacuity declaration depends on sorryAx " d)
      if($15=="true")bad("nonvacuity declaration concludes True " d)
      if($16=="true")bad("nonvacuity declaration restates its own hypothesis " d)
    }
    else if(direct||trans=="true")bad("unregistered sorryAx declaration " d)
  }
  END{exit failed} function bad(s){print s > "/dev/stderr";failed=1}
' "$REG/bindings.tsv" "$TMP/actual.tsv" || fail "primary/proof-hole bijection failed"

# Actual primary references to other claim statements must be admitted by the
# reviewed context or dependency registry and must target an earlier claim.
# Claim rows are in global source order, so row order is the order key.
# Assumption context edges must occur in a binder domain/antecedent.
awk -F '\t' '
  FILENAME==ARGV[1]{if(FNR>1)sequence[$1]=++claims;next}
  FILENAME==ARGV[2]{if(FNR>1)claimOf[$2]=$1;next}
  FILENAME==ARGV[3]{if(FNR>1){context[$1 SUBSEP $3]=$4;admitted[$1 SUBSEP $3]=1}next}
  FILENAME==ARGV[4]{if(FNR>1){if($2=="required_by")admitted[$3 SUBSEP $1]=1;else admitted[$1 SUBSEP $3]=1}next}
  {
    if($2 in claimOf){owner=claimOf[$2];n=split($10,a,",");for(i=1;i<=n;i++)if(a[i] in claimOf&&claimOf[a[i]]!=owner)actual[owner SUBSEP claimOf[a[i]]]=1
      n=split($12,g,",");for(i=1;i<=n;i++)if(g[i] in claimOf)guard[owner SUBSEP claimOf[g[i]]]=1}
  }
  END{
    for(k in context){if(!(k in actual))bad("registered context is absent from statement " k);if(context[k]=="assumption"&&!(k in guard))bad("assumption context is not a binder or antecedent " k)}
    for(k in actual){
      split(k,edge,SUBSEP)
      if(!(k in admitted))bad("actual setup reference lacks claim-context or dependency " k)
      else if(sequence[edge[2]]>=sequence[edge[1]])bad("statement references a claim that is not earlier " k)
    }
    exit failed
  }
  function bad(s){print s > "/dev/stderr";failed=1}
' "$REG/claims.tsv" "$REG/bindings.tsv" "$REG/claim-context.tsv" "$REG/dependencies.tsv" "$TMP/actual.tsv" ||
  fail "claim-context semantic mismatch"

awk -F '\t' '
  FILENAME==ARGV[1]{if(FNR>1){owner[$2]=$1;if($3!="NONE")owner[$3]=$1;if($13!="NONE")owner[$13]=$1}next}
  FILENAME==ARGV[2]{if(FNR>1){axiom[$2]=$1;used[$1]=0}next}
  FILENAME==ARGV[3]{if(FNR>1)expected[$1 SUBSEP $2]=1;next}
  {if($2 in owner){n=split($11,names,",");for(i=1;i<=n;i++)if(names[i] in axiom){actual[owner[$2] SUBSEP axiom[names[i]]]=1;used[axiom[names[i]]]=1}}}
  END{for(k in expected)if(!(k in actual))bad("approved claim axiom is not used");for(k in actual)if(!(k in expected))bad("unapproved claim axiom is used");for(id in used)if(!used[id])bad("registered axiom is unused " id);exit failed}
  function bad(s){print s > "/dev/stderr";failed=1}
' "$REG/bindings.tsv" "$REG/axioms.tsv" "$REG/claim-axioms.tsv" "$TMP/actual.tsv" || fail "claim axiom contract failed"

awk -F '\t' 'NR>1{print $0}' "$REG/statement-imports.tsv" | LC_ALL=C sort > "$TMP/expected-imports.tsv"
awk -F '\t' '$1=="I"&&$4!="Init"{p[$2]++;print $2 "\t" p[$2] "\t" $4 "\t" $5 "\t" $6 "\t" $7}' "$TMP/environment.tsv" | LC_ALL=C sort > "$TMP/actual-imports.tsv"
cmp -s "$TMP/expected-imports.tsv" "$TMP/actual-imports.tsv" || fail "statement import registry/environment mismatch"

awk -F '\t' '
  FILENAME==ARGV[1]{if(FNR>1){all[$1]=1;if($3=="root")root=$1}next}
  FILENAME==ARGV[2]{if(FNR>1){all[$1]=1;stmt[$1]=1;if($3=="leaf")leaf[$1]=1;else{umbrella=$1;umbrellas++}}next}
  FILENAME==ARGV[3]||FILENAME==ARGV[4]{if(FNR>1&&$3 in all)reach[$1 SUBSEP $3]=1}
  END{for(m in all)reach[m SUBSEP m]=1;for(k in all)for(i in all)for(j in all)if(reach[i SUBSEP k]&&reach[k SUBSEP j])reach[i SUBSEP j]=1
    if(umbrellas!=1)bad("skeleton needs exactly one umbrella");for(m in leaf)if(!reach[umbrella SUBSEP m])bad("umbrella misses " m);for(m in stmt)if(root!=""&&reach[root SUBSEP m])bad("production root reaches " m);exit failed}
  function bad(s){print s > "/dev/stderr";failed=1}
' "$REG/modules.tsv" "$REG/statement-modules.tsv" "$REG/imports.tsv" "$REG/statement-imports.tsv" || fail "skeleton import isolation failed"

stub_count=$(awk -F '\t' 'NR>1&&$9=="proof_stub"&&$12=="NONE"{n++}END{print n+0}' "$REG/bindings.tsv")
suppress_count=0
while IFS=$'\t' read -r module source_path role; do
  [[ "$module" != module && "$role" == leaf ]] || continue
  grep -Eq '^[[:space:]]*set_option[[:space:]]+warningAsError[[:space:]]+false[[:space:]]*$' "$ROOT/$source_path" &&
    fail "module-wide warningAsError suppression in $source_path"
  n=$(grep -Ec '^[[:space:]]*set_option[[:space:]]+warningAsError[[:space:]]+false[[:space:]]+in[[:space:]]*$' "$ROOT/$source_path" || true)
  suppress_count=$((suppress_count+n))
done < "$REG/statement-modules.tsv"
[[ $suppress_count -eq $stub_count ]] || fail "local warning suppression count does not match unresolved proof stubs"

if [[ $FIXTURE -eq 0 ]]; then
  awk -F '\t' 'NR>1&&$3=="umbrella"{if($1!="LatticeSystem.Skeleton")exit 1;found=1}END{exit !found}' "$REG/statement-modules.tsv" ||
    fail "production skeleton umbrella must be LatticeSystem.Skeleton"
  grep -Eq '^defaultTargets = \["LatticeSystem"\]$' "$ROOT/lakefile.toml" || fail "skeleton must remain nondefault"
  (cd "$ROOT" && lake build +LatticeSystem.Skeleton >/dev/null) || fail "nondefault Lake skeleton target failed"
fi
echo "check-skeleton: ok"
