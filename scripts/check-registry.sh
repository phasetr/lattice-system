#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=$(cd "$SCRIPT_DIR/.." && pwd)
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
ROOT=$(cd "$ROOT" && pwd) || { echo "check-registry: invalid root" >&2; exit 1; }
REG="$ROOT/registry"
MULTI_SOURCE=0
if [[ -f "$REG/sources.tsv" ]]; then
  MULTI_SOURCE=1
  SOURCE="$REG/sources.tsv"
else
  SOURCE="$ROOT/references/tasaki-2020.tsv"
fi
fail() { echo "check-registry: $*" >&2; exit 1; }

check_table() {
  local file=$1 header=$2 columns=$3
  [[ -f "$file" ]] || fail "missing ${file#"$ROOT/"}"
  IFS= read -r actual_header < "$file" || fail "empty ${file#"$ROOT/"}"
  [[ "$actual_header" == "$header" ]] || fail "bad header in ${file#"$ROOT/"}"
  LC_ALL=C awk -F '\t' -v n="$columns" '
    NF != n { print FILENAME ":" NR ": expected " n " columns, got " NF > "/dev/stderr"; bad=1 }
    {
      for (i=1; i<=NF; i++) {
        if ($i ~ /[[:cntrl:]]/) { print FILENAME ":" NR ": control character in field" > "/dev/stderr"; bad=1 }
        trimmed=$i; gsub(/^( | )+|( | )+$/, "", trimmed)
        if (trimmed != $i) { print FILENAME ":" NR ": surrounding whitespace in field" > "/dev/stderr"; bad=1 }
      }
    }
    END { exit bad }
  ' "$file" || exit 1
}
check_table "$REG/phase.tsv" 'phase' 1
check_table "$REG/pages.tsv" $'page_id\tsource_id\torder_key\tprinted_page\tpdf_page\tsection\tpage_kind\tpass1\tpass2\tsource_oid' 10
check_table "$REG/claims.tsv" $'claim_id\tsource_id\torder_key\tpage_id\tlocator\tdisposition\tsubkind\tnormalized_content\tcontent_oid\texclusion_rationale\texclusion_review_ref\ttombstone\tsuperseded_by\ttombstone_rationale\ttombstone_review_ref' 15
check_table "$REG/slices.tsv" $'slice_id\tposition\tclaim_id' 3
check_table "$REG/dependencies.tsv" $'claim_id\trole\ttarget_claim_id\trationale' 4
check_table "$REG/bindings.tsv" $'claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_kind\tstatement_shape\tstatement_type_oid\tstatement_value_oid\timplementation_status\tproof_kind\tproof_type_oid\tproof_value_oid\tnonvacuity_decl\tnonvacuity_oid\treview_ref' 15
check_table "$REG/claim-context.tsv" $'claim_id\tposition\tsetup_claim_id\tuse_kind\tscope\treview_ref' 6
check_table "$REG/axioms.tsv" $'axiom_id\tdeclaration\tmodule\tcategory\tsource_locator\trationale\treopen_condition' 7
check_table "$REG/claim-axioms.tsv" $'claim_id\taxiom_id' 2
check_table "$REG/claim-vocabulary-review.tsv" $'claim_id\tbasis\treview_ref' 3
check_table "$REG/vocabulary.tsv" $'vocabulary_id\tdeclaration\tmodule\tdeclaration_kind\torigin\tparent_vocabulary_id\ttype_oid\tdeclaration_oid\tdesign_role\tfiniteness_scope' 10
check_table "$REG/claim-vocabulary.tsv" $'claim_id\tvocabulary_id' 2
check_table "$REG/modules.tsv" $'module\tsource_path\trole' 3
check_table "$REG/imports.tsv" $'module\tposition\timported_module\tis_exported\tis_meta\timport_all' 6
check_table "$REG/statement-modules.tsv" $'module\tsource_path\trole' 3
check_table "$REG/statement-imports.tsv" $'module\tposition\timported_module\tis_exported\tis_meta\timport_all' 6
if [[ "$MULTI_SOURCE" -eq 1 ]]; then
  "$SCRIPT_DIR/check-schema.sh" "$ROOT" >/dev/null
else
  check_table "$SOURCE" $'source_id\tlocal_ref_key\tedition\tpdf_oid\ttext_oid\tcoverage\tnotes' 7
fi
[[ $(awk 'END { print NR }' "$REG/phase.tsv") -eq 2 ]] || fail "phase.tsv must have exactly one data row"
{ IFS= read -r _; IFS= read -r phase; } < "$REG/phase.tsv"
case "$phase" in bootstrap|census|vocabulary|skeleton|proof) ;; *) fail "bad phase: $phase" ;; esac
for file in "$REG/pages.tsv" "$REG/claims.tsv" "$REG/bindings.tsv" "$REG/axioms.tsv" "$REG/claim-vocabulary-review.tsv" "$REG/vocabulary.tsv" "$REG/modules.tsv" "$REG/statement-modules.tsv" "$SOURCE"; do
  LC_ALL=C awk -F '\t' 'NR > 1 && seen[$1]++ { print FILENAME ": duplicate first-column ID " $1 > "/dev/stderr"; bad=1 } END { exit bad }' "$file" || exit 1
done
for spec in "$REG/claim-axioms.tsv:1,2" "$REG/claim-vocabulary.tsv:1,2" "$REG/imports.tsv:1,2" "$REG/statement-imports.tsv:1,2" "$REG/claim-context.tsv:1,2"; do
  file=${spec%%:*}; columns=${spec#*:}
  LC_ALL=C awk -F '\t' -v columns="$columns" '
    NR == 1 { next }
    { n=split(columns,a,","); key=""; for (i=1;i<=n;i++) key=key SUBSEP $(a[i]); if (seen[key]++) { print FILENAME ": duplicate composite key" > "/dev/stderr"; bad=1 } }
    END { exit bad }
  ' "$file" || exit 1
done
if [[ "$MULTI_SOURCE" -eq 0 ]]; then
LC_ALL=C awk -F '\t' -v phase="$phase" '
  NR == FNR { if (FNR > 1) source[$1]=1; next }
  FNR == 1 { next }
  $1 !~ /^[A-Z][A-Z0-9_]*$/ { bad("bad source ID " $1) }
  $2 == "" || $3 == "" { bad("empty reference identity field") }
  $4 != "" && ($4 !~ /^[0-9a-f]+$/ || (length($4) != 40 && length($4) != 64)) { bad("bad PDF OID") }
  $5 != "" && ($5 !~ /^[0-9a-f]+$/ || (length($5) != 40 && length($5) != 64)) { bad("bad text OID") }
  ($4 == "") != ($5 == "") { bad("PDF and text OIDs must transition atomically") }
  $4 != "" && length($4) != length($5) { bad("PDF and text OIDs must have equal width") }
  $6 !~ /^(pending|pass1|pass2|reconciled|frozen)$/ { bad("bad coverage " $6) }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$SOURCE" "$SOURCE" || exit 1
[[ $(awk 'END { print NR }' "$SOURCE") -eq 2 ]] || fail "legacy fixture requires exactly one reference row"
awk -F '\t' 'NR == 2 && ($1 != "TASAKI2020" || $2 == "" || $3 == "") { exit 1 }' "$SOURCE" || fail "legacy fixture identity must be TASAKI2020"
else
  "$SCRIPT_DIR/check-sources.sh" "$ROOT" >/dev/null
fi
LC_ALL=C awk -F '\t' '
  NR == FNR { if (FNR > 1) source[$1]=1; next }
  FNR == 1 { next }
  $1 !~ /^PG-[A-Z0-9_]+-[0-9][0-9][0-9][0-9][0-9]*$/ { bad("bad page ID " $1) }
  !($2 in source) { bad("unknown source " $2) }
  $3 !~ /^[0-9][0-9][0-9][0-9][0-9][0-9]$/ { bad("bad page order key " $3) }
  $4 == "" || $4 == "unspecified" { bad("missing printed page label must use NONE") }
  $5 !~ /^[1-9][0-9]*$/ { bad("PDF page must be a positive integer") }
  $6 == "" { bad("missing section must use NONE") }
  $7 !~ /^(content|front_matter|back_matter|blank|index)$/ { bad("bad page kind " $7) }
  $8 !~ /^(pending|complete|disputed)$/ || $9 !~ /^(pending|complete|disputed)$/ { bad("bad census pass value") }
  $10 != "PENDING" && ($10 !~ /^[0-9a-f]+$/ || (length($10) != 40 && length($10) != 64)) { bad("bad source OID") }
  $8 == "complete" && $9 == "complete" && $10 == "PENDING" { bad("two-pass-complete page needs a frozen source OID") }
  ($2 in lastOrder) && $3 <= lastOrder[$2] { bad("page order is not strictly increasing") }
  { lastOrder[$2]=$3 }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$SOURCE" "$REG/pages.tsv" || exit 1
LC_ALL=C awk -F '\t' '
  function token(s) { return s ~ /^[A-Za-z0-9][A-Za-z0-9._:\/#@+-]*$/ }
  FILENAME == ARGV[1] { if (FNR > 1) source[$1]=1; next }
  FILENAME == ARGV[2] { if (FNR > 1) { page[$1]=1; pageSource[$1]=$2 } next }
  FNR == 1 { next }
  $1 !~ /^CL-[A-Z0-9_]+-[0-9][0-9][0-9][0-9][0-9]*$/ { bad("bad claim ID " $1) }
  !($2 in source) || !($4 in page) || pageSource[$4] != $2 { bad("bad claim source/page foreign key") }
  $3 !~ /^[0-9][0-9][0-9][0-9][0-9][0-9]\.[0-9][0-9][0-9][0-9](\.[0-9][0-9][0-9][0-9])?$/ { bad("bad claim order key " $3) }
  $5 == "" || $8 == "" { bad("empty locator or normalized content") }
  $6 !~ /^(assertion|definition|notation|hypothesis|domain|conjecture|out_of_scope)$/ { bad("bad disposition " $6) }
  $7 !~ /^(theorem|lemma|proposition|corollary|equation|definition|notation|problem|remark|subclaim|unnumbered_obligation|hypothesis|domain|conjecture)$/ { bad("bad subkind " $7) }
  $9 != "PENDING" && ($9 !~ /^[0-9a-f]+$/ || (length($9) != 40 && length($9) != 64)) { bad("bad content OID") }
  $6 == "out_of_scope" && (($10 == "" || $10 == "NONE") || ($11 == "" || $11 == "NONE")) { bad("out_of_scope needs exclusion rationale and review ref") }
  $6 != "out_of_scope" && ($10 != "NONE" || $11 != "NONE") { bad("non-excluded claim must use NONE exclusion fields") }
  $10 != "NONE" && !token($10) { bad("bad exclusion rationale token") }
  $11 != "NONE" && !token($11) { bad("bad exclusion review token") }
  $12 !~ /^(false|true)$/ { bad("bad tombstone flag") }
  $12 == "false" && ($13 != "NONE" || $14 != "NONE" || $15 != "NONE") { bad("active claim has supersession metadata") }
  $12 == "true" && (($13 == "" || $13 == "NONE") || ($14 == "" || $14 == "NONE") || ($15 == "" || $15 == "NONE")) { bad("tombstone needs successor, rationale, and review ref") }
  $14 != "NONE" && !token($14) { bad("bad tombstone rationale token") }
  $15 != "NONE" && !token($15) { bad("bad tombstone review token") }
  ($2 in lastOrder) && $3 <= lastOrder[$2] { bad("claim order is not strictly increasing") }
  { known[$1]=1; tombstone[$1]=$12; successor[$1]=$13; lastOrder[$2]=$3 }
  function visit(id, nxt) {
    if (mark[id] == 1) { bad("supersession cycle"); return }
    if (mark[id] == 2) return
    mark[id]=1; nxt=successor[id]
    if (nxt != "NONE") visit(nxt)
    mark[id]=2
  }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END {
    for (id in successor) if (successor[id] != "NONE") {
      if (!(successor[id] in known)) bad("unknown superseded_by " successor[id])
      if (successor[id] == id) bad("self supersession")
    }
    for (id in known) visit(id)
    exit failed
  }
' "$SOURCE" "$REG/pages.tsv" "$REG/claims.tsv" || exit 1
if [[ "$MULTI_SOURCE" -eq 0 ]]; then
LC_ALL=C awk -F '\t' '
  NR == FNR { if (FNR > 1) { claim[$1]=1; tombstone[$1]=$12 } next }
  FNR == 1 { next }
  $1 !~ /^SL-[A-Z0-9_]+-[0-9][0-9][0-9][0-9]$/ { bad("bad slice ID " $1) }
  $2 !~ /^[1-9][0-9]*$/ || !($3 in claim) { bad("bad slice position or claim") }
  seenClaim[$3]++ { bad("claim occurs in multiple slice rows " $3) }
  seenPair[$1 SUBSEP $3]++ { bad("duplicate slice membership") }
  $2+0 != ++count[$1] { bad("non-contiguous slice position") }
  { rows++ }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { if (rows) for (id in claim) if (tombstone[id] == "false" && !(id in seenClaim)) bad("claim missing from slices " id); exit failed }
' "$REG/claims.tsv" "$REG/slices.tsv" || exit 1
LC_ALL=C awk -F '\t' '
  function token(s) { return s ~ /^[A-Za-z0-9][A-Za-z0-9._:\/#@+-]*$/ }
  NR == FNR { if (FNR > 1) { claim[$1]=1; order[$1]=$3 } next }
  FNR == 1 { next }
  !($1 in claim) || !($3 in claim) { bad("unknown dependency claim") }
  $2 !~ /^(requires|required_by|consequence_of)$/ { bad("bad dependency role " $2) }
  $1 == $3 { bad("self dependency") }
  seen[$1 SUBSEP $3]++ { bad("duplicate dependency edge") }
  order[$3] >= order[$1] { bad("dependency target is not earlier in source order") }
  $2 == "required_by" && ($4 == "" || $4 == "NONE") { bad("required_by needs review rationale") }
  $4 != "NONE" && !token($4) { bad("bad dependency rationale token") }
  { if ($2 == "required_by") edge[$3 SUBSEP $1]=1; else edge[$1 SUBSEP $3]=1; node[$1]=node[$3]=1 }
  function visit(n, k,part,to) {
    if (mark[n] == 1) { bad("dependency cycle"); return }
    if (mark[n] == 2) return
    mark[n]=1
    for (k in edge) { split(k,part,SUBSEP); if (part[1] == n) { to=part[2]; visit(to) } }
    mark[n]=2
  }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { for (n in node) visit(n); exit failed }
' "$REG/claims.tsv" "$REG/dependencies.tsv" || exit 1
else
  "$SCRIPT_DIR/check-order.sh" "$ROOT" >/dev/null
fi
LC_ALL=C awk -F '\t' -v phase="$phase" '
  function oid(s) { return s ~ /^[0-9a-f]+$/ && (length(s)==40 || length(s)==64) }
  function name(s) { return s ~ /^[A-Za-z_][A-Za-z0-9_'"'"']*(\.[A-Za-z_][A-Za-z0-9_'"'"']*)*$/ }
  FILENAME == ARGV[1] { if (FNR > 1) { claim[$1]=1; disposition[$1]=$6; active[$1]=($12=="false") } next }
  FILENAME == ARGV[2] { if (FNR > 1) statementModule[$1]=$3; next }
  FNR == 1 { next }
  !($1 in claim) || !active[$1] { bad("unknown or inactive binding claim " $1) }
  disposition[$1] == "out_of_scope" { bad("out-of-scope claim has a binding " $1) }
  !name($2) || !name($4) { bad("bad statement declaration or module") }
  statementModule[$4] != "leaf" { bad("binding needs a registered statement leaf module " $4) }
  $5 !~ /^(definition|abbrev)$/ { bad("bad statement kind " $5) }
  $6 !~ /^(proof_proposition|definition_value|definition_relation|notation_expansion|notation_relation|hypothesis_prop|domain_type|domain_predicate|domain_context)$/ { bad("bad statement shape " $6) }
  $7 != "PENDING" && !oid($7) { bad("bad statement type OID") }
  $8 != "PENDING" && !oid($8) { bad("bad statement value OID") }
  $9 !~ /^(proof_stub|definitional)$/ { bad("bad implementation status " $9) }
  {
    proof=($9=="proof_stub")
    if (proof && (!name($3) || $10!="theorem" || ($11!="PENDING" && !oid($11)))) bad("proof stub metadata is incomplete")
    if (proof && phase!="proof" && $12!="NONE") bad("R4 proof stub value OID must be NONE")
    if (proof && phase=="proof" && $12!="NONE" && !oid($12)) bad("bad R5 proof value OID")
    if (!proof && ($3!="NONE" || $10!="NONE" || $11!="NONE" || $12!="NONE")) bad("definitional binding has proof metadata")
    if ((disposition[$1] ~ /^(assertion|conjecture)$/) != proof) bad("implementation status/disposition mismatch")
    if (proof && $6!="proof_proposition") bad("proof claim has non-proposition shape")
    if (disposition[$1]=="definition" && $6 !~ /^(definition_value|definition_relation)$/) bad("definition claim shape mismatch")
    if (disposition[$1]=="notation" && $6 !~ /^(notation_expansion|notation_relation)$/) bad("notation claim shape mismatch")
    if (disposition[$1]=="hypothesis" && $6!="hypothesis_prop") bad("hypothesis claim shape mismatch")
    if (disposition[$1]=="domain" && $6 !~ /^(domain_type|domain_predicate|domain_context)$/) bad("domain claim shape mismatch")
  }
  ($13=="NONE") != ($14=="NONE") { bad("nonvacuity declaration/OID must be NONE together") }
  $13!="NONE" && !name($13) { bad("bad nonvacuity declaration") }
  $14!="NONE" && $14!="PENDING" && !oid($14) { bad("bad nonvacuity OID") }
  $15=="" || $15=="NONE" { bad("binding needs review_ref") }
  seenStatement[$2]++ { bad("duplicate statement declaration " $2) }
  proof && seenProof[$3]++ { bad("duplicate proof declaration " $3) }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$REG/claims.tsv" "$REG/statement-modules.tsv" "$REG/bindings.tsv" || exit 1

if [[ $(awk 'END { print NR }' "$REG/claim-context.tsv") -gt 1 ]]; then
[[ -f "$REG/item-claims.tsv" ]] || fail "claim-context rows require registry/item-claims.tsv"
LC_ALL=C awk -F '\t' '
  FILENAME == ARGV[1] { if(FNR>1){claim[$1]=1; disposition[$1]=$6; sequence[$1]=++claimSequence} next }
  FILENAME == ARGV[2] { if(FNR>1){item[$3]=$1} next }
  FNR==1 { next }
  !($1 in claim) || !($3 in claim) { bad("unknown claim-context claim") }
  $1==$3 { bad("self claim-context") }
  sequence[$3]>=sequence[$1] { bad("claim-context target is not earlier") }
  disposition[$3] !~ /^(definition|notation|hypothesis|domain)$/ { bad("claim-context target is not a setup claim") }
  $2 !~ /^[1-9][0-9]*$/ || $2+0 != ++position[$1] { bad("non-contiguous claim-context position") }
  $4 !~ /^(assumption|term_reference)$/ { bad("bad claim-context use kind") }
  $5 !~ /^(same_item|inherited)$/ { bad("bad claim-context scope") }
  $5=="same_item" && (item[$1]=="" || item[$1]!=item[$3]) { bad("same_item claim-context crosses source items") }
  $6=="" || $6=="NONE" { bad("claim-context needs review_ref") }
  function bad(s){print FILENAME ":" FNR ": " s > "/dev/stderr";failed=1}
  END{exit failed}
' "$REG/claims.tsv" "$REG/item-claims.tsv" "$REG/claim-context.tsv" || exit 1
fi
LC_ALL=C awk -F '\t' '
  FNR == 1 { next }
  $1 !~ /^AX-[A-Z0-9_]+-[0-9][0-9][0-9][0-9]$/ { bad("bad axiom ID " $1) }
  $2 == "" || $3 == "" || $5 == "" || $6 == "" || $7 == "" { bad("empty axiom field") }
  $4 !~ /^(abstract_cstar|state|gns|kms|weak_dual|wigner|contentless_predicate)$/ { bad("bad axiom category " $4) }
  {
    suffix=$4=="abstract_cstar" ? "AbstractCStar" : $4=="state" ? "State" : $4=="gns" ? "GNS" : $4=="kms" ? "KMS" : $4=="weak_dual" ? "WeakDual" : $4=="wigner" ? "Wigner" : "ContentlessPredicate"
    expected="LatticeSystem.Axioms." suffix
    if ($3 != expected || index($2, expected ".") != 1) bad("axiom declaration/module does not match category namespace")
  }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$REG/axioms.tsv" || exit 1
LC_ALL=C awk -F '\t' '
  FILENAME == ARGV[1] { if (FNR > 1) claim[$1]=1; next }
  FILENAME == ARGV[2] { if (FNR > 1) axiom[$1]=1; next }
  FNR == 1 { next }
  !($1 in claim) || !($2 in axiom) { bad("bad claim-axiom foreign key") }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$REG/claims.tsv" "$REG/axioms.tsv" "$REG/claim-axioms.tsv" || exit 1

LC_ALL=C awk -F '\t' '
  function token(s) { return s ~ /^[A-Za-z0-9][A-Za-z0-9._:\/#@+-]*$/ }
  NR == FNR { if (FNR > 1) { claim[$1]=1; tombstone[$1]=$12 } next }
  FNR == 1 { next }
  !($1 in claim) { bad("unknown vocabulary-review claim " $1) }
  tombstone[$1] != "false" { bad("tombstoned claim has vocabulary review " $1) }
  $2 !~ /^(mathlib_only|project_vocabulary)$/ { bad("bad vocabulary basis " $2) }
  !token($3) { bad("bad vocabulary review token") }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$REG/claims.tsv" "$REG/claim-vocabulary-review.tsv" || exit 1

LC_ALL=C awk -F '\t' '
  function validName(s) { return s ~ /^LatticeSystem(\.[A-Za-z_][A-Za-z0-9_'"'"']*)+$/ }
  FNR == 1 { next }
  !($1 ~ /^VO-LS-[0-9][0-9][0-9][0-9][0-9]*$/ || $1 ~ /^VO-TASAKI2020-000[12]$/) { bad("bad vocabulary ID " $1) }
  !validName($2) || !validName($3) { bad("vocabulary declaration and module must be below LatticeSystem") }
  $4 !~ /^(definition|abbrev|inductive|structure|class|constructor|recursor|projection|instance)$/ { bad("bad vocabulary declaration kind " $4) }
  $5 !~ /^(primary|generated)$/ { bad("bad vocabulary origin " $5) }
  $7 != "PENDING" && ($7 !~ /^[0-9a-f]+$/ || (length($7) != 40 && length($7) != 64)) { bad("bad vocabulary type OID") }
  $8 != "PENDING" && ($8 !~ /^[0-9a-f]+$/ || (length($8) != 40 && length($8) != 64)) { bad("bad vocabulary declaration OID") }
  $9 !~ /^(graph_core|finite_volume|linear_algebra|operator_algebra|quantum_state|stat_mech|fermion|generated)$/ { bad("bad vocabulary design role " $9) }
  $10 !~ /^(none|local_operation|explicit_finite_volume|inherited)$/ { bad("bad vocabulary finiteness scope " $10) }
  $5 == "primary" && $6 != "NONE" { bad("primary vocabulary must use parent NONE") }
  $5 == "primary" && ($9 == "generated" || $10 == "inherited") { bad("primary vocabulary cannot use generated metadata") }
  $5 == "generated" && ($6 == "" || $6 == "NONE" || $6 == $1) { bad("generated vocabulary needs a distinct parent") }
  $5 == "generated" && $4 !~ /^(constructor|recursor|projection)$/ { bad("generated vocabulary has a non-generated declaration kind") }
  $5 == "generated" && ($9 != "generated" || $10 != "inherited") { bad("generated vocabulary needs generated/inherited metadata") }
  seenDecl[$2]++ { bad("duplicate vocabulary declaration " $2) }
  NR > 2 && $1 <= previous { bad("vocabulary IDs are not strictly increasing") }
  { known[$1]=1; origin[$1]=$5; parent[$1]=$6; previous=$1 }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END {
    for (id in parent) if (parent[id] != "NONE" && (!(parent[id] in known) || origin[parent[id]] != "primary")) bad("unknown or non-primary vocabulary parent " parent[id])
    exit failed
  }
' "$REG/vocabulary.tsv" || exit 1

LC_ALL=C awk -F '\t' '
  function validModule(s) { return s ~ /^LatticeSystem(\.[A-Za-z_][A-Za-z0-9_'"'"']*)*$/ }
  FNR == 1 { next }
  !validModule($1) { bad("bad registered module " $1) }
  $2 !~ /^LatticeSystem(\/[A-Za-z_][A-Za-z0-9_'"'"']*)*\.lean$/ { bad("bad module source path " $2) }
  $3 !~ /^(leaf|umbrella|root)$/ { bad("bad module role " $3) }
  {
    rows++
    expected=$1; gsub(/\./, "/", expected); expected=expected ".lean"
    if ($2 != expected) bad("module/source path mismatch")
    if ($3 == "root") { roots++; if ($1 != "LatticeSystem" || $2 != "LatticeSystem.lean") bad("root module identity mismatch") }
    else if ($1 == "LatticeSystem") bad("LatticeSystem module must have root role")
  }
  seenPath[$2]++ { bad("duplicate module source path " $2) }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { if (NR > 1 && roots != 1) bad("module registry needs exactly one root"); exit failed }
' "$REG/modules.tsv" || exit 1

LC_ALL=C awk -F '\t' '
  function validModule(s) { return s ~ /^LatticeSystem(\.[A-Za-z_][A-Za-z0-9_'"'"']*)*$/ }
  FILENAME == ARGV[1] { if (FNR > 1) vocabularyModule[$1]=1; next }
  FNR == 1 { next }
  !validModule($1) { bad("bad registered statement module " $1) }
  $2 !~ /^LatticeSystem(\/[A-Za-z_][A-Za-z0-9_'"'"']*)*\.lean$/ { bad("bad statement module source path " $2) }
  $3 !~ /^(leaf|umbrella)$/ { bad("bad statement module role " $3) }
  {
    rows++
    expected=$1; gsub(/\./, "/", expected); expected=expected ".lean"
    if ($2 != expected) bad("statement module/source path mismatch")
    if ($1 in vocabularyModule) bad("module is registered in both vocabulary and statement registries " $1)
    if ($3 == "umbrella") umbrellas++
  }
  seenPath[$2]++ { bad("duplicate statement module source path " $2) }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { if (rows && umbrellas != 1) bad("statement module registry needs exactly one umbrella"); exit failed }
' "$REG/modules.tsv" "$REG/statement-modules.tsv" || exit 1

LC_ALL=C awk -F '\t' '
  FILENAME == ARGV[1] { if (FNR > 1) { claim[$1]=1; tombstone[$1]=$12 } next }
  FILENAME == ARGV[2] { if (FNR > 1) { module[$1]=$3 } next }
  FILENAME == ARGV[3] {
    if (FNR > 1) {
      if (!($3 in module) || module[$3] != "leaf") bad("vocabulary declaration needs a registered leaf module " $3)
      vocabulary[$1]=1
    }
    next
  }
  FNR == 1 { next }
  !($1 in claim) || tombstone[$1] != "false" { bad("bad claim-vocabulary claim " $1) }
  !($2 in vocabulary) { bad("unknown claim-vocabulary ID " $2) }
  { usedClaim[$1]=1; usedVocabulary[$2]=1 }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$REG/claims.tsv" "$REG/modules.tsv" "$REG/vocabulary.tsv" "$REG/claim-vocabulary.tsv" || exit 1

LC_ALL=C awk -F '\t' '
  function validModule(s) { return s ~ /^[A-Za-z_][A-Za-z0-9_'"'"']*(\.[A-Za-z_][A-Za-z0-9_'"'"']*)*$/ }
  NR == FNR { if (FNR > 1) module[$1]=1; next }
  FNR == 1 { next }
  !($1 in module) { bad("import owner is not registered " $1) }
  $2 !~ /^[1-9][0-9]*$/ { bad("bad import position") }
  !validModule($3) { bad("bad imported module " $3) }
  $4 !~ /^(false|true)$/ || $5 !~ /^(false|true)$/ || $6 !~ /^(false|true)$/ { bad("bad import flag") }
  $2+0 != ++count[$1] { bad("non-contiguous import position") }
  $1 == $3 { bad("self import") }
  index($3, "LatticeSystem.") == 1 && !($3 in module) { bad("unregistered project import " $3) }
  index($3, "LatticeSystem.") != 1 && $3 != "LatticeSystem" && $3 !~ /^Mathlib(\.|$)/ { bad("unauthorized external import " $3) }
  { if ($3 in module) { edge[$1 SUBSEP $3]=1; node[$1]=node[$3]=1 } }
  function visit(n, k, part, to) {
    if (mark[n] == 1) { bad("project import cycle"); return }
    if (mark[n] == 2) return
    mark[n]=1
    for (k in edge) { split(k,part,SUBSEP); if (part[1] == n) { to=part[2]; visit(to) } }
    mark[n]=2
  }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { for (n in node) visit(n); exit failed }
' "$REG/modules.tsv" "$REG/imports.tsv" || exit 1

LC_ALL=C awk -F '\t' '
  function validModule(s) { return s ~ /^[A-Za-z_][A-Za-z0-9_'"'"']*(\.[A-Za-z_][A-Za-z0-9_'"'"']*)*$/ }
  FILENAME == ARGV[1] { if (FNR > 1) project[$1]=1; next }
  FILENAME == ARGV[2] { if (FNR > 1) { project[$1]=1; statement[$1]=1 } next }
  FNR == 1 { next }
  !($1 in statement) { bad("unknown statement import owner " $1) }
  $2 !~ /^[1-9][0-9]*$/ || $2+0 != ++count[$1] { bad("non-contiguous statement import position") }
  !validModule($3) { bad("bad statement imported module " $3) }
  $4 !~ /^(false|true)$/ || $5 !~ /^(false|true)$/ || $6 !~ /^(false|true)$/ { bad("bad statement import flag") }
  $1 == $3 { bad("self statement import") }
  index($3,"LatticeSystem.")==1 && !($3 in project) { bad("unregistered statement project import " $3) }
  index($3,"LatticeSystem.")!=1 && $3!="LatticeSystem" && $3 !~ /^Mathlib(\.|$)/ { bad("unauthorized statement external import " $3) }
  { if ($3 in statement) { edge[$1 SUBSEP $3]=1; node[$1]=node[$3]=1 } }
  function visit(n, k,p,to) { if(mark[n]==1){bad("statement import cycle");return} if(mark[n]==2)return; mark[n]=1; for(k in edge){split(k,p,SUBSEP);if(p[1]==n){to=p[2];visit(to)}} mark[n]=2 }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { for(n in node) visit(n); exit failed }
' "$REG/modules.tsv" "$REG/statement-modules.tsv" "$REG/statement-imports.tsv" || exit 1

if [[ "$phase" == vocabulary ]]; then
  for table in slices dependencies bindings claim-context axioms claim-axioms statement-modules statement-imports; do
    [[ $(awk 'END { print NR }' "$REG/$table.tsv") -eq 1 ]] || fail "vocabulary requires header-only $table.tsv"
  done
  if [[ "$MULTI_SOURCE" -eq 0 ]]; then
  LC_ALL=C awk -F '\t' '
    FILENAME == ARGV[1] { if (FNR > 1) { active[$1]=($12=="false"); target[$1]=($12=="false" && $6!="out_of_scope") } next }
    FILENAME == ARGV[2] { if (FNR > 1) { review[$1]=$2; reviewed[$1]++ } next }
    FILENAME == ARGV[3] { if (FNR > 1) { typeOid[$1]=$7; declarationOid[$1]=$8; vocabulary[$1]=1 } next }
    FNR == 1 { next }
    { claimUse[$1]++; vocabularyUse[$2]++ }
    END {
      for (id in active) {
        if (target[id] && reviewed[id] != 1) bad("active claim lacks exactly one vocabulary review " id)
        if (active[id] && !target[id] && reviewed[id]) bad("out-of-scope claim has vocabulary review " id)
        if (!active[id] && reviewed[id]) bad("tombstoned claim has vocabulary review " id)
        if (review[id] == "mathlib_only" && claimUse[id]) bad("mathlib-only claim has project vocabulary " id)
        if (review[id] == "project_vocabulary" && !claimUse[id]) bad("project-vocabulary claim lacks vocabulary use " id)
      }
      for (id in vocabulary) {
        if (typeOid[id] == "PENDING") bad("vocabulary phase has pending type OID " id)
        if (declarationOid[id] == "PENDING") bad("vocabulary phase has pending declaration OID " id)
        if (!vocabularyUse[id]) bad("unused vocabulary declaration " id)
      }
      exit failed
    }
    function bad(s) { print "vocabulary contract: " s > "/dev/stderr"; failed=1 }
  ' "$REG/claims.tsv" "$REG/claim-vocabulary-review.tsv" "$REG/vocabulary.tsv" "$REG/claim-vocabulary.tsv" || exit 1
  else
    awk -F '\t' 'FNR>1 && ($7=="PENDING" || $8=="PENDING") { bad=1 } END { exit bad }' "$REG/vocabulary.tsv" || fail "vocabulary capability forbids pending declaration OIDs"
  fi
fi

# R4 freeze means every registered binding OID is a real object ID. The skeleton
# semantic checker treats `PENDING` as a wildcard, so the ban lives here.
if [[ "$phase" == skeleton || "$phase" == proof ]]; then
  awk -F '\t' 'FNR>1 && ($7=="PENDING" || $8=="PENDING" || $11=="PENDING" || $14=="PENDING") { bad=1 } END { exit bad }' \
    "$REG/bindings.tsv" || fail "$phase capability forbids pending binding OIDs"
fi

if [[ "$phase" == bootstrap ]]; then
  for table in pages claims slices dependencies bindings axioms claim-axioms claim-vocabulary-review vocabulary claim-vocabulary modules imports; do
    [[ $(awk 'END { print NR }' "$REG/$table.tsv") -eq 1 ]] || fail "bootstrap requires header-only $table.tsv"
  done
  if [[ "$MULTI_SOURCE" -eq 0 ]]; then
  awk -F '\t' '
    function edition(s, lower) {
      lower=tolower(s)
      return s ~ /^[A-Za-z0-9][A-Za-z0-9._+-]*$/ && lower !~ /^(unspecified|pending|unknown|none)$/
    }
    NR == 2 {
      unverified=($3 == "unspecified" && $4 == "" && $5 == "" && $6 == "pending")
      verified=(edition($3) && $4 ~ /^[0-9a-f]+$/ && ($5 ~ /^[0-9a-f]+$/) && (length($4) == 40 || length($4) == 64) && length($4) == length($5) && $6 == "pending")
      if ($1 != "TASAKI2020" || $2 == "" || (!unverified && !verified)) exit 1
    }
  ' "$SOURCE" || fail "bootstrap reference must be either unverified or atomically source-frozen, with pending coverage"
  fi
else
  if [[ "$MULTI_SOURCE" -eq 0 ]]; then
    awk -F '\t' 'NR == 2 { e=tolower($3); if (e ~ /^(unspecified|pending|unknown|none)$/ || $3 !~ /^[A-Za-z0-9][A-Za-z0-9._+-]*$/ || $4 == "" || $5 == "" || length($4) != length($5) || $6 == "pending") exit 1 }' "$SOURCE" || fail "post-bootstrap reference requires verified edition, equal-width OIDs, and non-pending coverage"
  fi
fi
if [[ "$MULTI_SOURCE" -eq 1 ]]; then
  "$SCRIPT_DIR/check-lifecycle.sh" "$ROOT" >/dev/null
fi
echo "check-registry: ok"
