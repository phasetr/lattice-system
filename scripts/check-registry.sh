#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
REG="$ROOT/registry"
REF="$ROOT/references/tasaki-2020.tsv"
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
check_table "$REG/bindings.tsv" $'claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_oid\tnonvacuity_decl' 6
check_table "$REG/axioms.tsv" $'axiom_id\tdeclaration\tmodule\tcategory\tsource_locator\trationale\treopen_condition' 7
check_table "$REG/claim-axioms.tsv" $'claim_id\taxiom_id' 2
check_table "$REF" $'source_id\tlocal_ref_key\tedition\tpdf_oid\ttext_oid\tcoverage\tnotes' 7
[[ $(awk 'END { print NR }' "$REG/phase.tsv") -eq 2 ]] || fail "phase.tsv must have exactly one data row"
{ IFS= read -r _; IFS= read -r phase; } < "$REG/phase.tsv"
case "$phase" in bootstrap|census|vocabulary|skeleton|proof) ;; *) fail "bad phase: $phase" ;; esac
for file in "$REG/pages.tsv" "$REG/claims.tsv" "$REG/bindings.tsv" "$REG/axioms.tsv" "$REF"; do
  LC_ALL=C awk -F '\t' 'NR > 1 && seen[$1]++ { print FILENAME ": duplicate first-column ID " $1 > "/dev/stderr"; bad=1 } END { exit bad }' "$file" || exit 1
done
for spec in "$REG/claim-axioms.tsv:1,2"; do
  file=${spec%%:*}; columns=${spec#*:}
  LC_ALL=C awk -F '\t' -v columns="$columns" '
    NR == 1 { next }
    { n=split(columns,a,","); key=""; for (i=1;i<=n;i++) key=key SUBSEP $(a[i]); if (seen[key]++) { print FILENAME ": duplicate composite key" > "/dev/stderr"; bad=1 } }
    END { exit bad }
  ' "$file" || exit 1
done
LC_ALL=C awk -F '\t' '
  NR == FNR { if (FNR > 1) source[$1]=1; next }
  FNR == 1 { next }
  $1 !~ /^[A-Z][A-Z0-9_]*$/ { bad("bad source ID " $1) }
  $2 == "" || $3 == "" { bad("empty reference identity field") }
  $4 != "" && ($4 !~ /^[0-9a-f]+$/ || (length($4) != 40 && length($4) != 64)) { bad("bad PDF OID") }
  $5 != "" && ($5 !~ /^[0-9a-f]+$/ || (length($5) != 40 && length($5) != 64)) { bad("bad text OID") }
  $6 !~ /^(pending|pass1|pass2|reconciled|frozen)$/ { bad("bad coverage " $6) }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$REF" "$REF" || exit 1
[[ $(awk 'END { print NR }' "$REF") -eq 2 ]] || fail "every phase requires exactly one reference row"
awk -F '\t' 'NR == 2 && ($1 != "TASAKI2020" || $2 == "" || $3 == "") { exit 1 }' "$REF" || fail "reference identity must be the single TASAKI2020 source"
LC_ALL=C awk -F '\t' '
  NR == FNR { if (FNR > 1) source[$1]=1; next }
  FNR == 1 { next }
  $1 !~ /^PG-[A-Z0-9_]+-[0-9][0-9][0-9][0-9]$/ { bad("bad page ID " $1) }
  !($2 in source) { bad("unknown source " $2) }
  $3 !~ /^[0-9][0-9][0-9][0-9][0-9][0-9]$/ { bad("bad page order key " $3) }
  $7 !~ /^(content|front_matter|back_matter|blank|index)$/ { bad("bad page kind " $7) }
  $8 !~ /^(pending|complete|disputed)$/ || $9 !~ /^(pending|complete|disputed)$/ { bad("bad census pass value") }
  $10 != "PENDING" && ($10 !~ /^[0-9a-f]+$/ || (length($10) != 40 && length($10) != 64)) { bad("bad source OID") }
  ($2 in lastOrder) && $3 <= lastOrder[$2] { bad("page order is not strictly increasing") }
  { lastOrder[$2]=$3 }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$REF" "$REG/pages.tsv" || exit 1
LC_ALL=C awk -F '\t' '
  function token(s) { return s ~ /^[A-Za-z0-9][A-Za-z0-9._:\/#@+-]*$/ }
  FILENAME == ARGV[1] { if (FNR > 1) source[$1]=1; next }
  FILENAME == ARGV[2] { if (FNR > 1) { page[$1]=1; pageSource[$1]=$2 } next }
  FNR == 1 { next }
  $1 !~ /^CL-[A-Z0-9_]+-[0-9][0-9][0-9][0-9]$/ { bad("bad claim ID " $1) }
  !($2 in source) || !($4 in page) || pageSource[$4] != $2 { bad("bad claim source/page foreign key") }
  $3 !~ /^[0-9][0-9][0-9][0-9][0-9][0-9]\.[0-9][0-9][0-9][0-9]$/ { bad("bad claim order key " $3) }
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
' "$REF" "$REG/pages.tsv" "$REG/claims.tsv" || exit 1
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
LC_ALL=C awk -F '\t' '
  NR == FNR { if (FNR > 1) claim[$1]=1; next }
  FNR == 1 { next }
  !($1 in claim) { bad("unknown binding claim") }
  $2 == "" || $4 == "" { bad("empty statement declaration or module") }
  $5 != "PENDING" && ($5 !~ /^[0-9a-f]+$/ || (length($5) != 40 && length($5) != 64)) { bad("bad statement OID") }
  function bad(s) { print FILENAME ":" FNR ": " s > "/dev/stderr"; failed=1 }
  END { exit failed }
' "$REG/claims.tsv" "$REG/bindings.tsv" || exit 1
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
if [[ "$phase" == bootstrap ]]; then
  for table in pages claims slices dependencies bindings axioms claim-axioms; do
    [[ $(awk 'END { print NR }' "$REG/$table.tsv") -eq 1 ]] || fail "bootstrap requires header-only $table.tsv"
  done
  awk -F '\t' 'NR == 2 && ($1 != "TASAKI2020" || $2 == "" || $3 != "unspecified" || $4 != "" || $5 != "" || $6 != "pending") { exit 1 }' "$REF" || fail "bootstrap reference must use edition unspecified, blank OIDs, and pending coverage"
else
  awk -F '\t' 'NR == 2 { e=tolower($3); if (e ~ /^(unspecified|pending|unknown|none)$/ || $3 !~ /^[A-Za-z0-9][A-Za-z0-9._+-]*$/ || $4 == "" || $5 == "" || length($4) != length($5) || $6 == "pending") exit 1 }' "$REF" || fail "post-bootstrap reference requires verified edition, equal-width OIDs, and non-pending coverage"
fi
echo "check-registry: ok"
