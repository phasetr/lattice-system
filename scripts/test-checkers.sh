#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
PROJECT_ROOT=$(cd "$PROJECT_ROOT" && pwd)
TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-system-tests.checkers.XXXXXX")
trap 'rm -rf "$TMP"' EXIT
export LATTICE_TEST_ROOT=$TMP
ROOT=$TMP/runtime
mkdir -p "$ROOT/fixtures"
ln -s "$PROJECT_ROOT/scripts" "$ROOT/scripts"

# Every registry case starts from the production registry.  Independent copies
# plus whole-file replacement keep the immutable common baseline untouched.
mkdir -p "$TMP/production"
cp -R "$PROJECT_ROOT/registry" "$TMP/production/registry"
baseline_digest() {
  find "$TMP/production/registry" -type f -print0 | LC_ALL=C sort -z |
    xargs -0 shasum | shasum | awk '{print $1}'
}
BASELINE_DIGEST=$(baseline_digest)
clone_production() { mkdir -p "$1"; cp -R "$TMP/production/registry" "$1/registry"; }
rewrite() { local file=$1 program=$2; awk -F '\t' -v OFS='\t' "$program" "$file" > "$file.tmp"; mv "$file.tmp" "$file"; }
append_row() { local file=$1 row=$2; { awk '{print}' "$file"; printf '%s\n' "$row"; } > "$file.tmp"; mv "$file.tmp" "$file"; }

make_legacy_base() {
  local target=$1
  clone_production "$target"
  rm -f "$target/registry/sources.tsv"
  mkdir -p "$target/references"
  printf '%s\n' \
    $'source_id\tlocal_ref_key\tedition\tpdf_oid\ttext_oid\tcoverage\tnotes' \
    $'TASAKI2020\tfixture.pdf\t2020.ed1\t1111111111111111111111111111111111111111\t2222222222222222222222222222222222222222\tpass1\tfixture' > "$target/references/tasaki-2020.tsv"
  printf '%s\n' $'phase' $'census' > "$target/registry/phase.tsv"
  printf '%s\n' \
    $'page_id\tsource_id\torder_key\tprinted_page\tpdf_page\tsection\tpage_kind\tpass1\tpass2\tsource_oid' \
    $'PG-TASAKI2020-0001\tTASAKI2020\t000001\tNONE\t1\t1\tcontent\tcomplete\tpending\tPENDING' > "$target/registry/pages.tsv"
  printf '%s\n' \
    $'claim_id\tsource_id\torder_key\tpage_id\tlocator\tdisposition\tsubkind\tnormalized_content\tcontent_oid\texclusion_rationale\texclusion_review_ref\ttombstone\tsuperseded_by\ttombstone_rationale\ttombstone_review_ref' \
    $'CL-TASAKI2020-0001\tTASAKI2020\t000001.0001\tPG-TASAKI2020-0001\tpage 1\tassertion\ttheorem\tFixture theorem.\tPENDING\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE' > "$target/registry/claims.tsv"
  printf '%s\n' $'slice_id\tposition\tclaim_id' $'SL-TASAKI2020-0001\t1\tCL-TASAKI2020-0001' > "$target/registry/slices.tsv"
  printf '%s\n' $'claim_id\trole\ttarget_claim_id\trationale' > "$target/registry/dependencies.tsv"
  printf '%s\n' $'claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_oid\tnonvacuity_decl' $'CL-TASAKI2020-0001\tclaim0001\tNONE\tLatticeSystem.Claims.C0001\t0000000000000000000000000000000000000000\tNONE' > "$target/registry/bindings.tsv"
  printf '%s\n' $'axiom_id\tdeclaration\tmodule\tcategory\tsource_locator\trationale\treopen_condition' $'AX-PROJECT-0001\tLatticeSystem.Axioms.AbstractCStar.interfaceAxiom\tLatticeSystem.Axioms.AbstractCStar\tabstract_cstar\tnot-applicable\tfixture-rationale\treopen-when-implemented' > "$target/registry/axioms.tsv"
  printf '%s\n' $'claim_id\taxiom_id' $'CL-TASAKI2020-0001\tAX-PROJECT-0001' > "$target/registry/claim-axioms.tsv"
  printf '%s\n' $'claim_id\tbasis\treview_ref' > "$target/registry/claim-vocabulary-review.tsv"
  printf '%s\n' $'vocabulary_id\tdeclaration\tmodule\tdeclaration_kind\torigin\tparent_vocabulary_id\ttype_oid\tdeclaration_oid\tdesign_role\tfiniteness_scope' > "$target/registry/vocabulary.tsv"
  printf '%s\n' $'claim_id\tvocabulary_id' > "$target/registry/claim-vocabulary.tsv"
  printf '%s\n' $'module\tsource_path\trole' > "$target/registry/modules.tsv"
  printf '%s\n' $'module\tposition\timported_module\tis_exported\tis_meta\timport_all' > "$target/registry/imports.tsv"
}
clone_case() { local from=$1 to=$2; mkdir -p "$(dirname "$to")"; cp -R "$from" "$to"; }

GOOD="$ROOT/fixtures/registry-good"
"$PROJECT_ROOT/scripts/check-registry.sh" "$TMP/production" >/dev/null
make_legacy_base "$GOOD"

THREE="$TMP/legacy-three"
clone_case "$GOOD" "$THREE"
printf '%s\n' \
  $'claim_id\tsource_id\torder_key\tpage_id\tlocator\tdisposition\tsubkind\tnormalized_content\tcontent_oid\texclusion_rationale\texclusion_review_ref\ttombstone\tsuperseded_by\ttombstone_rationale\ttombstone_review_ref' \
  $'CL-TASAKI2020-0001\tTASAKI2020\t000001.0001\tPG-TASAKI2020-0001\tpage-1-claim-1\tassertion\ttheorem\tFirst-fixture-claim.\t1111111111111111111111111111111111111111\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE' \
  $'CL-TASAKI2020-0002\tTASAKI2020\t000001.0002\tPG-TASAKI2020-0001\tpage-1-claim-2\tassertion\tlemma\tSecond-fixture-claim.\t2222222222222222222222222222222222222222\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE' \
  $'CL-TASAKI2020-0003\tTASAKI2020\t000001.0003\tPG-TASAKI2020-0001\tpage-1-claim-3\tassertion\tlemma\tThird-fixture-claim.\t3333333333333333333333333333333333333333\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE' > "$THREE/registry/claims.tsv"
printf '%s\n' $'slice_id\tposition\tclaim_id' \
  $'SL-TASAKI2020-0001\t1\tCL-TASAKI2020-0001' \
  $'SL-TASAKI2020-0001\t2\tCL-TASAKI2020-0002' \
  $'SL-TASAKI2020-0001\t3\tCL-TASAKI2020-0003' > "$THREE/registry/slices.tsv"

case_from() { clone_case "$1" "$ROOT/fixtures/$2"; }
case_from "$GOOD" registry-duplicate-id
append_row "$ROOT/fixtures/registry-duplicate-id/registry/claims.tsv" $'CL-TASAKI2020-0001\tTASAKI2020\t000001.0001\tPG-TASAKI2020-0001\tduplicate\tassertion\ttheorem\tDuplicate.\tPENDING\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE'
case_from "$GOOD" registry-bad-fk; rewrite "$ROOT/fixtures/registry-bad-fk/registry/claims.tsv" 'NR==2 {$4="PG-TASAKI2020-9999"} {print}'
case_from "$GOOD" registry-bad-enum; rewrite "$ROOT/fixtures/registry-bad-enum/registry/pages.tsv" 'NR==2 {$7="invalid"} {print}'
case_from "$GOOD" registry-bad-order; rewrite "$ROOT/fixtures/registry-bad-order/registry/pages.tsv" 'NR==2 {$3="bad"} {print}'
case_from "$GOOD" registry-bad-header; rewrite "$ROOT/fixtures/registry-bad-header/registry/pages.tsv" 'NR==1 {$0="wrong_header"} {print}'
case_from "$GOOD" registry-bad-column; rewrite "$ROOT/fixtures/registry-bad-column/registry/pages.tsv" 'NR==2 {NF=9} {print}'
case_from "$GOOD" registry-control-char; rewrite "$ROOT/fixtures/registry-control-char/registry/pages.tsv" 'NR==2 {$6="bad\vcontrol"} {print}'
case_from "$GOOD" registry-bad-id; rewrite "$ROOT/fixtures/registry-bad-id/registry/pages.tsv" 'NR==2 {$1="bad-page-id"} {print}'; rewrite "$ROOT/fixtures/registry-bad-id/registry/claims.tsv" 'NR==2 {$4="bad-page-id"} {print}'
case_from "$GOOD" registry-page-missing-coordinate; rewrite "$ROOT/fixtures/registry-page-missing-coordinate/registry/pages.tsv" 'NR==2 {$4=""} {print}'

case_from "$THREE" registry-slice-duplicate; append_row "$ROOT/fixtures/registry-slice-duplicate/registry/slices.tsv" $'SL-TASAKI2020-0002\t1\tCL-TASAKI2020-0001'
case_from "$THREE" registry-slice-position; rewrite "$ROOT/fixtures/registry-slice-position/registry/slices.tsv" 'NR==2 {$2=2} {print}'
case_from "$THREE" registry-dep-bad-role; append_row "$ROOT/fixtures/registry-dep-bad-role/registry/dependencies.tsv" $'CL-TASAKI2020-0002\tprerequisite\tCL-TASAKI2020-0001\tNONE'
case_from "$THREE" registry-dep-order; append_row "$ROOT/fixtures/registry-dep-order/registry/dependencies.tsv" $'CL-TASAKI2020-0001\trequires\tCL-TASAKI2020-0002\tNONE'
case_from "$THREE" registry-dep-cycle; append_row "$ROOT/fixtures/registry-dep-cycle/registry/dependencies.tsv" $'CL-TASAKI2020-0002\trequired_by\tCL-TASAKI2020-0001\tfrontier-exception'; append_row "$ROOT/fixtures/registry-dep-cycle/registry/dependencies.tsv" $'CL-TASAKI2020-0003\trequired_by\tCL-TASAKI2020-0002\tfrontier-exception'; append_row "$ROOT/fixtures/registry-dep-cycle/registry/dependencies.tsv" $'CL-TASAKI2020-0003\trequires\tCL-TASAKI2020-0001\tNONE'
case_from "$THREE" registry-dep-self; append_row "$ROOT/fixtures/registry-dep-self/registry/dependencies.tsv" $'CL-TASAKI2020-0002\trequires\tCL-TASAKI2020-0002\tNONE'
case_from "$THREE" registry-dep-duplicate; append_row "$ROOT/fixtures/registry-dep-duplicate/registry/dependencies.tsv" $'CL-TASAKI2020-0002\trequires\tCL-TASAKI2020-0001\tNONE'; append_row "$ROOT/fixtures/registry-dep-duplicate/registry/dependencies.tsv" $'CL-TASAKI2020-0002\trequires\tCL-TASAKI2020-0001\tNONE'
case_from "$THREE" registry-dep-rationale; append_row "$ROOT/fixtures/registry-dep-rationale/registry/dependencies.tsv" $'CL-TASAKI2020-0002\trequired_by\tCL-TASAKI2020-0001\tNONE'
case_from "$THREE" registry-dep-whitespace; append_row "$ROOT/fixtures/registry-dep-whitespace/registry/dependencies.tsv" $'CL-TASAKI2020-0002\trequired_by\tCL-TASAKI2020-0001\t bad'
case_from "$THREE" registry-dep-whitespace-em; append_row "$ROOT/fixtures/registry-dep-whitespace-em/registry/dependencies.tsv" $'CL-TASAKI2020-0002\trequired_by\tCL-TASAKI2020-0001\t bad'
case_from "$THREE" registry-fk-slice; rewrite "$ROOT/fixtures/registry-fk-slice/registry/slices.tsv" 'NR==4 {$3="CL-TASAKI2020-9999"} {print}'
case_from "$THREE" registry-fk-dependency; append_row "$ROOT/fixtures/registry-fk-dependency/registry/dependencies.tsv" $'CL-TASAKI2020-0002\trequires\tCL-TASAKI2020-9999\tNONE'
case_from "$GOOD" registry-fk-binding; rewrite "$ROOT/fixtures/registry-fk-binding/registry/bindings.tsv" 'NR==2 {$1="CL-TASAKI2020-9999"} {print}'
case_from "$GOOD" registry-fk-claim-axiom-claim; rewrite "$ROOT/fixtures/registry-fk-claim-axiom-claim/registry/claim-axioms.tsv" 'NR==2 {$1="CL-TASAKI2020-9999"} {print}'
case_from "$GOOD" registry-fk-claim-axiom-axiom; rewrite "$ROOT/fixtures/registry-fk-claim-axiom-axiom/registry/claim-axioms.tsv" 'NR==2 {$2="AX-PROJECT-9999"} {print}'

SUPER="$TMP/legacy-super"
clone_case "$THREE" "$SUPER"
rewrite "$SUPER/registry/claims.tsv" 'NR==2 {$12="true";$13="CL-TASAKI2020-0002";$14="replacement-reason";$15="review-1"} NR!=4 {print}'
rewrite "$SUPER/registry/slices.tsv" 'NR==1 {print} NR==3 {$2=1; print}'
rewrite "$SUPER/registry/bindings.tsv" 'NR==1 {print}'
rewrite "$SUPER/registry/claim-axioms.tsv" 'NR==1 {print}'
case_from "$SUPER" registry-supersession-good
case_from "$GOOD" registry-supersession-self; rewrite "$ROOT/fixtures/registry-supersession-self/registry/claims.tsv" 'NR==2 {$12="true";$13=$1;$14="bad-self";$15="review-1"} {print}'
case_from "$THREE" registry-supersession-cycle; rewrite "$ROOT/fixtures/registry-supersession-cycle/registry/claims.tsv" 'NR==2 {$12="true";$13="CL-TASAKI2020-0002";$14="cycle-one";$15="review-1"} NR==3 {$12="true";$13="CL-TASAKI2020-0001";$14="cycle-two";$15="review-2"} NR<4 {print}'
case_from "$THREE" registry-supersession-incoherent; rewrite "$ROOT/fixtures/registry-supersession-incoherent/registry/claims.tsv" 'NR==2 {$13="CL-TASAKI2020-0002"} {print}'
case_from "$SUPER" registry-supersession-missing-rationale; rewrite "$ROOT/fixtures/registry-supersession-missing-rationale/registry/claims.tsv" 'NR==2 {$14="NONE"} {print}'
case_from "$SUPER" registry-supersession-missing-review; rewrite "$ROOT/fixtures/registry-supersession-missing-review/registry/claims.tsv" 'NR==2 {$15="NONE"} {print}'

case_from "$GOOD" registry-exclusion-good; rewrite "$ROOT/fixtures/registry-exclusion-good/registry/claims.tsv" 'NR==2 {$6="out_of_scope";$10="scope-reason";$11="review-1"} {print}'
case_from "$ROOT/fixtures/registry-exclusion-good" registry-exclusion-missing-rationale; rewrite "$ROOT/fixtures/registry-exclusion-missing-rationale/registry/claims.tsv" 'NR==2 {$10="NONE"} {print}'
case_from "$ROOT/fixtures/registry-exclusion-good" registry-exclusion-missing-review; rewrite "$ROOT/fixtures/registry-exclusion-missing-review/registry/claims.tsv" 'NR==2 {$11="NONE"} {print}'
case_from "$GOOD" registry-exclusion-incoherent; rewrite "$ROOT/fixtures/registry-exclusion-incoherent/registry/claims.tsv" 'NR==2 {$10="scope-reason";$11="review-1"} {print}'
case_from "$GOOD" registry-remark-good; rewrite "$ROOT/fixtures/registry-remark-good/registry/claims.tsv" 'NR==2 {$7="remark"} {print}'
case_from "$GOOD" registry-bad-subkind; rewrite "$ROOT/fixtures/registry-bad-subkind/registry/claims.tsv" 'NR==2 {$7="editorial"} {print}'
case_from "$GOOD" registry-axiom-bad-category; rewrite "$ROOT/fixtures/registry-axiom-bad-category/registry/axioms.tsv" 'NR==2 {$4="analytic-limit"} {print}'
case_from "$GOOD" registry-axiom-bad-path; rewrite "$ROOT/fixtures/registry-axiom-bad-path/registry/axioms.tsv" 'NR==2 {$2="LatticeSystem.Axioms.State.bad";$3="LatticeSystem.Axioms.State"} {print}'
case_from "$GOOD" registry-axiom-categories-good
axiom_number=2
for spec in 'State state' 'GNS gns' 'KMS kms' 'WeakDual weak_dual' 'Wigner wigner' 'ContentlessPredicate contentless_predicate'; do
  set -- $spec
  printf -v axiom_row 'AX-PROJECT-%04d\tLatticeSystem.Axioms.%s.fixture\tLatticeSystem.Axioms.%s\t%s\tnot-applicable\trationale\treopen' "$axiom_number" "$1" "$1" "$2"
  append_row "$ROOT/fixtures/registry-axiom-categories-good/registry/axioms.tsv" "$axiom_row"
  axiom_number=$((axiom_number + 1))
done

case_from "$GOOD" registry-source-missing; rewrite "$ROOT/fixtures/registry-source-missing/references/tasaki-2020.tsv" 'NR==1 {print}'
case_from "$GOOD" registry-source-duplicate; append_row "$ROOT/fixtures/registry-source-duplicate/references/tasaki-2020.tsv" $'TASAKI2020\tfixture.pdf\t2020.ed1\t1111111111111111111111111111111111111111\t2222222222222222222222222222222222222222\tpass1\tfixture'
case_from "$GOOD" registry-source-bad-identity; rewrite "$ROOT/fixtures/registry-source-bad-identity/references/tasaki-2020.tsv" 'NR==2 {$1="OTHER"} {print}'
case_from "$GOOD" registry-post-source-missing; rewrite "$ROOT/fixtures/registry-post-source-missing/references/tasaki-2020.tsv" 'NR==1 {print}'
case_from "$GOOD" registry-post-source-alternate; rewrite "$ROOT/fixtures/registry-post-source-alternate/references/tasaki-2020.tsv" 'NR==2 {$1="OTHER"} {print}'
case_from "$GOOD" registry-bootstrap-edition-pending; printf '%s\n' phase bootstrap > "$ROOT/fixtures/registry-bootstrap-edition-pending/registry/phase.tsv"; rewrite "$ROOT/fixtures/registry-bootstrap-edition-pending/references/tasaki-2020.tsv" 'NR==2 {$3="pending";$4="";$5="";$6="pending"} {print}'
case_from "$GOOD" registry-bootstrap-source-frozen; printf '%s\n' phase bootstrap > "$ROOT/fixtures/registry-bootstrap-source-frozen/registry/phase.tsv"; for f in pages claims slices bindings axioms claim-axioms; do rewrite "$ROOT/fixtures/registry-bootstrap-source-frozen/registry/$f.tsv" 'NR==1 {print}'; done; rewrite "$ROOT/fixtures/registry-bootstrap-source-frozen/references/tasaki-2020.tsv" 'NR==2 {$6="pending"} {print}'
case_from "$GOOD" registry-post-edition-pending; rewrite "$ROOT/fixtures/registry-post-edition-pending/references/tasaki-2020.tsv" 'NR==2 {$3="pending"} {print}'
case_from "$GOOD" registry-source-mixed-width; rewrite "$ROOT/fixtures/registry-source-mixed-width/references/tasaki-2020.tsv" 'NR==2 {$5="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"} {print}'

CENSUS="$ROOT/fixtures/registry-census-good"
make_legacy_base "$CENSUS"
rewrite "$CENSUS/references/tasaki-2020.tsv" 'NR==2 {$3="2020.ed1";$4="3333333333333333333333333333333333333333";$5="4444444444444444444444444444444444444444";$6="frozen"} {print}'
printf '%s\n' \
  $'page_id\tsource_id\torder_key\tprinted_page\tpdf_page\tsection\tpage_kind\tpass1\tpass2\tsource_oid' \
  $'PG-TASAKI2020-0001\tTASAKI2020\t000001\tNONE\t1\tNONE\tcontent\tcomplete\tcomplete\t4444444444444444444444444444444444444444' \
  $'PG-TASAKI2020-0002\tTASAKI2020\t000002\t1\t2\t1.1\tcontent\tcomplete\tcomplete\t4444444444444444444444444444444444444444' > "$CENSUS/registry/pages.tsv"
printf '%s\n' \
  $'claim_id\tsource_id\torder_key\tpage_id\tlocator\tdisposition\tsubkind\tnormalized_content\tcontent_oid\texclusion_rationale\texclusion_review_ref\ttombstone\tsuperseded_by\ttombstone_rationale\ttombstone_review_ref' \
  $'CL-TASAKI2020-0001\tTASAKI2020\t000001.0001\tPG-TASAKI2020-0001\tPDF p. 1; print p. NONE; NONE; equation (F.1)\tassertion\tequation\tFixture-equation.\tPENDING\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE' \
  $'CL-TASAKI2020-0002\tTASAKI2020\t000002.0001\tPG-TASAKI2020-0002\tPDF-p.2-section-1.1\tassertion\tunnumbered_obligation\tFixture-prose-claim.\tPENDING\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE' > "$CENSUS/registry/claims.tsv"
for f in slices dependencies bindings axioms claim-axioms; do rewrite "$CENSUS/registry/$f.tsv" 'NR==1 {print}'; done

case_from "$CENSUS" registry-census-source-identity; rewrite "$ROOT/fixtures/registry-census-source-identity/references/tasaki-2020.tsv" 'NR==2 {$4="bad"} {print}'
case_from "$CENSUS" registry-census-source-bad-header; rewrite "$ROOT/fixtures/registry-census-source-bad-header/references/tasaki-2020.tsv" 'NR==1 {$0="bad"} {print}'
case_from "$CENSUS" registry-census-source-header-only; rewrite "$ROOT/fixtures/registry-census-source-header-only/references/tasaki-2020.tsv" 'NR==1 {print}'
case_from "$CENSUS" registry-census-source-extra-row; append_row "$ROOT/fixtures/registry-census-source-extra-row/references/tasaki-2020.tsv" $'OTHER\tfixture2.pdf\t2020.ed1\t5555555555555555555555555555555555555555\t6666666666666666666666666666666666666666\tfrozen\tfixture'
case_from "$CENSUS" registry-census-source-malformed-column; rewrite "$ROOT/fixtures/registry-census-source-malformed-column/references/tasaki-2020.tsv" 'NR==2 {NF=6} {print}'
case_from "$CENSUS" registry-census-source-reserved-edition; rewrite "$ROOT/fixtures/registry-census-source-reserved-edition/references/tasaki-2020.tsv" 'NR==2 {$3="pending"} {print}'
case_from "$CENSUS" registry-census-claim-count; append_row "$ROOT/fixtures/registry-census-claim-count/registry/claims.tsv" $'CL-TASAKI2020-0003\tTASAKI2020\t000002.0002\tPG-TASAKI2020-0002\textra\tassertion\tunnumbered_obligation\tExtra.\tPENDING\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE'
case_from "$ROOT/fixtures/registry-census-claim-count" registry-census-claim-inactive; rewrite "$ROOT/fixtures/registry-census-claim-inactive/registry/claims.tsv" 'NR==2 {$12="true";$13="CL-TASAKI2020-0003";$14="duplicate";$15="review-1"} {print}'
case_from "$CENSUS" registry-census-claim-superseded; rewrite "$ROOT/fixtures/registry-census-claim-superseded/registry/claims.tsv" 'NR==2 {$13="CL-TASAKI2020-0002"} {print}'
case_from "$CENSUS" registry-census-equation-duplicate; append_row "$ROOT/fixtures/registry-census-equation-duplicate/registry/claims.tsv" $'CL-TASAKI2020-0003\tTASAKI2020\t000001.0002\tPG-TASAKI2020-0001\tPDF p. 1; print p. NONE; NONE; equation (F.1)\tassertion\tequation\tDuplicate.\tPENDING\tNONE\tNONE\tfalse\tNONE\tNONE\tNONE'; rewrite "$ROOT/fixtures/registry-census-equation-duplicate/registry/claims.tsv" 'NR<=2 {print} NR==3 {later=$0} NR==4 {print; print later}'
case_from "$CENSUS" registry-census-claims-empty; rewrite "$ROOT/fixtures/registry-census-claims-empty/registry/claims.tsv" 'NR==1 {print}'
for pair in slices:SL-TASAKI2020-0001$'\t'1$'\t'CL-TASAKI2020-0001 dependencies:CL-TASAKI2020-0002$'\t'required_by$'\t'CL-TASAKI2020-0001$'\t'fixture bindings:CL-TASAKI2020-0001$'\t'Fixture.statement$'\t'Fixture.proof$'\t'Fixture$'\t'PENDING$'\t'Fixture.nonvacuity axioms:AX-PROJECT-0002$'\t'LatticeSystem.Axioms.State.fixture$'\t'LatticeSystem.Axioms.State$'\t'state$'\t'not-applicable$'\t'rationale$'\t'reopen; do
  table=${pair%%:*}; row=${pair#*:}; name=registry-census-skeleton-$table; case_from "$CENSUS" "$name"; append_row "$ROOT/fixtures/$name/registry/$table.tsv" "$row"
done
append_row "$ROOT/fixtures/registry-census-skeleton-slices/registry/slices.tsv" $'SL-TASAKI2020-0001\t2\tCL-TASAKI2020-0002'
case_from "$ROOT/fixtures/registry-census-skeleton-axioms" registry-census-skeleton-claim-axioms; append_row "$ROOT/fixtures/registry-census-skeleton-claim-axioms/registry/claim-axioms.tsv" $'CL-TASAKI2020-0001\tAX-PROJECT-0002'
case_from "$CENSUS" registry-census-skeleton-claim-axioms-diagnostic; append_row "$ROOT/fixtures/registry-census-skeleton-claim-axioms-diagnostic/registry/claim-axioms.tsv" $'CL-TASAKI2020-0001\tAX-TASAKI2020-0001'

case_from "$CENSUS" registry-census-page-id; rewrite "$ROOT/fixtures/registry-census-page-id/registry/pages.tsv" 'NR==3 {$1="PG-TASAKI2020-0003"} {print}'; rewrite "$ROOT/fixtures/registry-census-page-id/registry/claims.tsv" 'NR==3 {$4="PG-TASAKI2020-0003"} {print}'
case_from "$CENSUS" registry-census-page-source; rewrite "$ROOT/fixtures/registry-census-page-source/registry/pages.tsv" 'NR==3 {$2="OTHER"} {print}'
case_from "$CENSUS" registry-census-page-order; rewrite "$ROOT/fixtures/registry-census-page-order/registry/pages.tsv" 'NR==3 {$3="000003"} {print}'; rewrite "$ROOT/fixtures/registry-census-page-order/registry/claims.tsv" 'NR==3 {$3="000003.0001"} {print}'
case_from "$CENSUS" registry-census-page-pdf; rewrite "$ROOT/fixtures/registry-census-page-pdf/registry/pages.tsv" 'NR==3 {$5=3} {print}'
case_from "$CENSUS" registry-census-page-printed; rewrite "$ROOT/fixtures/registry-census-page-printed/registry/pages.tsv" 'NR==3 {$4=""} {print}'
case_from "$CENSUS" registry-census-page-section; rewrite "$ROOT/fixtures/registry-census-page-section/registry/pages.tsv" 'NR==3 {$6=""} {print}'
case_from "$CENSUS" registry-census-page-kind; rewrite "$ROOT/fixtures/registry-census-page-kind/registry/pages.tsv" 'NR==3 {$7=""} {print}'
case_from "$CENSUS" registry-census-page-pass1; rewrite "$ROOT/fixtures/registry-census-page-pass1/registry/pages.tsv" 'NR==3 {$8="pending"} {print}'
case_from "$CENSUS" registry-census-page-pass2; rewrite "$ROOT/fixtures/registry-census-page-pass2/registry/pages.tsv" 'NR==3 {$9="pending"} {print}'
case_from "$CENSUS" registry-census-page-oid; rewrite "$ROOT/fixtures/registry-census-page-oid/registry/pages.tsv" 'NR==3 {$10="PENDING"} {print}'
case_from "$CENSUS" registry-census-claim-source; rewrite "$ROOT/fixtures/registry-census-claim-source/registry/claims.tsv" 'NR==3 {$2="OTHER"} {print}'
case_from "$CENSUS" registry-census-claim-locator; rewrite "$ROOT/fixtures/registry-census-claim-locator/registry/claims.tsv" 'NR==3 {$5=""} {print}'
case_from "$CENSUS" registry-census-claim-content; rewrite "$ROOT/fixtures/registry-census-claim-content/registry/claims.tsv" 'NR==3 {$8=""} {print}'
case_from "$CENSUS" registry-census-claim-page-order; rewrite "$ROOT/fixtures/registry-census-claim-page-order/registry/claims.tsv" 'NR==2 {$4="PG-TASAKI2020-0002"} {print}'
case_from "$CENSUS" registry-census-claim-source-order; rewrite "$ROOT/fixtures/registry-census-claim-source-order/registry/claims.tsv" 'NR==1 {h=$0; next} NR==2 {a=$0; next} NR==3 {print h; print; print a}'
case_from "$CENSUS" registry-census-equation-label; rewrite "$ROOT/fixtures/registry-census-equation-label/registry/claims.tsv" 'NR==2 {$5="PDF-p.1-equation-F.1"} {print}'

expect_pass() {
  local label=$1 output; shift
  if ! output=$("$@" 2>&1); then
    echo "test-checkers: expected pass: $label" >&2
    echo "$output" >&2
    exit 1
  fi
}

expect_fail() {
  local label=$1; shift
  local diagnostic= output
  if [[ ${1:-} == --diagnostic ]]; then
    [[ $# -ge 3 ]] || { echo "test-checkers: missing diagnostic or command: $label" >&2; exit 1; }
    diagnostic=$2
    shift 2
  fi
  if output=$("$@" 2>&1); then
    echo "test-checkers: expected failure: $label" >&2
    exit 1
  fi
  if [[ -n "$diagnostic" && "$output" != *"$diagnostic"* ]]; then
    echo "test-checkers: wrong failure diagnostic: $label" >&2
    echo "$output" >&2
    exit 1
  fi
}

expect_pass registry-good "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-good"
expect_fail duplicate-id "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-duplicate-id"
expect_fail bad-foreign-key "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-bad-fk"
expect_fail bad-enum "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-bad-enum"
expect_fail bad-order "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-bad-order"
expect_fail bad-header "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-bad-header"
expect_fail bad-column "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-bad-column"
expect_fail control-character "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-control-char"
expect_fail bad-id "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-bad-id"
expect_fail missing-page-coordinate "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-page-missing-coordinate"
expect_fail slice-duplicate "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-slice-duplicate"
expect_fail slice-position "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-slice-position"
expect_fail dependency-role "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-dep-bad-role"
expect_fail dependency-order "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-dep-order"
expect_fail dependency-cycle "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-dep-cycle"
expect_fail dependency-self "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-dep-self"
expect_fail dependency-duplicate "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-dep-duplicate"
expect_fail dependency-rationale "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-dep-rationale"
expect_fail fk-slice "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-fk-slice"
expect_fail fk-dependency "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-fk-dependency"
expect_fail fk-binding "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-fk-binding"
expect_fail fk-claim-axiom-claim "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-fk-claim-axiom-claim"
expect_fail fk-claim-axiom-axiom "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-fk-claim-axiom-axiom"
expect_pass supersession-registry-good "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-supersession-good"
expect_fail supersession-self "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-supersession-self"
expect_fail supersession-cycle "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-supersession-cycle"
expect_fail supersession-incoherent "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-supersession-incoherent"
expect_fail supersession-missing-rationale "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-supersession-missing-rationale"
expect_fail supersession-missing-review "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-supersession-missing-review"
expect_pass exclusion-good "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-exclusion-good"
expect_fail exclusion-missing-rationale "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-exclusion-missing-rationale"
expect_fail exclusion-missing-review "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-exclusion-missing-review"
expect_fail exclusion-incoherent "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-exclusion-incoherent"
expect_fail required-by-whitespace "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-dep-whitespace"
expect_fail required-by-em-whitespace "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-dep-whitespace-em"
expect_pass remark-good "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-remark-good"
expect_fail bad-subkind "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-bad-subkind"
expect_fail axiom-bad-category "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-axiom-bad-category"
expect_fail axiom-bad-path "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-axiom-bad-path"
expect_pass axiom-categories-good "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-axiom-categories-good"
expect_fail source-missing "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-source-missing"
expect_fail source-duplicate "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-source-duplicate"
expect_fail source-bad-identity "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-source-bad-identity"
expect_fail post-source-missing "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-post-source-missing"
expect_fail post-source-alternate "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-post-source-alternate"
expect_fail bootstrap-pending-edition "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-bootstrap-edition-pending"
expect_pass bootstrap-source-frozen "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-bootstrap-source-frozen"
expect_fail post-pending-edition "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-post-edition-pending"
expect_fail source-mixed-oid-width "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-source-mixed-width"
"$PROJECT_ROOT/scripts/test-tree-policy.sh" "$PROJECT_ROOT"
census_source_diagnostic="check-census: fixture source is not verified and frozen"
census_page_diagnostic="check-census: page census is not exact, contiguous, two-pass complete, and source-frozen"
census_claim_diagnostic="check-census: claim count, active state, source order, page coupling, or equation label/page pairs are not exact"

expect_pass census-complete-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-good"
expect_pass census-complete "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-good" 2 2 1
expect_fail census-page-count --diagnostic "$census_page_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-good" 3 2 1
expect_fail census-equation-count --diagnostic "$census_claim_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-good" 2 2 2
expect_fail census-source-identity --diagnostic "$census_source_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-source-identity" 2 2 1
expect_fail census-source-bad-header --diagnostic "$census_source_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-source-bad-header" 2 2 1
expect_fail census-source-header-only --diagnostic "$census_source_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-source-header-only" 2 2 1
expect_fail census-source-extra-row --diagnostic "$census_source_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-source-extra-row" 2 2 1
expect_fail census-source-malformed-column --diagnostic "$census_source_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-source-malformed-column" 2 2 1
expect_fail census-source-reserved-edition --diagnostic "$census_source_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-source-reserved-edition" 2 2 1
expect_pass census-claim-count-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-claim-count"
expect_fail census-claim-count --diagnostic "$census_claim_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-claim-count" 2 2 1
expect_pass census-claim-inactive-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-claim-inactive"
expect_fail census-claim-inactive --diagnostic "$census_claim_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-claim-inactive" 2 3 1
expect_fail census-claim-superseded --diagnostic "$census_claim_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-claim-superseded" 2 2 1
expect_pass census-equation-duplicate-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-equation-duplicate"
expect_fail census-equation-duplicate --diagnostic "$census_claim_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-equation-duplicate" 2 3 2
expect_pass census-claims-empty-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-claims-empty"
expect_fail census-claims-empty --diagnostic "$census_claim_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-claims-empty" 2 0 0
expect_pass census-skeleton-slices-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-skeleton-slices"
expect_fail census-skeleton-slices --diagnostic "check-census: census requires header-only slices.tsv" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-skeleton-slices" 2 2 1
expect_pass census-skeleton-dependencies-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-skeleton-dependencies"
expect_fail census-skeleton-dependencies --diagnostic "check-census: census requires header-only dependencies.tsv" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-skeleton-dependencies" 2 2 1
expect_pass census-skeleton-bindings-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-skeleton-bindings"
expect_fail census-skeleton-bindings --diagnostic "check-census: census requires header-only bindings.tsv" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-skeleton-bindings" 2 2 1
expect_pass census-skeleton-axioms-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-skeleton-axioms"
expect_fail census-skeleton-axioms --diagnostic "check-census: census requires header-only axioms.tsv" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-skeleton-axioms" 2 2 1
# A schema-valid claim-axiom relation necessarily carries its referenced axiom,
# so the census gate reports the earlier axioms table first. The paired
# diagnostic-only fixture omits that axiom solely to exercise the later
# claim-axioms diagnostic; it cannot pass registry FK validation by design.
expect_pass census-skeleton-claim-axioms-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-skeleton-claim-axioms"
expect_fail census-skeleton-claim-axioms-coupled --diagnostic "check-census: census requires header-only axioms.tsv" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-skeleton-claim-axioms" 2 2 1
expect_fail census-skeleton-claim-axioms-diagnostic --diagnostic "check-census: census requires header-only claim-axioms.tsv" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-skeleton-claim-axioms-diagnostic" 2 2 1
expect_pass census-page-id-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-page-id"
expect_fail census-page-id --diagnostic "$census_page_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-page-id" 2 2 1
expect_fail census-page-source --diagnostic "$census_page_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-page-source" 2 2 1
expect_pass census-page-order-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-page-order"
expect_fail census-page-order --diagnostic "$census_page_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-page-order" 2 2 1
expect_pass census-page-pdf-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-page-pdf"
expect_fail census-page-pdf --diagnostic "$census_page_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-page-pdf" 2 2 1
expect_fail census-page-printed --diagnostic "$census_page_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-page-printed" 2 2 1
expect_fail census-page-section --diagnostic "$census_page_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-page-section" 2 2 1
expect_fail census-page-kind --diagnostic "$census_page_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-page-kind" 2 2 1
expect_pass census-page-pass1-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-page-pass1"
expect_fail census-page-pass1 --diagnostic "$census_page_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-page-pass1" 2 2 1
expect_pass census-page-pass2-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-page-pass2"
expect_fail census-page-pass2 --diagnostic "$census_page_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-page-pass2" 2 2 1
expect_fail census-page-oid --diagnostic "$census_page_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-page-oid" 2 2 1
expect_fail census-claim-source --diagnostic "$census_claim_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-claim-source" 2 2 1
expect_fail census-claim-locator --diagnostic "$census_claim_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-claim-locator" 2 2 1
expect_fail census-claim-content --diagnostic "$census_claim_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-claim-content" 2 2 1
expect_pass census-claim-page-order-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-claim-page-order"
expect_fail census-claim-page-order --diagnostic "$census_claim_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-claim-page-order" 2 2 1
expect_fail census-claim-source-order --diagnostic "$census_claim_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-claim-source-order" 2 2 1
expect_pass census-equation-label-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/registry-census-equation-label"
expect_fail census-equation-label --diagnostic "$census_claim_diagnostic" "$ROOT/scripts/check-census.sh" --fixture "$ROOT/fixtures/registry-census-equation-label" 2 2 1
"$PROJECT_ROOT/scripts/test-vocabulary-registry.sh" "$PROJECT_ROOT"
"$PROJECT_ROOT/scripts/test-vocabulary-semantic.sh" "$PROJECT_ROOT"
"$PROJECT_ROOT/scripts/test-base-diff-runtime.sh" "$PROJECT_ROOT"
"$PROJECT_ROOT/scripts/test-multisource.sh" "$PROJECT_ROOT"

[[ $(baseline_digest) == "$BASELINE_DIGEST" ]] || { echo "test-checkers: production baseline was mutated" >&2; exit 1; }
echo "test-checkers: ok"
