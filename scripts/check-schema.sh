#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
REG="$ROOT/registry"
fail() { echo "check-schema: $*" >&2; exit 1; }

check_table() {
  local file=$1 header=$2 columns=$3
  [[ -f "$file" ]] || fail "missing ${file#"$ROOT/"}"
  IFS= read -r actual < "$file" || fail "empty ${file#"$ROOT/"}"
  [[ "$actual" == "$header" ]] || fail "bad header in ${file#"$ROOT/"}"
  LC_ALL=C awk -F '\t' -v n="$columns" '
    NF != n { print FILENAME ":" FNR ": expected " n " columns, got " NF > "/dev/stderr"; bad=1 }
    {
      for (i=1; i<=NF; i++) {
        if ($i ~ /[[:cntrl:]]/) { print FILENAME ":" FNR ": control character in field" > "/dev/stderr"; bad=1 }
        trimmed=$i; gsub(/^( | )+|( | )+$/, "", trimmed)
        if (trimmed != $i) { print FILENAME ":" FNR ": surrounding whitespace in field" > "/dev/stderr"; bad=1 }
      }
    }
    END { exit bad }
  ' "$file" || exit 1
}

check_table "$REG/phase.tsv" 'phase' 1
check_table "$REG/tracks.tsv" $'track_id\tposition\ttitle\tpublic_slug' 4
check_table "$REG/sources.tsv" $'source_id\ttrack_id\tsource_position\tsource_kind\tcitation_key\ttitle\tauthors\tyear\tedition\tidentifier_kind\tidentifier\tpublic_url\tpublic_slug\tlocal_ref_key\tpdf_oid\ttext_oid\tcoverage' 17
check_table "$REG/source-invariants.tsv" $'source_id\tphysical_page_count\tactive_claim_count\tformalization_target_count\tequation_pair_count\tno_claim_page_count\tcensus_oid\treview_ref' 8
check_table "$REG/source-progress.tsv" $'source_id\tlifecycle\treview_ref' 3
check_table "$REG/pages.tsv" $'page_id\tsource_id\torder_key\tprinted_page\tpdf_page\tsection\tpage_kind\tpass1\tpass2\tsource_oid' 10
check_table "$REG/claims.tsv" $'claim_id\tsource_id\torder_key\tpage_id\tlocator\tdisposition\tsubkind\tnormalized_content\tcontent_oid\texclusion_rationale\texclusion_review_ref\ttombstone\tsuperseded_by\ttombstone_rationale\ttombstone_review_ref' 15
check_table "$REG/source-items.tsv" $'item_id\tsource_id\torder_key\tpage_id\titem_kind\tsource_label\ttitle\tlocator\tpublic_group\tpublic_slug\treview_ref' 11
check_table "$REG/item-claims.tsv" $'item_id\tposition\tclaim_id' 3
check_table "$REG/slices.tsv" $'slice_id\tposition\tclaim_id' 3
check_table "$REG/dependencies.tsv" $'claim_id\trole\ttarget_claim_id\trationale' 4
check_table "$REG/bindings.tsv" $'claim_id\tstatement_decl\tproof_decl\tmodule\tstatement_oid\tnonvacuity_decl' 6
check_table "$REG/axioms.tsv" $'axiom_id\tdeclaration\tmodule\tcategory\tsource_locator\trationale\treopen_condition' 7
check_table "$REG/claim-axioms.tsv" $'claim_id\taxiom_id' 2
check_table "$REG/claim-vocabulary-review.tsv" $'claim_id\tbasis\treview_ref' 3
check_table "$REG/vocabulary.tsv" $'vocabulary_id\tdeclaration\tmodule\tdeclaration_kind\torigin\tparent_vocabulary_id\ttype_oid\tdeclaration_oid\tdesign_role\tfiniteness_scope' 10
check_table "$REG/claim-vocabulary.tsv" $'claim_id\tvocabulary_id' 2
check_table "$REG/modules.tsv" $'module\tsource_path\trole' 3
check_table "$REG/imports.tsv" $'module\tposition\timported_module\tis_exported\tis_meta\timport_all' 6
check_table "$REG/correction-events.tsv" $'event_id\tevent_position\tsource_id\tbase_commit\treview_ref' 5
check_table "$REG/claim-normalization-reviews.tsv" $'review_id\tevent_id\treview_position\tclaim_id\treview_scope\toutcome\tstatus\trationale\treview_ref' 9
check_table "$REG/claim-corrections.tsv" $'correction_id\tevent_id\tcorrection_position\treview_id\tclaim_id\taction\told_disposition\told_subkind\tnew_disposition\tnew_subkind' 10
check_table "$REG/claim-successors.tsv" $'successor_edge_id\tevent_id\tcorrection_id\tpredecessor_claim_id\tsuccessor_position\trelation\tsuccessor_claim_id' 7

[[ $(awk 'END { print NR }' "$REG/phase.tsv") -eq 2 ]] || fail "phase.tsv must have exactly one data row"
{ IFS= read -r _; IFS= read -r phase; } < "$REG/phase.tsv"
case "$phase" in bootstrap|census|vocabulary|skeleton|proof) ;; *) fail "bad checker capability: $phase" ;; esac

echo "check-schema: ok"
