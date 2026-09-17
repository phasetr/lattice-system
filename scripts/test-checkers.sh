#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}

expect_pass() {
  local label=$1; shift
  if ! "$@" >/dev/null 2>&1; then
    echo "test-checkers: expected pass: $label" >&2
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
expect_fail fake-tracked-files-bypass "$ROOT/scripts/check-tree.sh" "$ROOT/fixtures/tree-fake-bypass"
expect_fail unexpected-path "$ROOT/scripts/check-tree.sh" --fixture "$ROOT/fixtures/tree-unexpected"
expect_fail unlisted-fixture "$ROOT/scripts/check-tree.sh" --fixture "$ROOT/fixtures/tree-unlisted"
expect_fail forbidden-token "$ROOT/scripts/check-policy.sh" "$ROOT/fixtures/policy-forbidden"
expect_fail root-check "$ROOT/scripts/check-policy.sh" "$ROOT/fixtures/policy-root-check"
expect_pass comment-theorem-allowed "$ROOT/scripts/check-policy.sh" "$ROOT/fixtures/policy-comment-allowed"
expect_fail merge-gate-missing "$ROOT/scripts/check-policy.sh" "$ROOT/fixtures/policy-merge-missing"
expect_fail merge-gate-checked "$ROOT/scripts/check-policy.sh" "$ROOT/fixtures/policy-merge-checked"
expect_pass census-phase "$ROOT/scripts/check-policy.sh" "$ROOT/fixtures/policy-phase-advance"
expect_fail future-phase "$ROOT/scripts/check-policy.sh" "$ROOT/fixtures/policy-future-phase"
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
expect_pass base-snapshot-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/base-diff/base"
expect_pass good-snapshot-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/base-diff/good"
expect_pass supersession-snapshot-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/base-diff/supersession-good"
expect_pass claim-oid-base-snapshot-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/base-diff/claim-oid-base"
expect_pass claim-oid-good-snapshot-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/base-diff/claim-oid-good"
expect_pass lifecycle-base-snapshot-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/base-diff/lifecycle-base"
expect_pass lifecycle-good-snapshot-registry "$ROOT/scripts/check-registry.sh" "$ROOT/fixtures/base-diff/lifecycle-good"
expect_pass base-good "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/base" "$ROOT/fixtures/base-diff/good"
expect_fail base-deletion "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/base" "$ROOT/fixtures/base-diff/deletion"
expect_fail base-drift "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/base" "$ROOT/fixtures/base-diff/drift"
expect_fail base-regression "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/base" "$ROOT/fixtures/base-diff/regression"
expect_fail supersession-default-reject "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/base" "$ROOT/fixtures/base-diff/supersession-good"
expect_pass supersession-dedicated-accept "$ROOT/scripts/check-base-diff.sh" --allow-supersession --fixture-dirs "$ROOT/fixtures/base-diff/base" "$ROOT/fixtures/base-diff/supersession-good"
expect_fail supersession-dedicated-reject "$ROOT/scripts/check-base-diff.sh" --allow-supersession --fixture-dirs "$ROOT/fixtures/base-diff/base" "$ROOT/fixtures/base-diff/supersession-bad"
expect_pass claim-oid-transition "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/claim-oid-base" "$ROOT/fixtures/base-diff/claim-oid-good"
expect_fail claim-oid-invalid "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/claim-oid-base" "$ROOT/fixtures/base-diff/claim-oid-bad"
expect_fail claim-oid-frozen "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/base" "$ROOT/fixtures/base-diff/claim-oid-freeze-bad"
expect_pass reference-lifecycle "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/lifecycle-base" "$ROOT/fixtures/base-diff/lifecycle-good"
expect_fail reference-partial-oid "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/lifecycle-base" "$ROOT/fixtures/base-diff/lifecycle-partial-oid"
expect_fail reference-bad-edition "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/lifecycle-base" "$ROOT/fixtures/base-diff/lifecycle-bad-edition"
expect_fail reference-pending-edition "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/lifecycle-base" "$ROOT/fixtures/registry-post-edition-pending"
expect_fail reference-mixed-oid-width "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/lifecycle-base" "$ROOT/fixtures/registry-source-mixed-width"
expect_fail reference-coverage-regress "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/base" "$ROOT/fixtures/base-diff/lifecycle-regress"
expect_fail reference-edition-frozen "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/lifecycle-good" "$ROOT/fixtures/base-diff/lifecycle-edition-drift"
expect_fail reference-oid-frozen "$ROOT/scripts/check-base-diff.sh" --fixture-dirs "$ROOT/fixtures/base-diff/lifecycle-good" "$ROOT/fixtures/base-diff/lifecycle-oid-drift"
IFS= read -r invalid_ref < "$ROOT/fixtures/base-invalid/ref.txt"
expect_fail invalid-base-ref "$ROOT/scripts/check-base-diff.sh" "$ROOT" "$invalid_ref"

echo "test-checkers: ok"
