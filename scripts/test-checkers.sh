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
  if "$@" >/dev/null 2>&1; then
    echo "test-checkers: expected failure: $label" >&2
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
expect_fail phase-advance "$ROOT/scripts/check-policy.sh" "$ROOT/fixtures/policy-phase-advance"
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
