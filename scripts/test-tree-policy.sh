#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
PROJECT_ROOT=$(cd "$PROJECT_ROOT" && pwd)
TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-system-tests.tree-policy.XXXXXX")
trap 'rm -rf "$TMP"' EXIT
export LATTICE_TEST_ROOT=$TMP

expect_pass() {
  local label=$1
  shift
  if ! "$@" >/dev/null 2>&1; then
    echo "test-tree-policy: expected pass: $label" >&2
    exit 1
  fi
}

expect_fail() {
  local label=$1
  shift
  if "$@" >/dev/null 2>&1; then
    echo "test-tree-policy: expected failure: $label" >&2
    exit 1
  fi
}

expect_fail_diagnostic() {
  local label=$1 diagnostic=$2 output
  shift 2
  if output=$("$@" 2>&1); then
    echo "test-tree-policy: expected failure: $label" >&2
    exit 1
  fi
  [[ "$output" == *"$diagnostic"* ]] || {
    echo "test-tree-policy: wrong failure diagnostic: $label" >&2
    echo "$output" >&2
    exit 1
  }
}

make_tree_case() {
  local name=$1
  shift
  local target="$TMP/$name"
  mkdir -p "$target"
  printf '%s\n' "$@" > "$target/tracked-files.txt"
}

make_tree_case tree-fake-bypass README.md
make_tree_case tree-unexpected README.md unexpected.txt
make_tree_case tree-unlisted fixtures/tree-ghost/tracked-files.txt

expect_fail fake-tracked-files-bypass \
  "$PROJECT_ROOT/scripts/check-tree.sh" "$TMP/tree-fake-bypass"
expect_fail unexpected-path \
  "$PROJECT_ROOT/scripts/check-tree.sh" --fixture "$TMP/tree-unexpected"
expect_fail unlisted-fixture \
  "$PROJECT_ROOT/scripts/check-tree.sh" --fixture "$TMP/tree-unlisted"
expect_fail_diagnostic fixture-root-repository-reject "must be repository-external" \
  env LATTICE_TEST_ROOT="$PROJECT_ROOT" \
  "$PROJECT_ROOT/scripts/check-tree.sh" --fixture "$PROJECT_ROOT"
expect_fail_diagnostic fixture-root-ancestor-census-reject "must not contain the repository" \
  env LATTICE_TEST_ROOT=/ \
  "$PROJECT_ROOT/scripts/check-census.sh" --fixture "$TMP/tree-unexpected"
expect_fail_diagnostic fixture-root-ancestor-vocabulary-reject "must not contain the repository" \
  env LATTICE_TEST_ROOT=/ \
  "$PROJECT_ROOT/scripts/check-vocabulary.sh" --fixture "$TMP/tree-unexpected"
expect_fail_diagnostic fixture-root-ancestor-base-diff-reject "must not contain the repository" \
  env LATTICE_TEST_ROOT=/ \
  "$PROJECT_ROOT/scripts/check-base-diff.sh" --fixture-dirs "$TMP/tree-fake-bypass" "$TMP/tree-unexpected"

write_canonical_root() {
  printf '%s\n' \
    '/-!' \
    '# LatticeSystem' \
    '' \
    'Empty production root for the from-scratch Tasaki formalization.' \
    'No theorem declarations, imports, commands, or notation exist here.' \
    '-/'
}

make_policy_case() {
  local name=$1 phase=$2 root_kind=$3
  local target="$TMP/$name"
  mkdir -p "$target/.github" "$target/registry"
  printf '%s\n' phase "$phase" > "$target/registry/phase.tsv"
  printf '%s\n' 'The exact PR and exact head SHA are required.' > "$target/README.md"
  printf '%s\n' 'The exact PR and exact head SHA are required.' > "$target/DESIGN.md"
  printf '%s\n' \
    'The exact PR and exact head SHA are required.' \
    '' \
    '- [ ] USER ONLY' > "$target/.github/pull_request_template.md"
  case "$root_kind" in
    canonical) write_canonical_root > "$target/LatticeSystem.lean" ;;
    vocabulary) cp "$PROJECT_ROOT/LatticeSystem.lean" "$target/LatticeSystem.lean" ;;
    *) echo "test-tree-policy: unknown policy root kind: $root_kind" >&2; exit 1 ;;
  esac
}

make_policy_case policy-forbidden bootstrap canonical
printf '%s\n' '/-! Forbidden-token fixture. -/' 'axiom escapedProof : True' \
  > "$TMP/policy-forbidden/LatticeSystem.lean"

make_policy_case policy-root-check bootstrap canonical
printf '%s\n' '#check True' >> "$TMP/policy-root-check/LatticeSystem.lean"

make_policy_case policy-comment-allowed bootstrap canonical

make_policy_case policy-merge-missing bootstrap canonical
printf '%s\n' 'This fixture intentionally omits the merge authorization wording.' \
  > "$TMP/policy-merge-missing/DESIGN.md"

make_policy_case policy-merge-checked bootstrap canonical
printf '%s\n' \
  'The exact PR and exact head SHA are required.' \
  '' \
  '- [x] USER ONLY' > "$TMP/policy-merge-checked/.github/pull_request_template.md"

make_policy_case policy-phase-advance census canonical
make_policy_case policy-future-phase vocabulary vocabulary

expect_fail forbidden-token \
  "$PROJECT_ROOT/scripts/check-policy.sh" "$TMP/policy-forbidden"
expect_fail root-check \
  "$PROJECT_ROOT/scripts/check-policy.sh" "$TMP/policy-root-check"
expect_pass comment-theorem-allowed \
  "$PROJECT_ROOT/scripts/check-policy.sh" "$TMP/policy-comment-allowed"
expect_fail merge-gate-missing \
  "$PROJECT_ROOT/scripts/check-policy.sh" "$TMP/policy-merge-missing"
expect_fail merge-gate-checked \
  "$PROJECT_ROOT/scripts/check-policy.sh" "$TMP/policy-merge-checked"
expect_pass census-phase \
  "$PROJECT_ROOT/scripts/check-policy.sh" "$TMP/policy-phase-advance"
expect_pass vocabulary-policy \
  "$PROJECT_ROOT/scripts/check-policy.sh" "$TMP/policy-future-phase"

echo "test-tree-policy: ok"
