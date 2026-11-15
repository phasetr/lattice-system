#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
CHECK_PROJECT=$(cd -P "$SCRIPT_DIR/.." && pwd)
CHECK_ALL=(env "ELAN_TOOLCHAIN=$(<"$CHECK_PROJECT/lean-toolchain")" "LATTICE_CHECK_ALL_PROJECT=$CHECK_PROJECT"
  lake -d "$CHECK_PROJECT" env lean -DwarningAsError=true --run "$CHECK_PROJECT/Checker/CheckAll.lean" --gate)
if [[ -n ${LATTICE_CHECK_ALL_EXEC:-} ]]; then
  CHECK_ALL=(env "LATTICE_CHECK_ALL_PROJECT=$CHECK_PROJECT" "$LATTICE_CHECK_ALL_EXEC" --gate)
fi

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
  "${CHECK_ALL[@]}" tree "$TMP/tree-fake-bypass"
expect_fail unexpected-path \
  "${CHECK_ALL[@]}" tree --fixture "$TMP/tree-unexpected"
expect_fail unlisted-fixture \
  "${CHECK_ALL[@]}" tree --fixture "$TMP/tree-unlisted"
expect_fail_diagnostic fixture-root-repository-reject "must be repository-external" \
  env LATTICE_TEST_ROOT="$PROJECT_ROOT" \
  "${CHECK_ALL[@]}" tree --fixture "$PROJECT_ROOT"
expect_fail_diagnostic fixture-root-ancestor-census-reject "must not contain the repository" \
  env LATTICE_TEST_ROOT=/ \
  "${CHECK_ALL[@]}" census --fixture "$TMP/tree-unexpected"
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

# Lexical hygiene reads the tracked file set, so a policy fixture that exercises
# it has to be a real index rather than a bare directory.
make_policy_repo() {
  local target=$1
  git -C "$target" init --quiet
  git -C "$target" add -A
}
expect_fail_diagnostic vocabulary-policy-missing-index "external operation failed: git" \
  "${CHECK_ALL[@]}" policy "$TMP/policy-future-phase"
make_policy_repo "$TMP/policy-future-phase"
make_skeleton_case() {
  local name=$1 registered_path=$2 vocabulary_body=$3
  local claim_body=${4:-'theorem stub : True := by sorry'}
  local target="$TMP/$name"
  make_policy_case "$name" skeleton vocabulary
  mkdir -p "$target/registry" "$target/LatticeSystem/Vocabulary" "$target/LatticeSystem/Claims"
  printf '%s\n' $'module\tsource_path\trole' > "$target/registry/statement-modules.tsv"
  case "$registered_path" in
    none) ;;
    *) printf '%s\t%s\tleaf\n' \
        "$(printf '%s' "${registered_path%.lean}" | tr '/' '.')" "$registered_path" \
        >> "$target/registry/statement-modules.tsv" ;;
  esac
  printf '%s\n' '/-! Vocabulary fixture. -/' "$vocabulary_body" \
    > "$target/LatticeSystem/Vocabulary/Quantum.lean"
  printf '%s\n' '/-! Claim fixture. -/' "$claim_body" \
    > "$target/LatticeSystem/Claims/Front.lean"
  printf '%s\n' '/-! Second claim fixture. -/' > "$target/LatticeSystem/Claims/Other.lean"
  make_policy_repo "$target"
}

make_skeleton_case policy-skeleton-good LatticeSystem/Claims/Front.lean 'def quantumDimension : Nat := 2'
make_skeleton_case policy-skeleton-empty none 'def quantumDimension : Nat := 2'
make_skeleton_case policy-skeleton-unregistered LatticeSystem/Claims/Other.lean 'def quantumDimension : Nat := 2'
make_skeleton_case policy-skeleton-hygiene LatticeSystem/Claims/Front.lean 'theorem leaked : True := trivial'
# A registered statement module legitimately carries registered axioms, claim
# theorems, and proof stubs. It never carries `admit` or `native_decide`.
make_skeleton_case policy-skeleton-axiom LatticeSystem/Claims/Front.lean \
  'def quantumDimension : Nat := 2' 'axiom interfaceAxiom : True'
make_skeleton_case policy-skeleton-native LatticeSystem/Claims/Front.lean \
  'def quantumDimension : Nat := 2' 'theorem stub : True := by native_decide'
make_skeleton_case policy-skeleton-admit LatticeSystem/Claims/Front.lean \
  'def quantumDimension : Nat := 2' 'theorem stub : True := by admit'
# Registering one path in both module registries must not buy the statement
# exemption; check-policy closes that on its own.
make_skeleton_case policy-skeleton-dual LatticeSystem/Claims/Front.lean \
  'def quantumDimension : Nat := 2' 'theorem sneaky : True := trivial'
printf '%s\n' $'module\tsource_path\trole' \
  $'LatticeSystem.Claims.Front\tLatticeSystem/Claims/Front.lean\tleaf' \
  > "$TMP/policy-skeleton-dual/registry/modules.tsv"
git -C "$TMP/policy-skeleton-dual" add -A

expect_pass skeleton-policy \
  "${CHECK_ALL[@]}" policy "$TMP/policy-skeleton-good"
expect_fail_diagnostic skeleton-policy-no-statement-modules "skeleton phase requires registered statement modules" \
  "${CHECK_ALL[@]}" policy "$TMP/policy-skeleton-empty"
expect_fail_diagnostic skeleton-policy-unregistered-statement "forbidden token (nonsemantic check): LatticeSystem/Claims/Front.lean" \
  "${CHECK_ALL[@]}" policy "$TMP/policy-skeleton-unregistered"
expect_fail_diagnostic skeleton-policy-hygiene "forbidden token (nonsemantic check): LatticeSystem/Vocabulary/Quantum.lean" \
  "${CHECK_ALL[@]}" policy "$TMP/policy-skeleton-hygiene"
expect_pass skeleton-policy-registered-axiom \
  "${CHECK_ALL[@]}" policy "$TMP/policy-skeleton-axiom"
expect_fail_diagnostic skeleton-policy-native-decide "forbidden token (nonsemantic check): LatticeSystem/Claims/Front.lean" \
  "${CHECK_ALL[@]}" policy "$TMP/policy-skeleton-native"
expect_fail_diagnostic skeleton-policy-admit "forbidden token (nonsemantic check): LatticeSystem/Claims/Front.lean" \
  "${CHECK_ALL[@]}" policy "$TMP/policy-skeleton-admit"
expect_fail_diagnostic skeleton-policy-dual-registration "registered as both a vocabulary and a statement module" \
  "${CHECK_ALL[@]}" policy "$TMP/policy-skeleton-dual"

expect_fail forbidden-token \
  "${CHECK_ALL[@]}" policy "$TMP/policy-forbidden"
expect_fail root-check \
  "${CHECK_ALL[@]}" policy "$TMP/policy-root-check"
expect_pass comment-theorem-allowed \
  "${CHECK_ALL[@]}" policy "$TMP/policy-comment-allowed"
expect_fail merge-gate-missing \
  "${CHECK_ALL[@]}" policy "$TMP/policy-merge-missing"
expect_fail merge-gate-checked \
  "${CHECK_ALL[@]}" policy "$TMP/policy-merge-checked"
expect_pass census-phase \
  "${CHECK_ALL[@]}" policy "$TMP/policy-phase-advance"
expect_pass vocabulary-policy \
  "${CHECK_ALL[@]}" policy "$TMP/policy-future-phase"

echo "test-tree-policy: ok"
