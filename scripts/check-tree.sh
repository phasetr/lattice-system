#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=$(cd -P "$SCRIPT_DIR/.." && pwd)
ANCHOR=01bcb49d49db92c225cfa74b74d409dd0a9c4edc
fail() { echo "check-tree: $*" >&2; exit 1; }

if [[ ${1:-} == --fixture ]]; then
  [[ $# -eq 2 ]] || fail "usage: check-tree.sh --fixture FIXTURE_ROOT"
  ROOT=$(cd "$2" && pwd) || fail "invalid fixture root"
  [[ -n "${LATTICE_TEST_ROOT:-}" ]] || fail "fixture mode requires LATTICE_TEST_ROOT"
  TEST_ROOT=$(cd "$LATTICE_TEST_ROOT" && pwd) || fail "invalid LATTICE_TEST_ROOT"
  case "$TEST_ROOT" in "$PROJECT_ROOT"|"$PROJECT_ROOT"/*) fail "LATTICE_TEST_ROOT must be repository-external" ;; esac
  [[ "$TEST_ROOT" != / ]] || fail "LATTICE_TEST_ROOT must not contain the repository"
  case "$PROJECT_ROOT" in "$TEST_ROOT"|"$TEST_ROOT"/*) fail "LATTICE_TEST_ROOT must not contain the repository" ;; esac
  case "$ROOT/" in "$TEST_ROOT/"*) ;; *) fail "fixture root must be below LATTICE_TEST_ROOT" ;; esac
  [[ -f "$ROOT/tracked-files.txt" ]] || fail "fixture mode requires tracked-files.txt"
  tracked=$(<"$ROOT/tracked-files.txt")
  FIXTURE_MODE=1
else
  ROOT=${1:-$PROJECT_ROOT}
  ROOT=$(cd "$ROOT" && pwd) || fail "invalid repository root"
  [[ $(git -C "$ROOT" rev-parse --show-toplevel 2>/dev/null) == "$ROOT" ]] || fail "ROOT must be the repository top; fixture mode is explicit"
  tracked=$(git -C "$ROOT" ls-files)
  FIXTURE_MODE=0
fi

allowed_path() {
  local candidate=$1
  case "$candidate" in
    .github/CODEOWNERS|.github/pull_request_template.md|.github/workflows/rewrite-ci.yml|.gitignore|DESIGN.md|LatticeSystem.lean|README.md|lake-manifest.json|lakefile.toml|lean-toolchain) return 0 ;;
    registry/phase.tsv|registry/tracks.tsv|registry/sources.tsv|registry/source-invariants.tsv|registry/source-progress.tsv|registry/pages.tsv|registry/claims.tsv|registry/source-items.tsv|registry/item-claims.tsv|registry/slices.tsv|registry/dependencies.tsv|registry/bindings.tsv|registry/axioms.tsv|registry/claim-axioms.tsv|registry/claim-vocabulary-review.tsv|registry/vocabulary.tsv|registry/claim-vocabulary.tsv|registry/modules.tsv|registry/imports.tsv|registry/correction-events.tsv|registry/claim-corrections.tsv|registry/claim-successors.tsv) return 0 ;;
    scripts/check-all.sh|scripts/check-tree.sh|scripts/check-schema.sh|scripts/check-sources.sh|scripts/check-source-items.sh|scripts/check-order.sh|scripts/check-lifecycle.sh|scripts/check-registry.sh|scripts/check-census.sh|scripts/check-policy.sh|scripts/check-base-diff.sh|scripts/check-base-diff-ci.sh|scripts/check-claim-corrections.sh|scripts/check-vocabulary.sh|scripts/test-base-diff-runtime.sh|scripts/test-base-diff-ci-runtime.sh|scripts/test-claim-corrections-runtime.sh|scripts/test-checkers.sh|scripts/test-multisource.sh|scripts/test-tree-policy.sh|scripts/test-vocabulary-registry.sh|scripts/test-vocabulary-semantic.sh|scripts/generate-public-docs.py) return 0 ;;
    docs/index.md|docs/generated/index.md|docs/generated/catalog.json|docs/generated/groups/*.md|docs/generated/sources/*.md|docs/generated/tracks/*.md) return 0 ;;
    Checker/Vocabulary.lean) return 0 ;;
    LatticeSystem/*.lean|LatticeSystem/**/*.lean)
      [[ -f "$ROOT/registry/modules.tsv" ]] || return 1
      awk -F '\t' -v path="$candidate" 'FNR > 1 && $2 == path { found=1 } END { exit !found }' "$ROOT/registry/modules.tsv"
      return
      ;;
    *) return 1 ;;
  esac
}

while IFS= read -r path; do
  [[ -z "$path" ]] && continue
  allowed_path "$path" || fail "unexpected tracked path: $path"
  case "$path" in tex/*|formalization-status/*) fail "forbidden legacy path: $path" ;; esac
done <<< "$tracked"

if [[ "$FIXTURE_MODE" -eq 1 ]]; then
  echo "check-tree: fixture ok"
  exit 0
fi

[[ -z $(git -C "$ROOT" ls-files 'fixtures/**') ]] || fail "tracked fixture data is forbidden; tests must generate runtime fixtures"

if [[ -f "$ROOT/registry/modules.tsv" && $(awk 'END { print NR }' "$ROOT/registry/modules.tsv") -gt 1 ]]; then
  awk -F '\t' '
    NR == FNR { if (FNR > 1) registered[$2]=1; next }
    { tracked[$0]=1; if (!($0 in registered)) bad=1 }
    END { for (path in registered) if (!(path in tracked)) bad=1; exit bad }
  ' "$ROOT/registry/modules.tsv" <(printf '%s\n' "$tracked" | awk '$0 == "LatticeSystem.lean" || $0 ~ /^LatticeSystem\/.*\.lean$/') || fail "registered modules do not exactly match tracked production Lean sources"
fi

if git -C "$ROOT" ls-files -s | awk '$1 == "120000" { found=1 } END { exit !found }'; then
  git -C "$ROOT" ls-files -s | awk '$1 == "120000" { print $4 }' >&2
  fail "tracked symlink found"
fi

for pin in lean-toolchain lake-manifest.json; do
  expected=$(git -C "$ROOT" rev-parse "$ANCHOR:$pin")
  actual=$(git -C "$ROOT" hash-object "$pin")
  [[ "$actual" == "$expected" ]] || fail "$pin differs from legacy anchor"
done
echo "check-tree: ok"
