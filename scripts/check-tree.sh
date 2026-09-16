#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=$(cd "$SCRIPT_DIR/.." && pwd)
ANCHOR=01bcb49d49db92c225cfa74b74d409dd0a9c4edc
MANIFEST="$PROJECT_ROOT/fixtures/manifest.tsv"
fail() { echo "check-tree: $*" >&2; exit 1; }

if [[ ${1:-} == "--fixture" ]]; then
  [[ $# -eq 2 ]] || fail "usage: check-tree.sh --fixture FIXTURE_ROOT"
  ROOT=$(cd "$2" && pwd) || fail "invalid fixture root"
  case "$ROOT/" in "$PROJECT_ROOT/fixtures/"*) ;; *) fail "fixture root must be below fixtures/" ;; esac
  [[ "$ROOT" != "$PROJECT_ROOT" ]] || fail "production root cannot use fixture mode"
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
  local candidate=$1 variant rest
  case "$candidate" in
    fixtures/base-diff/*)
      variant=${candidate#fixtures/base-diff/}; variant=${variant%%/*}
      case "$variant" in base|good|deletion|drift|regression|supersession-good|supersession-bad|lifecycle-base|lifecycle-good|lifecycle-partial-oid|lifecycle-bad-edition|lifecycle-regress|lifecycle-edition-drift|lifecycle-oid-drift|claim-oid-base|claim-oid-good|claim-oid-bad|claim-oid-freeze-bad) ;; *) return 1 ;; esac
      rest=${candidate#fixtures/base-diff/$variant/}
      case "$rest" in
        registry/phase.tsv|registry/pages.tsv|registry/claims.tsv|registry/slices.tsv|registry/dependencies.tsv|registry/bindings.tsv|registry/axioms.tsv|registry/claim-axioms.tsv|references/tasaki-2020.tsv) return 0 ;;
        *) return 1 ;;
      esac
      ;;
    fixtures/registry-*/registry/*)
      rest=${candidate##*/}
      case "$rest" in phase.tsv|pages.tsv|claims.tsv|slices.tsv|dependencies.tsv|bindings.tsv|axioms.tsv|claim-axioms.tsv) return 0 ;; *) return 1 ;; esac
      ;;
    fixtures/registry-*/references/tasaki-2020.tsv) return 0 ;;
  esac
  case "$1" in
    .github/CODEOWNERS|.github/pull_request_template.md|.github/workflows/rewrite-ci.yml|.gitignore|DESIGN.md|LatticeSystem.lean|README.md|lake-manifest.json|lakefile.toml|lean-toolchain) return 0 ;;
    references/tasaki-2020.tsv) return 0 ;;
    registry/phase.tsv|registry/pages.tsv|registry/claims.tsv|registry/slices.tsv|registry/dependencies.tsv|registry/bindings.tsv|registry/axioms.tsv|registry/claim-axioms.tsv) return 0 ;;
    scripts/check-all.sh|scripts/check-tree.sh|scripts/check-registry.sh|scripts/check-policy.sh|scripts/check-base-diff.sh|scripts/test-checkers.sh) return 0 ;;
    fixtures/manifest.tsv) return 0 ;;
    fixtures/policy-*/LatticeSystem.lean|fixtures/policy-*/README.md|fixtures/policy-*/DESIGN.md|fixtures/policy-*/.github/pull_request_template.md|fixtures/policy-*/registry/phase.tsv) return 0 ;;
    fixtures/tree-*/tracked-files.txt|fixtures/base-invalid/ref.txt) return 0 ;;
    *) return 1 ;;
  esac
}

while IFS= read -r path; do
  [[ -z "$path" ]] && continue
  allowed_path "$path" || fail "unexpected tracked path: $path"
  case "$path" in LatticeSystem/*|docs/*|tex/*|formalization-status/*) fail "forbidden legacy path: $path" ;; esac
done <<< "$tracked"

[[ -f "$MANIFEST" ]] || fail "missing fixtures/manifest.tsv"
IFS= read -r manifest_header < "$MANIFEST"
[[ "$manifest_header" == $'path\toid' ]] || fail "bad fixture manifest header"
awk -F '\t' '
  NR == 1 { next }
  NF != 2 || $1 !~ /^fixtures\// || $2 !~ /^[0-9a-f]+$/ || length($2) != 40 { bad=1 }
  $1 == "fixtures/manifest.tsv" || seen[$1]++ { bad=1 }
  NR > 2 && $1 <= previous { bad=1 }
  { previous=$1 }
  END { exit bad }
' "$MANIFEST" || fail "invalid, duplicate, or unsorted fixture manifest row"

if [[ "$FIXTURE_MODE" -eq 1 ]]; then
  while IFS= read -r path; do
    [[ -z "$path" || "$path" == "fixtures/manifest.tsv" ]] && continue
    awk -F '\t' -v path="$path" 'NR > 1 && $1 == path { found=1 } END { exit !found }' "$MANIFEST" || fail "fixture path is not listed in manifest: $path"
  done <<< "$tracked"
  echo "check-tree: fixture ok"
  exit 0
fi

if git -C "$ROOT" ls-files -s | awk '$1 == "120000" { found=1 } END { exit !found }'; then
  git -C "$ROOT" ls-files -s | awk '$1 == "120000" { print $4 }' >&2
  fail "tracked symlink found"
fi
manifest_oid=$(git -C "$ROOT" rev-parse :fixtures/manifest.tsv)
[[ $(git -C "$ROOT" cat-file -s "$manifest_oid") -le 65536 ]] || fail "oversized fixture manifest"

awk -F '\t' '
  NR == FNR { if (FNR > 1) expected[$1]=$2; next }
  { path=$1; oid=$2; actual[path]=oid; if (!(path in expected) || expected[path] != oid) bad=1 }
  END { for (path in expected) if (!(path in actual)) bad=1; exit bad }
' "$MANIFEST" <(git -C "$ROOT" ls-files -s 'fixtures/**' | awk '$4 != "fixtures/manifest.tsv" { print $4 "\t" $2 }') || fail "fixture manifest does not exactly match index paths and OIDs"

while IFS=$'\t' read -r path oid; do
  [[ -z "$path" ]] && continue
  allowed_path "$path" || fail "unexpected fixture path or extension: $path"
  size=$(git -C "$ROOT" cat-file -s "$oid")
  [[ "$size" -le 65536 ]] || fail "oversized fixture: $path"
  git -C "$ROOT" grep -I -l -e '' --cached -- "$path" >/dev/null || fail "NUL/binary or empty fixture: $path"
done < <(git -C "$ROOT" ls-files -s 'fixtures/**' | awk '$4 != "fixtures/manifest.tsv" { print $4 "\t" $2 }')

for pin in lean-toolchain lake-manifest.json; do
  expected=$(git -C "$ROOT" rev-parse "$ANCHOR:$pin")
  actual=$(git -C "$ROOT" hash-object "$pin")
  [[ "$actual" == "$expected" ]] || fail "$pin differs from legacy anchor"
done
echo "check-tree: ok"
