#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=${BASH_SOURCE[0]%/*}
[[ "$SCRIPT_DIR" == "${BASH_SOURCE[0]}" ]] && SCRIPT_DIR=.
PROJECT_ROOT=${1:-$(cd "$SCRIPT_DIR/.." && pwd)}
PROJECT_ROOT=$(cd "$PROJECT_ROOT" && pwd)
SELECTOR=$PROJECT_ROOT/scripts/check-base-diff-ci.sh
TMP=$(mktemp -d "${TMPDIR:-/tmp}/lattice-system-tests.base-diff-ci.XXXXXX")
trap 'rm -rf "$TMP"' EXIT HUP INT TERM
REPO=$TMP/repo
mkdir -p "$REPO/registry"
git -C "$REPO" init -q
git -C "$REPO" config user.name "Runtime Test"
git -C "$REPO" config user.email "runtime@example.invalid"
printf '%s\n' $'event_id\tevent_position\tsource_id\tbase_commit\treview_ref' > "$REPO/registry/correction-events.tsv"
git -C "$REPO" add registry/correction-events.tsv
git -C "$REPO" commit -qm base
BASE=$(git -C "$REPO" rev-parse HEAD)

STUB=$TMP/check-base-diff-stub.sh
apply_stub() {
  local mode=$1
  if [[ "$mode" == correction ]]; then
    printf '%s\n' '#!/usr/bin/env bash' \
      'set -euo pipefail' \
      '[[ $# -eq 4 && $1 == --correction-event ]]' \
      'echo "stub-correction-$2-ok"' > "$STUB"
  else
    printf '%s\n' '#!/usr/bin/env bash' \
      'set -euo pipefail' \
      '[[ $# -eq 2 ]]' \
      'echo stub-normal-ok' > "$STUB"
  fi
  chmod +x "$STUB"
}

expect_pass() {
  local label=$1 expected=$2
  shift 2
  local output
  if ! output=$("$@" 2>&1); then
    echo "test-base-diff-ci-runtime: expected pass: $label" >&2
    echo "$output" >&2
    exit 1
  fi
  [[ "$output" == *"$expected"* ]] || {
    echo "test-base-diff-ci-runtime: wrong mode: $label" >&2
    echo "$output" >&2
    exit 1
  }
}

expect_fail() {
  local label=$1 diagnostic=$2
  shift 2
  local output
  if output=$("$@" 2>&1); then
    echo "test-base-diff-ci-runtime: expected failure: $label" >&2
    exit 1
  fi
  [[ "$output" == *"$diagnostic"* ]] || {
    echo "test-base-diff-ci-runtime: wrong diagnostic: $label" >&2
    echo "$output" >&2
    exit 1
  }
}

printf '%s\n' \
  $'event_id\tevent_position\tsource_id\tbase_commit\treview_ref' \
  "CORPUS-NORMALIZATION-TASAKI2020-2026"$'\t1\tTASAKI2020\t'"$BASE"$'\tINDEPENDENT-REVIEW' \
  > "$REPO/registry/correction-events.tsv"
apply_stub correction
expect_pass new-event-selects-correction stub-correction-CORPUS-NORMALIZATION-TASAKI2020-2026-ok \
  env CHECK_BASE_DIFF="$STUB" "$SELECTOR" "$REPO" "$BASE"

git -C "$REPO" add registry/correction-events.tsv
git -C "$REPO" commit -qm correction
HISTORICAL=$(git -C "$REPO" rev-parse HEAD)
apply_stub normal
expect_pass historical-event-uses-normal stub-normal-ok \
  env CHECK_BASE_DIFF="$STUB" "$SELECTOR" "$REPO" "$HISTORICAL"

printf '%s\n' \
  $'event_id\tevent_position\tsource_id\tbase_commit\treview_ref' \
  "CORPUS-NORMALIZATION-TASAKI2020-2026"$'\t1\tTASAKI2020\t'"$BASE"$'\tINDEPENDENT-REVIEW' \
  "SECOND-CORRECTION"$'\t2\tTASAKI2020\t'"$HISTORICAL"$'\tSECOND-INDEPENDENT-REVIEW' \
  > "$REPO/registry/correction-events.tsv"
apply_stub correction
expect_pass future-second-event-selects-correction stub-correction-SECOND-CORRECTION-ok \
  env CHECK_BASE_DIFF="$STUB" "$SELECTOR" "$REPO" "$HISTORICAL"

git -C "$REPO" reset -q --hard "$BASE"
printf '%s\n' \
  $'event_id\tevent_position\tsource_id\tbase_commit\treview_ref' \
  $'CORPUS-NORMALIZATION-TASAKI2020-2026\t1\tTASAKI2020\t0000000000000000000000000000000000000000\tINDEPENDENT-REVIEW' \
  > "$REPO/registry/correction-events.tsv"
expect_fail mismatched-base "does not match the actual merge base" \
  env CHECK_BASE_DIFF="$STUB" "$SELECTOR" "$REPO" "$BASE"

printf '%s\n' \
  $'event_id\tevent_position\tsource_id\tbase_commit\treview_ref' \
  "CORPUS-NORMALIZATION-TASAKI2020-2026"$'\t1\tTASAKI2020\t'"$BASE"$'\tINDEPENDENT-REVIEW' \
  "SECOND-CORRECTION"$'\t2\tTASAKI2020\t'"$BASE"$'\tINDEPENDENT-REVIEW' \
  > "$REPO/registry/correction-events.tsv"
expect_fail multiple-new-events "multiple new correction events" \
  env CHECK_BASE_DIFF="$STUB" "$SELECTOR" "$REPO" "$BASE"

expect_fail invalid-base "invalid or unfetched base ref" \
  env CHECK_BASE_DIFF="$STUB" "$SELECTOR" "$REPO" refs/heads/does-not-exist

echo "test-base-diff-ci-runtime: ok"
