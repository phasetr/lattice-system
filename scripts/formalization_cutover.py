#!/usr/bin/env python3
"""Shared, dependency-free formalization-status cutover baseline checks."""

from __future__ import annotations

import hashlib
import re
import subprocess
from pathlib import Path
from typing import Any, Iterable


BASELINE_COMMIT = "6519099024bf156b87ac0c807c6633c513792581"
BASELINE_PATH = "docs/index.md"
BASELINE_FIRST_LINE = 217
BASELINE_LAST_LINE = 2731
BASELINE_ROW_COUNT = 2052
CUTOVER_BASELINE_KEYS = {
    "baseline_commit",
    "baseline_path",
    "cutover_record_ids",
    "legacy_rows",
    "non_legacy_record_ids",
    "schema_version",
}
LEGACY_ROW_KEYS = {
    "legacy_source_line",
    "mapped_record_ids",
    "ordinal",
    "outcome",
    "reason",
    "row_sha256",
}
OUTCOMES = {"mapped", "not_a_declaration"}
PROTOTYPE_RECORD_IDS = {
    "shastry-1992-staggered-susceptibility-bound",
    "tasaki-2020-section-2-1-pauli-x-involutive",
    "tasaki-2020-theorem-3-1-finite-dimensional-core",
    "tasaki-2020-theorem-4-2-shastry-no-ssb",
}
SHA256_RE = re.compile(r"[0-9a-f]{64}")
STABLE_ID_RE = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")


def _is_separator(line: str) -> bool:
    return line.startswith("|") and set(line.strip()) <= set("|-: ")


def reconstruct_legacy_rows(repo_root: Path) -> list[dict[str, Any]]:
    """Reconstruct the exact 2,052 legacy rows from the pinned source commit."""
    text = subprocess.run(
        ["git", "show", f"{BASELINE_COMMIT}:{BASELINE_PATH}"],
        cwd=repo_root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    lines = text.splitlines()
    rows: list[dict[str, Any]] = []
    for source_line in range(BASELINE_FIRST_LINE, BASELINE_LAST_LINE + 1):
        line = lines[source_line - 1]
        if not line.startswith("|") or _is_separator(line):
            continue
        if source_line < len(lines) and _is_separator(lines[source_line]):
            continue
        rows.append(
            {
                "legacy_source_line": source_line,
                "ordinal": len(rows) + 1,
                "row_sha256": hashlib.sha256(line.encode("utf-8")).hexdigest(),
            }
        )
    if len(rows) != BASELINE_ROW_COUNT:
        raise ValueError(
            f"pinned legacy reconstruction produced {len(rows)} rows, "
            f"expected {BASELINE_ROW_COUNT}"
        )
    return rows


def _sorted_unique_strings(value: Any) -> bool:
    return (
        isinstance(value, list)
        and all(isinstance(item, str) for item in value)
        and value == sorted(set(value))
    )


def validate_cutover_baseline(
    baseline: Any,
    records: Iterable[dict[str, Any]],
    expected_rows: list[dict[str, Any]],
) -> list[str]:
    """Validate exhaustive historical coverage and irreversible cutover IDs."""
    errors: list[str] = []
    if not isinstance(baseline, dict):
        return ["cutover baseline: expected object"]
    if set(baseline) != CUTOVER_BASELINE_KEYS:
        errors.append("cutover baseline: field contract differs")
    if baseline.get("schema_version") != 1:
        errors.append("cutover baseline: bad schema version")
    if baseline.get("baseline_commit") != BASELINE_COMMIT:
        errors.append("cutover baseline: baseline commit is not pinned")
    if baseline.get("baseline_path") != BASELINE_PATH:
        errors.append("cutover baseline: baseline path differs")
    cutover_ids = baseline.get("cutover_record_ids")
    non_legacy_ids = baseline.get("non_legacy_record_ids")
    if not _sorted_unique_strings(cutover_ids):
        errors.append("cutover baseline: cutover_record_ids must be sorted and unique")
        cutover_ids = []
    if not _sorted_unique_strings(non_legacy_ids):
        errors.append("cutover baseline: non_legacy_record_ids must be sorted and unique")
        non_legacy_ids = []
    for name, values in (
        ("cutover_record_ids", cutover_ids),
        ("non_legacy_record_ids", non_legacy_ids),
    ):
        if any(STABLE_ID_RE.fullmatch(item) is None for item in values):
            errors.append(f"cutover baseline: {name} contains an invalid record ID")
    rows = baseline.get("legacy_rows")
    if not isinstance(rows, list) or len(rows) != len(expected_rows):
        errors.append(
            f"cutover baseline: expected {len(expected_rows)} legacy rows, "
            f"found {len(rows) if isinstance(rows, list) else 'non-array'}"
        )
        rows = []
    mapped_ids: list[str] = []
    for index, (row, expected) in enumerate(zip(rows, expected_rows), 1):
        location = f"cutover baseline row {index}"
        if not isinstance(row, dict):
            errors.append(f"{location}: expected object")
            continue
        if set(row) != LEGACY_ROW_KEYS:
            errors.append(f"{location}: field contract differs")
        for field in ("ordinal", "legacy_source_line", "row_sha256"):
            if row.get(field) != expected[field]:
                errors.append(f"{location}: {field} differs from pinned legacy row")
        outcome = row.get("outcome")
        mapped = row.get("mapped_record_ids")
        reason = row.get("reason")
        if outcome not in OUTCOMES:
            errors.append(f"{location}: invalid outcome")
        if not _sorted_unique_strings(mapped):
            errors.append(f"{location}: mapped_record_ids must be sorted and unique")
            mapped = []
        if any(STABLE_ID_RE.fullmatch(item) is None for item in mapped):
            errors.append(f"{location}: invalid mapped record ID")
        if outcome == "mapped":
            if not mapped:
                errors.append(f"{location}: mapped outcome requires at least one record ID")
            if reason is not None:
                errors.append(f"{location}: mapped outcome requires a null reason")
        elif outcome == "not_a_declaration":
            if mapped:
                errors.append(f"{location}: not_a_declaration outcome cannot map records")
            if not isinstance(reason, str) or not reason.strip() or "\n" in reason:
                errors.append(f"{location}: not_a_declaration requires an inline reason")
        mapped_ids.extend(mapped)
    if len(mapped_ids) != len(set(mapped_ids)):
        errors.append("cutover baseline: a record ID is mapped from more than one legacy row")
    mapped_set = set(mapped_ids)
    non_legacy_set = set(non_legacy_ids)
    cutover_set = set(cutover_ids)
    if mapped_set & non_legacy_set:
        errors.append("cutover baseline: mapped and non-legacy record IDs overlap")
    missing_prototype_mappings = sorted(PROTOTYPE_RECORD_IDS - mapped_set)
    if missing_prototype_mappings:
        errors.append(
            "cutover baseline: original prototype records must map to legacy rows: "
            f"{missing_prototype_mappings}"
        )
    if mapped_set | non_legacy_set != cutover_set:
        errors.append("cutover baseline: mapped/non-legacy union differs from cutover_record_ids")
    current_ids = {record.get("id") for record in records if isinstance(record.get("id"), str)}
    missing = sorted(cutover_set - current_ids)
    if missing:
        errors.append(f"cutover baseline: cutover records were deleted or are missing: {missing}")
    return errors


def validate_cutover_requirement(catalog_state: Any, baseline_name: Any) -> list[str]:
    """Require the fixed baseline only when authority has been cut over."""
    if baseline_name is not None and baseline_name != "cutover-baseline.json":
        return ["manifest cutover baseline path is not fixed"]
    if catalog_state == "authoritative" and baseline_name is None:
        return ["authoritative catalogue requires manifest.json.cutover_baseline"]
    return []


def self_test(repo_root: Path) -> list[str]:
    """Exercise positive and mutation fixtures without requiring a live baseline file."""
    failures: list[str] = []
    rows = reconstruct_legacy_rows(repo_root)
    fixture_rows = [
        {
            **row,
            "outcome": "not_a_declaration",
            "mapped_record_ids": [],
            "reason": "Self-test fixture only.",
        }
        for row in rows
    ]
    prototype_ids = sorted(PROTOTYPE_RECORD_IDS)
    for index, record_id in enumerate(prototype_ids):
        fixture_rows[index].update(
            outcome="mapped", mapped_record_ids=[record_id], reason=None
        )
    fixture_rows[len(prototype_ids)].update(
        outcome="mapped", mapped_record_ids=["fixture-record"], reason=None
    )
    baseline = {
        "schema_version": 1,
        "baseline_commit": BASELINE_COMMIT,
        "baseline_path": BASELINE_PATH,
        "cutover_record_ids": sorted(["fixture-record", "new-record", *prototype_ids]),
        "legacy_rows": fixture_rows,
        "non_legacy_record_ids": ["new-record"],
    }
    records = [
        {"id": record_id}
        for record_id in ["fixture-record", "new-record", "post-cutover-record", *prototype_ids]
    ]
    if validate_cutover_baseline(baseline, records, rows):
        failures.append("valid exhaustive fixture was rejected")
    mutations = []
    import copy

    missing_row = copy.deepcopy(baseline)
    missing_row["legacy_rows"].pop()
    mutations.append(missing_row)
    bad_hash = copy.deepcopy(baseline)
    bad_hash["legacy_rows"][0]["row_sha256"] = "0" * 64
    mutations.append(bad_hash)
    overlap = copy.deepcopy(baseline)
    overlap["non_legacy_record_ids"] = ["fixture-record", "new-record"]
    mutations.append(overlap)
    bad_union = copy.deepcopy(baseline)
    bad_union["cutover_record_ids"] = ["fixture-record"]
    mutations.append(bad_union)
    duplicate_mapping = copy.deepcopy(baseline)
    duplicate_mapping["legacy_rows"][1].update(
        outcome="mapped", mapped_record_ids=["fixture-record"], reason=None
    )
    mutations.append(duplicate_mapping)
    for number, mutated in enumerate(mutations, 1):
        if not validate_cutover_baseline(mutated, records, rows):
            failures.append(f"mutation fixture {number} was accepted")
    if not validate_cutover_baseline(
        baseline, [{"id": "new-record"}, *({"id": item} for item in prototype_ids)], rows
    ):
        failures.append("deletion of a cutover record was accepted")
    if validate_cutover_requirement("prototype", None):
        failures.append("prototype incorrectly required cutover evidence")
    if not validate_cutover_requirement("authoritative", None):
        failures.append("authoritative catalogue without cutover evidence was accepted")
    if not validate_cutover_requirement("prototype", "other.json"):
        failures.append("non-fixed optional baseline path was accepted")
    return failures
