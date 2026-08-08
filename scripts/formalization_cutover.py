#!/usr/bin/env python3
"""Shared, dependency-free formalization-status cutover baseline checks."""

from __future__ import annotations

import hashlib
import json
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
    "disposition",
    "legacy_declaration_refs",
    "legacy_source_line",
    "mapped_record_ids",
    "ordinal",
    "outcome",
    "row_sha256",
}
OUTCOMES = {"mapped", "not_a_declaration"}
DISPOSITIONS = {"non_declaration"}
CUTOVER_CERTIFICATE_KEYS = {
    "baseline_sha256",
    "cutover_record_ids_sha256",
    "exceptional_mapping_ordinals",
    "legacy_mapping_sha256",
    "non_record_ordinals",
    "schema_version",
}
# PR E must replace this with the SHA-256 of the independently audited canonical
# certificate in the same atomic change that flips the catalogue authority.
ACCEPTED_CUTOVER_CERTIFICATE_SHA256: str | None = None
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
                "legacy_declaration_refs": re.findall(
                    r"`([^`]+)`", line.removeprefix("| ").split(" | ", 1)[0]
                ),
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


def canonical_bytes(value: Any) -> bytes:
    """Serialize certificate inputs with the canonical JSON byte contract."""
    return (
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    """Return the lowercase SHA-256 of exact bytes."""
    return hashlib.sha256(raw).hexdigest()


def _legacy_ref_matches_leaf(reference: str, leaf: str) -> bool:
    """Match an exact leaf or the audited slash shorthand used by legacy rows."""
    reference_leaf = reference.rsplit(".", 1)[-1]
    if reference_leaf == leaf:
        return True
    if "/" not in reference_leaf:
        return False
    alternatives = reference_leaf.split("/")
    first = re.fullmatch(r"(.*)([A-Z0-9])", alternatives[0])
    last = re.fullmatch(r"([A-Z0-9])(.*)", alternatives[-1])
    if first is None or last is None:
        return False
    prefix, first_choice = first.groups()
    last_choice, suffix = last.groups()
    choices = [first_choice, *alternatives[1:-1], last_choice]
    return leaf in {prefix + choice + suffix for choice in choices}


def certificate_projection(baseline: dict[str, Any]) -> tuple[list[str], list[dict[str, Any]]]:
    """Return the immutable ID and row-mapping projections covered by a certificate."""
    cutover_ids = baseline.get("cutover_record_ids", [])
    mappings = [
        {
            "disposition": row.get("disposition"),
            "mapped_record_ids": row.get("mapped_record_ids"),
            "ordinal": row.get("ordinal"),
            "outcome": row.get("outcome"),
            "row_sha256": row.get("row_sha256"),
        }
        for row in baseline.get("legacy_rows", [])
        if isinstance(row, dict)
    ]
    return cutover_ids, mappings


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
    allowed_non_record_ordinals: set[int] | None = None,
    exceptional_mapping_ordinals: set[int] | None = None,
) -> list[str]:
    """Validate exhaustive historical coverage and irreversible cutover IDs."""
    errors: list[str] = []
    allowed_non_record_ordinals = allowed_non_record_ordinals or set()
    exceptional_mapping_ordinals = exceptional_mapping_ordinals or set()
    record_map = {
        record.get("id"): record
        for record in records
        if isinstance(record, dict) and isinstance(record.get("id"), str)
    }
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
    actual_non_record_ordinals: set[int] = set()
    needed_exceptional_ordinals: set[int] = set()
    for index, (row, expected) in enumerate(zip(rows, expected_rows), 1):
        location = f"cutover baseline row {index}"
        if not isinstance(row, dict):
            errors.append(f"{location}: expected object")
            continue
        if set(row) != LEGACY_ROW_KEYS:
            errors.append(f"{location}: field contract differs")
        for field in (
            "legacy_declaration_refs",
            "ordinal",
            "legacy_source_line",
            "row_sha256",
        ):
            if row.get(field) != expected[field]:
                errors.append(f"{location}: {field} differs from pinned legacy row")
        outcome = row.get("outcome")
        mapped = row.get("mapped_record_ids")
        disposition = row.get("disposition")
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
            if disposition is not None:
                errors.append(f"{location}: mapped outcome requires a null disposition")
            references = row.get("legacy_declaration_refs")
            if not isinstance(references, list):
                references = []
            for record_id in mapped:
                record = record_map.get(record_id, {})
                lean_name = record.get("lean_name")
                leaf = lean_name.rsplit(".", 1)[-1] if isinstance(lean_name, str) else ""
                if not any(_legacy_ref_matches_leaf(ref, leaf) for ref in references):
                    grouped_reference = not references or any(
                        any(marker in ref for marker in ("/", "{", "}", ","))
                        for ref in references
                    )
                    if index not in exceptional_mapping_ordinals or not grouped_reference:
                        errors.append(
                            f"{location}: mapped record {record_id} is not bound to a legacy declaration reference"
                        )
                    else:
                        needed_exceptional_ordinals.add(index)
        elif outcome == "not_a_declaration":
            if mapped:
                errors.append(f"{location}: not_a_declaration outcome cannot map records")
            if disposition not in DISPOSITIONS:
                errors.append(f"{location}: invalid closed non-record disposition")
            if index not in allowed_non_record_ordinals:
                errors.append(f"{location}: non-record outcome is absent from the certificate")
            if row.get("legacy_declaration_refs"):
                errors.append(f"{location}: a declaration-bearing row cannot be a non-record")
            actual_non_record_ordinals.add(index)
        mapped_ids.extend(mapped)
    if actual_non_record_ordinals != allowed_non_record_ordinals:
        errors.append(
            "cutover baseline: certificate non-record ordinals differ from row outcomes"
        )
    if needed_exceptional_ordinals != exceptional_mapping_ordinals:
        errors.append(
            "cutover baseline: certificate exceptional-mapping ordinals differ from required bindings"
        )
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
    current_ids = set(record_map)
    missing = sorted(cutover_set - current_ids)
    if missing:
        errors.append(f"cutover baseline: cutover records were deleted or are missing: {missing}")
    return errors


def _sorted_unique_ordinals(value: Any) -> bool:
    return (
        isinstance(value, list)
        and all(isinstance(item, int) and 1 <= item <= BASELINE_ROW_COUNT for item in value)
        and value == sorted(set(value))
    )


def validate_cutover_certificate(
    certificate: Any,
    certificate_raw: bytes,
    baseline: Any,
    baseline_raw: bytes,
    catalog_state: Any,
    records: Iterable[dict[str, Any]],
    accepted_certificate_sha256: str | None = ACCEPTED_CUTOVER_CERTIFICATE_SHA256,
) -> list[str]:
    """Bind one baseline and its immutable cutover projections to a certificate."""
    errors: list[str] = []
    if not isinstance(certificate, dict):
        return ["cutover certificate: expected object"]
    if set(certificate) != CUTOVER_CERTIFICATE_KEYS:
        errors.append("cutover certificate: field contract differs")
    if certificate.get("schema_version") != 1:
        errors.append("cutover certificate: bad schema version")
    if canonical_bytes(certificate) != certificate_raw:
        errors.append("cutover certificate: bytes are not canonical JSON")
    if not isinstance(baseline, dict) or canonical_bytes(baseline) != baseline_raw:
        errors.append("cutover certificate: baseline bytes are not canonical JSON")
        baseline = {}
    cutover_ids, mappings = certificate_projection(baseline)
    expected_hashes = {
        "baseline_sha256": sha256_bytes(baseline_raw),
        "cutover_record_ids_sha256": sha256_bytes(canonical_bytes(cutover_ids)),
        "legacy_mapping_sha256": sha256_bytes(canonical_bytes(mappings)),
    }
    for field, expected in expected_hashes.items():
        if certificate.get(field) != expected:
            errors.append(f"cutover certificate: {field} does not bind the baseline")
    for field in ("exceptional_mapping_ordinals", "non_record_ordinals"):
        if not _sorted_unique_ordinals(certificate.get(field)):
            errors.append(f"cutover certificate: {field} must be sorted unique ordinals")
    if set(certificate.get("exceptional_mapping_ordinals", [])) & set(
        certificate.get("non_record_ordinals", [])
    ):
        errors.append("cutover certificate: exceptional mappings and non-record rows overlap")
    current_ids = {
        record.get("id")
        for record in records
        if isinstance(record, dict) and isinstance(record.get("id"), str)
    }
    cutover_set = set(cutover_ids) if isinstance(cutover_ids, list) else set()
    if catalog_state == "prototype" and current_ids != cutover_set:
        errors.append(
            "prototype cutover freeze requires current record IDs to equal cutover_record_ids"
        )
    if catalog_state == "authoritative" and not cutover_set <= current_ids:
        errors.append("authoritative catalogue deleted a certified cutover record")
    certificate_digest = sha256_bytes(certificate_raw)
    if catalog_state == "authoritative":
        if accepted_certificate_sha256 is None:
            errors.append("authoritative catalogue lacks a pinned accepted certificate digest")
        elif certificate_digest != accepted_certificate_sha256:
            errors.append("authoritative cutover certificate differs from the accepted fingerprint")
    return errors


def validate_cutover_requirement(
    catalog_state: Any, baseline_name: Any, certificate_name: Any = None
) -> list[str]:
    """Require paired fixed cutover evidence only when authority has been cut over."""
    errors: list[str] = []
    if baseline_name is not None and baseline_name != "cutover-baseline.json":
        errors.append("manifest cutover baseline path is not fixed")
    if certificate_name is not None and certificate_name != "cutover-certificate.json":
        errors.append("manifest cutover certificate path is not fixed")
    if (baseline_name is None) != (certificate_name is None):
        errors.append("manifest cutover baseline and certificate must be owned together")
    if catalog_state == "authoritative" and baseline_name is None:
        errors.append("authoritative catalogue requires cutover baseline and certificate")
    return errors


def self_test(repo_root: Path) -> list[str]:
    """Exercise positive and mutation fixtures without requiring a live baseline file."""
    import copy

    failures: list[str] = []
    rows = reconstruct_legacy_rows(repo_root)
    fixture_rows: list[dict[str, Any]] = []
    records: list[dict[str, Any]] = []
    non_record_ordinals: list[int] = []
    for row in rows:
        references = row["legacy_declaration_refs"]
        if references:
            record_id = f"fixture-row-{row['ordinal']:04d}"
            fixture_rows.append(
                {
                    **row,
                    "disposition": None,
                    "mapped_record_ids": [record_id],
                    "outcome": "mapped",
                }
            )
            records.append(
                {"id": record_id, "lean_name": f"LatticeSystem.Fixture.{references[0]}"}
            )
        else:
            fixture_rows.append(
                {
                    **row,
                    "disposition": "non_declaration",
                    "mapped_record_ids": [],
                    "outcome": "not_a_declaration",
                }
            )
            non_record_ordinals.append(row["ordinal"])
    prototype_names = {
        "shastry-1992-staggered-susceptibility-bound": "shastry_staggered_susceptibility_bound",
        "tasaki-2020-section-2-1-pauli-x-involutive": "pauliX_mul_self",
        "tasaki-2020-theorem-3-1-finite-dimensional-core": "horsch_vonderLinden_lowLying",
        "tasaki-2020-theorem-4-2-shastry-no-ssb": "shastry_no_symmetry_breaking_1d",
    }
    for record_id, leaf in prototype_names.items():
        target = next(
            row
            for row in fixture_rows
            if any(_legacy_ref_matches_leaf(ref, leaf) for ref in row["legacy_declaration_refs"])
        )
        target["mapped_record_ids"].append(record_id)
        target["mapped_record_ids"].sort()
        records.append({"id": record_id, "lean_name": f"LatticeSystem.Fixture.{leaf}"})
    cutover_ids = sorted(record["id"] for record in records)
    baseline = {
        "schema_version": 1,
        "baseline_commit": BASELINE_COMMIT,
        "baseline_path": BASELINE_PATH,
        "cutover_record_ids": cutover_ids,
        "legacy_rows": fixture_rows,
        "non_legacy_record_ids": [],
    }
    baseline_raw = canonical_bytes(baseline)
    ids, mappings = certificate_projection(baseline)
    certificate = {
        "baseline_sha256": sha256_bytes(baseline_raw),
        "cutover_record_ids_sha256": sha256_bytes(canonical_bytes(ids)),
        "exceptional_mapping_ordinals": [],
        "legacy_mapping_sha256": sha256_bytes(canonical_bytes(mappings)),
        "non_record_ordinals": non_record_ordinals,
        "schema_version": 1,
    }
    certificate_raw = canonical_bytes(certificate)
    baseline_errors = validate_cutover_baseline(
        baseline,
        records,
        rows,
        set(non_record_ordinals),
        set(),
    )
    certificate_errors = validate_cutover_certificate(
        certificate,
        certificate_raw,
        baseline,
        baseline_raw,
        "prototype",
        records,
    )
    if baseline_errors or certificate_errors:
        failures.append(
            "valid exhaustive fixture was rejected: "
            f"baseline={baseline_errors}, certificate={certificate_errors}"
        )

    all_non_record = copy.deepcopy(baseline)
    for row in all_non_record["legacy_rows"]:
        if not any(record_id in PROTOTYPE_RECORD_IDS for record_id in row["mapped_record_ids"]):
            row.update(
                disposition="non_declaration",
                mapped_record_ids=[],
                outcome="not_a_declaration",
            )
    if not validate_cutover_baseline(
        all_non_record,
        records,
        rows,
        set(range(1, BASELINE_ROW_COUNT + 1)),
        set(),
    ):
        failures.append("all-rows-non-record-except-prototype fixture was accepted")

    remapped = copy.deepcopy(baseline)
    remapped["legacy_rows"][0]["mapped_record_ids"] = remapped["legacy_rows"][1][
        "mapped_record_ids"
    ]
    if not validate_cutover_certificate(
        certificate,
        certificate_raw,
        remapped,
        canonical_bytes(remapped),
        "prototype",
        records,
    ):
        failures.append("row remapping without a new certificate was accepted")
    shrunk = copy.deepcopy(baseline)
    shrunk["cutover_record_ids"].pop()
    if not validate_cutover_certificate(
        certificate,
        certificate_raw,
        shrunk,
        canonical_bytes(shrunk),
        "prototype",
        records,
    ):
        failures.append("cutover ID shrink without a new certificate was accepted")
    omitted_current = [*records, {"id": "unfrozen", "lean_name": "LatticeSystem.Fixture.unfrozen"}]
    if not validate_cutover_certificate(
        certificate,
        certificate_raw,
        baseline,
        baseline_raw,
        "prototype",
        omitted_current,
    ):
        failures.append("prototype freeze omitted a current record")
    accepted_digest = sha256_bytes(certificate_raw)
    if validate_cutover_certificate(
        certificate,
        certificate_raw,
        baseline,
        baseline_raw,
        "authoritative",
        omitted_current,
        accepted_digest,
    ):
        failures.append("authoritative post-cutover record superset was rejected")
    deleted = records[1:]
    if not validate_cutover_certificate(
        certificate,
        certificate_raw,
        baseline,
        baseline_raw,
        "authoritative",
        deleted,
        accepted_digest,
    ):
        failures.append("authoritative deletion of a certified record was accepted")

    if validate_cutover_requirement("prototype", None, None):
        failures.append("prototype incorrectly required cutover evidence")
    if not validate_cutover_requirement("authoritative", None, None):
        failures.append("authoritative catalogue without cutover evidence was accepted")
    if not validate_cutover_requirement("prototype", "other.json", "other.json"):
        failures.append("non-fixed optional baseline path was accepted")
    return failures
