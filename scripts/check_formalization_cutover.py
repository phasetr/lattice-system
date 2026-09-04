#!/usr/bin/env python3
"""Check staged formalization cutover coverage against the pinned legacy ledger."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from formalization_cutover import (
    exceptional_mapping_map,
    reconstruct_legacy_rows,
    retired_declaration_map,
    self_test,
    validate_cutover_baseline,
    validate_cutover_certificate,
    validate_cutover_requirement,
)


def read_json(path: Path) -> tuple[Any, bytes]:
    """Read one UTF-8 JSON document without accepting duplicate object keys."""
    def object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate key {key!r} in {path}")
            result[key] = value
        return result

    raw = path.read_bytes()
    return json.loads(raw.decode("utf-8"), object_pairs_hook=object_pairs), raw


def main() -> int:
    """Validate optional staging evidence or mandatory authoritative evidence."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    root = repo_root / "formalization-status" / "v2"
    failures = self_test(repo_root) if args.self_test else []
    manifest, _manifest_raw = read_json(root / "manifest.json")
    baseline_name = manifest.get("cutover_baseline")
    certificate_name = manifest.get("cutover_certificate")
    failures.extend(
        validate_cutover_requirement(
            manifest.get("catalog_state"), baseline_name, certificate_name
        )
    )
    if baseline_name is not None and certificate_name is not None:
        if baseline_name != "cutover-baseline.json":
            failures.append("manifest cutover baseline path is not fixed")
        elif certificate_name != "cutover-certificate.json":
            failures.append("manifest cutover certificate path is not fixed")
        else:
            records: list[dict[str, Any]] = []
            for shard in manifest.get("record_shards", []):
                shard_data, _shard_raw = read_json(root / shard)
                records.extend(shard_data.get("records", []))
            baseline, baseline_raw = read_json(root / baseline_name)
            certificate, certificate_raw = read_json(root / certificate_name)
            failures.extend(
                validate_cutover_certificate(
                    certificate,
                    certificate_raw,
                    baseline,
                    baseline_raw,
                    manifest.get("catalog_state"),
                    records,
                    repo_root,
                )
            )
            exceptional_mappings, _exceptional_errors = exceptional_mapping_map(
                certificate.get("exceptional_mappings")
            )
            retired_declarations, _retired_errors = retired_declaration_map(
                certificate.get("retired_declarations"), repo_root
            )
            failures.extend(
                validate_cutover_baseline(
                    baseline,
                    records,
                    reconstruct_legacy_rows(repo_root),
                    set(certificate.get("non_record_ordinals", [])),
                    exceptional_mappings,
                    retired_declarations,
                )
            )
    if failures:
        for failure in failures:
            print(f"error: {failure}", file=sys.stderr)
        return 1
    suffix = " and self-tests" if args.self_test else ""
    if baseline_name is None:
        print(f"formalization cutover: prototype staging valid{suffix}; no baseline owned")
    else:
        print(f"formalization cutover: exhaustive baseline valid{suffix}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
