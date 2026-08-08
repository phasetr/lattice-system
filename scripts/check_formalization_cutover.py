#!/usr/bin/env python3
"""Check staged formalization cutover coverage against the pinned legacy ledger."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from formalization_cutover import (
    reconstruct_legacy_rows,
    self_test,
    validate_cutover_baseline,
    validate_cutover_requirement,
)


def read_json(path: Path) -> Any:
    """Read one UTF-8 JSON document without accepting duplicate object keys."""
    def object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate key {key!r} in {path}")
            result[key] = value
        return result

    with path.open(encoding="utf-8") as source:
        return json.load(source, object_pairs_hook=object_pairs)


def main() -> int:
    """Validate optional staging evidence or mandatory authoritative evidence."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    root = repo_root / "formalization-status" / "v1"
    failures = self_test(repo_root) if args.self_test else []
    manifest = read_json(root / "manifest.json")
    baseline_name = manifest.get("cutover_baseline")
    failures.extend(validate_cutover_requirement(manifest.get("catalog_state"), baseline_name))
    if baseline_name is not None:
        if baseline_name != "cutover-baseline.json":
            failures.append("manifest cutover baseline path is not fixed")
        else:
            records: list[dict[str, Any]] = []
            for shard in manifest.get("record_shards", []):
                shard_data = read_json(root / shard)
                records.extend(shard_data.get("records", []))
            failures.extend(
                validate_cutover_baseline(
                    read_json(root / baseline_name),
                    records,
                    reconstruct_legacy_rows(repo_root),
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
