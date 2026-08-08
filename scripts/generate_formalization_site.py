#!/usr/bin/env python3
"""Stage deterministic human and machine formalization-status documentation."""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


GENERATOR_VERSION = 1
MARKER_RE = re.compile(
    r"(?ms)^<!-- formalization-status-generated:start ([^\n]+) -->\n.*?"
    r"^<!-- formalization-status-generated:end -->$"
)
OWNERSHIP_MARKER_RE = re.compile(
    r"(?ms)^<!-- formalization-status-generated:start ([^\n]+) -->\n(.*?)"
    r"^<!-- formalization-status-generated:end -->$"
)
REVISION_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9._/-]{0,199}")


def html_text(value: Any) -> str:
    """Escape HTML and hide Liquid openers while preserving browser text."""
    return (
        html.escape(str(value), quote=True)
        .replace("{", "&#123;")
        .replace("}", "&#125;")
    )


def locator(item: dict[str, Any]) -> str:
    """Render a typed, structured source locator."""
    parts = [f"{item['item_kind']} {item['item_number']}" if item["item_number"] else item["item_kind"]]
    if item["section"]:
        parts.append(f"section {item['section']}")
    if item["equations"]:
        parts.append("equations " + ", ".join(item["equations"]))
    if item["pages"]:
        parts.append(f"pages {item['pages']}")
    return "; ".join(parts)


def human_status(record: dict[str, Any]) -> str:
    """Derive the human label without introducing another stored status."""
    if record["implementation_state"] == "in_progress":
        return "in progress"
    if record["declaration_kind"] == "axiom":
        return "documented axiom"
    if record["declaration_kind"] not in {"lemma", "theorem"}:
        return "definition only"
    if record["trust_state"] == "depends_on_documented_axioms":
        return "proved with documented axioms"
    return "proved"


def metadata(aggregate: dict[str, Any], revision: str) -> list[str]:
    """Return the visible provenance header shared by every generated view."""
    return [
        "> **Generated formalization-status view.** Do not edit this section by hand.",
        "> The interim legacy catalogue remains authoritative until Issue #5228.",
        "",
        '<ul data-generated-metadata="true">',
        f'<li data-meta="catalog-state">Catalogue state: {html_text(aggregate["catalog_state"])}</li>',
        f'<li data-meta="schema-version">Schema version: {html_text(aggregate["schema_version"])}</li>',
        f'<li data-meta="input-sha256">Input SHA-256: {html_text(aggregate["input_sha256"])}</li>',
        f'<li data-meta="revision">Deploy revision: {html_text(revision)}</li>',
        '<li data-meta="catalog-link" data-href="/lattice-system/formalization-status/v1/catalog.json"><a href="/lattice-system/formalization-status/v1/catalog.json">Machine data: version 1 catalogue</a></li>',
        '<li data-meta="schema-link" data-href="/lattice-system/formalization-status/v1/schema.json"><a href="/lattice-system/formalization-status/v1/schema.json">Schema: version 1 schema</a></li>',
        '<li data-meta="publication-link" data-href="/lattice-system/formalization-status/v1/publication.json"><a href="/lattice-system/formalization-status/v1/publication.json">Build metadata: publication sidecar</a></li>',
        '<li data-meta="authority-link" data-href="/lattice-system/formalization/legacy/"><a href="/lattice-system/formalization/legacy/">Current authority: complete interim legacy catalogue</a></li>',
        "</ul>",
        "",
    ]


def record_lines(
    record: dict[str, Any],
    source_items: dict[str, dict[str, Any]],
    sources: dict[str, dict[str, Any]],
    relation_filter: str | None = None,
) -> list[str]:
    """Render one record as escaped, structured raw HTML for Kramdown."""
    def field(label: str, name: str, value: Any, **attributes: Any) -> list[str]:
        """Render one visible label/value pair with escaped data attributes."""
        rendered_attributes = "".join(
            f' data-{key.replace("_", "-")}="{html_text(item)}"'
            for key, item in attributes.items()
        )
        return [
            f'<dt data-label-for="{html_text(name)}">{html_text(label)}</dt>',
            f'<dd data-field="{html_text(name)}"{rendered_attributes}>{html_text(value)}</dd>',
        ]

    lines = [
        f'<article id="record-{html_text(record["id"])}" data-record-id="{html_text(record["id"])}">',
        f'<h3 data-field="summary">{html_text(record["summary"])}</h3>',
        "<dl>",
    ]
    for label, name, value in (
        ("Record ID", "record-id", record["id"]),
        ("Lean declaration", "lean-name", record["lean_name"]),
        ("Human status", "human-status", human_status(record)),
        ("Implementation state", "implementation-state", record["implementation_state"]),
        ("Source coverage", "source-coverage", record["source_coverage"]),
        ("Trust state", "trust-state", record["trust_state"]),
        ("Capstone", "capstone", str(record["capstone"]).lower()),
        ("Module", "module", record["module"]),
    ):
        lines.extend(field(label, name, value))
    dependencies = record["axiom_dependencies"]
    if dependencies:
        for item in dependencies:
            lines.extend(field("Axiom dependency", "axiom-dependency", item))
    else:
        lines.extend(field("Axiom dependency", "axiom-dependency", "none", empty="true"))
    for relation in record["source_relations"]:
        item = source_items[relation["source_item_id"]]
        if relation_filter is not None and item["source_id"] != relation_filter:
            continue
        source = sources[item["source_id"]]
        lines.extend(
            field(
                "Citation",
                "citation",
                f"{source.get('title', source['id'])}, {locator(item)} — {item['title']}",
                relation=relation["relation"],
                source_id=item["source_id"],
                source_item_id=item["id"],
            )
        )
    lines.extend(("</dl>", "</article>", ""))
    return lines


def source_for_record(record: dict[str, Any], item_map: dict[str, dict[str, Any]], source_id: str) -> bool:
    """Return whether a record has any typed relation to a source."""
    return any(item_map[edge["source_item_id"]]["source_id"] == source_id for edge in record["source_relations"])


def index_row(
    kind: str,
    attributes: dict[str, Any],
    visible_text: str,
    href: str | None = None,
) -> str:
    """Render one centrally escaped index row with exact attributes and text."""
    rendered = "".join(
        f' data-{name}="{html_text(value)}"' for name, value in attributes.items()
    )
    content = html_text(visible_text)
    if href is not None:
        rendered += f' data-href="{html_text(href)}"'
        content = f'<a href="{html_text(href)}">{content}</a>'
    return f'<li data-row-kind="{html_text(kind)}"{rendered}>{content}</li>'


def render_marker(
    specification: str,
    aggregate: dict[str, Any],
    revision: str,
) -> str:
    """Render one declared marker from the canonical aggregate only."""
    tokens = specification.split()
    if not tokens:
        raise ValueError("empty generated marker specification")
    kind = tokens[0]
    argument = tokens[1] if len(tokens) == 2 else None
    if len(tokens) > 2:
        raise ValueError(f"invalid generated marker specification: {specification}")
    records = aggregate["records"]
    sources = {item["id"]: item for item in aggregate["sources"]}
    source_items = {item["id"]: item for item in aggregate["source_items"]}
    topics = {item["id"]: item for item in aggregate["topics"]}
    lines = metadata(aggregate, revision)

    if kind == "overview" and argument is None:
        lines.extend(
            (
                "## Generated catalogue snapshot",
                "",
                '<ul data-index="overview">',
                index_row(
                    "overview-counts",
                    {
                        "record-count": len(records),
                        "source-count": len(sources),
                        "topic-count": len(topics),
                    },
                    f"This prototype snapshot contains {len(records)} records, "
                    f"{len(sources)} sources, and {len(topics)} topics.",
                ),
                "</ul>",
                "",
                "- [Browse generated source projections](/lattice-system/formalization/sources/)",
                "- [Browse generated topic projections](/lattice-system/formalization/topics/)",
                "- [Browse generated status summary](/lattice-system/formalization/status/)",
                "",
            )
        )
    elif kind == "status" and argument is None:
        counts: dict[str, int] = {}
        for record in records:
            label = human_status(record)
            counts[label] = counts.get(label, 0) + 1
        lines.extend(("## Generated status summary", "", '<ul data-index="status">'))
        for label in sorted(counts):
            lines.append(
                index_row(
                    "status",
                    {"status-label": label, "record-count": counts[label]},
                    f"{label}: {counts[label]}",
                )
            )
        lines.extend(("</ul>", "", "The three machine status dimensions remain visible on every record page.", ""))
    elif kind == "source-index" and argument is None:
        lines.extend(("## Generated source index", "", '<ul data-index="sources">'))
        for source_id, source in sorted(sources.items()):
            count = sum(source_for_record(record, source_items, source_id) for record in records)
            lines.append(
                index_row(
                    "source",
                    {
                        "source-id": source_id,
                        "source-title": source.get("title", source_id),
                        "record-count": count,
                    },
                    f'{source.get("title", source_id)}: {count} related record(s)',
                    f"/lattice-system/formalization/sources/{source_id}/",
                )
            )
        project_count = sum(record["origin"] == "project_original" for record in records)
        lines.append(
            index_row(
                "project-original",
                {"source-id": "foundations", "record-count": project_count},
                f"Project-original foundations: {project_count} record(s)",
                "/lattice-system/formalization/sources/foundations/",
            )
        )
        lines.extend(("</ul>", ""))
    elif kind == "source" and argument in sources:
        selected = [record for record in records if source_for_record(record, source_items, argument)]
        lines.extend(("## Generated records related to this source", ""))
        if not selected:
            lines.extend(("No prototype record currently has a typed relation to this source.", ""))
        for record in selected:
            lines.extend(record_lines(record, source_items, sources, argument))
    elif kind == "project-original" and argument is None:
        selected = [record for record in records if record["origin"] == "project_original"]
        lines.extend(("## Generated project-original foundation records", ""))
        if not selected:
            lines.extend(("No project-original record is present in this prototype catalogue.", ""))
        for record in selected:
            lines.extend(record_lines(record, source_items, sources))
    elif kind == "topic-index" and argument is None:
        lines.extend(("## Generated topic index", "", '<ul data-index="topics">'))
        for topic_id, topic in sorted(topics.items()):
            count = sum(topic_id in record["topic_ids"] for record in records)
            lines.append(
                index_row(
                    "topic",
                    {
                        "topic-id": topic_id,
                        "topic-label": topic["label"],
                        "record-count": count,
                    },
                    f'{topic["label"]}: {count} record(s)',
                    f"/lattice-system/formalization/topics/{topic_id}/",
                )
            )
        lines.extend(("</ul>", ""))
    elif kind == "topic" and argument in topics:
        selected = [record for record in records if argument in record["topic_ids"]]
        lines.extend(
            (
                f'<h2 data-heading-kind="topic" data-topic-id="{html_text(argument)}" '
                f'data-topic-label="{html_text(topics[argument]["label"])}">'
                f'Generated {html_text(topics[argument]["label"])} records</h2>',
                "",
            )
        )
        for record in selected:
            lines.extend(record_lines(record, source_items, sources))
    else:
        raise ValueError(f"unknown generated marker specification: {specification}")

    return (
        f"<!-- formalization-status-generated:start {specification} -->\n"
        + "\n".join(lines).rstrip()
        + "\n<!-- formalization-status-generated:end -->"
    )


def replace_markers(source_root: Path, aggregate: dict[str, Any], revision: str) -> int:
    """Replace every explicit marker in the staged documentation tree."""
    count = 0
    seen_specs: set[str] = set()
    for path in sorted(source_root.rglob("*.md")):
        text = path.read_text(encoding="utf-8")

        def replacement(match: re.Match[str]) -> str:
            nonlocal count
            specification = match.group(1)
            if specification in seen_specs:
                raise ValueError(
                    f"duplicate marker collision at {path.relative_to(source_root)}: {specification}"
                )
            seen_specs.add(specification)
            count += 1
            return render_marker(specification, aggregate, revision)

        replaced = MARKER_RE.sub(replacement, text)
        if replaced != text:
            with path.open("w", encoding="utf-8", newline="\n") as output:
                output.write(replaced)
    if count == 0:
        raise ValueError("no formalization-status generated markers found")
    return count


def safe_output(repo_root: Path, requested: Path) -> Path:
    """Resolve a fresh output directory under the repository scratch root."""
    if requested.exists() or requested.is_symlink():
        raise ValueError(f"output directory must not exist: {requested}")
    resolved = requested.resolve(strict=False)
    scratch = (repo_root / ".self-local" / "tmp").resolve()
    if resolved == scratch or scratch not in resolved.parents:
        raise ValueError("output directory must be below .self-local/tmp")
    return resolved


def validate_marker_ownership(docs_root: Path, expected_specs: set[str]) -> None:
    """Require empty, unique, complete canonical markers and a free machine-output root."""
    machine_root = docs_root / "formalization-status"
    if machine_root.exists() or machine_root.is_symlink():
        raise ValueError(f"committed documentation owns generated machine output: {machine_root}")
    found: list[str] = []
    start_count = 0
    end_count = 0
    for path in sorted(docs_root.rglob("*.md")):
        text = path.read_text(encoding="utf-8")
        start_count += text.count("<!-- formalization-status-generated:start ")
        end_count += text.count("<!-- formalization-status-generated:end -->")
        for match in OWNERSHIP_MARKER_RE.finditer(text):
            specification, body = match.groups()
            if body.strip():
                raise ValueError(
                    f"canonical generated marker body must be empty: {path.relative_to(docs_root)}: {specification}"
                )
            found.append(specification)
    if start_count != end_count or len(found) != start_count:
        raise ValueError("canonical generated markers are malformed or unpaired")
    if len(found) != len(set(found)):
        raise ValueError("canonical generated marker specifications collide")
    if set(found) != expected_specs:
        raise ValueError(
            f"canonical generated marker set mismatch: expected {sorted(expected_specs)}, found {sorted(found)}"
        )


def canonical_marker_specs(repo_root: Path) -> set[str]:
    """Derive the required canonical marker ownership from checked-in registries."""
    root = repo_root / "formalization-status/v1"
    sources = json.loads((root / "sources.json").read_text(encoding="utf-8"))["sources"]
    topics = json.loads((root / "topics.json").read_text(encoding="utf-8"))["topics"]
    result = {"overview", "project-original", "source-index", "status", "topic-index"}
    result.update(f"source {item['id']}" for item in sources)
    result.update(f"topic {item['id']}" for item in topics)
    return result


def run_self_tests(repo_root: Path) -> None:
    """Exercise escaping, status derivation, and marker rejection regressions."""
    assert html_text('<script> & "') == "&lt;script&gt; &amp; &quot;"
    assert REVISION_RE.fullmatch("refs/pull/5229/merge") is not None
    assert REVISION_RE.fullmatch("bad revision") is None
    fixture = {
        "implementation_state": "implemented",
        "declaration_kind": "theorem",
        "trust_state": "axiom_free",
    }
    assert human_status(fixture) == "proved"
    try:
        render_marker(
            "topic missing",
            {
                "catalog_state": "prototype",
                "input_sha256": "0" * 64,
                "records": [],
                "schema_version": 1,
                "source_items": [],
                "sources": [],
                "topics": [],
            },
            "r",
        )
    except ValueError:
        pass
    else:
        raise AssertionError("unknown topic marker was accepted")
    project_record = {
        "axiom_dependencies": [],
        "capstone": False,
        "declaration_kind": "definition",
        "id": "project-fixture",
        "implementation_state": "implemented",
        "lean_name": "LatticeSystem.Fixture.value",
        "module": "LatticeSystem.Fixture",
        "origin": "project_original",
        "source_coverage": "not_applicable",
        "source_relations": [],
        "summary": "Lieb's \"theorem\"",
        "topic_ids": ["fixture-topic"],
        "trust_state": "axiom_free",
    }
    project_aggregate = {
        "catalog_state": "prototype",
        "input_sha256": "0" * 64,
        "records": [project_record],
        "schema_version": 1,
        "source_items": [],
        "sources": [],
        "topics": [{"description": "Fixture", "id": "fixture-topic", "label": "Fixture"}],
    }
    project_view = render_marker("project-original", project_aggregate, "r")
    topic_view = render_marker("topic fixture-topic", project_aggregate, "r")
    assert 'id="record-project-fixture"' in project_view
    assert 'id="record-project-fixture"' in topic_view
    assert '<h3 data-field="summary">Lieb&#x27;s &quot;theorem&quot;</h3>' in project_view
    assert '<dt data-label-for="human-status">Human status</dt>' in project_view
    assert '<dd data-field="human-status">definition only</dd>' in project_view
    assert "LatticeSystem.Fixture.value" in project_view
    assert 'data-field="citation"' not in project_view
    liquid_fixture = dict(project_record)
    liquid_fixture["summary"] = '{{ 7 | plus: 1 }} and {% include x %}'
    liquid_aggregate = dict(project_aggregate)
    liquid_aggregate["records"] = [liquid_fixture]
    liquid_view = render_marker("project-original", liquid_aggregate, "r")
    assert "{{" not in liquid_view and "{%" not in liquid_view
    assert "&#123;&#123; 7 | plus: 1 &#125;&#125;" in liquid_view
    hostile = 'Lieb\'s "theorem" {{ 7 | plus: 1 }} {% include x %}'
    literature_record = dict(project_record)
    literature_record.update(
        {
            "id": "literature-fixture",
            "origin": "literature",
            "source_relations": [
                {"relation": "formalizes", "source_item_id": "fixture-item"}
            ],
            "summary": hostile,
        }
    )
    hostile_aggregate = dict(project_aggregate)
    hostile_aggregate.update(
        {
            "records": [literature_record],
            "source_items": [
                {
                    "equations": [],
                    "id": "fixture-item",
                    "item_kind": "theorem",
                    "item_number": "1",
                    "pages": "1",
                    "section": "1",
                    "source_id": "fixture-source",
                    "title": hostile,
                }
            ],
            "sources": [{"id": "fixture-source", "title": hostile}],
            "topics": [
                {"description": hostile, "id": "fixture-topic", "label": hostile}
            ],
        }
    )
    hostile_views = "\n".join(
        render_marker(specification, hostile_aggregate, "r")
        for specification in (
            "source-index",
            "source fixture-source",
            "topic-index",
            "topic fixture-topic",
        )
    )
    assert "{{" not in hostile_views and "{%" not in hostile_views
    assert "Lieb&#x27;s &quot;theorem&quot;" in hostile_views

    scratch = repo_root / ".self-local/tmp"
    scratch.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix="generator-ownership-self-test-", dir=scratch))
    try:
        page = temporary / "page.md"
        page.write_text(
            "before\n<!-- formalization-status-generated:start overview -->\n"
            "<!-- formalization-status-generated:end -->\nafter\n",
            encoding="utf-8",
        )
        validate_marker_ownership(temporary, {"overview"})
        replace_markers(temporary, project_aggregate, "r")
        replaced = page.read_text(encoding="utf-8")
        assert replaced.startswith("before\n") and replaced.endswith("\nafter\n")
        for label, mutation in (
            ("non-empty body", "generated content"),
            (
                "duplicate marker",
                "<!-- formalization-status-generated:start overview -->\n"
                "<!-- formalization-status-generated:end -->",
            ),
        ):
            page.write_text(
                "<!-- formalization-status-generated:start overview -->\n"
                f"{mutation}\n<!-- formalization-status-generated:end -->\n",
                encoding="utf-8",
            )
            try:
                validate_marker_ownership(temporary, {"overview"})
            except ValueError:
                pass
            else:
                raise AssertionError(f"marker ownership accepted {label}")
        page.write_text("no marker\n", encoding="utf-8")
        try:
            validate_marker_ownership(temporary, {"overview"})
        except ValueError:
            pass
        else:
            raise AssertionError("marker ownership accepted a missing marker")
        (temporary / "formalization-status/v1").mkdir(parents=True)
        try:
            validate_marker_ownership(temporary, set())
        except ValueError:
            pass
        else:
            raise AssertionError("marker ownership accepted committed machine output")
    finally:
        shutil.rmtree(temporary)


def parse_args() -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--self-test", action="store_true")
    return parser.parse_args()


def main() -> int:
    """Validate inputs, stage docs, and inject deterministic generated views."""
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    if REVISION_RE.fullmatch(args.revision) is None:
        raise SystemExit("error: revision must be a safe non-empty revision identifier")
    if args.self_test:
        run_self_tests(repo_root)
    try:
        output = safe_output(repo_root, args.output_dir)
        symlinks = [path for path in (repo_root / "docs").rglob("*") if path.is_symlink()]
        if symlinks:
            raise ValueError(f"documentation source contains unsupported symlinks: {symlinks}")
        validate_marker_ownership(repo_root / "docs", canonical_marker_specs(repo_root))
        output.mkdir(parents=True)
        source = output / "source"
        shutil.copytree(repo_root / "docs", source)
        machine = source / "formalization-status" / "v1"
        machine.mkdir(parents=True)
        aggregate_path = machine / "catalog.json"
        subprocess.run(
            [
                sys.executable,
                str(repo_root / "scripts" / "validate_formalization_status.py"),
                "--emit-aggregate",
                str(aggregate_path),
            ],
            cwd=repo_root,
            check=True,
        )
        schema_source = repo_root / "formalization-status" / "v1" / "schema.json"
        shutil.copyfile(schema_source, machine / "schema.json")
        aggregate = json.loads(aggregate_path.read_text(encoding="utf-8"))
        publication = {
            "catalog_state": aggregate["catalog_state"],
            "generated_by": "scripts/generate_formalization_site.py",
            "generator_version": GENERATOR_VERSION,
            "input_sha256": aggregate["input_sha256"],
            "revision": args.revision,
            "schema_version": aggregate["schema_version"],
        }
        with (machine / "publication.json").open("w", encoding="utf-8", newline="\n") as sidecar:
            sidecar.write(json.dumps(publication, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
        marker_count = replace_markers(source, aggregate, args.revision)
        tree_digest = hashlib.sha256()
        for path in sorted(item for item in source.rglob("*") if item.is_file()):
            relative = str(path.relative_to(source))
            tree_digest.update(relative.encode("utf-8") + b"\0")
            tree_digest.update(path.read_bytes() + b"\0")
        generation_text = (
            json.dumps(
                {
                    "generator_version": GENERATOR_VERSION,
                    "input_sha256": aggregate["input_sha256"],
                    "marker_count": marker_count,
                    "revision": args.revision,
                    "source_tree_sha256": tree_digest.hexdigest(),
                },
                indent=2,
                sort_keys=True,
            )
            + "\n"
        )
        with (output / "generation.json").open("w", encoding="utf-8", newline="\n") as generated:
            generated.write(generation_text)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"error: {error}") from error
    print(f"formalization site staged at {output} ({marker_count} generated sections)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
