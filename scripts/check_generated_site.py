#!/usr/bin/env python3
"""Check staged or Jekyll-built formalization-status publication artifacts."""

from __future__ import annotations

import argparse
import hashlib
import html
import html.parser
import json
import posixpath
import re
import shutil
import tempfile
from pathlib import Path
from typing import Any
from urllib.parse import unquote, urlsplit


BASEURL = "/lattice-system"
DIGEST_RE = re.compile(r"[0-9a-f]{64}")
REPO_ROOT = Path(__file__).resolve().parents[1]
AUTHORITATIVE_FORBIDDEN_PHRASES = (
    "catalogue state: prototype",
    "complete interim legacy catalogue",
    "interim legacy catalogue remains authoritative",
    "accepted prototype contract",
    "the json catalogue is a non-authoritative prototype",
    "prototype navigation only",
    "remains incomplete and non-authoritative until the governance cutover",
    "this remains prototype-only status data",
    "until issue #5228",
    "version 1 structured catalogue is not yet complete or authoritative",
)


class PageParser(html.parser.HTMLParser):
    """Parse exact record grammar plus scoped metadata and index structures."""

    def __init__(
        self,
        generated_marker_scoped: bool = False,
        require_generated_container: bool = False,
    ) -> None:
        """Initialize parsing, optionally limiting record grammar to marker comments."""
        super().__init__(convert_charrefs=True)
        self.generated_marker_scoped = generated_marker_scoped
        self.require_generated_container = require_generated_container
        self.generated_scope_active = not generated_marker_scoped
        self.generated_container_specs: list[str] = []
        self.current_generated_container: str | None = None
        self.unowned_generated_tags: list[str] = []
        self.unowned_generated_text: list[str] = []
        self.current_generated_notice: tuple[str, list[str]] | None = None
        self.generated_notices: list[tuple[str, str]] = []
        self.ids: list[str] = []
        self.links: list[str] = []
        self.text: list[str] = []
        self.current_record: str | None = None
        self.record_headings: dict[str, str] = {}
        self.record_fields: dict[
            str, list[tuple[str, str, tuple[tuple[str, str], ...], str]]
        ] = {}
        self.current_heading: list[str] | None = None
        self.record_phase: str | None = None
        self.current_label: tuple[str, list[str]] | None = None
        self.current_record_field: (
            tuple[str, tuple[tuple[str, str], ...], list[str]] | None
        ) = None
        self.metadata_rows: list[tuple[str, str | None, str | None, str]] = []
        self.current_metadata: tuple[str, str | None, list[str]] | None = None
        self.index_rows: list[
            tuple[str, tuple[tuple[str, str], ...], str | None, str]
        ] = []
        self.current_index_row: tuple[str, tuple[tuple[str, str], ...], list[str]] | None = None
        self.structured_anchor_count = 0
        self.structured_anchor_href: str | None = None
        self.structured_in_anchor = False
        self.dynamic_headings: list[tuple[str, tuple[tuple[str, str], ...], str]] = []
        self.record_like_outside_canonical: list[str] = []
        self.current_dynamic_heading: tuple[
            str, tuple[tuple[str, str], ...], list[str]
        ] | None = None

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        """Collect link targets and all HTML ID attributes."""
        attributes = dict(attrs)
        if len(attributes) != len(attrs):
            raise ValueError("HTML element contains duplicate attributes")
        structured_active = self.current_metadata is not None or self.current_index_row is not None
        if structured_active and tag == "li":
            raise ValueError("structured metadata/index rows cannot be nested")
        identifier = attributes.get("id")
        if self.require_generated_container and self.generated_scope_active:
            if self.current_generated_container is None:
                specification = attributes.get("data-formalization-generated")
                if (
                    tag == "div"
                    and specification
                    and set(attributes) == {"data-formalization-generated"}
                ):
                    self.current_generated_container = specification
                    self.generated_container_specs.append(specification)
                else:
                    self.unowned_generated_tags.append(tag)
            elif tag == "div":
                self.unowned_generated_tags.append(tag)
            elif tag == "p":
                notice = attributes.get("data-generated-notice")
                if (
                    notice not in {"editing", "authority", "note"}
                    or set(attributes) != {"data-generated-notice"}
                    or self.current_generated_notice is not None
                ):
                    self.unowned_generated_tags.append(tag)
                else:
                    self.current_generated_notice = (notice, [])
            elif tag == "ul":
                if not (
                    attributes == {"data-generated-metadata": "true"}
                    or (set(attributes) == {"data-index"} and bool(attributes["data-index"]))
                ):
                    self.unowned_generated_tags.append(tag)
            elif tag not in {"li", "a", "h2", "article", "h3", "dl", "dt", "dd"}:
                self.unowned_generated_tags.append(tag)
        exact_article_start = (
            tag == "article"
            and bool(attributes.get("data-record-id"))
            and identifier == f"record-{attributes.get('data-record-id')}"
            and set(attributes) == {"id", "data-record-id"}
        )
        exact_projection_row = (
            tag == "li"
            and attributes.get("data-row-kind") == "record-projection"
            and bool(attributes.get("data-record-id"))
            and identifier == f"record-{attributes.get('data-record-id')}"
            and set(attributes)
            == {
                "id",
                "data-row-kind",
                "data-record-id",
                "data-href",
                "data-projection-kind",
                "data-projection-id",
            }
        )
        record_like = (
            tag in {"article", "dl", "dt", "dd"}
            or any(key in attributes for key in ("data-field", "data-label-for", "data-record-id"))
            or bool(identifier and identifier.startswith("record-"))
        )
        if (
            self.generated_scope_active
            and self.current_record is None
            and record_like
            and not exact_article_start
            and not exact_projection_row
        ):
            self.record_like_outside_canonical.append(tag)
        if identifier is not None:
            self.ids.append(identifier)
        if (
            self.generated_scope_active
            and tag == "article"
            and attributes.get("data-record-id") is not None
        ):
            record_id = attributes["data-record-id"] or ""
            if identifier != f"record-{record_id}" or not record_id:
                raise ValueError("generated record article has inconsistent identity attributes")
            if self.current_record is not None or record_id in self.record_fields:
                raise ValueError(f"duplicate or nested generated record article: {record_id}")
            if set(attributes) != {"id", "data-record-id"}:
                raise ValueError(f"generated record {record_id} has unexpected article attributes")
            self.current_record = record_id
            self.record_fields[record_id] = []
            self.record_phase = "expect-heading"
        elif self.current_record is not None and tag not in {"h3", "dl", "dt", "dd"}:
            raise ValueError(f"generated record {self.current_record} has unexpected tag {tag}")
        if self.current_record is not None and tag == "h3":
            if (
                attributes != {"data-field": "summary"}
                or self.current_heading is not None
                or self.record_phase != "expect-heading"
            ):
                raise ValueError(f"generated record {self.current_record} has an invalid heading")
            self.current_heading = []
            self.record_phase = "in-heading"
        if self.current_record is not None and tag == "dl":
            if attributes or self.record_phase != "after-heading":
                raise ValueError(f"generated record {self.current_record} has an invalid definition list")
            self.record_phase = "expect-label"
        if self.current_record is not None and tag == "dt":
            label_for = attributes.get("data-label-for")
            if (
                set(attributes) != {"data-label-for"}
                or not label_for
                or self.record_phase != "expect-label"
            ):
                raise ValueError(f"generated record {self.current_record} has an invalid field label")
            self.current_label = (label_for, [])
            self.record_phase = "in-label"
        if self.current_record is not None and tag == "dd":
            field_name = attributes.get("data-field")
            if (
                not field_name
                or self.current_record_field is not None
                or self.record_phase != "expect-value"
                or self.current_label is None
                or self.current_label[0] != field_name
            ):
                raise ValueError(f"generated record {self.current_record} has an invalid field value")
            field_attributes = tuple(
                sorted(
                    (
                        key.removeprefix("data-") if key.startswith("data-") else key,
                        value or "",
                    )
                    for key, value in attrs
                    if key != "data-field"
                )
            )
            self.current_record_field = (field_name, field_attributes, [])
            self.record_phase = "in-value"
        if self.current_record is None and tag == "li" and attributes.get("data-meta"):
            if set(attributes) - {"data-meta", "data-href"}:
                raise ValueError("metadata row has unexpected attributes")
            self.current_metadata = (
                attributes["data-meta"] or "",
                attributes.get("data-href"),
                [],
            )
            self.structured_anchor_count = 0
            self.structured_anchor_href = None
            self.structured_in_anchor = False
        if self.current_record is None and tag == "li" and attributes.get("data-row-kind"):
            kind = attributes["data-row-kind"] or ""
            row_attributes = tuple(
                sorted(
                    (key.removeprefix("data-"), value or "")
                    for key, value in attrs
                    if key != "data-row-kind"
                )
            )
            self.current_index_row = (kind, row_attributes, [])
            self.structured_anchor_count = 0
            self.structured_anchor_href = None
            self.structured_in_anchor = False
        if self.current_record is None and tag == "h2" and attributes.get("data-heading-kind"):
            kind = attributes["data-heading-kind"] or ""
            heading_attributes = tuple(
                sorted(
                    (key.removeprefix("data-"), value or "")
                    for key, value in attrs
                    if key != "data-heading-kind"
                )
            )
            self.current_dynamic_heading = (kind, heading_attributes, [])
        structured_active = self.current_metadata is not None or self.current_index_row is not None
        if structured_active and tag == "a":
            if attributes.keys() != {"href"} or self.structured_anchor_count != 0:
                raise ValueError("structured row must contain exactly one plain direct anchor")
            self.structured_anchor_count = 1
            self.structured_anchor_href = attributes.get("href")
            self.structured_in_anchor = True
        elif structured_active and tag != "li":
            raise ValueError(f"structured row has unexpected nested tag {tag}")
        if tag in {"a", "link"} and attributes.get("href") is not None:
            self.links.append(attributes["href"] or "")
        if tag in {"img", "script"} and attributes.get("src") is not None:
            self.links.append(attributes["src"] or "")

    def handle_data(self, data: str) -> None:
        """Collect rendered text for generated-metadata assertions."""
        self.text.append(data)
        generated_text_claimed = False
        if self.current_generated_notice is not None:
            self.current_generated_notice[1].append(data)
            generated_text_claimed = True
        if self.current_heading is not None:
            self.current_heading.append(data)
            generated_text_claimed = True
        if self.current_label is not None and self.record_phase == "in-label":
            self.current_label[1].append(data)
            generated_text_claimed = True
        if self.current_record_field is not None:
            self.current_record_field[2].append(data)
            generated_text_claimed = True
        if (
            self.current_record is not None
            and self.current_heading is None
            and self.current_label is None
            and self.current_record_field is None
            and data.strip()
        ):
            raise ValueError(f"generated record {self.current_record} has untyped visible text")
        if self.current_metadata is not None:
            generated_text_claimed = True
            if self.current_metadata[1] is not None and not self.structured_in_anchor and data.strip():
                raise ValueError("linked metadata row has text outside its direct anchor")
            self.current_metadata[2].append(data)
        if self.current_index_row is not None:
            generated_text_claimed = True
            encoded_href = dict(self.current_index_row[1]).get("href")
            if encoded_href is not None and not self.structured_in_anchor and data.strip():
                raise ValueError("linked index row has text outside its direct anchor")
            self.current_index_row[2].append(data)
        if self.current_dynamic_heading is not None:
            self.current_dynamic_heading[2].append(data)
            generated_text_claimed = True
        if (
            self.generated_scope_active
            and self.current_generated_container is not None
            and data.strip()
            and not generated_text_claimed
        ):
            self.unowned_generated_text.append(data.strip())

    def handle_endtag(self, tag: str) -> None:
        """Finish one normalized rendered list item."""
        if tag == "p" and self.current_generated_notice is not None:
            kind, parts = self.current_generated_notice
            self.generated_notices.append((kind, normalized_rendered_text(parts)))
            self.current_generated_notice = None
        if tag == "a" and (self.current_metadata is not None or self.current_index_row is not None):
            if not self.structured_in_anchor:
                raise ValueError("structured row has a mismatched anchor end")
            self.structured_in_anchor = False
        if tag == "dt" and self.current_record is not None:
            if self.record_phase != "in-label" or self.current_label is None:
                raise ValueError(f"generated record {self.current_record} has a mismatched label end")
            self.record_phase = "expect-value"
        if tag == "dd" and self.current_record_field is not None:
            if self.current_record is None:
                raise ValueError("generated record field closed outside its article")
            name, attributes, parts = self.current_record_field
            if self.current_label is None:
                raise ValueError(f"generated record {self.current_record} lacks a field label")
            _, label_parts = self.current_label
            self.record_fields[self.current_record].append(
                ("".join(label_parts), name, attributes, "".join(parts))
            )
            self.current_record_field = None
            self.current_label = None
            self.record_phase = "expect-label"
        if tag == "h3" and self.current_heading is not None:
            if self.current_record is None or self.current_record in self.record_headings:
                raise ValueError("generated record heading is duplicate or outside its article")
            self.record_headings[self.current_record] = "".join(self.current_heading)
            self.current_heading = None
            self.record_phase = "after-heading"
        if tag == "dl" and self.current_record is not None:
            if self.record_phase != "expect-label" or self.current_label is not None:
                raise ValueError(f"generated record {self.current_record} has an invalid definition list end")
            self.record_phase = "after-fields"
        if tag == "article" and self.current_record is not None:
            if (
                self.current_heading is not None
                or self.current_record_field is not None
                or self.current_label is not None
                or self.record_phase != "after-fields"
            ):
                raise ValueError(f"generated record {self.current_record} has an unclosed field")
            self.current_record = None
            self.record_phase = None
        if tag == "li" and self.current_metadata is not None:
            name, encoded_href, parts = self.current_metadata
            if self.structured_in_anchor:
                raise ValueError("metadata row closes inside its anchor")
            if encoded_href is None:
                if self.structured_anchor_count != 0:
                    raise ValueError("nonlink metadata row contains an anchor")
            elif self.structured_anchor_count != 1 or self.structured_anchor_href != encoded_href:
                raise ValueError("metadata row href is not bound to its direct anchor")
            self.metadata_rows.append(
                (name, encoded_href, self.structured_anchor_href, normalized_rendered_text(parts))
            )
            self.current_metadata = None
        if tag == "li" and self.current_index_row is not None:
            kind, attributes, parts = self.current_index_row
            encoded_href = dict(attributes).get("href")
            if self.structured_in_anchor:
                raise ValueError("index row closes inside its anchor")
            if encoded_href is None:
                if self.structured_anchor_count != 0:
                    raise ValueError("nonlink index row contains an anchor")
            elif self.structured_anchor_count != 1 or self.structured_anchor_href != encoded_href:
                raise ValueError("index row href is not bound to its direct anchor")
            self.index_rows.append(
                (kind, attributes, self.structured_anchor_href, normalized_rendered_text(parts))
            )
            self.current_index_row = None
        if tag == "h2" and self.current_dynamic_heading is not None:
            kind, attributes, parts = self.current_dynamic_heading
            self.dynamic_headings.append((kind, attributes, normalized_rendered_text(parts)))
            self.current_dynamic_heading = None
        if tag == "div" and self.current_generated_container is not None:
            self.current_generated_container = None

    def handle_comment(self, data: str) -> None:
        """Stop record capture at the generated-section boundary."""
        comment = data.strip()
        if comment.startswith("formalization-status-generated:start "):
            if self.generated_marker_scoped and self.generated_scope_active:
                raise ValueError("generated marker sections cannot be nested")
            self.generated_scope_active = True
        elif comment == "formalization-status-generated:end":
            if self.current_record is not None:
                raise ValueError(f"generated record {self.current_record} crosses its marker boundary")
            if self.generated_marker_scoped and not self.generated_scope_active:
                raise ValueError("generated marker section has an unmatched end")
            self.generated_scope_active = False


def canonical_json(value: Any) -> bytes:
    """Serialize repository canonical JSON bytes."""
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode()


def ensure_tree(root: Path) -> Path:
    """Resolve a publication tree and reject all symlinks."""
    resolved = root.resolve(strict=True)
    if not resolved.is_dir():
        raise ValueError(f"not a directory: {root}")
    for path in resolved.rglob("*"):
        if path.is_symlink():
            raise ValueError(f"publication tree contains unsupported symlink: {path}")
    return resolved


def regular_file_bytes(root: Path) -> int:
    """Return the exact uncompressed byte sum after rejecting non-regular entries."""
    tree = ensure_tree(root)
    total = 0
    for path in tree.rglob("*"):
        if path.is_dir():
            continue
        if not path.is_file():
            raise ValueError(f"publication tree contains a non-regular entry: {path}")
        total += path.stat().st_size
    return total


def check_staged_fragment_pins(source: Path) -> None:
    """Require every staged internal fragment to have an explicit render-stable ID."""
    pages: dict[str, tuple[Path, str, set[str]]] = {}
    texts: list[str] = []
    for path in sorted(source.rglob("*.md")):
        text = path.read_text(encoding="utf-8")
        texts.append(text)
        permalink = re.search(r"(?m)^permalink:\s*(\S+)\s*$", text)
        if permalink is None:
            continue
        route = permalink.group(1).strip('"')
        explicit = re.findall(r'<[A-Za-z][^>]*\sid="([^"]+)"[^>]*>', text)
        pinned = re.findall(r"(?m)^#{1,6} .*\n\{:\s+#([^ }]+)\s*\}$", text)
        stable = [*explicit, *pinned]
        duplicates = sorted({item for item in stable if stable.count(item) > 1})
        if duplicates:
            raise ValueError(
                f"staged page has duplicate explicit fragment pins: "
                f"{path.relative_to(source)}: {duplicates}"
            )
        if route in pages:
            raise ValueError(
                f"staged pages have a duplicate permalink: {route}: "
                f"{pages[route][0].relative_to(source)} and {path.relative_to(source)}"
            )
        pages[route] = (path, text, set(stable))

    url_pattern = re.compile(r"/lattice-system/[^\s)\"]+#[^\s)\"]+")
    for text in texts:
        for raw_url in url_pattern.findall(text):
            split = urlsplit(raw_url)
            route = unquote(split.path).removeprefix(BASEURL)
            fragment = unquote(split.fragment)
            target = pages.get(route)
            if target is None:
                raise ValueError(f"staged internal fragment target is missing: {raw_url}")
            if fragment not in target[2]:
                raise ValueError(
                    f"staged internal fragment lacks an explicit render-stable pin: {raw_url} "
                    f"in {target[0].relative_to(source)}"
                )


def load_catalog(path: Path) -> tuple[dict[str, Any], bytes]:
    """Load and require canonical aggregate JSON."""
    raw = path.read_bytes()
    data = json.loads(raw)
    if not isinstance(data, dict) or canonical_json(data) != raw:
        raise ValueError(f"catalogue is not canonical JSON: {path}")
    if not DIGEST_RE.fullmatch(str(data.get("input_sha256", ""))):
        raise ValueError("catalogue has invalid input_sha256")
    return data, raw


def manifest_input_names(manifest: dict[str, Any]) -> list[str]:
    """Return the exact validator input order, including paired cutover evidence."""
    listed = [manifest["schema"]]
    listed.extend(manifest["registries"][key] for key in sorted(manifest["registries"]))
    listed.extend(manifest["record_shards"])
    baseline = manifest.get("cutover_baseline")
    certificate = manifest.get("cutover_certificate")
    if (baseline is None) != (certificate is None):
        raise ValueError("manifest cutover baseline and certificate must be paired")
    if baseline is not None:
        listed.extend([baseline, certificate])
    return listed


def framed_input_digest(inputs: list[tuple[str, bytes]]) -> str:
    """Hash canonical manifest inputs with the validator's exact path framing."""
    digest = hashlib.sha256()
    for name, raw in inputs:
        digest.update(name.encode("utf-8"))
        digest.update(b"\0")
        digest.update(raw)
        digest.update(b"\0")
    return digest.hexdigest()


def recompute_input_digest(catalog: dict[str, Any]) -> None:
    """Independently recompute aggregate content and the framed input digest."""
    root = REPO_ROOT / "formalization-status/v1"
    manifest_path = root / "manifest.json"
    manifest_raw = manifest_path.read_bytes()
    manifest = json.loads(manifest_raw)

    def input_path(name: Any) -> Path:
        if not isinstance(name, str) or not name or "\\" in name:
            raise ValueError(f"unsafe manifest input path: {name!r}")
        candidate = (root / name).resolve(strict=True)
        if root.resolve() not in candidate.parents or not candidate.is_file():
            raise ValueError(f"manifest input escapes the catalogue root: {name!r}")
        return candidate

    listed = manifest_input_names(manifest)
    digest_inputs = [
        ("manifest.json", manifest_raw),
        *[(name, input_path(name).read_bytes()) for name in listed],
    ]
    digest = framed_input_digest(digest_inputs)
    if digest != catalog["input_sha256"]:
        raise ValueError("expected catalogue input_sha256 does not match canonical manifest inputs")
    registries = {
        key: json.loads(input_path(path).read_text(encoding="utf-8"))
        for key, path in manifest["registries"].items()
    }
    records: list[dict[str, Any]] = []
    for shard in manifest["record_shards"]:
        records.extend(json.loads(input_path(shard).read_text(encoding="utf-8"))["records"])
    reconstructed = {
        "catalog_state": manifest["catalog_state"],
        "generated_by": "scripts/validate_formalization_status.py",
        "generator_version": 2,
        "input_sha256": digest,
        "records": sorted(records, key=lambda item: item["id"]),
        "schema_version": manifest["schema_version"],
        "source_items": sorted(registries["source_items"]["source_items"], key=lambda item: item["id"]),
        "sources": sorted(registries["sources"]["sources"], key=lambda item: item["id"]),
        "topics": sorted(registries["topics"]["topics"], key=lambda item: item["id"]),
    }
    if catalog != reconstructed:
        raise ValueError("expected catalogue content differs from independently aggregated manifest inputs")


def publication_file(site: Path, url_path: str) -> Path:
    """Map one safe baseurl publication path to a built-site file."""
    site = site.resolve()
    decoded = unquote(url_path)
    if "\\" in decoded or not decoded.startswith(BASEURL + "/"):
        raise ValueError(f"unsafe internal publication path: {url_path}")
    relative = decoded.removeprefix(BASEURL).lstrip("/")
    parts = relative.split("/")
    if any(part in {"", ".", ".."} for part in parts[:-1]) or ".." in parts:
        raise ValueError(f"unsafe internal publication path: {url_path}")
    normalized = posixpath.normpath("/" + relative).lstrip("/")
    if relative.endswith("/"):
        normalized = normalized.rstrip("/") + "/index.html"
    candidate = (site / normalized).resolve(strict=False)
    if site != candidate and site not in candidate.parents:
        raise ValueError(f"publication path escapes site: {url_path}")
    return candidate


def parse_site(site: Path) -> dict[Path, PageParser]:
    """Parse every HTML file and reject duplicate IDs per document."""
    result: dict[Path, PageParser] = {}
    for path in sorted(site.rglob("*.html")):
        parser = PageParser()
        parser.feed(path.read_text(encoding="utf-8"))
        duplicates = sorted({identifier for identifier in parser.ids if parser.ids.count(identifier) > 1})
        if duplicates:
            raise ValueError(f"duplicate HTML IDs in {path.relative_to(site)}: {duplicates}")
        result[path.resolve()] = parser
    return result


def check_links(site: Path, pages: dict[Path, PageParser]) -> None:
    """Check all baseurl-internal paths and HTML fragments."""
    for page, parser in pages.items():
        for href in parser.links:
            split = urlsplit(href)
            if split.scheme or split.netloc or not split.path.startswith(BASEURL + "/"):
                continue
            target = publication_file(site, split.path)
            if not target.is_file():
                raise ValueError(f"broken internal link from {page.relative_to(site)}: {href}")
            if split.fragment and target.suffix == ".html":
                target_parser = pages.get(target.resolve())
                if target_parser is None or unquote(split.fragment) not in target_parser.ids:
                    raise ValueError(f"broken internal fragment from {page.relative_to(site)}: {href}")


def required_page(site: Path, relative: str, pages: dict[Path, PageParser]) -> PageParser:
    """Return one required HTML page or fail clearly."""
    path = (site / relative).resolve()
    if path not in pages:
        raise ValueError(f"required generated page is missing: {relative}")
    return pages[path]


def reject_authority_contradictions(
    catalog: dict[str, Any], texts: list[tuple[str, str]]
) -> None:
    """Reject stale prototype/legacy-authority claims across an authoritative tree."""
    if catalog.get("catalog_state") != "authoritative":
        return
    for label, text in texts:
        lowered = " ".join(text.lower().split())
        for phrase in AUTHORITATIVE_FORBIDDEN_PHRASES:
            if phrase in lowered:
                raise ValueError(
                    f"{label}: authoritative publication contains stale authority prose {phrase!r}"
                )


def assert_metadata(parser: PageParser, catalog: dict[str, Any], revision: str, label: str) -> None:
    """Require visible state, schema, digest, revision, and generated notice."""
    authoritative = catalog["catalog_state"] == "authoritative"
    authority_phrase = (
        "validated version 1 catalogue"
        if authoritative
        else "complete interim legacy catalogue"
    )
    text = " ".join(" ".join(parser.text).split())
    for expected in (
        "Generated formalization-status view",
        authority_phrase,
    ):
        if expected not in text:
            raise ValueError(f"{label}: missing generated metadata {expected!r}")
    catalog_href = f"{BASEURL}/formalization-status/v1/catalog.json"
    schema_href = f"{BASEURL}/formalization-status/v1/schema.json"
    publication_href = f"{BASEURL}/formalization-status/v1/publication.json"
    authority_href = (
        catalog_href if authoritative else f"{BASEURL}/formalization/legacy/"
    )
    authority_label = (
        "Current authority: validated version 1 catalogue"
        if authoritative
        else "Current authority: complete interim legacy catalogue"
    )
    expected_rows = [
        ("catalog-state", None, None, f"Catalogue state: {catalog['catalog_state']}"),
        ("schema-version", None, None, f"Schema version: {catalog['schema_version']}"),
        ("input-sha256", None, None, f"Input SHA-256: {catalog['input_sha256']}"),
        ("revision", None, None, f"Deploy revision: {revision}"),
        ("catalog-link", catalog_href, catalog_href, "Machine data: version 1 catalogue"),
        ("schema-link", schema_href, schema_href, "Schema: version 1 schema"),
        (
            "publication-link",
            publication_href,
            publication_href,
            "Build metadata: publication sidecar",
        ),
        (
            "authority-link",
            authority_href,
            authority_href,
            authority_label,
        ),
    ]
    if parser.metadata_rows != expected_rows:
        raise ValueError(f"{label}: generated metadata contains duplicates or additive poisoning")


def derived_human_label(record: dict[str, Any]) -> str:
    """Independently derive the human label from orthogonal status fields."""
    if record["implementation_state"] == "in_progress":
        return "in progress"
    if record["declaration_kind"] == "axiom":
        return "documented axiom"
    if record["declaration_kind"] not in {"lemma", "theorem"}:
        return "definition only"
    if record["trust_state"] == "depends_on_documented_axioms":
        return "proved with documented axioms"
    return "proved"


def source_locator(item: dict[str, Any]) -> str:
    """Independently format the complete typed source locator."""
    result = (
        f"{item['item_kind']} {item['item_number']}"
        if item["item_number"] is not None
        else item["item_kind"]
    )
    if item["section"] is not None:
        result += f"; section {item['section']}"
    if item["equations"]:
        result += "; equations " + ", ".join(item["equations"])
    if item["pages"] is not None:
        result += f"; pages {item['pages']}"
    return result


def normalized_rendered_text(parts: list[str]) -> str:
    """Normalize HTML text-node boundaries without weakening field contents."""
    value = " ".join(" ".join(parts).split())
    return re.sub(r"\s+([;,:.!?])", r"\1", value)


def expected_record_structure(
    record: dict[str, Any],
    catalog: dict[str, Any],
) -> tuple[str, list[tuple[str, str, tuple[tuple[str, str], ...], str]]]:
    """Independently compute the exact heading and ordered typed field sequence."""
    fields: list[tuple[str, str, tuple[tuple[str, str], ...], str]] = [
        ("Record ID", "record-id", (), record["id"]),
        ("Lean declaration", "lean-name", (), record["lean_name"]),
        ("Declaration kind", "declaration-kind", (), record["declaration_kind"]),
        ("Human status", "human-status", (), derived_human_label(record)),
        ("Implementation state", "implementation-state", (), record["implementation_state"]),
        ("Source coverage", "source-coverage", (), record["source_coverage"]),
        ("Trust state", "trust-state", (), record["trust_state"]),
        ("Capstone", "capstone", (), str(record["capstone"]).lower()),
        ("Module", "module", (), record["module"]),
        ("Source path", "source-path", (), record["source_path"]),
        ("Origin", "origin", (), record["origin"]),
    ]
    fields.extend(("Topic", "topic-id", (), topic_id) for topic_id in record["topic_ids"])
    dependencies = record["axiom_dependencies"]
    if dependencies:
        fields.extend(
            ("Axiom dependency", "axiom-dependency", (), dependency)
            for dependency in dependencies
        )
    else:
        fields.append(
            ("Axiom dependency", "axiom-dependency", (("empty", "true"),), "none")
        )
    if record["proof_guide_anchor"] is None:
        fields.append(
            ("Proof-guide anchor", "proof-guide-anchor", (("empty", "true"),), "none")
        )
    else:
        fields.append(
            ("Proof-guide anchor", "proof-guide-anchor", (), record["proof_guide_anchor"])
        )
    item_map = {item["id"]: item for item in catalog["source_items"]}
    source_map = {item["id"]: item for item in catalog["sources"]}
    for relation in record["source_relations"]:
        item = item_map[relation["source_item_id"]]
        source = source_map[item["source_id"]]
        fields.append(
            (
                "Citation",
                "citation",
                (
                    ("relation", relation["relation"]),
                    ("source-id", item["source_id"]),
                    ("source-item-id", item["id"]),
                ),
                f"{source.get('title', source['id'])}, {source_locator(item)} — {item['title']}",
            )
        )
    return record["summary"], fields


def marker_body(path: Path, specification: str) -> str:
    """Return exactly one generated marker body from staged Markdown."""
    text = path.read_text(encoding="utf-8")
    pattern = re.compile(
        rf"(?ms)^<!-- formalization-status-generated:start {re.escape(specification)} -->\n"
        r"(.*?)^<!-- formalization-status-generated:end -->$"
    )
    matches = pattern.findall(text)
    if len(matches) != 1:
        raise ValueError(f"{path}: expected exactly one marker {specification!r}")
    return matches[0]


def parse_record_html(body: str, label: str) -> PageParser:
    """Parse structured raw or rendered HTML and reject duplicate identities."""
    generated_marker_scoped = "formalization-status-generated:start " in body
    require_generated_container = (
        generated_marker_scoped or "data-formalization-generated=" in body
    )
    parser = PageParser(
        generated_marker_scoped=generated_marker_scoped,
        require_generated_container=require_generated_container,
    )
    parser.feed(body)
    duplicates = sorted({identifier for identifier in parser.ids if parser.ids.count(identifier) > 1})
    if duplicates:
        raise ValueError(f"{label}: duplicate record HTML IDs: {duplicates}")
    if (
        parser.current_record is not None
        or parser.current_record_field is not None
        or parser.current_metadata is not None
        or parser.current_index_row is not None
        or parser.structured_in_anchor
        or parser.current_generated_notice is not None
        or parser.current_generated_container is not None
        or (generated_marker_scoped and parser.generated_scope_active)
    ):
        raise ValueError(f"{label}: unclosed generated record structure")
    return parser


def expected_marker_body(
    specification: str, catalog: dict[str, Any], revision: str
) -> str:
    """Render and extract the generator's exact owned marker serialization."""
    from generate_formalization_site import render_marker

    rendered = render_marker(specification, catalog, revision)
    prefix = f"<!-- formalization-status-generated:start {specification} -->\n"
    suffix = "\n<!-- formalization-status-generated:end -->"
    if not rendered.startswith(prefix) or not rendered.endswith(suffix):
        raise ValueError(f"generator returned malformed marker {specification}")
    return rendered[len(prefix) : -len(suffix)] + "\n"


def require_generated_ownership(
    parser: PageParser, label: str, expected_specification: str | None = None
) -> None:
    """Reject content outside the one typed generator-owned container."""
    if not parser.require_generated_container:
        return
    if len(parser.generated_container_specs) != 1:
        raise ValueError(f"{label}: expected exactly one typed generated container")
    if (
        expected_specification is not None
        and parser.generated_container_specs != [expected_specification]
    ):
        raise ValueError(f"{label}: generated container specification differs")
    if parser.unowned_generated_tags or parser.unowned_generated_text:
        raise ValueError(
            f"{label}: generated region contains unowned tags/text: "
            f"{parser.unowned_generated_tags}, {parser.unowned_generated_text}"
        )


def validate_record_blocks(
    parser: PageParser,
    expected_records: list[dict[str, Any]],
    catalog: dict[str, Any],
    label: str,
) -> None:
    """Require exact membership, heading, attributes, order, and field values."""
    require_generated_ownership(parser, label)
    if parser.record_like_outside_canonical:
        raise ValueError(
            f"{label}: record-like structure exists outside the exact canonical article: "
            f"{parser.record_like_outside_canonical}"
        )
    expected_ids = {record["id"] for record in expected_records}
    actual_ids = set(parser.record_fields)
    if actual_ids != expected_ids or set(parser.record_headings) != expected_ids:
        raise ValueError(
            f"{label}: record IDs differ; expected {sorted(expected_ids)}, found {sorted(actual_ids)}"
        )
    for record in expected_records:
        expected_heading, expected_fields = expected_record_structure(record, catalog)
        identifier = record["id"]
        if parser.record_headings[identifier] != expected_heading:
            raise ValueError(
                f"{label}/{identifier}: heading differs; expected {expected_heading!r}, "
                f"found {parser.record_headings[identifier]!r}"
            )
        if parser.record_fields[identifier] != expected_fields:
            raise ValueError(
                f"{label}/{identifier}: ordered structured fields differ; "
                f"expected {expected_fields!r}, found {parser.record_fields[identifier]!r}"
            )


def records_for_source(catalog: dict[str, Any], source_id: str) -> list[dict[str, Any]]:
    """Independently project records with any typed relation to a source."""
    item_map = {item["id"]: item for item in catalog["source_items"]}
    return [
        record
        for record in catalog["records"]
        if any(
            item_map[relation["source_item_id"]]["source_id"] == source_id
            for relation in record["source_relations"]
        )
    ]


def records_for_topic(catalog: dict[str, Any], topic_id: str) -> list[dict[str, Any]]:
    """Independently project records assigned to a controlled topic."""
    return [record for record in catalog["records"] if topic_id in record["topic_ids"]]


def expected_source_index_rows(
    catalog: dict[str, Any],
) -> list[tuple[str, tuple[tuple[str, str], ...], str | None, str]]:
    """Independently derive exact source-index attributes and visible values."""
    rows = []
    for source in sorted(catalog["sources"], key=lambda item: item["id"]):
        count = len(records_for_source(catalog, source["id"]))
        title = source.get("title", source["id"])
        href = f"{BASEURL}/formalization/sources/{source['id']}/"
        rows.append(
            (
                "source",
                (
                    ("href", href),
                    ("record-count", str(count)),
                    ("source-id", source["id"]),
                    ("source-title", title),
                ),
                href,
                f"{title}: {count} related record(s)",
            )
        )
    project_count = sum(record["origin"] == "project_original" for record in catalog["records"])
    rows.append(
        (
            "project-original",
            (
                ("href", f"{BASEURL}/formalization/sources/foundations/"),
                ("record-count", str(project_count)),
                ("source-id", "foundations"),
            ),
            f"{BASEURL}/formalization/sources/foundations/",
            f"Project-original foundations: {project_count} record(s)",
        )
    )
    return rows


def expected_overview_index_rows(
    catalog: dict[str, Any],
) -> list[tuple[str, tuple[tuple[str, str], ...], str | None, str]]:
    """Independently derive exact overview counts and navigation rows."""
    rows = [
        (
            "overview-counts",
            (
                ("record-count", str(len(catalog["records"]))),
                ("source-count", str(len(catalog["sources"]))),
                ("topic-count", str(len(catalog["topics"]))),
            ),
            None,
            f"This {catalog['catalog_state']} snapshot contains {len(catalog['records'])} records, "
            f"{len(catalog['sources'])} sources, and {len(catalog['topics'])} topics.",
        )
    ]
    for navigation_id, visible in (
        ("sources", "Browse generated source projections"),
        ("topics", "Browse generated topic projections"),
        ("status", "Browse generated status summary"),
    ):
        href = f"{BASEURL}/formalization/{navigation_id}/"
        rows.append(
            (
                "overview-navigation",
                (("href", href), ("navigation-id", navigation_id)),
                href,
                visible,
            )
        )
    return rows


def expected_topic_index_rows(
    catalog: dict[str, Any],
) -> list[tuple[str, tuple[tuple[str, str], ...], str | None, str]]:
    """Independently derive exact topic-index attributes and visible values."""
    rows = []
    for topic in sorted(catalog["topics"], key=lambda item: item["id"]):
        count = len(records_for_topic(catalog, topic["id"]))
        href = f"{BASEURL}/formalization/topics/{topic['id']}/"
        rows.append(
            (
                "topic",
                (
                    ("href", href),
                    ("record-count", str(count)),
                    ("topic-id", topic["id"]),
                    ("topic-label", topic["label"]),
                ),
                href,
                f"{topic['label']}: {count} record(s)",
            )
        )
    return rows


def canonical_record_href(record_id: str) -> str:
    """Return the independently derived stable human record route."""
    return f"{BASEURL}/formalization/records/{record_id}/"


def expected_projection_rows(
    records: list[dict[str, Any]], projection_kind: str, projection_id: str
) -> list[tuple[str, tuple[tuple[str, str], ...], str | None, str]]:
    """Derive one exact count and the compact ordered links for a projection."""
    result = [
        (
            "projection-count",
            (
                ("projection-id", projection_id),
                ("projection-kind", projection_kind),
                ("record-count", str(len(records))),
            ),
            None,
            f"{len(records)} record(s)",
        )
    ]
    for record in records:
        href = canonical_record_href(record["id"])
        result.append(
            (
                "record-projection",
                (
                    ("href", href),
                    ("id", f"record-{record['id']}"),
                    ("projection-id", projection_id),
                    ("projection-kind", projection_kind),
                    ("record-id", record["id"]),
                ),
                href,
                record["summary"],
            )
        )
    return result


def expected_status_index_rows(
    catalog: dict[str, Any],
) -> list[tuple[str, tuple[tuple[str, str], ...], str | None, str]]:
    """Independently derive exact derived-status rows."""
    counts: dict[str, int] = {}
    for record in catalog["records"]:
        label = derived_human_label(record)
        counts[label] = counts.get(label, 0) + 1
    result = []
    for label in sorted(counts):
        result.append(
            (
                "status-count",
                (("record-count", str(counts[label])), ("status-label", label)),
                None,
                f"{label}: {counts[label]}",
            )
        )
        result.extend(
            expected_projection_rows(
                [record], "status", label
            )[1]
            for record in catalog["records"]
            if derived_human_label(record) == label
        )
    return result


def require_index_rows(
    parser: PageParser,
    expected: list[tuple[str, tuple[tuple[str, str], ...], str | None, str]],
    label: str,
    *,
    allow_canonical_record: bool = False,
) -> None:
    """Require exact structured dynamic-row membership, attributes, order, and text."""
    require_generated_ownership(parser, label)
    if parser.record_like_outside_canonical:
        raise ValueError(
            f"{label}: record-like structure is forbidden outside an exact canonical article: "
            f"{parser.record_like_outside_canonical}"
        )
    if parser.record_fields and not allow_canonical_record:
        raise ValueError(f"{label}: canonical record article is forbidden on this page")
    if parser.index_rows != expected:
        raise ValueError(
            f"{label}: structured index rows differ; expected {expected!r}, "
            f"found {parser.index_rows!r}"
        )


def check_staged_record_outputs(source: Path, catalog: dict[str, Any]) -> None:
    """Require an exact one-file-per-record generated Markdown root."""
    root = source / "formalization" / "records"
    if not root.is_dir() or root.is_symlink():
        raise ValueError("staged canonical record root is missing or unsafe")
    expected = {f"{record['id']}.md" for record in catalog["records"]}
    actual: set[str] = set()
    for path in root.rglob("*"):
        if path.is_symlink() or not path.is_file() or path.parent != root:
            raise ValueError(f"unexpected staged canonical record output: {path}")
        actual.add(path.name)
    if actual != expected:
        raise ValueError(
            f"staged canonical record filenames differ: expected {sorted(expected)}, "
            f"found {sorted(actual)}"
        )
    for record in catalog["records"]:
        path = root / f"{record['id']}.md"
        route = f"/formalization/records/{record['id']}/"
        text = path.read_text(encoding="utf-8")
        if re.findall(r"(?m)^permalink:\s*(\S+)\s*$", text) != [route]:
            raise ValueError(f"staged canonical record has the wrong permalink: {record['id']}")


def check_built_record_outputs(site: Path, catalog: dict[str, Any]) -> None:
    """Require an exact one-directory-per-record rendered HTML root."""
    root = site / "formalization" / "records"
    if not root.is_dir() or root.is_symlink():
        raise ValueError("rendered canonical record root is missing or unsafe")
    expected = {record["id"] for record in catalog["records"]}
    actual = {path.name for path in root.iterdir() if path.is_dir() and not path.is_symlink()}
    if actual != expected:
        raise ValueError(
            f"rendered canonical record directories differ: expected {sorted(expected)}, "
            f"found {sorted(actual)}"
        )
    for path in root.rglob("*"):
        if path.is_symlink():
            raise ValueError(f"rendered canonical record output contains a symlink: {path}")
        if path.is_file() and (path.name != "index.html" or path.parent.parent != root):
            raise ValueError(f"unexpected rendered canonical record output: {path}")
        if path.is_dir() and path.parent != root:
            raise ValueError(f"unexpected nested rendered canonical record directory: {path}")


def check_built_site(
    site_dir: Path,
    source_dir: Path,
    expected_catalog_path: Path,
    revision: str,
) -> None:
    """Validate the complete rendered site and stable publication interface."""
    site = ensure_tree(site_dir)
    source = ensure_tree(source_dir)
    expected_path = expected_catalog_path.resolve(strict=True)
    if source in expected_path.parents:
        raise ValueError("expected catalogue must be generated independently outside the staged source")
    expected_catalog, expected_raw = load_catalog(expected_path)
    recompute_input_digest(expected_catalog)
    catalog_path = site / "formalization-status/v1/catalog.json"
    source_catalog_path = source / "formalization-status/v1/catalog.json"
    catalog, catalog_raw = load_catalog(catalog_path)
    _, source_catalog_raw = load_catalog(source_catalog_path)
    if catalog_raw != source_catalog_raw or catalog_raw != expected_raw or catalog != expected_catalog:
        raise ValueError("built/staged catalogue differs byte-for-byte from the independent expected catalogue")
    built_schema = (site / "formalization-status/v1/schema.json").read_bytes()
    source_schema = (source / "formalization-status/v1/schema.json").read_bytes()
    canonical_schema = (REPO_ROOT / "formalization-status/v1/schema.json").read_bytes()
    if not (built_schema == source_schema == canonical_schema):
        raise ValueError("published schema is not byte-identical to the canonical schema")
    built_publication = (site / "formalization-status/v1/publication.json").read_bytes()
    source_publication = (source / "formalization-status/v1/publication.json").read_bytes()
    if built_publication != source_publication:
        raise ValueError("built publication sidecar differs from the staged sidecar")
    publication = json.loads(built_publication)
    if canonical_json(publication) != built_publication or publication != {
        "catalog_state": catalog["catalog_state"],
        "generated_by": "scripts/generate_formalization_site.py",
        "generator_version": 2,
        "input_sha256": catalog["input_sha256"],
        "revision": revision,
        "schema_version": catalog["schema_version"],
    }:
        raise ValueError("publication sidecar metadata does not match the build")

    pages = parse_site(site)
    check_built_record_outputs(site, catalog)
    reject_authority_contradictions(
        catalog,
        [
            (str(path.relative_to(site)), " ".join(parser.text))
            for path, parser in pages.items()
        ],
    )
    check_links(site, pages)
    overview = required_page(site, "formalization/index.html", pages)
    status = required_page(site, "formalization/status/index.html", pages)
    source_index = required_page(site, "formalization/sources/index.html", pages)
    topic_index = required_page(site, "formalization/topics/index.html", pages)
    for label, parser in (
        ("overview", overview),
        ("status", status),
        ("source index", source_index),
        ("topic index", topic_index),
    ):
        assert_metadata(parser, catalog, revision, label)
    require_index_rows(
        overview,
        expected_overview_index_rows(catalog),
        "built overview",
    )
    require_index_rows(source_index, expected_source_index_rows(catalog), "built source index")
    require_index_rows(topic_index, expected_topic_index_rows(catalog), "built topic index")
    require_index_rows(status, expected_status_index_rows(catalog), "built status index")

    source_pages: dict[str, PageParser] = {}
    for source in catalog["sources"]:
        source_id = source["id"]
        parser = required_page(site, f"formalization/sources/{source_id}/index.html", pages)
        assert_metadata(parser, catalog, revision, f"source {source_id}")
        source_pages[source_id] = parser
        expected_href = f"{BASEURL}/formalization/sources/{source_id}/"
        if expected_href not in source_index.links:
            raise ValueError(f"source index lacks {expected_href}")
        expected_records = records_for_source(catalog, source_id)
        require_index_rows(
            parser,
            expected_projection_rows(expected_records, "source", source_id),
            f"built source {source_id}",
        )
        if parser.record_fields:
            raise ValueError(f"built source {source_id}: projection duplicates full record truth")

    foundation_parser = required_page(site, "formalization/sources/foundations/index.html", pages)
    assert_metadata(foundation_parser, catalog, revision, "project-original foundations")
    project_records = [record for record in catalog["records"] if record["origin"] == "project_original"]
    require_index_rows(
        foundation_parser,
        expected_projection_rows(project_records, "source", "foundations"),
        "built project-original foundations",
    )
    if foundation_parser.record_fields:
        raise ValueError("built project-original foundations duplicate full record truth")

    topic_pages: dict[str, PageParser] = {}
    for topic in catalog["topics"]:
        topic_id = topic["id"]
        parser = required_page(site, f"formalization/topics/{topic_id}/index.html", pages)
        assert_metadata(parser, catalog, revision, f"topic {topic_id}")
        topic_pages[topic_id] = parser
        expected_href = f"{BASEURL}/formalization/topics/{topic_id}/"
        if expected_href not in topic_index.links:
            raise ValueError(f"topic index lacks {expected_href}")
        require_index_rows(
            parser,
            expected_projection_rows(records_for_topic(catalog, topic_id), "topic", topic_id),
            f"built topic {topic_id}",
        )
        if parser.record_fields:
            raise ValueError(f"built topic {topic_id}: projection duplicates full record truth")
        expected_heading = [
            (
                "topic",
                (("topic-id", topic_id), ("topic-label", topic["label"])),
                f"Generated {topic['label']} records",
            )
        ]
        if parser.dynamic_headings != expected_heading:
            raise ValueError(f"built topic {topic_id}: dynamic heading differs")

    if status.record_fields:
        raise ValueError("built status projection duplicates full record truth")

    detail_pages: dict[str, PageParser] = {}
    for record in catalog["records"]:
        record_id = record["id"]
        detail = required_page(
            site, f"formalization/records/{record_id}/index.html", pages
        )
        assert_metadata(detail, catalog, revision, f"record {record_id}")
        validate_record_blocks(detail, [record], catalog, f"built record {record_id}")
        require_index_rows(
            detail, [], f"built record {record_id}", allow_canonical_record=True
        )
        detail_pages[record_id] = detail
        anchor = f"record-{record['id']}"
        href = canonical_record_href(record_id)
        related_sources = {
            next(
                item["source_id"]
                for item in catalog["source_items"]
                if item["id"] == relation["source_item_id"]
            )
            for relation in record["source_relations"]
        }
        if related_sources and not all(anchor in source_pages[source_id].ids for source_id in related_sources):
            raise ValueError(f"record lacks stable source projection anchor: {record['id']}")
        if not related_sources and record["origin"] != "project_original":
            raise ValueError(f"non-project record lacks a source projection: {record['id']}")
        if record["origin"] == "project_original" and anchor not in foundation_parser.ids:
            raise ValueError(f"project-original record lacks foundation anchor: {record['id']}")
        if not all(anchor in topic_pages[topic_id].ids for topic_id in record["topic_ids"]):
            raise ValueError(f"record lacks stable topic projection anchor: {record['id']}")
        projection_pages = [
            *(source_pages[source_id] for source_id in related_sources),
            *(topic_pages[topic_id] for topic_id in record["topic_ids"]),
            status,
        ]
        if record["origin"] == "project_original":
            projection_pages.append(foundation_parser)
        if not all(href in parser.links for parser in projection_pages):
            raise ValueError(f"record projection lacks canonical detail link: {record_id}")

    full_truth_occurrences: dict[str, int] = {record["id"]: 0 for record in catalog["records"]}
    for parser in pages.values():
        for record_id in parser.record_fields:
            if record_id not in full_truth_occurrences:
                raise ValueError(f"rendered site contains an unknown full record: {record_id}")
            full_truth_occurrences[record_id] += 1
    if any(count != 1 for count in full_truth_occurrences.values()):
        raise ValueError(
            f"full record truth must occur exactly once: {full_truth_occurrences}"
        )



def check_staged_source(source_dir: Path, expected_catalog_path: Path, revision: str) -> None:
    """Perform pre-Jekyll checks on a generated staged source tree."""
    source = ensure_tree(source_dir)
    check_staged_fragment_pins(source)
    expected_path = expected_catalog_path.resolve(strict=True)
    if source in expected_path.parents:
        raise ValueError("expected catalogue must be generated independently outside the staged source")
    expected_catalog, expected_raw = load_catalog(expected_path)
    recompute_input_digest(expected_catalog)
    catalog, staged_raw = load_catalog(source / "formalization-status/v1/catalog.json")
    if staged_raw != expected_raw or catalog != expected_catalog:
        raise ValueError("staged catalogue differs byte-for-byte from the independent expected catalogue")
    schema = (source / "formalization-status/v1/schema.json").read_bytes()
    if schema != (REPO_ROOT / "formalization-status/v1/schema.json").read_bytes():
        raise ValueError("staged schema differs from canonical schema")
    publication_raw = (source / "formalization-status/v1/publication.json").read_bytes()
    publication = json.loads(publication_raw)
    if canonical_json(publication) != publication_raw or publication.get("revision") != revision:
        raise ValueError("staged publication sidecar is non-canonical or has the wrong revision")
    if publication.get("input_sha256") != catalog["input_sha256"]:
        raise ValueError("staged publication sidecar has the wrong catalogue digest")
    generated_files = sorted((source / "formalization").rglob("*.md"))
    check_staged_record_outputs(source, catalog)
    reject_authority_contradictions(
        catalog,
        [
            (str(path.relative_to(source)), path.read_text(encoding="utf-8"))
            for path in sorted(source.rglob("*.md"))
        ],
    )
    marker_specs: list[str] = []
    marker_parsers: list[PageParser] = []
    for path in generated_files:
        text = path.read_text(encoding="utf-8")
        marker_specs.extend(
            re.findall(r"<!-- formalization-status-generated:start ([^\n]+) -->", text)
        )
        for match in re.finditer(
            r"(?ms)^<!-- formalization-status-generated:start ([^\n]+) -->\n"
            r"(.*?)^<!-- formalization-status-generated:end -->$",
            text,
        ):
            body = match.group(2)
            if body != expected_marker_body(match.group(1), catalog, revision):
                raise ValueError(
                    f"staged marker {match.group(1)} differs from exact generated serialization"
                )
            body_parser = parse_record_html(body, f"staged marker {match.group(1)}")
            require_generated_ownership(
                body_parser,
                f"staged marker {match.group(1)}",
                match.group(1),
            )
            marker_parsers.append(body_parser)
            assert_metadata(
                body_parser,
                catalog,
                revision,
                f"staged marker {match.group(1)}",
            )
            for expected in (
                "/lattice-system/formalization-status/v1/catalog.json",
                "/lattice-system/formalization-status/v1/schema.json",
                "/lattice-system/formalization-status/v1/publication.json",
            ):
                if expected not in body:
                    raise ValueError(
                        f"{path.relative_to(source)} lacks staged metadata {expected!r}"
                    )
    expected_specs = {"overview", "project-original", "source-index", "status", "topic-index"}
    expected_specs.update(f"source {item['id']}" for item in catalog["sources"])
    expected_specs.update(f"topic {item['id']}" for item in catalog["topics"])
    expected_specs.update(f"record {item['id']}" for item in catalog["records"])
    if len(marker_specs) != len(set(marker_specs)) or set(marker_specs) != expected_specs:
        raise ValueError(
            f"generated marker set mismatch: expected {sorted(expected_specs)}, found {sorted(marker_specs)}"
        )

    for source_item in catalog["sources"]:
        source_id = source_item["id"]
        body = marker_body(
            source / "formalization/sources" / f"{source_id}.md",
            f"source {source_id}",
        )
        source_parser = parse_record_html(body, f"staged source {source_id}")
        require_index_rows(
            source_parser,
            expected_projection_rows(records_for_source(catalog, source_id), "source", source_id),
            f"staged source {source_id}",
        )
        if source_parser.record_fields:
            raise ValueError(f"staged source {source_id} duplicates full record truth")
    foundation_body = marker_body(
        source / "formalization/sources/foundations.md", "project-original"
    )
    project_records = [record for record in catalog["records"] if record["origin"] == "project_original"]
    foundation_parser = parse_record_html(
        foundation_body, "staged project-original foundations"
    )
    require_index_rows(
        foundation_parser,
        expected_projection_rows(project_records, "source", "foundations"),
        "staged project-original foundations",
    )
    if foundation_parser.record_fields:
        raise ValueError("staged project-original foundations duplicate full record truth")
    for topic in catalog["topics"]:
        topic_id = topic["id"]
        body = marker_body(
            source / "formalization/topics" / f"{topic_id}.md",
            f"topic {topic_id}",
        )
        topic_parser = parse_record_html(body, f"staged topic {topic_id}")
        require_index_rows(
            topic_parser,
            expected_projection_rows(records_for_topic(catalog, topic_id), "topic", topic_id),
            f"staged topic {topic_id}",
        )
        if topic_parser.record_fields:
            raise ValueError(f"staged topic {topic_id} duplicates full record truth")
        expected_heading = [
            (
                "topic",
                (("topic-id", topic_id), ("topic-label", topic["label"])),
                f"Generated {topic['label']} records",
            )
        ]
        if topic_parser.dynamic_headings != expected_heading:
            raise ValueError(f"staged topic {topic_id}: dynamic heading differs")

    source_index_parser = parse_record_html(
        marker_body(source / "formalization/sources/index.md", "source-index"),
        "staged source index",
    )
    require_index_rows(
        source_index_parser, expected_source_index_rows(catalog), "staged source index"
    )
    topic_index_parser = parse_record_html(
        marker_body(source / "formalization/topics/index.md", "topic-index"),
        "staged topic index",
    )
    require_index_rows(
        topic_index_parser, expected_topic_index_rows(catalog), "staged topic index"
    )
    overview_parser = parse_record_html(
        marker_body(source / "formalization/index.md", "overview"), "staged overview"
    )
    require_index_rows(
        overview_parser,
        expected_overview_index_rows(catalog),
        "staged overview",
    )
    status_parser = parse_record_html(
        marker_body(source / "formalization/status.md", "status"), "staged status"
    )
    require_index_rows(status_parser, expected_status_index_rows(catalog), "staged status")
    if status_parser.record_fields:
        raise ValueError("staged status projection duplicates full record truth")

    full_truth_occurrences: dict[str, int] = {record["id"]: 0 for record in catalog["records"]}
    for record in catalog["records"]:
        record_id = record["id"]
        detail_path = source / "formalization" / "records" / f"{record_id}.md"
        detail_body = marker_body(detail_path, f"record {record_id}")
        detail_parser = parse_record_html(detail_body, f"staged record {record_id}")
        validate_record_blocks(detail_parser, [record], catalog, f"staged record {record_id}")
        require_index_rows(
            detail_parser,
            [],
            f"staged record {record_id}",
            allow_canonical_record=True,
        )
    for parser in marker_parsers:
        for record_id in parser.record_fields:
            if record_id not in full_truth_occurrences:
                raise ValueError(f"staged source contains an unknown full record: {record_id}")
            full_truth_occurrences[record_id] += 1
    if any(count != 1 for count in full_truth_occurrences.values()):
        raise ValueError(
            f"staged full record truth must occur exactly once: {full_truth_occurrences}"
        )


def check_scaled_human_fixture(
    source_dir: Path, catalog: dict[str, Any], revision: str
) -> None:
    """Run the complete human-page semantic grammar over a synthetic large catalogue."""
    source = ensure_tree(source_dir)
    check_staged_record_outputs(source, catalog)
    parsed_markers: dict[str, PageParser] = {}
    for path in sorted((source / "formalization").rglob("*.md")):
        text = path.read_text(encoding="utf-8")
        for match in re.finditer(
            r"(?ms)^<!-- formalization-status-generated:start ([^\n]+) -->\n"
            r"(.*?)^<!-- formalization-status-generated:end -->$",
            text,
        ):
            specification, body = match.groups()
            if specification in parsed_markers:
                raise ValueError(f"scaled fixture duplicates marker {specification}")
            parser = parse_record_html(body, f"scaled marker {specification}")
            if body != expected_marker_body(specification, catalog, revision):
                raise ValueError(
                    f"scaled marker {specification} differs from exact generated serialization"
                )
            require_generated_ownership(
                parser, f"scaled marker {specification}", specification
            )
            assert_metadata(parser, catalog, revision, f"scaled marker {specification}")
            parsed_markers[specification] = parser
    expected_specs = {"overview", "project-original", "source-index", "status", "topic-index"}
    expected_specs.update(f"source {item['id']}" for item in catalog["sources"])
    expected_specs.update(f"topic {item['id']}" for item in catalog["topics"])
    expected_specs.update(f"record {item['id']}" for item in catalog["records"])
    if set(parsed_markers) != expected_specs:
        raise ValueError("scaled fixture marker set differs from the catalogue")
    for specification, parser in parsed_markers.items():
        if not specification.startswith("record ") and parser.record_fields:
            raise ValueError(
                f"scaled fixture duplicates full record truth in {specification}"
            )

    require_index_rows(
        parsed_markers["overview"], expected_overview_index_rows(catalog), "scaled overview"
    )
    require_index_rows(
        parsed_markers["source-index"],
        expected_source_index_rows(catalog),
        "scaled source index",
    )
    require_index_rows(
        parsed_markers["topic-index"],
        expected_topic_index_rows(catalog),
        "scaled topic index",
    )
    require_index_rows(
        parsed_markers["status"], expected_status_index_rows(catalog), "scaled status"
    )
    project_records = [
        record for record in catalog["records"] if record["origin"] == "project_original"
    ]
    require_index_rows(
        parsed_markers["project-original"],
        expected_projection_rows(project_records, "source", "foundations"),
        "scaled foundations",
    )
    for source_item in catalog["sources"]:
        source_id = source_item["id"]
        require_index_rows(
            parsed_markers[f"source {source_id}"],
            expected_projection_rows(records_for_source(catalog, source_id), "source", source_id),
            f"scaled source {source_id}",
        )
    for topic in catalog["topics"]:
        topic_id = topic["id"]
        parser = parsed_markers[f"topic {topic_id}"]
        require_index_rows(
            parser,
            expected_projection_rows(records_for_topic(catalog, topic_id), "topic", topic_id),
            f"scaled topic {topic_id}",
        )
        if parser.dynamic_headings != [
            (
                "topic",
                (("topic-id", topic_id), ("topic-label", topic["label"])),
                f"Generated {topic['label']} records",
            )
        ]:
            raise ValueError(f"scaled topic {topic_id} has the wrong dynamic heading")
    occurrences = {record["id"]: 0 for record in catalog["records"]}
    for record in catalog["records"]:
        specification = f"record {record['id']}"
        parser = parsed_markers[specification]
        validate_record_blocks(parser, [record], catalog, f"scaled {specification}")
        require_index_rows(
            parser, [], f"scaled {specification}", allow_canonical_record=True
        )
    for parser in parsed_markers.values():
        for record_id in parser.record_fields:
            if record_id not in occurrences:
                raise ValueError(f"scaled fixture contains unknown full record {record_id}")
            occurrences[record_id] += 1
    if any(count != 1 for count in occurrences.values()):
        raise ValueError("scaled fixture does not render every full record exactly once")


def check_workflow_invariants(repo_root: Path) -> None:
    """Enforce the sole main-only deploy owner and read-only Lean workflow."""
    workflow_dir = repo_root / ".github/workflows"
    pages_path = workflow_dir / "formalization_pages.yml"
    lean_path = workflow_dir / "lean_action_ci.yml"
    pages = pages_path.read_text(encoding="utf-8")
    lean = lean_path.read_text(encoding="utf-8")
    workflow_paths = sorted(
        {*workflow_dir.glob("*.yml"), *workflow_dir.glob("*.yaml")}
    )
    if not workflow_paths:
        raise ValueError("repository has no workflows to audit")
    competing_tokens = (
        "actions/" + "deploy-pages",
        "pages" + ": write",
        "id-token" + ": write",
    )
    for workflow_path in workflow_paths:
        if workflow_path == pages_path:
            continue
        workflow = workflow_path.read_text(encoding="utf-8")
        for token in competing_tokens:
            if token in workflow:
                raise ValueError(
                    f"competing Pages owner in {workflow_path.name}: {token}"
                )
    lean_forbidden = (
        *competing_tokens,
        "environment" + ":",
    )
    for token in lean_forbidden:
        if token in lean:
            raise ValueError(f"Lean workflow contains forbidden Pages ownership: {token}")
    jobs = pages.split("\njobs:\n", 1)
    if len(jobs) != 2:
        raise ValueError("formalization workflow lacks one jobs block")
    job_names = re.findall(r"(?m)^  ([A-Za-z0-9_-]+):\n    ", jobs[1])
    if job_names != ["build", "deploy", "verify-publication"]:
        raise ValueError(
            "formalization workflow must contain exactly build, deploy, then "
            f"verify-publication: {job_names}"
        )
    workflow_block = jobs[0]
    build_block, remaining_jobs = jobs[1].split("\n  deploy:\n", 1)
    deploy_block, verify_block = remaining_jobs.split(
        "\n  verify-publication:\n", 1
    )
    if "concurrency:" in workflow_block or "concurrency:" in build_block:
        raise ValueError("Pages concurrency must be scoped only to the deploy job")
    for token in lean_forbidden:
        if token in build_block:
            raise ValueError(f"Pages build job contains deploy capability: {token}")
    required = (
        "permissions:\n  contents: read",
        "pull_request:",
        "branches: [main]",
        "workflow_dispatch:",
        "actions/checkout@v6",
        "actions/configure-pages@v5",
        "actions/jekyll-build-pages@v1",
        "actions/upload-pages-artifact@v4",
        "timeout-minutes: 5",
        "python3 scripts/check_live_formalization_site.py --self-test",
        "cmp .self-local/tmp/catalog.json "
        ".self-local/tmp/formalization-site-a/source/formalization-status/v1/catalog.json",
        "--expected-catalog .self-local/tmp/catalog.json",
        "--print-regular-file-bytes .self-local/tmp/formalization-site-a/site",
    )
    for token in required:
        if token not in pages:
            raise ValueError(f"formalization workflow lacks required invariant: {token}")
    if "paths:" in pages or "paths-ignore:" in pages:
        raise ValueError("formalization workflow must run on every pull request")
    upload_binding = (
        "uses: actions/upload-pages-artifact@v4\n"
        "        with:\n"
        "          name: github-pages"
    )
    if upload_binding not in build_block:
        raise ValueError("Pages build job must upload the explicitly named github-pages artifact")
    deploy_required = (
        "if: github.event_name == 'push' && github.ref == 'refs/heads/main'",
        "needs: build",
        "concurrency:\n      group: pages\n      cancel-in-progress: false",
        "permissions:\n      pages: write\n      id-token: write",
        "environment:\n      name: github-pages",
        "url: ${{ steps.deployment.outputs.page_url }}",
        "id: deployment",
        "uses: actions/deploy-pages@v4\n"
        "        with:\n"
        "          artifact_name: github-pages",
    )
    for token in deploy_required:
        if token not in deploy_block:
            raise ValueError(f"Pages deploy job lacks required invariant: {token}")
    verify_required = (
        "if: github.event_name == 'push' && github.ref == 'refs/heads/main'",
        "needs: deploy",
        "timeout-minutes: 5",
        "permissions:\n      contents: read",
        "uses: actions/checkout@v6",
        "python3 scripts/check_live_formalization_site.py",
        "--base-url https://phasetr.github.io/lattice-system/",
        '--revision "$GITHUB_SHA"',
        "--canonical-schema formalization-status/v1/schema.json",
        "--attempts 7",
        "--initial-delay 5",
        "--timeout 10",
        "--deadline 240",
    )
    for token in verify_required:
        if token not in verify_block:
            raise ValueError(
                f"live publication verification lacks required invariant: {token}"
            )
    for token in (*competing_tokens, "environment:", "concurrency:"):
        if token in verify_block:
            raise ValueError(
                f"live publication verification has forbidden capability: {token}"
            )
    verify_permissions = re.findall(
        r"(?m)^    permissions:\n((?:      [^\n]+\n)+)", verify_block
    )
    if verify_permissions != ["      contents: read\n"]:
        raise ValueError(
            "live publication verification permissions must be exactly contents: read"
        )
    strict_guard = "if: github.event_name == 'push' && github.ref == 'refs/heads/main'"
    if pages.count(strict_guard) != 2:
        raise ValueError("deploy and live verification must share the exact main-push guard")
    if pages.count("actions/deploy-pages@v4") != 1:
        raise ValueError("formalization workflow must have exactly one Pages deploy action")
    if pages.count("concurrency:") != 1 or pages.count("group: pages") != 1:
        raise ValueError("Pages concurrency must have exactly one deploy-job owner")
    if pages.count("pages: write") != 1 or pages.count("id-token: write") != 1:
        raise ValueError("Pages/OIDC write permissions must occur only in the deploy job")
    if "permissions:\n  contents: read" not in lean:
        raise ValueError("Lean CI does not have the expected read-only top permission")
    if "--emit-lean-check" not in lean or "lake env lean .self-local/tmp/formalization-axioms.lean" not in lean:
        raise ValueError("Lean CI lacks the generated exact axiom gate")
    if "  # docs:" not in lean:
        raise ValueError("the disabled doc-gen4 block was unexpectedly re-enabled")


def run_staged_mutation_tests(
    source_dir: Path,
    expected_catalog_path: Path,
    revision: str,
) -> None:
    """Prove representative status, identity, citation, count, and projection mutations fail."""
    source = source_dir.resolve(strict=True)
    scratch = REPO_ROOT / ".self-local/tmp"
    expected_catalog, _ = load_catalog(expected_catalog_path)
    aggregate_mutation = Path(
        tempfile.mkdtemp(prefix="catalog-semantic-mutation-", dir=scratch)
    )
    try:
        mutated_catalog = json.loads(json.dumps(expected_catalog))
        mutated_catalog["records"][0]["implementation_state"] = "in_progress"
        mutated_path = aggregate_mutation / "catalog.json"
        mutated_path.write_bytes(canonical_json(mutated_catalog))
        try:
            check_staged_source(source, mutated_path, revision)
        except ValueError:
            pass
        else:
            raise AssertionError("independently recomputed aggregate accepted a status mutation")
    finally:
        shutil.rmtree(aggregate_mutation)
    first_record = expected_catalog["records"][0]
    record_id = first_record["id"]
    detail_relative = f"formalization/records/{record_id}.md"
    detail_text = (source / detail_relative).read_text(encoding="utf-8")
    detail_href = canonical_record_href(record_id)
    source_item_map = {item["id"]: item for item in expected_catalog["source_items"]}
    related_source = source_item_map[first_record["source_relations"][0]["source_item_id"]][
        "source_id"
    ]
    source_relative = f"formalization/sources/{related_source}.md"
    source_text = (source / source_relative).read_text(encoding="utf-8")
    projection_pattern = re.compile(
        rf'<li id="record-{re.escape(record_id)}" .*?</li>'
    )
    projection_match = projection_pattern.search(source_text)
    if projection_match is None:
        raise AssertionError("canonical source projection mutation fixture is absent")
    projection_row = projection_match.group(0)
    status_text = (source / "formalization/status.md").read_text(encoding="utf-8")
    status_count_match = re.search(
        r'(data-row-kind="status-count"[^>]*data-record-count=")(\d+)(")',
        status_text,
    )
    if status_count_match is None:
        raise AssertionError("status count mutation fixture is absent")
    wrong_status_count = (
        status_text[: status_count_match.start(2)]
        + str(int(status_count_match.group(2)) + 1)
        + status_text[status_count_match.end(2) :]
    )
    mutation_cases = [
        (
            "detail implementation status",
            detail_relative,
            detail_text.replace(
                f'<dd data-field="implementation-state">{first_record["implementation_state"]}</dd>',
                '<dd data-field="implementation-state">in_progress</dd>',
                1,
            ),
        ),
        (
            "detail source path omission",
            detail_relative,
            detail_text.replace(
                '<dt data-label-for="source-path">Source path</dt>\n'
                f'<dd data-field="source-path">{first_record["source_path"]}</dd>\n',
                "",
                1,
            ),
        ),
        (
            "source projection omission",
            source_relative,
            source_text.replace(projection_row + "\n", "", 1),
        ),
        (
            "source projection wrong detail link",
            source_relative,
            source_text.replace(detail_href, f"{BASEURL}/formalization/records/wrong/", 1),
        ),
        (
            "source projection duplicate full truth",
            source_relative,
            source_text.replace(
                "<!-- formalization-status-generated:end -->",
                re.search(r"(?ms)<article .*?</article>", detail_text).group(0)
                + "\n<!-- formalization-status-generated:end -->",
                1,
            ),
        ),
        (
            "source projection stripped-identity full truth",
            source_relative,
            source_text.replace(
                "<!-- formalization-status-generated:end -->",
                "<article><h3>Stripped identity</h3><dl>"
                "<dt>Implementation state</dt><dd>implemented</dd>"
                "</dl></article>\n<!-- formalization-status-generated:end -->",
                1,
            ),
        ),
        (
            "source projection unrecognized record-like container",
            source_relative,
            source_text.replace(
                "<!-- formalization-status-generated:end -->",
                f'<section id="record-{record_id}"><dl><dt>Status</dt>'
                "<dd>implemented</dd></dl></section>\n"
                "<!-- formalization-status-generated:end -->",
                1,
            ),
        ),
        (
            "source projection unowned paragraph",
            source_relative,
            source_text.replace(
                "</div>\n<!-- formalization-status-generated:end -->",
                "<p>poison</p>\n</div>\n"
                "<!-- formalization-status-generated:end -->",
                1,
            ),
        ),
        (
            "status count",
            "formalization/status.md",
            wrong_status_count,
        ),
    ]
    fragment_relative = (
        "formalization/legacy/"
        "04-3d-rotation-matrices-general-tasaki-2-1-eq-2-1-11.md"
    )
    fragment_text = (source / fragment_relative).read_text(encoding="utf-8")
    fragment_pin = (
        "{: #legacy-catalogue-3d-rotation-matrices-r-general--tasaki-21-eq-2111}\n"
    )
    if fragment_pin not in fragment_text:
        raise AssertionError("staged fragment-pin mutation fixture is absent")
    mutation_cases.append(
        (
            "missing render-stable legacy fragment pin",
            fragment_relative,
            fragment_text.replace(fragment_pin, "", 1),
        )
    )
    for label, relative, mutated_text in mutation_cases:
        temporary = Path(tempfile.mkdtemp(prefix="site-a2-semantic-mutation-", dir=scratch))
        try:
            mutated = temporary / "source"
            shutil.copytree(source, mutated)
            path = mutated / relative
            if mutated_text == path.read_text(encoding="utf-8"):
                raise AssertionError(f"A2 semantic mutation made no change: {label}")
            path.write_text(mutated_text, encoding="utf-8")
            try:
                check_staged_source(mutated, expected_catalog_path, revision)
            except ValueError:
                pass
            else:
                raise AssertionError(f"staged A2 semantic mutation was accepted: {label}")
        finally:
            shutil.rmtree(temporary)
    missing_temporary = Path(tempfile.mkdtemp(prefix="site-a2-missing-detail-", dir=scratch))
    try:
        missing_source = missing_temporary / "source"
        shutil.copytree(source, missing_source)
        (missing_source / detail_relative).unlink()
        try:
            check_staged_source(missing_source, expected_catalog_path, revision)
        except ValueError:
            pass
        else:
            raise AssertionError("staged source accepted a missing canonical detail page")
    finally:
        shutil.rmtree(missing_temporary)
    replacements = (
        (
            "implementation status",
            "formalization/records/tasaki-2020-theorem-3-1-finite-dimensional-core.md",
            '<dd data-field="implementation-state">implemented</dd>',
            '<dd data-field="implementation-state">in_progress</dd>',
        ),
        (
            "Lean name",
            "formalization/records/tasaki-2020-section-2-1-pauli-x-involutive.md",
            '<dd data-field="lean-name">LatticeSystem.Quantum.pauliX_mul_self</dd>',
            '<dd data-field="lean-name">LatticeSystem.Quantum.changed</dd>',
        ),
        (
            "module",
            "formalization/records/tasaki-2020-section-2-1-pauli-x-involutive.md",
            '<dd data-field="module">LatticeSystem.Quantum.Pauli</dd>',
            '<dd data-field="module">LatticeSystem.Quantum.Changed</dd>',
        ),
        (
            "axiom dependency",
            "formalization/records/shastry-1992-staggered-susceptibility-bound.md",
            '<dd data-field="axiom-dependency">'
            "LatticeSystem.Quantum.shastry_staggered_susceptibility_subcubic</dd>",
            '<dd data-field="axiom-dependency">LatticeSystem.Quantum.changed</dd>',
        ),
        (
            "citation locator",
            "formalization/records/tasaki-2020-section-2-1-pauli-x-involutive.md",
            "exercise 2.41; section 2.1.9; pages 78",
            "exercise 2.41; section 2.1.9; pages 79",
        ),
        (
            "summary",
            "formalization/records/tasaki-2020-section-2-1-pauli-x-involutive.md",
            '<h3 data-field="summary">The Pauli X matrix squares to the identity.</h3>',
            '<h3 data-field="summary">The Pauli X matrix has changed.</h3>',
        ),
        (
            "status count",
            "formalization/status.md",
            'data-status-label="proved" data-record-count="3">proved: 3',
            'data-status-label="proved" data-record-count="4">proved: 4',
        ),
        (
            "extra unrelated record",
            "formalization/topics/low-energy-spectrum.md",
            "<!-- formalization-status-generated:end -->",
            '<article id="record-poison" data-record-id="poison">'
            '<h3 data-field="summary">Poison</h3><dl></dl></article>\n'
            "<!-- formalization-status-generated:end -->",
        ),
    )
    mutation_cases: list[tuple[str, str, str]] = []
    for label, relative, before, after in replacements:
        original = (source / relative).read_text(encoding="utf-8")
        if before not in original:
            raise AssertionError(f"mutation fixture text is absent: {label}")
        mutation_cases.append((label, relative, original.replace(before, after, 1)))

    pauli_relative = (
        "formalization/records/tasaki-2020-section-2-1-pauli-x-involutive.md"
    )
    pauli_text = (source / pauli_relative).read_text(encoding="utf-8")
    human_row = (
        '<dt data-label-for="human-status">Human status</dt>\n'
        '<dd data-field="human-status">proved</dd>'
    )
    module_row = (
        '<dt data-label-for="module">Module</dt>\n'
        '<dd data-field="module">LatticeSystem.Quantum.Pauli</dd>'
    )
    mutation_cases.extend(
        (
            (
                "extra contradictory status",
                pauli_relative,
                pauli_text.replace(
                    human_row,
                    human_row + '\n<dt data-label-for="human-status">Human status</dt>'
                    '\n<dd data-field="human-status">in progress</dd>',
                    1,
                ),
            ),
            (
                "extra contradictory module",
                pauli_relative,
                pauli_text.replace(
                    module_row,
                    module_row + '\n<dt data-label-for="module">Module</dt>'
                    '\n<dd data-field="module">LatticeSystem.Wrong</dd>',
                    1,
                ),
            ),
            (
                "duplicate field",
                pauli_relative,
                pauli_text.replace(module_row, module_row + module_row, 1),
            ),
            (
                "missing Module despite matching summary text",
                pauli_relative,
                pauli_text.replace(
                    "The Pauli X matrix squares to the identity.",
                    "The Pauli X matrix squares to the identity in LatticeSystem.Quantum.Pauli.",
                    1,
                ).replace(module_row, "", 1),
            ),
            (
                "additive field poisoning",
                pauli_relative,
                pauli_text.replace(
                    "</dl>",
                    '<dt data-label-for="unrecognized">Poison</dt>\n'
                    '<dd data-field="unrecognized">poison</dd>\n</dl>',
                    1,
                ),
            ),
            (
                "moved heading after fields",
                pauli_relative,
                pauli_text.replace(
                    '<h3 data-field="summary">The Pauli X matrix squares to the identity.</h3>\n',
                    "",
                    1,
                ).replace(
                    "</dl>\n</article>",
                    '</dl>\n<h3 data-field="summary">The Pauli X matrix squares to the identity.</h3>\n</article>',
                    1,
                ),
            ),
            (
                "extra empty definition list",
                pauli_relative,
                pauli_text.replace("</article>", "<dl></dl>\n</article>", 1),
            ),
            (
                "extra empty list",
                pauli_relative,
                pauli_text.replace("</article>", "<ol></ol>\n</article>", 1),
            ),
            (
                "extra article text",
                pauli_relative,
                pauli_text.replace("</article>", "poison\n</article>", 1),
            ),
            (
                "extra article container",
                pauli_relative,
                pauli_text.replace("</article>", "<div></div>\n</article>", 1),
            ),
            (
                "missing dt",
                pauli_relative,
                pauli_text.replace('<dt data-label-for="module">Module</dt>\n', "", 1),
            ),
            (
                "duplicate dt",
                pauli_relative,
                pauli_text.replace(
                    '<dt data-label-for="module">Module</dt>\n',
                    '<dt data-label-for="module">Module</dt>\n' * 2,
                    1,
                ),
            ),
            (
                "missing dd",
                pauli_relative,
                pauli_text.replace(
                    '<dd data-field="module">LatticeSystem.Quantum.Pauli</dd>\n', "", 1
                ),
            ),
            (
                "duplicate dd",
                pauli_relative,
                pauli_text.replace(
                    '<dd data-field="module">LatticeSystem.Quantum.Pauli</dd>\n',
                    '<dd data-field="module">LatticeSystem.Quantum.Pauli</dd>\n' * 2,
                    1,
                ),
            ),
            (
                "visible label mismatch",
                pauli_relative,
                pauli_text.replace(">Module</dt>", ">Wrong label</dt>", 1),
            ),
            (
                "label target mismatch",
                pauli_relative,
                pauli_text.replace('data-label-for="module"', 'data-label-for="lean-name"', 1),
            ),
        )
    )
    source_index_relative = "formalization/sources/index.md"
    source_index_text = (source / source_index_relative).read_text(encoding="utf-8")
    source_ids = sorted(item["id"] for item in expected_catalog["sources"])
    first_source_href = f"{BASEURL}/formalization/sources/{source_ids[0]}/"
    second_source_href = f"{BASEURL}/formalization/sources/{source_ids[1]}/"
    foundation_href = f"{BASEURL}/formalization/sources/foundations/"
    swapped_source_hrefs = source_index_text.replace(
        f'<a href="{first_source_href}">', '<a href="SOURCE-SWAP">', 1
    ).replace(
        f'<a href="{second_source_href}">', f'<a href="{first_source_href}">', 1
    ).replace('<a href="SOURCE-SWAP">', f'<a href="{second_source_href}">', 1)
    mutation_cases.extend(
        (
            ("swapped source hrefs", source_index_relative, swapped_source_hrefs),
            (
                "deleted foundations href",
                source_index_relative,
                source_index_text.replace(f'<a href="{foundation_href}">', "", 1).replace(
                    "Project-original foundations: 0 record(s)</a>",
                    "Project-original foundations: 0 record(s)",
                    1,
                ),
            ),
            (
                "wrong href on correct row",
                source_index_relative,
                source_index_text.replace(
                    f'<a href="{first_source_href}">',
                    '<a href="/lattice-system/wrong-source/">',
                    1,
                ),
            ),
            (
                "extra second source anchor",
                source_index_relative,
                source_index_text.replace(
                    "</a></li>",
                    f'</a><a href="{first_source_href}">extra</a></li>',
                    1,
                ),
            ),
            (
                "nested second source anchor",
                source_index_relative,
                source_index_text.replace(
                    f'<a href="{first_source_href}">',
                    f'<a href="{first_source_href}"><a href="{first_source_href}">',
                    1,
                ),
            ),
        )
    )
    topic_index_relative = "formalization/topics/index.md"
    topic_index_text = (source / topic_index_relative).read_text(encoding="utf-8")
    topic_ids = sorted(item["id"] for item in expected_catalog["topics"])
    first_topic_href = f"{BASEURL}/formalization/topics/{topic_ids[0]}/"
    second_topic_href = f"{BASEURL}/formalization/topics/{topic_ids[1]}/"
    swapped_topic_hrefs = topic_index_text.replace(
        f'<a href="{first_topic_href}">', '<a href="TOPIC-SWAP">', 1
    ).replace(
        f'<a href="{second_topic_href}">', f'<a href="{first_topic_href}">', 1
    ).replace('<a href="TOPIC-SWAP">', f'<a href="{second_topic_href}">', 1)
    mutation_cases.append(("swapped topic hrefs", topic_index_relative, swapped_topic_hrefs))
    metadata_relative = "formalization/sources/nielsen-chuang-2010.md"
    metadata_text = (source / metadata_relative).read_text(encoding="utf-8")
    catalog_href = f"{BASEURL}/formalization-status/v1/catalog.json"
    mutation_cases.extend(
        (
            (
                "removed metadata href",
                metadata_relative,
                metadata_text.replace(f'<a href="{catalog_href}">', "", 1).replace(
                    "Machine data: version 1 catalogue</a>",
                    "Machine data: version 1 catalogue",
                    1,
                ),
            ),
            (
                "changed metadata href",
                metadata_relative,
                metadata_text.replace(
                    f'<a href="{catalog_href}">', '<a href="/lattice-system/wrong-catalog.json">', 1
                ),
            ),
        )
    )
    # The citation fixtures need a record carrying several typed relations in canonical
    # order. The staggered-susceptibility axiom no longer qualifies: it is a project
    # assumption with no bibliographic edge at all.
    multi_citation_relative = (
        "formalization/records/tasaki-2020-theorem-4-2-shastry-no-ssb.md"
    )
    multi_citation_text = (source / multi_citation_relative).read_text(encoding="utf-8")
    citation_rows = re.findall(
        r'<dt data-label-for="citation">.*?</dt>\n<dd data-field="citation"[^>]*>.*?</dd>',
        multi_citation_text,
    )
    if len(citation_rows) < 2:
        raise AssertionError("staged citation-order fixture lacks two citations")
    mutation_cases.extend(
        (
            (
                "reordered citations",
                multi_citation_relative,
                multi_citation_text.replace(
                    citation_rows[0] + "\n" + citation_rows[1],
                    citation_rows[1] + "\n" + citation_rows[0],
                    1,
                ),
            ),
            (
                "extra citation",
                multi_citation_relative,
                multi_citation_text.replace(
                    "</dl>",
                    '<dt data-label-for="citation">Citation</dt>\n'
                    '<dd data-field="citation" data-relation="supports" '
                    'data-source-id="shastry-1992" data-source-item-id="poison">poison</dd>\n</dl>',
                    1,
                ),
            ),
        )
    )
    fragment_relative = (
        "formalization/legacy/"
        "04-3d-rotation-matrices-general-tasaki-2-1-eq-2-1-11.md"
    )
    fragment_text = (source / fragment_relative).read_text(encoding="utf-8")
    fragment_pin = (
        "{: #legacy-catalogue-3d-rotation-matrices-r-general--tasaki-21-eq-2111}\n"
    )
    if fragment_pin not in fragment_text:
        raise AssertionError("staged fragment-pin mutation fixture is absent")
    mutation_cases.append(
        (
            "missing render-stable legacy fragment pin",
            fragment_relative,
            fragment_text.replace(fragment_pin, "", 1),
        )
    )
    for label, relative, mutated_text in mutation_cases:
        temporary = Path(tempfile.mkdtemp(prefix="site-semantic-mutation-", dir=scratch))
        try:
            mutated = temporary / "source"
            shutil.copytree(source, mutated)
            path = mutated / relative
            if mutated_text == path.read_text(encoding="utf-8"):
                raise AssertionError(f"semantic mutation made no change: {label}")
            path.write_text(mutated_text, encoding="utf-8")
            try:
                check_staged_source(mutated, expected_catalog_path, revision)
            except ValueError:
                pass
            else:
                raise AssertionError(f"staged semantic mutation was accepted: {label}")
        finally:
            shutil.rmtree(temporary)


def run_self_tests() -> None:
    """Exercise duplicate-ID, unsafe-path, fragment, and byte-mismatch failures."""
    manifest_fixture = {
        "schema": "schema.json",
        "registries": {"topics": "topics.json", "sources": "sources.json"},
        "record_shards": ["records/a.json"],
    }
    expected_without_cutover = [
        "schema.json",
        "sources.json",
        "topics.json",
        "records/a.json",
    ]
    if manifest_input_names(manifest_fixture) != expected_without_cutover:
        raise AssertionError("manifest digest order without cutover evidence drifted")
    with_cutover = {
        **manifest_fixture,
        "cutover_baseline": "cutover-baseline.json",
        "cutover_certificate": "cutover-certificate.json",
    }
    if manifest_input_names(with_cutover) != [
        *expected_without_cutover,
        "cutover-baseline.json",
        "cutover-certificate.json",
    ]:
        raise AssertionError("manifest digest order with cutover evidence drifted")
    absent_manifest_raw = canonical_json(manifest_fixture)
    absent_digest = framed_input_digest(
        [("manifest.json", absent_manifest_raw),
         *[(name, name.encode("utf-8")) for name in expected_without_cutover]]
    )
    present_names = manifest_input_names(with_cutover)
    present_manifest_raw = canonical_json(with_cutover)
    present_digest = framed_input_digest(
        [("manifest.json", present_manifest_raw),
         *[(name, name.encode("utf-8")) for name in present_names]]
    )
    reordered_names = [*present_names[:-2], *reversed(present_names[-2:])]
    reordered_digest = framed_input_digest(
        [("manifest.json", present_manifest_raw),
         *[(name, name.encode("utf-8")) for name in reordered_names]]
    )
    if len({absent_digest, present_digest, reordered_digest}) != 3:
        raise AssertionError("cutover digest presence/order is not cryptographically visible")
    for incomplete in (
        {**manifest_fixture, "cutover_baseline": "cutover-baseline.json"},
        {**manifest_fixture, "cutover_certificate": "cutover-certificate.json"},
    ):
        try:
            manifest_input_names(incomplete)
        except ValueError:
            pass
        else:
            raise AssertionError("unpaired optional cutover digest input was accepted")
    reject_authority_contradictions(
        {"catalog_state": "prototype"},
        [("prototype fixture", "The interim legacy catalogue remains authoritative")],
    )
    for phrase in AUTHORITATIVE_FORBIDDEN_PHRASES:
        try:
            reject_authority_contradictions(
                {"catalog_state": "authoritative"},
                [("authoritative contradiction fixture", phrase)],
            )
        except ValueError:
            pass
        else:
            raise AssertionError(
                f"authoritative stale-authority phrase was accepted: {phrase}"
            )
    assert publication_file(
        Path("/tmp/site"), "/lattice-system/formalization/"
    ) == Path("/tmp/site/formalization/index.html").resolve()
    for unsafe in (
        "/lattice-system/../secret",
        "/lattice-system/%2e%2e/secret",
        "/lattice-system/a\\b",
    ):
        try:
            publication_file(Path("/tmp/site"), unsafe)
        except ValueError:
            pass
        else:
            raise AssertionError(f"unsafe publication path accepted: {unsafe}")
    scratch_root = REPO_ROOT / ".self-local/tmp"
    scratch_root.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix="site-check-self-test-", dir=scratch_root))
    try:
        page = temporary / "index.html"
        page.write_bytes(b"12345")
        if regular_file_bytes(temporary) != 5:
            raise AssertionError("regular-file byte metric is not exact")
        page.write_text('<div id="same"></div><div id="same"></div>', encoding="utf-8")
        try:
            parse_site(temporary)
        except ValueError:
            pass
        else:
            raise AssertionError("duplicate HTML ID mutation was accepted")
        page.write_text('<a id="ok" href="/lattice-system/missing/#absent">x</a>', encoding="utf-8")
        parsed = parse_site(temporary)
        try:
            check_links(temporary, parsed)
        except ValueError:
            pass
        else:
            raise AssertionError("broken path/fragment mutation was accepted")
        bad_catalog = temporary / "catalog.json"
        bad_catalog.write_text('{}\n', encoding="utf-8")
        try:
            load_catalog(bad_catalog)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid catalogue mutation was accepted")

        stripped_record_html = (
            "<article><h3>Stripped identity</h3><dl><dt>Status</dt>"
            "<dd>implemented</dd></dl></article>"
        )
        rendered_stripped_record_html = (
            '<article class="page-layout"><!-- formalization-status-generated:start source fixture -->'
            '<div data-formalization-generated="source fixture">'
            + stripped_record_html
            + "</div><!-- formalization-status-generated:end --></article>"
        )
        require_index_rows(
            parse_record_html(
                '<article class="page-layout"><!-- formalization-status-generated:start source fixture -->'
                '<div data-formalization-generated="source fixture"></div>'
                "<!-- formalization-status-generated:end --></article>",
                "clean rendered marker scope",
            ),
            [],
            "clean rendered marker scope",
        )
        for label, value in (
            ("raw stripped-identity projection", stripped_record_html),
            ("rendered stripped-identity projection", rendered_stripped_record_html),
        ):
            try:
                require_index_rows(parse_record_html(value, label), [], label)
            except ValueError:
                pass
            else:
                raise AssertionError(f"{label} was accepted")

        record_tree = temporary / "record-tree"
        rendered_record = record_tree / "formalization/records/fixture-record"
        rendered_record.mkdir(parents=True)
        (rendered_record / "index.html").write_text("fixture", encoding="utf-8")
        record_catalog = {"records": [{"id": "fixture-record"}]}
        check_built_record_outputs(record_tree, record_catalog)
        (rendered_record / "poison.txt").write_text("poison", encoding="utf-8")
        try:
            check_built_record_outputs(record_tree, record_catalog)
        except ValueError:
            pass
        else:
            raise AssertionError("rendered record output accepted an unexpected file")

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
            "source_path": "LatticeSystem/Fixture.lean",
            "source_relations": [],
            "summary": "Lieb's \"theorem\" in LatticeSystem.Fixture",
            "topic_ids": ["fixture-topic"],
            "trust_state": "axiom_free",
            "proof_guide_anchor": None,
        }
        project_catalog = {
            "records": [project_record],
            "source_items": [],
            "sources": [],
            "topics": [{"description": "Fixture", "id": "fixture-topic", "label": "Fixture"}],
        }
        hostile_text = 'Lieb\'s "theorem" {{ 7 | plus: 1 }} {% include x %}'
        literature_record = {
            "axiom_dependencies": ["LatticeSystem.Fixture.axiom"],
            "capstone": True,
            "declaration_kind": "theorem",
            "id": "literature-fixture",
            "implementation_state": "implemented",
            "lean_name": "LatticeSystem.Fixture.theorem",
            "module": "LatticeSystem.Fixture",
            "origin": "literature",
            "source_coverage": "complete",
            "source_path": "LatticeSystem/Fixture.lean",
            "source_relations": [
                {"relation": "formalizes", "source_item_id": "fixture-theorem"},
                {"relation": "supports", "source_item_id": "fixture-equation"},
            ],
            "summary": hostile_text,
            "topic_ids": ["fixture-topic", "second-topic"],
            "trust_state": "depends_on_documented_axioms",
            "proof_guide_anchor": "fixture-anchor",
        }
        literature_catalog = {
            "records": [literature_record],
            "source_items": [
                {
                    "equations": ["(1)"],
                    "id": "fixture-theorem",
                    "item_kind": "theorem",
                    "item_number": "1",
                    "pages": "10",
                    "section": "2",
                    "source_id": "fixture-source",
                    "title": "Current authority: " + hostile_text,
                },
                {
                    "equations": ["(2)"],
                    "id": "fixture-equation",
                    "item_kind": "equation",
                    "item_number": "2",
                    "pages": "11",
                    "section": "3",
                    "source_id": "fixture-source",
                    "title": "Schema: " + hostile_text,
                }
            ],
            "sources": [{"id": "fixture-source", "title": "Schema: " + hostile_text}],
            "topics": [
                {"description": hostile_text, "id": "fixture-topic", "label": hostile_text},
                {"description": "Second", "id": "second-topic", "label": "Second topic"},
            ],
        }
        def fixture_escape(value: Any) -> str:
            """Escape fixture text exactly as browser-visible HTML."""
            return (
                html.escape(str(value), quote=True)
                .replace("{", "&#123;")
                .replace("}", "&#125;")
            )

        def fixture_html(record: dict[str, Any], catalog: dict[str, Any]) -> str:
            """Render an independent structured HTML fixture for checker tests."""
            heading, fields = expected_record_structure(record, catalog)
            result = [
                f'<article id="record-{record["id"]}" data-record-id="{record["id"]}">',
                f'<h3 data-field="summary">{fixture_escape(heading)}</h3>',
                "<dl>",
            ]
            for label, name, attributes, value in fields:
                extra = "".join(
                    f' data-{key}="{fixture_escape(item)}"'
                    for key, item in attributes
                )
                result.extend(
                    (
                        f'<dt data-label-for="{name}">{fixture_escape(label)}</dt>',
                        f'<dd data-field="{name}"{extra}>{fixture_escape(value)}</dd>',
                    )
                )
            result.extend(("</dl>", "</article>"))
            return "".join(result)

        def validate_fixture(
            value: str,
            record: dict[str, Any],
            catalog: dict[str, Any],
            label: str,
        ) -> None:
            """Require one synthetic raw or built HTML fixture to match exactly."""
            validate_record_blocks(
                parse_record_html(value, label),
                [record],
                catalog,
                label,
            )

        project_html = fixture_html(project_record, project_catalog)
        validate_fixture(
            project_html, project_record, project_catalog, "project-original checker fixture"
        )
        project_parser = parse_record_html(project_html, "quoted heading fixture")
        if project_parser.record_headings["project-fixture"] != project_record["summary"]:
            raise AssertionError("HTMLParser did not preserve apostrophes and quotes exactly")
        if any(field[1] == "citation" for field in project_parser.record_fields["project-fixture"]):
            raise AssertionError("project-original fixture unexpectedly contains a citation")

        html_body = fixture_html(literature_record, literature_catalog)
        if "{{" in html_body or "{%" in html_body:
            raise AssertionError("synthetic built HTML fixture exposes a Liquid opener")
        validate_fixture(html_body, literature_record, literature_catalog, "built HTML fixture")
        if parse_record_html(html_body, "Liquid roundtrip").record_headings[
            "literature-fixture"
        ] != hostile_text:
            raise AssertionError("Liquid-safe entities did not roundtrip to canonical text")
        citation_rows = re.findall(
            r'<dt data-label-for="citation">.*?</dt><dd data-field="citation"[^>]*>.*?</dd>',
            html_body,
        )
        if len(citation_rows) != 2:
            raise AssertionError("built HTML fixture does not contain two typed citations")
        module_row = (
            '<dt data-label-for="module">Module</dt>'
            '<dd data-field="module">LatticeSystem.Fixture</dd>'
        )
        mutations = (
            (
                "extra contradictory status",
                html_body.replace(
                    "</dl>",
                    '<dt data-label-for="human-status">Human status</dt>'
                    '<dd data-field="human-status">proved</dd></dl>',
                    1,
                ),
            ),
            (
                "extra contradictory module",
                html_body.replace(
                    "</dl>",
                    '<dt data-label-for="module">Module</dt>'
                    '<dd data-field="module">LatticeSystem.Wrong</dd></dl>',
                    1,
                ),
            ),
            ("duplicate field", html_body.replace(module_row, module_row + module_row, 1)),
            ("reordered citations", html_body.replace(citation_rows[0] + citation_rows[1], citation_rows[1] + citation_rows[0], 1)),
            (
                "extra citation",
                html_body.replace(
                    "</dl>",
                    '<dt data-label-for="citation">Citation</dt>'
                    '<dd data-field="citation" data-relation="supports" '
                    'data-source-id="fixture-source" data-source-item-id="fixture-theorem">poison</dd></dl>',
                    1,
                ),
            ),
            ("wrong heading", html_body.replace("Lieb&#x27;s", "Wrong", 1)),
            (
                "additive poisoning",
                html_body.replace(
                    "</dl>",
                    '<dt data-label-for="unrecognized">Poison</dt>'
                    '<dd data-field="unrecognized">poison</dd></dl>',
                    1,
                ),
            ),
            ("moved heading after fields", html_body.replace(
                f'<h3 data-field="summary">{fixture_escape(hostile_text)}</h3>', "", 1
            ).replace(
                "</dl>",
                f'</dl><h3 data-field="summary">{fixture_escape(hostile_text)}</h3>',
                1,
            )),
            ("extra empty definition list", html_body.replace("</article>", "<dl></dl></article>", 1)),
            ("extra empty list", html_body.replace("</article>", "<ol></ol></article>", 1)),
            ("extra text", html_body.replace("</article>", "poison</article>", 1)),
            ("extra container", html_body.replace("</article>", "<div></div></article>", 1)),
            ("missing dt", html_body.replace('<dt data-label-for="module">Module</dt>', "", 1)),
            ("duplicate dt", html_body.replace(
                '<dt data-label-for="module">Module</dt>',
                '<dt data-label-for="module">Module</dt><dt data-label-for="module">Module</dt>',
                1,
            )),
            ("missing dd", html_body.replace('<dd data-field="module">LatticeSystem.Fixture</dd>', "", 1)),
            ("duplicate dd", html_body.replace(
                '<dd data-field="module">LatticeSystem.Fixture</dd>',
                '<dd data-field="module">LatticeSystem.Fixture</dd>' * 2,
                1,
            )),
            ("label mismatch", html_body.replace(">Module</dt>", ">Wrong label</dt>", 1)),
            ("label target mismatch", html_body.replace('data-label-for="module"', 'data-label-for="lean-name"', 1)),
        )
        for label, mutated in mutations:
            try:
                validate_fixture(mutated, literature_record, literature_catalog, label)
            except ValueError:
                pass
            else:
                raise AssertionError(f"built HTML semantic mutation was accepted: {label}")

        def fixture_rows(
            rows: list[tuple[str, tuple[tuple[str, str], ...], str | None, str]],
        ) -> str:
            """Render independent structured index rows for parser roundtrip tests."""
            rendered = []
            for kind, attributes, anchor_href, visible in rows:
                extra = "".join(
                    f' data-{key}="{fixture_escape(value)}"'
                    for key, value in attributes
                )
                content = fixture_escape(visible)
                if anchor_href is not None:
                    content = f'<a href="{fixture_escape(anchor_href)}">{content}</a>'
                rendered.append(
                    f'<li data-row-kind="{kind}"{extra}>{content}</li>'
                )
            return "".join(rendered)

        source_rows = expected_source_index_rows(literature_catalog)
        topic_rows = expected_topic_index_rows(literature_catalog)
        index_fixture = fixture_rows([*source_rows, *topic_rows])
        if "{{" in index_fixture or "{%" in index_fixture:
            raise AssertionError("source/topic index fixture exposes a Liquid opener")
        index_parser = parse_record_html(index_fixture, "quoted/Liquid index fixture")
        if index_parser.index_rows != [*source_rows, *topic_rows]:
            raise AssertionError("source/topic index text or attributes did not roundtrip exactly")

        def require_structure_rejection(value: str, label: str) -> None:
            """Require a malformed structured navigation fixture to fail parsing."""
            try:
                parse_record_html(value, label)
            except ValueError:
                return
            raise AssertionError(f"structured navigation mutation was accepted: {label}")

        source_href = f"{BASEURL}/formalization/sources/fixture-source/"
        foundation_href = f"{BASEURL}/formalization/sources/foundations/"
        topic_href = f"{BASEURL}/formalization/topics/fixture-topic/"
        second_topic_href = f"{BASEURL}/formalization/topics/second-topic/"
        swapped_sources = index_fixture.replace(
            f'<a href="{source_href}">', '<a href="SOURCE-SWAP">', 1
        ).replace(
            f'<a href="{foundation_href}">', f'<a href="{source_href}">', 1
        ).replace('<a href="SOURCE-SWAP">', f'<a href="{foundation_href}">', 1)
        require_structure_rejection(swapped_sources, "swapped source hrefs")
        swapped_topics = index_fixture.replace(
            f'<a href="{topic_href}">', '<a href="TOPIC-SWAP">', 1
        ).replace(
            f'<a href="{second_topic_href}">', f'<a href="{topic_href}">', 1
        ).replace('<a href="TOPIC-SWAP">', f'<a href="{second_topic_href}">', 1)
        require_structure_rejection(swapped_topics, "swapped topic hrefs")
        require_structure_rejection(
            index_fixture.replace(
                f'<a href="{foundation_href}">Project-original foundations: 0 record(s)</a>',
                "Project-original foundations: 0 record(s)",
                1,
            ),
            "deleted foundations href",
        )
        require_structure_rejection(
            index_fixture.replace(
                f'<a href="{source_href}">', '<a href="/lattice-system/wrong/">', 1
            ),
            "wrong href on correct source row",
        )
        require_structure_rejection(
            index_fixture.replace(
                f'<a href="{source_href}">',
                f'<a href="{source_href}"><a href="{source_href}">',
                1,
            ),
            "nested second anchor",
        )
        require_structure_rejection(
            index_fixture.replace(
                "</a></li>",
                f'</a><a href="{source_href}">extra</a></li>',
                1,
            ),
            "extra second anchor",
        )
        require_structure_rejection(
            index_fixture.replace("</a></li>", "</a>outside</li>", 1),
            "text outside a linked row anchor",
        )
        anchorless_index = re.sub(r"<a href=\"[^\"]+\">(.*?)</a>", r"\1", index_fixture)
        require_structure_rejection(anchorless_index, "anchorless linked rows")
        status_fixture = fixture_rows(expected_status_index_rows(literature_catalog))
        status_with_moved_href = status_fixture.replace(
            ">proved with documented axioms: 1</li>",
            f'><a href="{foundation_href}">proved with documented axioms: 1</a></li>',
            1,
        )
        require_structure_rejection(
            status_with_moved_href, "href moved onto a nonlink status row"
        )
        moved_href = (
            index_fixture.replace(
                f'<a href="{foundation_href}">Project-original foundations: 0 record(s)</a>',
                "Project-original foundations: 0 record(s)",
                1,
            )
            + status_with_moved_href
        )
        require_structure_rejection(moved_href, "href moved to a nonlink status row")

        metadata_fixture = (
            'Generated formalization-status view complete interim legacy catalogue'
            '<ul data-generated-metadata="true">'
            '<li data-meta="catalog-state">Catalogue state: prototype</li>'
            '<li data-meta="schema-version">Schema version: 1</li>'
            f'<li data-meta="input-sha256">Input SHA-256: {"0" * 64}</li>'
            '<li data-meta="revision">Deploy revision: r</li>'
            '<li data-meta="catalog-link" data-href="/lattice-system/formalization-status/v1/catalog.json"><a href="/lattice-system/formalization-status/v1/catalog.json">Machine data: version 1 catalogue</a></li>'
            '<li data-meta="schema-link" data-href="/lattice-system/formalization-status/v1/schema.json"><a href="/lattice-system/formalization-status/v1/schema.json">Schema: version 1 schema</a></li>'
            '<li data-meta="publication-link" data-href="/lattice-system/formalization-status/v1/publication.json"><a href="/lattice-system/formalization-status/v1/publication.json">Build metadata: publication sidecar</a></li>'
            '<li data-meta="authority-link" data-href="/lattice-system/formalization/legacy/"><a href="/lattice-system/formalization/legacy/">Current authority: complete interim legacy catalogue</a></li>'
            '</ul>'
            + index_fixture
        )
        metadata_parser = parse_record_html(metadata_fixture, "metadata collision fixture")
        assert_metadata(
            metadata_parser,
            {"catalog_state": "prototype", "input_sha256": "0" * 64, "schema_version": 1},
            "r",
            "metadata collision fixture",
        )
        authoritative_metadata = (
            metadata_fixture.replace(
                "complete interim legacy catalogue",
                "validated version 1 catalogue",
            )
            .replace("Catalogue state: prototype", "Catalogue state: authoritative")
            .replace(
                'data-href="/lattice-system/formalization/legacy/"',
                'data-href="/lattice-system/formalization-status/v1/catalog.json"',
            )
            .replace(
                'href="/lattice-system/formalization/legacy/"',
                'href="/lattice-system/formalization-status/v1/catalog.json"',
            )
        )
        assert_metadata(
            parse_record_html(authoritative_metadata, "authoritative metadata fixture"),
            {
                "catalog_state": "authoritative",
                "input_sha256": "0" * 64,
                "schema_version": 1,
            },
            "r",
            "authoritative metadata fixture",
        )
        require_structure_rejection(
            metadata_fixture.replace(
                '<a href="/lattice-system/formalization-status/v1/catalog.json">'
                "Machine data: version 1 catalogue</a>",
                "Machine data: version 1 catalogue",
                1,
            ),
            "removed metadata anchor",
        )
        require_structure_rejection(
            metadata_fixture.replace(
                '<a href="/lattice-system/formalization-status/v1/schema.json">',
                '<a href="/lattice-system/wrong-schema.json">',
                1,
            ),
            "changed metadata anchor href",
        )

        missing_module = project_html.replace(module_row, "", 1)
        try:
            validate_fixture(
                missing_module,
                project_record,
                project_catalog,
                "summary-containing-module fixture",
            )
        except ValueError:
            pass
        else:
            raise AssertionError("missing Module field was hidden by matching summary text")
    finally:
        shutil.rmtree(temporary)
    check_workflow_invariants(REPO_ROOT)
    with tempfile.TemporaryDirectory(
        prefix="formalization-workflow-owner-",
        dir=REPO_ROOT / ".self-local/tmp",
    ) as workflow_temporary:
        fixture_root = Path(workflow_temporary)
        fixture_workflows = fixture_root / ".github/workflows"
        fixture_workflows.mkdir(parents=True)
        shutil.copy2(
            REPO_ROOT / ".github/workflows/formalization_pages.yml",
            fixture_workflows / "formalization_pages.yml",
        )
        shutil.copy2(
            REPO_ROOT / ".github/workflows/lean_action_ci.yml",
            fixture_workflows / "lean_action_ci.yml",
        )
        (fixture_workflows / "second_owner.yaml").write_text(
            "name: Competing owner\n"
            "jobs:\n"
            "  deploy:\n"
            "    permissions:\n"
            "      pages: write\n"
            "      id-token: write\n"
            "    steps:\n"
            "      - uses: actions/deploy-pages@v4\n",
            encoding="utf-8",
        )
        try:
            check_workflow_invariants(fixture_root)
        except ValueError as error:
            if "competing Pages owner" not in str(error):
                raise AssertionError(
                    "second-owner workflow failed for an unrelated reason"
                ) from error
        else:
            raise AssertionError("second Pages deployment owner was accepted")


def parse_args() -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--site-dir", type=Path)
    parser.add_argument("--source-dir", type=Path)
    parser.add_argument("--expected-catalog", type=Path)
    parser.add_argument("--revision")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--print-regular-file-bytes", type=Path)
    return parser.parse_args()


def main() -> int:
    """Run requested staged-source, rendered-site, and regression checks."""
    args = parse_args()
    try:
        if args.print_regular_file_bytes is not None:
            print(regular_file_bytes(args.print_regular_file_bytes))
            return 0
        if args.self_test:
            run_self_tests()
        if args.source_dir is not None:
            if not args.revision or args.expected_catalog is None:
                raise ValueError("--source-dir requires --expected-catalog and --revision")
            check_staged_source(args.source_dir, args.expected_catalog, args.revision)
            if args.self_test:
                run_staged_mutation_tests(
                    args.source_dir,
                    args.expected_catalog,
                    args.revision,
                )
        if args.site_dir is not None:
            if args.source_dir is None or args.expected_catalog is None or not args.revision:
                raise ValueError(
                    "--site-dir requires --source-dir, --expected-catalog, and --revision"
                )
            check_built_site(
                args.site_dir,
                args.source_dir,
                args.expected_catalog,
                args.revision,
            )
        if (
            not args.self_test
            and args.source_dir is None
            and args.site_dir is None
            and args.print_regular_file_bytes is None
        ):
            raise ValueError("select --self-test, --source-dir, or --site-dir")
    except (OSError, ValueError, AssertionError, json.JSONDecodeError) as error:
        raise SystemExit(f"error: {error}") from error
    print("generated formalization site: checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
