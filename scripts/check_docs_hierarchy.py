#!/usr/bin/env python3
r"""Validate the staged human-documentation hierarchy with the Python stdlib.

The published catalogue is `docs/index.md` frozen at `BASELINE_COMMIT` and put through
`approved_changes`: a single chain of audited literal rewrites. The removal entries search
verbatim baseline text -- a row leaves the published catalogue only by a rewrite of its own full
frozen row text, trailing newline included, to the empty string -- while some correction entries
search text an earlier entry in the chain inserts, as their own comments record. That no entry
retires a row by keying on a Lean name is enforced by
`approved_replacements_shape_and_row_identity_self_test`: `_approved_replacements` has to stay a
chain of two-string-literal `.replace` calls, and `BASELINE_CATALOGUE_ROW_COUNT - (rows that
chain drops) == len(published_catalogue_rows())` has to hold with every row-count-changing entry
spelled as one whole frozen line, so a rewrite keyed on a name, at any narrowing and at any
depth, leaves the catalogue short of what the chain accounts for. An entry that adds a row is
refused there too, until a reviewed diff generalizes the identity to carry a term for one. The
absence of a declaration from the Lean tree is in any case never on its own a reason to retire
the row that records it: at the revision this was measured, 91 of the 2050 published catalogue
rows (4.4%) name at least one identifier the Lean tree no longer spells -- 64 of them name
nothing else -- across 148 distinct absent identifier tokens.

Two pins cover the transform. `APPROVED_CHANGES_SHA256` pins sha256 over

    approved_changes(catalogue_baseline_text())

and `PUBLISHED_ROWS_SHA256` pins sha256 over

    "\n".join(published_catalogue_rows())

both encoded as UTF-8. `catalogue_baseline_text()` is the single spelling of the compared slice
and `published_catalogue_rows()` the single spelling of the row sequence `main()` compares the
legacy pages against, so narrowing the slice moves the first pin and skipping a row in the
extractor moves the second, instead of quietly unpublishing the rows they drop. Every edit to
`_approved_replacements` or `_drop_private_instructions_ref` that changes the transformed bytes
moves the first pin, and moves the second as well whenever the change reaches a table row;
output-neutral edits, such as dropping a rewrite that no longer matches anything, move neither.
An edit that does move a pin recomputes it in the same commit with

    python3 -c 'import sys, hashlib; sys.path.insert(0, "scripts"); \
    import check_docs_hierarchy as c; \
    print(hashlib.sha256(c.approved_changes(c.catalogue_baseline_text()) \
    .encode("utf-8")).hexdigest())'

    python3 -c 'import sys, hashlib; sys.path.insert(0, "scripts"); \
    import check_docs_hierarchy as c; \
    print(hashlib.sha256("\n".join(c.published_catalogue_rows()) \
    .encode("utf-8")).hexdigest())'

and states which rows the new values reflect. Recomputing a pin is never on its own an
authorization for what moved: the legacy pages still have to be edited to match, and the
catalogue-row comparison is what proves they do. What the pins buy is that a change to the
published catalogue is a legible diff and a moved hash rather than a silent edit.

Two further pins cover the machinery rather than the content. `ROW_PATH_SOURCE_SHA256` pins
sha256 over the source text of the row-derivation nodes `_ROW_PATH_SOURCE_NAMES` lists, and
`APPROVED_ENTRIES_SHA256` pins sha256 over the ordered literal pairs of the audited chain, so
that surgery which leaves the published bytes alone is a moved pin rather than a silent edit.
Both hash text this file already carries, never a serialization of the parsed tree or of a
literal, so their values are the same on every interpreter that can parse this file. They are
recomputed with

    python3 -c 'import sys; sys.path.insert(0, "scripts"); \
    import check_docs_hierarchy as c; print(c._row_path_source_sha256())'

    python3 -c 'import sys; sys.path.insert(0, "scripts"); \
    import check_docs_hierarchy as c; \
    print(c._approved_entries_sha256(c._approved_replacements_chain(c._own_source())[0]))'

under the same clause: a recompute is never on its own an authorization for what moved.
`BASELINE_CATALOGUE_ROW_COUNT` describes a blob frozen at `BASELINE_COMMIT` and
`ROW_PATH_SOURCE_SHA256` the machinery that derives rows from it, so no catalogue content edit
moves either; a commit that moves one is machinery surgery, and that is the signature review
looks for.

One residual stays with review. Editing the row-derivation machinery and recomputing its pins
passes every check here, as does editing the pages and recomputing the two byte-parity pins,
because a recompute restates what the machinery now produces and judges nothing about it. What
the identity buys against that is a single channel: a row can leave the published catalogue only
through one full-row literal of one reviewed list, and every other route now moves a constant no
content edit touches.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import html
import posixpath
import re
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from collections.abc import Callable
from pathlib import Path
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
BASELINE_COMMIT = "6519099024bf156b87ac0c807c6633c513792581"
LEDGER_BASELINE_COMMIT = "94385e4521a36025496bffae7a825aab8362d46b"
# The published catalogue is this half-open line range of the frozen index. Spelled once, so
# that the pin below hashes the same object the page comparison uses instead of a re-spelled
# copy of it that could be narrowed on its own.
CATALOGUE_BASELINE_SLICE = slice(216, 2731)
# Pins the published catalogue text; this module's docstring records exactly what is hashed
# and how the pin is legitimately updated.
APPROVED_CHANGES_SHA256 = "2d57e7b3d3e02f04ee3f19c864c9f1cbfc125115d37bd13086832aa50b079da0"
# Pins the row sequence `main()` actually compares the legacy pages against. The text pin above
# does not reach it: the rows are derived from the transformed text by `table_data_rows`, which
# is outside the pinned text, so without this pin a row skipped there would go unpublished with
# the text pin undisturbed.
PUBLISHED_ROWS_SHA256 = "4af128f2c5f915e46c4df1aad461c5869ace8ac257525a0c31112ec95a102fdf"
SCOPED_ROOTS = [DOCS / name for name in ("formalization", "roadmap", "limitations", "history")]
PAGES = [DOCS / "index.md"] + sorted(path for root in SCOPED_ROOTS for path in root.rglob("*.md"))
ALL_DOC_PAGES = sorted(DOCS.rglob("*.md"))
SOFT_BYTES = 64 * 1024
HARD_BYTES = 128 * 1024
SOFT_LINES = 500
HARD_LINES = 1000
SOFT_ROWS = 100
LONG_CELL_BYTES = 2 * 1024
LEGACY_DETAIL = re.compile(
    r"<!-- legacy-detail:start:(\d+) -->\n(.*?)<!-- legacy-detail:end:\1 -->",
    re.DOTALL,
)
LEGACY_DETAIL_LEAN = re.compile(
    r"<!-- legacy-detail-lean:start:(\d+) -->(.*?)<!-- legacy-detail-lean:end:\1 -->",
    re.DOTALL,
)
LEGACY_DETAIL_FILE = re.compile(
    r"<!-- legacy-detail-file:start:(\d+) -->(.*?)<!-- legacy-detail-file:end:\1 -->",
    re.DOTALL,
)
# Published Kramdown basic_generate_id values from main:docs/index.md.  This is
# deliberately a fixed migration fixture, not regenerated from the old page at
# validation time.
FORMER_ROOT_IDS = (
    (6, 'lattice-system'),
    (14, 'design-axis-graphs-not-lattices'),
    (42, 'scope'),
    (53, 'refactoring-conventions-and-review-criteria'),
    (72, 'deleted-routes-what-this-index-used-to-document'),
    (110, 'roadmap'),
    (155, 'appendix-a-status-and-axiomatization-policy'),
    (217, 'formalized-theorems'),
    (229, 'single-site-pauli-operators'),
    (244, 'spin-12-operators-tasaki-21'),
    (259, 'spin-12-rotation-operators-tasaki-21-eq-2126'),
    (297, 'd-rotation-matrices-r-general--tasaki-21-eq-2111'),
    (305, 'z--z-representation-tasaki-21-eqs-2127-2134'),
    (313, 'd-rotation-matrices-r-tasaki-21-eq-2128'),
    (325, 'pauli-basis-decomposition-tasaki-21-problem-21a-s--12'),
    (337, 'polynomial-basis-decomposition-for-s--1-tasaki-21-problem-21a-s--1'),
    (353, 's--1-matrix-representations-tasaki-21-eq-219'),
    (365, 'spin-s-operators-general-s--0-parameterised-by-n--2s--'),
    (410, 'basis-states-and-raisinglowering-tasaki-21'),
    (425, 'basis-states-and-raisinglowering-for-s--1-tasaki-21'),
    (467, 'time-reversal-map-for-s--12-tasaki-23'),
    (506, 'multi-body-operator-space-abstract-lattice'),
    (525, 'generic-matrix-analysis-helpers-mathmatrixanalysis'),
    (549, 'horschvon-der-linden-low-lying-states-tasaki-34-theorem-31'),
    (730, 'boseeinstein-condensation-of-hard-core-bosons-tasaki-5152'),
    (739, 'antiferromagnetic-heisenberg-chains-and-the-haldane-conjecture-tasaki-61'),
    (752, 'the-aklt-model-tasaki-71'),
    (784, 'total-spin-operator-tasaki-22-eq-227-228'),
    (1256, 'two-site-spin-inner-product-tasaki-22-eq-2216'),
    (1301, 'one-dimensional-open-chain-quantum-ising'),
    (1325, 'testing-infrastructure'),
    (1349, 'gibbs-state-tasaki-33'),
    (1444, 'heisenberg-chain-tasaki-35'),
    (1562, 'perron-frobenius-theorem-mathperronfrobeniuslean-mathperronfrobeniusprimitivelean-mathcollatzwielandtlean-mathperronfrobeniusmainlean'),
    (1588, 'spin-s-marshallliebmattis-on-the-magnetization-sector-tasaki-25-theorem-22-generic-s-sector-form'),
    (2017, 'spin-s-saturated-ferromagnetic-state-tasaki-24-generalised'),
    (2149, 'single-mode-fermion-p2-skeleton'),
    (2246, 'multi-mode-fermion-via-jordanwigner-p2-backbone'),
    (2364, 'fock-space-representation-and-slater-determinants-tasaki-923'),
    (2379, 'hubbard-spin-symmetry--full-su2-invariance-tasaki-933'),
    (2400, 'hubbard-all-up-spin-state-and-saturated-ferromagnetism-tasaki-1111'),
    (2425, 'hubbard-hard-core-subspace-tasaki-112'),
    (2435, 'hubbard-hard-core-projection-tasaki-112'),
    (2452, 'hubbard-one-hole-hard-core-basis-states-tasaki-112'),
    (2464, 'jordanwigner-string-action-on-basis-states-tasaki-112-infrastructure'),
    (2476, 'span-of-the-one-hole-hard-core-sector-tasaki-112-footnote-8'),
    (2487, 'hole-filling-hop-configuration-tasaki-112-eq-1124-spatial-content'),
    (2496, 'degenerate-perturbation-theory-second-order-effective-hamiltonian-tasaki-101-lemma-101'),
    (2505, 'liebs-theorem-for-the-attractive-hubbard-model-tasaki-1021-theorems-102--103'),
    (2514, 'spin-reflection-positivity-foundation-for-liebs-theorem-tasaki-1021-pr1-toward-discharging-theorem-102'),
    (2598, 'liebs-theorem-for-the-repulsive-hubbard-model-at-half-filling-tasaki-1022-theorem-104'),
    (2619, 'kubokishi-finite-temperature-susceptibility-bound-tasaki-1025-theorem-1011-axiom'),
    (2629, 'hubbard-effective-hamiltonian-on-the-hard-core-sector-tasaki-112'),
    (2639, 'tasaki-ordered-creation-basis-tasaki-112-eq-1123'),
    (2651, 'uniform-sign-hole-filling-action-tasaki-112-eq-1124'),
    (2661, 'effective-hamiltonian-matrix-element-tasaki-112-eq-1125'),
    (2668, 'cauchyschwarz-energy-bound-tasaki-112-eq-1129'),
    (2681, 'su2-symmetry-of-the-effective-hamiltonian-tasaki-112'),
    (2689, 'weak-nagaoka-spin-multiplet-tasaki-1121-theorem-115-core'),
    (2718, 'nagaokas-theorem-on-a-magnetization-sector-tasaki-1122-theorem-117--lemma-119'),
    (2725, 'general-flat-band-ground-states-the-annihilation-peel-behind-eq-11346-tasaki-1134'),
    (2732, 'continuum-limit-roadmap'),
    (2780, 'open-items--axioms'),
    (2786, 'todo-p1d--problem-21a-for-general-s--1-done'),
    (2808, 'todo--tasaki-problem-22c-su2-non-invariance--averaged-state-done'),
    (2828, 'tasaki-25-antiferromagnetic-status-issues-240-412'),
    (3028, 'todo--remove-remaining-7-per-theorem-linter-suppressions-issue-377'),
    (3038, 'links'),
)

# Published Kramdown basic_generate_id values from the single-page documented-axiom
# ledger, in the same fixed-fixture spirit as FORMER_ROOT_IDS.  Each id must stay
# reachable on the ledger page: either the heading still lives there, or the page
# carries an explicit compatibility anchor for it.
FORMER_LEDGER_IDS = (
    (7, 'documented-axiom-status-and-axiomatization-policy'),
    (12, 'appendix-a-status-and-axiomatization-policy'),
    (76, 'theorem-77-hexagonal-aklt-correlation-decay-and-infinite-volume-uniqueness'),
    (155, 'theorem-72-aklt-infinite-chain-unique-ground-state-with-a-nonzero-gap'),
    (212, 'theorem-73-stability-of-the-aklt-gap-under-small-local-perturbations'),
    (317, 'theorem-81-large-d-phase-of-the-anisotropic-s--1-chain-l-uniform-gap-and-clustering'),
    (339, 'theorem-83--d-model-nel-order-bounded-by-string-order'),
    (356, 'eq-833-oshikawa-parity-dependence-of-the-spin-s-vbs-string-order'),
    (369, 'spt-phase-markers-isshortrangegappeduniquegs-isproductstatehamiltonian'),
    (381, 'general-s-bond-inversion-parity-of-the-vbs-state-p-259-unnumbered-display'),
    (437, 'entanglement-entropy-marker-entanglemententropys'),
    (451, 'theorem-86-lieb-schultz-mattis-type-theorem-without-continuous-symmetry'),
    (464, 'theorem-88-rigorous-index-theorem-and-the-spt-phase-transition'),
    (480, 'theorem-89-stability-of-the-toric-codes-topological-order-under-arbitrary-local-perturbations'),
)

# Exact public targets for every Tasaki chapter projection.  These are a fixed
# review fixture: fragments are intentionally retained and validated.
CHAPTER_EXPECTED_TARGETS = {
    2: (
        "/formalization/legacy/01-single-site-pauli-operators/#legacy-catalogue-single-site-pauli-operators",
        "/formalization/legacy/02-spin-1-2-operators-tasaki-2-1/#legacy-catalogue-spin-12-operators-tasaki-21",
        "/formalization/legacy/03-spin-1-2-rotation-operators-tasaki-2-1-eq-2-1-26/#legacy-catalogue-spin-12-rotation-operators-tasaki-21-eq-2126",
        "/formalization/legacy/04-3d-rotation-matrices-general-tasaki-2-1-eq-2-1-11/#legacy-catalogue-3d-rotation-matrices-r-general--tasaki-21-eq-2111",
        "/formalization/legacy/05-z-z-representation-tasaki-2-1-eqs-2-1-27-2-1-34/#legacy-catalogue-z--z-representation-tasaki-21-eqs-2127-2134",
        "/formalization/legacy/06-3d-rotation-matrices-tasaki-2-1-eq-2-1-28/#legacy-catalogue-3d-rotation-matrices-r-tasaki-21-eq-2128",
        "/formalization/legacy/07-pauli-basis-decomposition-tasaki-2-1-problem-2-1-a-s-1-2/#legacy-catalogue-pauli-basis-decomposition-tasaki-21-problem-21a-s--12",
        "/formalization/legacy/08-polynomial-basis-decomposition-for-s-1-tasaki-2-1-problem-/#legacy-catalogue-polynomial-basis-decomposition-for-s--1-tasaki-21-problem-21a-s--1",
        "/formalization/legacy/09-s-1-matrix-representations-tasaki-2-1-eq-2-1-9/#legacy-catalogue-s--1-matrix-representations-tasaki-21-eq-219",
        "/formalization/legacy/10-spin-operators-general-s-0-parameterised-by/#legacy-catalogue-spin-s-operators-general-s--0-parameterised-by-n--2s--",
        "/formalization/legacy/11-basis-states-and-raising-lowering-tasaki-2-1/#legacy-catalogue-basis-states-and-raisinglowering-tasaki-21",
        "/formalization/legacy/12-basis-states-and-raising-lowering-for-s-1-tasaki-2-1/#legacy-catalogue-basis-states-and-raisinglowering-for-s--1-tasaki-21",
        "/formalization/legacy/13-time-reversal-map-for-tasaki-2-3/#legacy-catalogue-time-reversal-map-for-s--12-tasaki-23",
        "/formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-01/#legacy-catalogue-total-spin-operator-tasaki-22-eq-227-228-part-1-of-5",
        "/formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-02/#legacy-catalogue-total-spin-operator-tasaki-22-eq-227-228-part-2-of-5",
        "/formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-03/#legacy-catalogue-total-spin-operator-tasaki-22-eq-227-228-part-3-of-5",
        "/formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-04/#legacy-catalogue-total-spin-operator-tasaki-22-eq-227-228-part-4-of-5",
        "/formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-05/#legacy-catalogue-total-spin-operator-tasaki-22-eq-227-228-part-5-of-5",
        "/formalization/legacy/21-two-site-spin-inner-product-tasaki-2-2-eq-2-2-16/#legacy-catalogue-two-site-spin-inner-product-tasaki-22-eq-2216",
        "/formalization/legacy/27-spin-marshall-lieb-mattis-on-the-magnetization-sector-tasa-part-01/#legacy-catalogue-spin-s-marshallliebmattis-on-the-magnetization-sector-tasaki-25-theorem-22-generic-s-sector-form-part-1-of-4",
        "/formalization/legacy/27-spin-marshall-lieb-mattis-on-the-magnetization-sector-tasa-part-02/#legacy-catalogue-spin-s-marshallliebmattis-on-the-magnetization-sector-tasaki-25-theorem-22-generic-s-sector-form-part-2-of-4",
        "/formalization/legacy/27-spin-marshall-lieb-mattis-on-the-magnetization-sector-tasa-part-03/#legacy-catalogue-spin-s-marshallliebmattis-on-the-magnetization-sector-tasaki-25-theorem-22-generic-s-sector-form-part-3-of-4",
        "/formalization/legacy/27-spin-marshall-lieb-mattis-on-the-magnetization-sector-tasa-part-04/#legacy-catalogue-spin-s-marshallliebmattis-on-the-magnetization-sector-tasaki-25-theorem-22-generic-s-sector-form-part-4-of-4",
        "/formalization/legacy/28-spin-saturated-ferromagnetic-state-tasaki-2-4-generalised-part-01/#legacy-catalogue-spin-s-saturated-ferromagnetic-state-tasaki-24-generalised-part-1-of-2",
        "/formalization/legacy/28-spin-saturated-ferromagnetic-state-tasaki-2-4-generalised-part-02/#legacy-catalogue-spin-s-saturated-ferromagnetic-state-tasaki-24-generalised-part-2-of-2",
    ),
    3: (
        "/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-01/#legacy-catalogue-horschvon-der-linden-low-lying-states-tasaki-34-theorem-31-part-1-of-4",
        "/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-02/#legacy-catalogue-horschvon-der-linden-low-lying-states-tasaki-34-theorem-31-part-2-of-4",
        "/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-03/#authoritative-supplemental-implementation-record-34-trial-state-locality-core-and-problem-34b",
        "/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-04/#the-low-lying-state--eqs-3416-3417",
        "/formalization/legacy/24-gibbs-state-tasaki-3-3/#legacy-catalogue-gibbs-state-tasaki-33",
        "/formalization/legacy/25-heisenberg-chain-tasaki-3-5-part-01/#legacy-catalogue-heisenberg-chain-tasaki-35-part-1-of-2",
        "/formalization/legacy/25-heisenberg-chain-tasaki-3-5-part-02/#legacy-catalogue-heisenberg-chain-tasaki-35-part-2-of-2",
    ),
    4: (
        "/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-01/#tasaki-chapter-4-part-01",
        "/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-02/#tasaki-chapter-4-part-02",
    ),
    5: ("/formalization/legacy/17-bose-einstein-condensation-of-hard-core-bosons-tasaki-5-1-/#legacy-catalogue-boseeinstein-condensation-of-hard-core-bosons-tasaki-5152",),
    6: ("/formalization/legacy/18-antiferromagnetic-heisenberg-chains-and-the-haldane-conjec/#legacy-catalogue-antiferromagnetic-heisenberg-chains-and-the-haldane-conjecture-tasaki-61",),
    7: ("/formalization/legacy/19-the-aklt-model-tasaki-7-1/#legacy-catalogue-the-aklt-model-tasaki-71",),
    8: ("/formalization/legacy/19-the-aklt-model-tasaki-7-1/#tasaki-chapter-8-records",),
    9: (
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02/#tasaki-chapter-9-part-01",
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03/#tasaki-chapter-9-part-02",
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/#tasaki-chapter-9-part-03",
    ),
    10: (
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03/#tasaki-chapter-10-part-01",
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/#tasaki-chapter-10-part-02",
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-05/#authoritative-supplemental-implementation-record-1022-eq-1029-uniformsymmetric-ground-submodule-reduction",
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-06/#tasaki-chapter-10-part-03",
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-07/#authoritative-supplemental-implementation-record-theorem-106-discharge-arc-pr-1-staggered-spin-component-algebra",
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-08/#authoritative-supplemental-implementation-record-theorem-108-discharge-arc-pr-1-generic-shiftuniqueness-lemmas-and-the-shiba-hamiltonian-bridge",
    ),
    11: (
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02/#tasaki-chapter-11-part-01",
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03/#tasaki-chapter-11-part-02",
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/#tasaki-chapter-11-part-03",
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-09/#authoritative-supplemental-implementation-record-theorem-114-discharge-arc-pr-1-axiom-hypothesis-correction",
    ),
    "appendix-a": (
        "/formalization/legacy/15-generic-matrix-analysis-helpers/#legacy-catalogue-generic-matrix-analysis-helpers-mathmatrixanalysis",
        "/formalization/legacy/26-perron-frobenius-theorem/#legacy-catalogue-perron-frobenius-theorem-mathperronfrobeniuslean-mathperronfrobeniusprimitivelean-mathcollatzwielandtlean-mathperronfrobeniusmainlean",
    ),
}
CHAPTER_ROW_ANCHORS = {
    559: "tasaki-chapter-4-part-01",
    653: "tasaki-chapter-4-part-02",
    773: "tasaki-chapter-8-records",
    2368: "tasaki-chapter-9-part-01",
    2592: "tasaki-chapter-9-part-02",
    2606: "tasaki-chapter-9-part-03",
    2500: "tasaki-chapter-10-part-01",
    2605: "tasaki-chapter-10-part-02",
    2404: "tasaki-chapter-11-part-01",
    2482: "tasaki-chapter-11-part-02",
    2633: "tasaki-chapter-11-part-03",
}
SOURCE_MARKER = re.compile(
    r"<!-- legacy-source:start:(\d+):(\d+) -->\n(.*?)<!-- legacy-source:end:\1:\2 -->",
    re.DOTALL,
)


def fail(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


def baseline_index() -> str:
    return subprocess.run(
        ["git", "show", f"{BASELINE_COMMIT}:docs/index.md"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout


def catalogue_baseline_text() -> str:
    """The frozen catalogue region of the baseline index, before any audited rewrite.

    `main()` compares the legacy pages against the rows of `approved_changes` of this text,
    and `approved_changes_byte_parity_self_test` pins sha256 of that transformed text and of that
    row sequence, both reached through the same two helpers `main()` calls, so neither the pinned
    text nor the pinned rows can drift from the compared ones.
    """
    return "".join(baseline_index().splitlines(keepends=True)[CATALOGUE_BASELINE_SLICE])


def baseline_ledger() -> str:
    return subprocess.run(
        ["git", "show", f"{LEDGER_BASELINE_COMMIT}:docs/limitations/documented-axioms.md"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout


def front_matter(path: Path) -> tuple[dict[str, str], str]:
    text = path.read_text()
    if not text.startswith("---\n"):
        fail(f"missing front matter: {path.relative_to(ROOT)}")
    try:
        raw, body = text[4:].split("\n---\n", 1)
    except ValueError:
        fail(f"unterminated front matter: {path.relative_to(ROOT)}")
    values: dict[str, str] = {}
    for line in raw.splitlines():
        if ":" not in line:
            fail(f"invalid front matter line in {path.relative_to(ROOT)}: {line}")
        key, value = line.split(":", 1)
        values[key.strip()] = value.strip().strip('"')
    if not values.get("permalink", "").startswith("/"):
        fail(f"missing absolute permalink: {path.relative_to(ROOT)}")
    return values, body


def heading_anchor(heading: str) -> str:
    heading = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", heading)
    heading = re.sub(r"<[^>]*>", "", heading)
    heading = re.sub(r"^[^A-Za-z]+", "", heading)
    heading = re.sub(r"[^A-Za-z0-9 -]", "", heading)
    return heading.replace(" ", "-").lower()


def anchor_list(body: str) -> list[str]:
    result = re.findall(r'<a\s+id="([^"]+)"\s*></a>', body)
    result.extend(
        heading_anchor(match.group(1))
        for match in re.finditer(r"^#{1,6} (.+)$", body, flags=re.MULTILINE)
    )
    return result


def is_separator(line: str) -> bool:
    return line.startswith("|") and set(line.strip()) <= set("|-: ")


def validate_pipe_blocks(path: Path, body: str) -> None:
    lines = body.splitlines()
    for index, line in enumerate(lines):
        if not line.startswith("|") or (index and lines[index - 1].startswith("|")):
            continue
        if index + 1 >= len(lines) or not is_separator(lines[index + 1]):
            fail(f"pipe block lacks header/separator: {path.relative_to(ROOT)}:{index + 1}")


def table_data_rows(lines: list[str]) -> list[str]:
    result: list[str] = []
    for index, line in enumerate(lines):
        if not line.startswith("|") or is_separator(line):
            continue
        if index + 1 < len(lines) and is_separator(lines[index + 1]):
            continue
        result.append(line)
    return result


# Baseline catalogue rows carry two kinds of pointer to a working note that is not part of this
# repository: a trailing "; see ... (Issue #3542)." clause, and a parenthesised section pointer
# sitting directly after a backticked symbol. Both are dropped from the published rows; the issue
# reference the first one carries is kept. Each pattern is matched structurally, by the shape of
# its punctuation, so that the removed text is not reproduced here.
_WORKING_NOTE_CITATION = re.compile(r"; see `[^`]+` \(Issue #3542\)\.")
_WORKING_NOTE_SECTION_REF = re.compile(r" \(\w[\w-]* §\d+\.\d+ \w+ \d+\)")

# The same class of pointer appears once in baseline prose rather than in a table row, in the
# whitespace-normalized (still blockquote-prefixed) form handled here.
_WORKING_NOTE_PROSE_CITATION = re.compile(r"See > `[^`]+` and Issue #3542\.")

# Number of baseline sites each of the three removals above matches, in declaration order. Pinned
# for the same reason as MOVED_PROSE_LINK_REWRITE_COUNTS: a structural pattern that starts matching
# more (or fewer) sites than audited must fail loudly instead of silently editing the baseline.
WORKING_NOTE_REMOVAL_COUNTS = (2, 1, 1)


def _drop_working_note_citations(text: str) -> str:
    """Drop both catalogue-row pointers to the working note outside this repository."""
    text = _WORKING_NOTE_CITATION.sub(" (Issue #3542).", text)
    return _WORKING_NOTE_SECTION_REF.sub("", text)


def _drop_working_note_prose_citation(text: str) -> str:
    """Drop the prose form of the same working-note pointer."""
    return _WORKING_NOTE_PROSE_CITATION.sub("See Issue #3542.", text)


# One baseline catalogue row points at this repository's private, gitignored project-instructions
# file. The pointer is dropped from the published row; the sentence it trailed stands on its own.
# Matched structurally, by the shape of a parenthesised dotted Markdown filename, so that the
# private identifier is not reproduced here.
_PRIVATE_INSTRUCTIONS_REF = re.compile(r" \(\w+\.\w+\.md\)")

# Number of sites the removal above matches. Counted on the post-replacement baseline, which is the
# text the removal actually runs against, so that a literal rewrite introducing a match cannot slip
# past the audit. Pinned for the same reason as WORKING_NOTE_REMOVAL_COUNTS: a structural pattern
# that starts matching more (or fewer) sites than audited must fail loudly instead of silently
# editing the baseline.
PRIVATE_INSTRUCTIONS_REMOVAL_COUNT = 1


def _drop_private_instructions_ref(text: str) -> str:
    """Drop the catalogue-row pointer to the private project-instructions file."""
    return _PRIVATE_INSTRUCTIONS_REF.sub("", text)


def _approved_replacements(text: str) -> str:
    """Apply every audited literal rewrite, before the structural removals that follow them."""
    return _drop_working_note_citations(
        text.replace("(refactoring-conventions.html)", "(/lattice-system/refactoring-conventions/)")
        .replace(
            "(deprecations.html#remaining-linter-suppressions)",
            "(/lattice-system/deprecations/#remaining-linter-suppressions)",
        )
        .replace("(deprecations.html)", "(/lattice-system/deprecations/)")
        .replace("(jordan-wigner-overview.html)", "(/lattice-system/jordan-wigner-overview/)")
        .replace(
            "](#deleted-routes-what-this-index-used-to-document)",
            "](/lattice-system/history/deleted-routes/#deleted-routes-what-this-index-used-to-document)",
        )
        .replace(
            "mps_theorem_7_5` (**PROVED axiom-free; Standard 3; PR pending**)",
            "mps_theorem_7_5` (**PROVED axiom-free; Standard 3; merged in commit `8286635d`**)",
        )
        .replace(
            "commutes with every single-site operator farther than `r` from `x`, equivalent to "
            "`support ⊆ {y : ringDist x y ≤ r}` by factor double-commutant;",
            "commutes with every single-site operator farther than `r` from `x`; the general "
            "equivalence between this commutant form and `support ⊆ {y : ringDist x y ≤ r}` is a "
            "proved theorem of this repository, `supportedOnS_iff_commute_onSiteS` "
            "(`Quantum/SpinS/OperatorSupport.lean`, fixture "
            "`Tests/SupportCommutantBridgePin.lean`), and `IsLocalRangeR` is connected to it by "
            "`isLocalRangeR_iff_supportedOnS`: the marker holds exactly when `ĥ_x` is "
            "`SupportedOnS` on the window `window L r x`, which `window_eq_siteBall` identifies "
            "with the ring-distance ball `siteBall (ringDist L) r x` "
            "(`Math/Combinatorics/SiteBall.lean`), fixture "
            "`Tests/RingBallLocalityBridgePin.lean`; the same general equivalence carries the "
            "open-chain window `chainWindow L a b` (`supportedOnS_chainWindow_iff`, "
            "`Quantum/SpinS/ChainWindowSupport.lean`, fixture "
            "`Tests/ChainWindowSupportPin.lean`);",
        )
        .replace(
            "mps_theorem_7_6` is **PROVED axiom-free; Standard 3; PR pending**",
            "mps_theorem_7_6` is **PROVED axiom-free; Standard 3; merged in commit `50b30949`**",
        )
        .replace(
            "| `openAnisotropicChainHamiltonianS` / `HasStringLRO` / `tasaki_theorem_8_2` | "
            "**§8.1.2–§8.1.3 Hidden order forces edge states** (Theorem 8.2, Koma–Tasaki; "
            "eqs. (8.1.9)–(8.1.11)): in the anisotropic chain, hidden antiferromagnetic order "
            "(positive den Nijs–Rommelse string order `O_string^{(α)}(D)`, §7.2.1) distinguishes "
            "the Haldane phase (`0≤D<D_c`) from the large-`D` phase, and forces low-lying edge "
            "states. `openAnisotropicChainHamiltonianS L D` is the **open-boundary** anisotropic "
            "chain (`openAnisotropicChainCoupling`, no wrap-around — the free ends carry the "
            "`S=1/2` edge spins). `HasStringLRO L D Φ q` (marker) is the hidden-order bound "
            "(8.1.10) `⟨Φ\\|(Ô_string^{(α)}/L)²\\|Φ⟩ ≥ q_α` (`q_α>0`). `tasaki_theorem_8_2` "
            "(**AXIOM**): for fixed `D, q` there are **L-independent** `C_ν>0` such that for "
            "every `L>0`, whenever `Φ` is the **unique** ground state "
            "(`IsUniqueChainGroundState`) of `Ĥ_D^open` at `E₀` with `HasStringLRO`, there are "
            "**three linearly independent excited states** `Ψ_ν` (`ν:Fin 3`, "
            "`LinearIndependent ℂ Ψ`) with `Ĥ_D^open Ψ_ν = E_ν Ψ_ν` and "
            "`E₀ < E_ν ≤ E₀ + C_ν/L` — hidden order ⟹ near four-fold degeneracy (free `S=1/2` "
            "edge spins). `C_ν` quantified outside `∀L` (genuinely length-uniform). Proof: "
            "Horsch–von der Linden / Koma–Tasaki variational argument (as Theorem 3.1) | "
            "`Quantum/SpinS/AnisotropicEdgeStates.lean` |",
            "| `openAnisotropicChainHamiltonianS` / `HasStringLRO` / `tasaki_theorem_8_2` | "
            "**§8.1.2–§8.1.3 Hidden order forces edge states** (Theorem 8.2, Koma–Tasaki; "
            "**PROVED**, `#print axioms` = std3, merged in commit `244c3ea9`; "
            "eqs. (8.1.8)–(8.1.12), pp. 236–238): hidden antiferromagnetic order (positive "
            "den Nijs–Rommelse string order `O_string^{(α)}(D)`, §7.2.1) distinguishes the "
            "Haldane phase (`0≤D<D_c`) from the large-`D` phase and forces low-lying edge "
            "states. `openAnisotropicChainHamiltonianS L D` is the **open-boundary** anisotropic "
            "chain (`openAnisotropicChainCoupling`, no wrap-around — the free ends carry the "
            "`S=1/2` edge spins). `HasStringLRO L Φ q` (no `D` argument; now a **concrete** "
            "predicate, not an uninterpreted marker) is the hidden-order bound (8.1.10) "
            "`⟨Φ\\|(Ô_string^{(α)}/L)²\\|Φ⟩ ≥ q_α` (`q_α>0`), built via the spin-one half turn "
            "`spinOneHalfTurnS α = 1 − 2(Ŝ^{(α)})²` (closed form of `exp(iπŜ^{(α)})`). "
            "`tasaki_theorem_8_2` (now a **theorem**, formerly a documented axiom): for fixed "
            "`D≥0, q>0` there are an eventual threshold `L₀` (`=1`) and **L-independent** "
            "`C_ν = 64(3+D)/q_ν > 0` such that for every `L≥L₀`, whenever `Φ` is the **unique** "
            "ground state (`IsUniqueChainGroundState`) of `Ĥ_D^open` at `E₀` with "
            "`HasStringLRO`, there are **three linearly independent excited states** `Ψ_ν` "
            "with `Ĥ_D^open Ψ_ν = E_ν Ψ_ν` and `E₀ < E_ν ≤ E₀ + C_ν/L` — hidden order ⟹ near "
            "four-fold degeneracy (free `S=1/2` edge spins). Proof: `Z₂×Z₂` half-turn symmetry "
            "(`manyBodyReversalS`, `magParityDiagS`) selects three sector eigenvectors; a "
            "double-commutator support bound feeds the Horsch–von der Linden / Koma–Tasaki "
            "variational gap estimate (as Theorem 3.1) | "
            "`Quantum/SpinS/AnisotropicEdgeStates.lean`; "
            "`Quantum/SpinS/AnisotropicEdgeStringOrder.lean`; "
            "`Quantum/SpinS/AnisotropicEdgeSymmetry.lean`; "
            "`Quantum/SpinS/AnisotropicEdgeEnergy.lean`; "
            "`Quantum/SpinS/AnisotropicEdgeStatesDischarge.lean` |",
        )
        .replace(
            "| `ktUnitaryS` / `piRotationS` / `IsZ2Z2Invariant` / `tasaki_prop_8_4` | "
            "**§8.2.2–§8.2.3 Kennedy–Tasaki transformation + Proposition 8.4** (Pollmann–Turner–Berg–"
            "Oshikawa; eqs. (8.2.5)–(8.2.7)): the nonlocal unitary realizing hidden Z₂×Z₂ symmetry "
            "breaking. `ktUnitaryS L` (marker) is the Kennedy–Tasaki unitary "
            "`Û_KT = ∏_{u<v} exp(iπ Ŝ_u^{(3)} Ŝ_v^{(1)})` (eq. 8.2.5), with `ktUnitaryS_sq` "
            "(`Û_KT²=1`) and `ktUnitaryS_selfAdjoint` (`Û_KT=Û_KT†`) — a self-adjoint involution. "
            "`piRotationS L α = ∏_x exp(iπ Ŝ_x^{(α)})` (**concrete**, on-site matrix exponentials) "
            "is the π-rotation about axis `α`; `IsZ2Z2Invariant H` = "
            "`(Û_π^{(α)})† H Û_π^{(α)} = H` for all `α` (commutes with all three π-rotations). "
            "`HasShortRangeInteraction`/`HasSomeShortRangeInteraction` (markers) capture range-`r` "
            "locality. `tasaki_prop_8_4` (**AXIOM**): for a short-range open-chain `Ĥ`, "
            "`Û_KT Ĥ Û_KT` is again short-range **iff** `Ĥ` is Z₂×Z₂ invariant — the "
            "hidden-symmetry-breaking picture is effective exactly when `Ĥ` has Z₂×Z₂ symmetry | "
            "`Quantum/SpinS/KennedyTasakiTransformation.lean` |",
            "| `ktUnitaryS` / `piRotationS` / `IsZ2Z2Invariant` / `tasaki_prop_8_4_local_monomial` | "
            "**§8.2.2–§8.2.3 Kennedy–Tasaki transformation + Proposition 8.4** (Pollmann–Turner–Berg–"
            "Oshikawa; **PROVED**, `#print axioms` = std3, merged in commit `2cb2cfc8`; "
            "eqs. (8.2.5)–(8.2.7), (8.2.12)–(8.2.15), (8.2.17)): the nonlocal unitary realizing "
            "hidden Z₂×Z₂ symmetry breaking. `ktUnitaryS L = ∏_{u<v} (1 − 2(Ŝ_u^{(3)} Ŝ_v^{(1)})²)` "
            "is now **concrete** (not a marker): the `S=1` closed form of "
            "`Û_KT = ∏_{u<v} exp(iπ Ŝ_u^{(3)} Ŝ_v^{(1)})` (eq. 8.2.5), a self-adjoint involution "
            "(`ktUnitaryS_sq`, `ktUnitaryS_selfAdjoint`). `piRotationS L α = "
            "∏_x (1 − 2(Ŝ_x^{(α)})²)` is likewise **concrete** (the `S=1` closed form of the "
            "π-rotation about axis `α`); `IsZ2Z2Invariant H` = "
            "`(Û_π^{(α)})† H Û_π^{(α)} = H` for all `α`. `tasaki_prop_8_4_local_monomial` (now a "
            "**theorem**, formerly an axiom): the printed Proposition quantifies over short-range "
            "Hamiltonians, but §8.2.2–§8.2.3 argue and prove only a **single local monomial** "
            "`O_w = ∏_i Ŝ_{x_i}^{(α_i)}` (`w : List (Fin L × Fin 3)`); `IsLocalWindowS L N a b` "
            "(commutant form) replaces the deleted markers "
            "`HasShortRangeInteraction`/`HasSomeShortRangeInteraction`. For `w` supported in an "
            "interior window `[a,b]` with margin on both sides (`0<a`, `b+1<L`), "
            "`Û_KT O_w Û_KT` is again local in `[a,b]` **iff** `O_w` is Z₂×Z₂ invariant — via "
            "the sign identity `Û_π^{(α)} O_w Û_π^{(α)} = (−1)^{c_α} O_w` "
            "(`c_α = #{i∣α_i≠α}`) rather than a bare parity biconditional (false as an iff at "
            "`O_w = 0`). Proof: half-turn control-polynomial algebra of §8.2.2; the "
            "Hamiltonian-level (sum) statement is deliberately out of scope | "
            "`Quantum/SpinS/SpinOneHalfTurnRegion.lean`; "
            "`Quantum/SpinS/KennedyTasakiTransformation.lean`; "
            "`Quantum/SpinS/KennedyTasakiTransformRules.lean`; "
            "`Quantum/SpinS/KennedyTasakiMonomial.lean`; "
            "`Quantum/SpinS/KennedyTasakiProp84.lean` |",
        )
        # (Applied after the row replacement above: what it matches is the locality sentence
        # and file column that replacement inserts, not baseline text, so the order of those
        # two entries is load-bearing.)
        .replace(
            "`IsLocalWindowS L N a b` (commutant form) replaces the deleted markers "
            "`HasShortRangeInteraction`/`HasSomeShortRangeInteraction`. For `w` supported in an "
            "interior window `[a,b]` with margin on both sides (`0<a`, `b+1<L`), `Û_KT O_w Û_KT` is "
            "again local in `[a,b]` **iff** `O_w` is Z₂×Z₂ invariant — via the sign identity "
            "`Û_π^{(α)} O_w Û_π^{(α)} = (−1)^{c_α} O_w` (`c_α = #{i∣α_i≠α}`) rather than a bare "
            "parity biconditional (false as an iff at `O_w = 0`). Proof: half-turn "
            "control-polynomial algebra of §8.2.2; the Hamiltonian-level (sum) statement is "
            "deliberately out of scope | `Quantum/SpinS/SpinOneHalfTurnRegion.lean`; "
            "`Quantum/SpinS/KennedyTasakiTransformation.lean`; "
            "`Quantum/SpinS/KennedyTasakiTransformRules.lean`; "
            "`Quantum/SpinS/KennedyTasakiMonomial.lean`; `Quantum/SpinS/KennedyTasakiProp84.lean` |",
            "locality is `SupportedOnS (chainWindow L a b)`, replacing the deleted markers "
            "`HasShortRangeInteraction`/`HasSomeShortRangeInteraction`. For `w` supported in an "
            "interior window `[a,b]` with margin on both sides (`0<a`, `b+1<L`), `Û_KT O_w Û_KT` is "
            "again local in `[a,b]` **iff** `O_w` is Z₂×Z₂ invariant — via the sign identity "
            "`Û_π^{(α)} O_w Û_π^{(α)} = (−1)^{c_α} O_w` (`c_α = #{i∣α_i≠α}`) rather than a bare "
            "parity biconditional (false as an iff at `O_w = 0`). Proof: half-turn "
            "control-polynomial algebra of §8.2.2; the Hamiltonian-level (sum) statement is "
            "deliberately out of scope | `Quantum/SpinS/ChainWindowSupport.lean`; "
            "`Quantum/SpinS/SpinOneHalfTurnRegion.lean`; "
            "`Quantum/SpinS/KennedyTasakiTransformation.lean`; "
            "`Quantum/SpinS/KennedyTasakiTransformRules.lean`; "
            "`Quantum/SpinS/KennedyTasakiMonomial.lean`; `Quantum/SpinS/KennedyTasakiProp84.lean` |",
        )
        .replace(
            "| `IsTimeReversalInvariant` / `IsBondInversionInvariant` / `vbsInversionParityS` / "
            "`tasaki_spt_classification` | **§8.3.2–§8.3.3 Protecting symmetries + topological indices "
            "for SPT** (Pollmann–Turner–Berg–Oshikawa; eqs. (8.3.6)–(8.3.10)): the Haldane phase is "
            "protected by any of three symmetries — (S1) Z₂×Z₂ (`IsZ2Z2Invariant`), (S2) time-reversal "
            "(`IsTimeReversalInvariant` marker), (S3) bond-centered inversion (`IsBondInversionInvariant` "
            "marker). `vbsInversionParityS L S` (marker, ℤ) + `tasaki_vbs_inversion_parity` (**AXIOM**): "
            "`Û_inv|Φ_VBS^S⟩ = (−1)^{L·S}|Φ_VBS^S⟩` — odd `L·S` ⟹ odd parity ⟹ Z₂ obstruction to "
            "connecting to the trivial state. `IsSpinSVBSNontrivialSPT S` (marker) + "
            "`tasaki_spt_classification` (**AXIOM**): the spin-`S` VBS is a nontrivial SPT phase **iff "
            "`S` is odd** (even `S` ⇒ trivial). `entanglementEntropyS` (marker, eqs. 8.3.7–8.3.8): the "
            "bipartite entanglement entropy `−Σ p_j log p_j` from the Schmidt decomposition. §8.3.3 is "
            "heuristic; precise indices come in §8.3.4 (MPS) / §8.3.6 (Ogata) | "
            "`Quantum/SpinS/SPTTopologicalIndex.lean` |",
            "| `IsTimeReversalInvariant` / `IsBondInversionInvariant` / `vbsInversionParityS` / "
            "`entanglementEntropyS` | "
            "**§8.3.2–§8.3.3 Protecting symmetries + topological indices for SPT** "
            "(Pollmann–Turner–Berg–Oshikawa; eqs. (8.3.6)–(8.3.10), pp. 256–263): the Haldane phase is "
            "protected by any of three symmetries — (S1) Z₂×Z₂ (`IsZ2Z2Invariant`), (S2) time-reversal "
            "(`IsTimeReversalInvariant` marker — a duplicate of `IsTimeReversalSymmetricS` "
            "(`LiebSchultzMattisDiscrete.lean`, prose cross-reference, not a Lean consumer) at "
            "`N = 2`, kept in parallel since consolidating it is a deletion needing its own approval), "
            "and (S3) bond-centered inversion (`IsBondInversionInvariant` marker). "
            "`vbsInversionParityS L S` (marker, ℤ) + `tasaki_vbs_inversion_parity` (**AXIOM**, a "
            "**discharge target**, not a documented won't-do): `Û_inv|Φ_VBS^S⟩ = (−1)^{L·S}|Φ_VBS^S⟩` — "
            "odd `L·S` ⟹ odd parity ⟹ Z₂ obstruction to the trivial state; discharge means replacing the "
            "opaque parity marker by a real definition of the `Û_inv` eigenvalue (site reflection "
            "`ringReflect` / `ringConfigReflect`, not the on-site reversal `manyBodyReversalS`), with `S "
            "= 1` (`akltVBSState`) the first case. Caveat: `ringReflect` is even-ring only "
            "(`Fin (2 * n)`, bond-centered); the axiom covers every `L`, and odd `L` fixes the middle "
            "site, so discharge needs a general `Fin L` inversion or an even-`L` restriction. "
            "`entanglementEntropyS` (**AXIOM**, eqs. 8.3.7–8.3.8): "
            "the bipartite entanglement entropy `−Σ p_j log p_j` from the half-infinite-chain Schmidt "
            "decomposition — a contentless marker with zero consumers, recorded in "
            "`docs/limitations/documented-axioms.md`. The odd/even-`S` SPT classification is **not "
            "formalized here at all**: the book states it only as a belief (p. 258), so the contentless, "
            "self-satisfiable pair `IsSpinSVBSNontrivialSPT` / `tasaki_spt_classification` was "
            "**deleted** (same ledger). §8.3.3 is heuristic; precise indices come in §8.3.4 (MPS) / "
            "§8.3.6 (Ogata) | `Quantum/SpinS/SPTTopologicalIndex.lean` |",
        )
        .replace(
            "| `IsTimeReversalInvariant` / `IsBondInversionInvariant` / `vbsInversionParityS` / "
            "`entanglementEntropyS` | "
            "**§8.3.2–§8.3.3 Protecting symmetries + topological indices for SPT** "
            "(Pollmann–Turner–Berg–Oshikawa; eqs. (8.3.6)–(8.3.10), pp. 256–263): the Haldane phase is "
            "protected by any of three symmetries — (S1) Z₂×Z₂ (`IsZ2Z2Invariant`), (S2) time-reversal "
            "(`IsTimeReversalInvariant` marker — a duplicate of `IsTimeReversalSymmetricS` "
            "(`LiebSchultzMattisDiscrete.lean`, prose cross-reference, not a Lean consumer) at "
            "`N = 2`, kept in parallel since consolidating it is a deletion needing its own approval), "
            "and (S3) bond-centered inversion (`IsBondInversionInvariant` marker). "
            "`vbsInversionParityS L S` (marker, ℤ) + `tasaki_vbs_inversion_parity` (**AXIOM**, a "
            "**discharge target**, not a documented won't-do): `Û_inv|Φ_VBS^S⟩ = (−1)^{L·S}|Φ_VBS^S⟩` — "
            "odd `L·S` ⟹ odd parity ⟹ Z₂ obstruction to the trivial state; discharge means replacing the "
            "opaque parity marker by a real definition of the `Û_inv` eigenvalue (site reflection "
            "`ringReflect` / `ringConfigReflect`, not the on-site reversal `manyBodyReversalS`), with `S "
            "= 1` (`akltVBSState`) the first case. Caveat: `ringReflect` is even-ring only "
            "(`Fin (2 * n)`, bond-centered); the axiom covers every `L`, and odd `L` fixes the middle "
            "site, so discharge needs a general `Fin L` inversion or an even-`L` restriction. "
            "`entanglementEntropyS` (**AXIOM**, eqs. 8.3.7–8.3.8): "
            "the bipartite entanglement entropy `−Σ p_j log p_j` from the half-infinite-chain Schmidt "
            "decomposition — a contentless marker with zero consumers, recorded in "
            "`docs/limitations/documented-axioms.md`. The odd/even-`S` SPT classification is **not "
            "formalized here at all**: the book states it only as a belief (p. 258), so the contentless, "
            "self-satisfiable pair `IsSpinSVBSNontrivialSPT` / `tasaki_spt_classification` was "
            "**deleted** (same ledger). §8.3.3 is heuristic; precise indices come in §8.3.4 (MPS) / "
            "§8.3.6 (Ogata) | `Quantum/SpinS/SPTTopologicalIndex.lean` |",
            "| `IsTimeReversalInvariant` / `IsBondInversionInvariant` / "
            "`tasaki_vbs_inversion_parity_spin_one` / `entanglementEntropyS` | "
            "**§8.3.2–§8.3.3 Protecting symmetries + topological indices for SPT** "
            "(Pollmann–Turner–Berg–Oshikawa; **`S = 1` bond-inversion parity PROVED**, "
            "`#print axioms` = std3, p. 257 unnumbered display at `S = 1`, pp. 256–263): the Haldane phase is "
            "protected by any of three symmetries — (S1) Z₂×Z₂ (`IsZ2Z2Invariant`), (S2) time-reversal "
            "(`IsTimeReversalInvariant` marker, kept alongside `IsTimeReversalSymmetricS` since "
            "consolidating is its own deletion), (S3) bond-centered inversion "
            "(`IsBondInversionInvariant` marker). `bondInversionConfigS`/`bondInversionUnitaryS L N` "
            "(now **concrete**) are the site reflection `σ ↦ σ ∘ Fin.rev` and its permutation operator "
            "`Û_inv`, defined for every `L` (`Fin.rev` reflects the cycle for odd `L` too, no parity "
            "restriction needed). `tasaki_vbs_inversion_parity_spin_one` (**PROVED**, `S = 1` only): "
            "`Û_inv|Φ_VBS⟩ = (−1)^L|Φ_VBS⟩`, matching worked example (S.63), p. 505, at `L = 3`; "
            "`tasaki_vbs_inversion_parity_ground_state_spin_one` (**PROVED**) transfers the parity to "
            "every ground state via `aklt_ring_ground_state_unique` (§7.1.3). The general-`S` markers "
            "`vbsInversionParityS`/`tasaki_vbs_inversion_parity` (p. 259 unnumbered display, "
            "`(−1)^{L·S}`) were **deleted**: no "
            "general-`S` VBS construction exists. `entanglementEntropyS` (**AXIOM**, eqs. 8.3.7–8.3.8): "
            "the bipartite entanglement entropy `−Σ p_j log p_j` from the Schmidt decomposition — "
            "contentless, zero consumers, recorded in `docs/limitations/documented-axioms.md`. The "
            "odd/even-`S` SPT classification is **not formalized here**: a belief (p. 258), so the "
            "contentless pair `IsSpinSVBSNontrivialSPT` / `tasaki_spt_classification` was **deleted** "
            "(same ledger). §8.3.3 is heuristic; precise indices come in §8.3.4 (MPS) / §8.3.6 (Ogata) "
            "| `Quantum/SpinS/VBSInversionParity.lean`; `Quantum/SpinS/SPTTopologicalIndex.lean` |",
        )
        .replace(
            "`tasaki_vbs_edge_degeneracy` (**AXIOM**): the spin-`S` AKLT open chain has "
            "`(S+1)²`-fold edge degeneracy.",
            "`tasaki_vbs_edge_degeneracy` was an **AXIOM** here and has been **discharged and "
            "deleted** (Issue #5292): the `(S+1)²`-fold edge degeneracy of the spin-`S` AKLT open "
            "chain is proved as `finrank_openAKLTGroundSpaceGeneralS_eq_succ_sq`, see the "
            "supplemental §8.3.1 record below.",
        )
        .replace(
            "All items below are formally proved with **zero `sorry`**.",
            "The catalogue below includes proved results, conditional results, and documented axioms as recorded, with **zero `sorry`**.",
        )
        .replace(
            "**Phase A (current, this PR)**",
            "**Phase A (historical scaffold; implementation recorded at the time)**",
        )
        .replace(
            "The operator order is preserved exactly. | `Quantum/SpinS/AndersonTowerSphereMoment.lean` |",
            "The operator order is preserved exactly. `stagOpVec` is defined in `CartesianAxis.lean`; `directionStaggeredOp_eq_sum` and `sphereAverage_directionStaggeredOp_pow` remain in `AndersonTowerSphereMoment.lean`. | `Quantum/SpinS/CartesianAxis.lean` / `Quantum/SpinS/AndersonTowerSphereMoment.lean` |",
        )
        .replace(
            "isolated to this proof. | `Quantum/SpinS/AndersonTowerLeviCivita.lean` |",
            "isolated to this proof. `leviCivita3` and `totalSpinSOpVec` are defined in `CartesianAxis.lean`; the three diagonal commutators and `totalSpinSOpVec_commutator_stagOpVec` remain in `AndersonTowerLeviCivita.lean`. | `Quantum/SpinS/CartesianAxis.lean` / `Quantum/SpinS/AndersonTowerLeviCivita.lean` |",
        )
        .replace(
            "3×3 real rotation matrices by angle θ about each axis",
            "3×3 real rotation matrices by angle θ about each axis. Internal implementation "
            "record (private, not public API): `rot3D1`, `rot3D2`, `rot3D3` are `axisRot3D a θ` "
            "at `a = 0, 1, 2` for the private def "
            "`axisRot3D : Fin 3 → ℝ → Matrix (Fin 3) (Fin 3) ℝ`, and the two rows below are "
            "proved from the private theorems `axisRot3D_zero` and `axisRot3D_pi` in the same "
            "file.",
        )
        .replace(
            "3×3 real orthogonal π-rotation matrices",
            "3×3 real orthogonal π-rotation matrices. Internal implementation record (private, "
            "not public API): `rot3D1Pi`, `rot3D2Pi`, `rot3D3Pi` are `axisRot3DPi a` at "
            "`a = 0, 1, 2` for the private def "
            "`axisRot3DPi : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ`, and the three rows below are "
            "proved from the private theorems `axisRot3DPi_sq`, `axisRot3DPi_mul_succ`, and "
            "`axisRot3DPi_comm_succ` in the same file.",
        )
        .replace(
            "(Tasaki Problem 2.1.c, all 3 axes)",
            "(Tasaki Problem 2.1.c, all 3 axes). Internal implementation record "
            "(private, not public API): `spinOneRot1`, `spinOneRot2`, `spinOneRot3` are "
            "`spinOneRotOf S θ` at `S = spinOneOp1, spinOneOp2, spinOneOp3` for the "
            "private def `spinOneRotOf : Matrix (Fin 3) (Fin 3) ℂ → ℝ → "
            "Matrix (Fin 3) (Fin 3) ℂ`.",
        )
        .replace(
            "boundary checks `Û^(α)_0 = 1` and `Û^(α)_π = û_α`",
            "boundary checks `Û^(α)_0 = 1` and `Û^(α)_π = û_α`. Internal implementation "
            "record (private, not public API): both rows are proved from the private "
            "theorems `spinOneRotOf_zero` and `spinOneRotOf_pi` in the same file, "
            "combined with `spinOnePiRot{1,2,3}_eq`.",
        )
        # The directed open-chain coupling moved to `Quantum/SpinS/HeisenbergCore.lean` under the
        # name `openBondCoupling`, shared by the §8.1/§8.2 open chains and the §7.2.3 open AKLT
        # chain.  Both catalogue mentions follow the identifier.  (Applied last, so it also
        # rewrites the Theorem 8.2 replacement text produced above.)
        .replace(
            "chain (`openAnisotropicChainCoupling`, no wrap-around — the free ends carry the "
            "`S=1/2` edge spins)",
            "chain (`openBondCoupling`, no wrap-around — the free ends carry the "
            "`S=1/2` edge spins)",
        )
        .replace(
            "Σ_{x,y} [openAnisotropicChainCoupling] · spinSDotXXZ",
            "Σ_{x,y} [openBondCoupling] · spinSDotXXZ",
        )
        # PR-1 of the §8.3.1 item (1) general-S arc (#5292/#5293) generalizes `weylMap` in
        # place from the fixed-`Fin 3` (spin-1) form to a `{N : ℕ}`-parametrized form and
        # renames its home module `WeylSpinOneMap.lean` to `WeylSpinMap.lean`.  This is a pure
        # rename/generalization with no change to the recorded `N = 2` statement, so both the
        # long-form detail record (line 763) and its compact-row File column are updated.
        .replace(
            "the Weyl map `weylMap : ((Fin L → Fin 3) → ℂ) →ₗ[ℂ] "
            "MvPolynomial (Fin L × Fin 2) ℂ` (`Math/MvPolynomial/WeylSpinOneMap.lean`, "
            "eq. (7.1.22))",
            "the Weyl map `weylMap`, at `N = 2` of type "
            "`((Fin L → Fin 3) → ℂ) →ₗ[ℂ] MvPolynomial (Fin L × Fin 2) ℂ` "
            "(`Math/MvPolynomial/WeylSpinMap.lean`, eq. (7.1.22))",
        )
        .replace(
            "`Quantum/SpinS/AKLTUniqueness/LocalBondDivisibility.lean`; "
            "`Math/MvPolynomial/WeylSpinOneMap.lean`; "
            "`Math/MvPolynomial/BilinearFactorCoprime.lean`; "
            "`Math/MvPolynomial/PairwiseCoprimeProd.lean`",
            "`Quantum/SpinS/AKLTUniqueness/LocalBondDivisibility.lean`; "
            "`Math/MvPolynomial/WeylSpinMap.lean`; "
            "`Math/MvPolynomial/BilinearFactorCoprime.lean`; "
            "`Math/MvPolynomial/PairwiseCoprimeProd.lean`",
        )
        # PR-3 of the §8.3.4 invariance/gauge arc (#5306) inserts
        # `exists_unitary_gauge_data_of_eventually` between the word-transport equivalence and the
        # gauge data, and weakens `exists_word_transport_algEquiv` to the threshold (eventual
        # agreement) hypothesis.  The recorded Theorem 7.6 DAG is corrected to the actual chain;
        # the statement it proves is unchanged.
        .replace(
            "The verified DAG is `GeneratesSameMPS` → `exists_word_transport_algEquiv` → "
            "`exists_unitary_gauge_data` → `mps_theorem_7_6`: fixed-length word transport gives",
            "The verified DAG is `GeneratesSameMPS` → (`.eventually`) → "
            "`GeneratesSameMPSEventually` → `exists_word_transport_algEquiv` → "
            "`exists_unitary_gauge_data_of_eventually` → `exists_unitary_gauge_data` / "
            "`mps_theorem_7_6_of_eventual_agreement` → `mps_theorem_7_6`: "
            "`exists_word_transport_algEquiv` now takes only the threshold hypothesis "
            "(agreement for all sufficiently large lengths), fixed-length word transport gives",
        )
        .replace(
            "| `IsTrivialProjectiveRep` / `tasaki_theorem_8_7` / `tasaki_corollary_8_5` | **§8.3.4 "
            "Matrix-product SPT index** (Theorem 8.7 Tachikawa + Corollary 8.5; eqs. "
            "(8.3.42)–(8.3.47)): the precise MPS invariant. A protecting symmetry `G` acts on the "
            "bond space by a projective representation with phase function (2-cocycle) `φ : G→G→ℝ` "
            "(`IsProjectiveRep` marker); it is **trivial** (`IsTrivialProjectiveRep` marker) iff `φ` "
            "is a coboundary (eq. 8.3.43) — the cohomology class is the SPT index. "
            "`SymmetricInjectiveMPSExists G φ` (marker): an injective MPS invariant up to phase under "
            "`V̂(g)`. `tasaki_theorem_8_7` (**AXIOM**): symmetric injective MPS ⟹ trivial projective "
            "rep. For half-odd-integer spin (`N` odd), `z2z2Spin_nontrivial_of_odd` (**AXIOM**, eq. "
            "2.1.31): the Z₂×Z₂ rep is nontrivial. `tasaki_corollary_8_5` (**PROVED**, contrapositive "
            "of Thm 8.7): for `N` odd there is **no** Z₂×Z₂-invariant injective MPS — the "
            "matrix-product Lieb–Schultz–Mattis no-go | `Quantum/SpinS/SPTMatrixProductIndex.lean` |",
            "| `IsTrivialProjectiveRep` / `tasaki_theorem_8_7` / `tasaki_corollary_8_5_z2z2` / "
            "`tasaki_corollary_8_5_time_reversal` | **§8.3.4–§8.3.5 Matrix-product SPT index** (Theorem 8.7 "
            "Tachikawa + Corollary 8.5; **all PROVED**, `#print axioms` = std3, Issue #5306 PR-4, PR #5310; "
            "eqs. (8.3.40)–(8.3.54), pp. 276–280): the precise MPS invariant. `G` acts on the "
            "**single-spin** space (p. 277, not the bond space) by a projective representation `u` with sign "
            "character `s : G →* ℤˣ` and phase `φ` (`Math.IsProjectiveRep`); it is **trivial** "
            "(`Math.IsTrivialProjectiveRep`) iff `φ` is a coboundary (eq. (8.3.43)) — the cohomology class "
            "is the SPT index. `SymmetricInjectiveMPSExists u s` is a real **`def`** (eq. (8.3.45)): an "
            "injective MPS whose transported family agrees with it up to a phase for every `g`. "
            "`tasaki_theorem_8_7`: symmetric injective MPS ⟹ trivial projective rep, by running the cocycle "
            "chase (8.3.49)–(8.3.54) **forwards**: transport composition, `symmetryTransportMPS_conj` "
            "through the gauge relation (8.3.48), then footnote 52's `W†A^σW = cA^σ` with `c = 1` from "
            "Theorem 7.5(ii). **Both** halves of Corollary 8.5 (p. 278) are proved at half-odd-integer spin: "
            "`tasaki_corollary_8_5_z2z2` — no Z₂×Z₂-invariant injective MPS, from the closed-form `π` "
            "rotations `û₁`, `û₃` (eq. (2.1.29)) anticommuting for odd `N` (eq. (2.1.31)); "
            "`tasaki_corollary_8_5_time_reversal` — no time-reversally invariant one, from `G = Z₂` (as "
            "`ℤˣ`) acting antiunitarily by `Θ̂ = û₁û₃K̂` with `Θ̂² = -1̂` for odd `N`. The module's seven "
            "axioms are retired: two became this `def` and this theorem, "
            "`IsProjectiveRep`/`IsTrivialProjectiveRep` are superseded by the definitions in "
            "`Math/ProjectiveRepresentation.lean`, and `z2z2SpinCocycle`, `z2z2Spin_isProjectiveRep`, "
            "`z2z2Spin_nontrivial_of_odd` are **deleted** with their carrier `abbrev Z2xZ2Spin := Fin 4` "
            "(never an axiom) | `Quantum/SpinS/SPTMatrixProductIndex.lean`; "
            "`Quantum/SpinS/SpinSPiRotation.lean`; `Math/ProjectiveRepresentation.lean` |",
        )
        # `spinSFlip` was a duplicate of `spinReversalS`, so the §8.3.5 `π` rotation `û₁` is built
        # from `spinReversalS` instead; its self-adjointness and real-entry lemmas are public API
        # now and belong in the recorded Lean-name cell.
        .replace(
            "| `spinReversalS`, `spinReversalS_conj_spinSOp3`, `spinReversalS_conj_spinSOpPlus`, "
            "`spinReversalS_conj_spinSOpMinus`, `spinReversalS_conj_spinSOp1`, `spinReversalS_conj_spinSOp2` "
            "| **Single-site spin reversal (π-rotation about axis 1)** (Tasaki §2.5 Theorem 2.4, Issue #3739, "
            "PR #3743): the permutation matrix `F` of `Fin.rev` (`k ↦ N−k`); conjugation reindexes by "
            "`Fin.rev` (`(F·M·F) i j = M (rev i) (rev j)`), giving `F Ŝ³ F = −Ŝ³`, `F Ŝ⁺ F = Ŝ⁻`, `F Ŝ⁻ F = "
            "Ŝ⁺` (hence `Ŝ¹↦Ŝ¹`, `Ŝ²↦−Ŝ²`), and `F` is an involution. The many-site product `Θ = ⊗_x F` will "
            "give the `M ↔ −M` reflection symmetry `Θ Ŝ³_tot Θ⁻¹ = −Ŝ³_tot`, `Θ Ĥ Θ⁻¹ = Ĥ` used in the "
            "Mattis–Nishimori uniqueness argument. Tasaki, Springer 2020, §2.5 Theorem 2.4, p. 43–44 (file "
            "`Quantum/SpinS/SpinSReversal.lean`) |",
            "| `spinReversalS`, `spinReversalS_conjTranspose`, `spinReversalS_map_conj`, "
            "`spinReversalS_conj_spinSOp3`, `spinReversalS_conj_spinSOpPlus`, "
            "`spinReversalS_conj_spinSOpMinus`, `spinReversalS_conj_spinSOp1`, `spinReversalS_conj_spinSOp2` "
            "| **Single-site spin reversal (π-rotation about axis 1)** (Tasaki §2.5 Theorem 2.4, Issue #3739, "
            "PR #3743): the permutation matrix `F` of `Fin.rev` (`k ↦ N−k`); conjugation reindexes by "
            "`Fin.rev` (`(F·M·F) i j = M (rev i) (rev j)`), giving `F Ŝ³ F = −Ŝ³`, `F Ŝ⁺ F = Ŝ⁻`, `F Ŝ⁻ F = "
            "Ŝ⁺` (hence `Ŝ¹↦Ŝ¹`, `Ŝ²↦−Ŝ²`), and `F` is an involution.  `F` is also self-adjoint with real "
            "entries (`spinReversalS_conjTranspose`, `spinReversalS_map_conj`), which is what makes it the "
            "real involution behind the closed-form `π` rotation `û₁ = i^{2S}F` of "
            "`Quantum/SpinS/SpinSPiRotation.lean`. The many-site product `Θ = ⊗_x F` will give the `M ↔ −M` "
            "reflection symmetry `Θ Ŝ³_tot Θ⁻¹ = −Ŝ³_tot`, `Θ Ĥ Θ⁻¹ = Ĥ` used in the Mattis–Nishimori "
            "uniqueness argument. Tasaki, Springer 2020, §2.5 Theorem 2.4, p. 43–44 (file "
            "`Quantum/SpinS/SpinSReversal.lean`) |",
        )
        # The §10.1 arc (#5313) discharges Lemma 10.1: the documented axiom becomes a theorem
        # assembled from the five layers, so the recorded verdict and the File column (the
        # capstone now lives in `DegeneratePerturbationConvergence.lean`) follow the declaration.
        .replace(
            "| `tasaki_lemma_10_1_degenerate_perturbation` | **Lemma 10.1** (Tasaki §10.1, p. 346, "
            "**AXIOM**): assuming the first-order term vanishes on the degenerate subspace (`P̂₀ "
            "V̂ P̂₀ = 0`, so the effective theory is second-order, eq. (10.1.6)), if `Ĥeff` has a "
            "unique ground state on `ker Ĥ₀`, then `Ĥ(λ)` has a unique ground state for all "
            "sufficiently small `λ > 0`, converging (phase choice) to the effective ground state "
            "as `λ → 0⁺`. Analytic degenerate-perturbation theory → faithful documented axiom "
            "(companion to the strong-coupling `effectiveHamiltonian_strongCoupling_limit`, "
            "Theorem A.12). | `Math/MatrixAnalysis/DegeneratePerturbation.lean` |",
            "| `tasaki_lemma_10_1_degenerate_perturbation` | **Lemma 10.1** (Tasaki §10.1, p. 346, "
            "**PROVED**, axiom-free, `#print axioms` = std3): assuming the first-order term "
            "vanishes on the degenerate subspace (`P̂₀ V̂ P̂₀ = 0`, so the effective theory is "
            "second-order, eq. (10.1.6)), if `Ĥeff` has a unique ground state on `ker Ĥ₀`, then "
            "`Ĥ(λ)` has a unique ground state for all sufficiently small `λ > 0`, converging "
            "(phase choice) to the effective ground state as `λ → 0⁺`. At fixed finite volume this "
            "is ordinary linear algebra: the whole statement is assembled from the five layers "
            "listed below, with the convergence conjunct discharged by the quantitative rate "
            "`‖Philam λ − Φeff‖² ≤ Kλ` rather than by an eigenvalue-branch continuation argument "
            "(companion to the strong-coupling `effectiveHamiltonian_strongCoupling_limit`, "
            "Theorem A.12, likewise axiom-free). | "
            "`Math/MatrixAnalysis/DegeneratePerturbationConvergence.lean` |",
        )
        # PR-1 of the Theorem 10.4 discharge arc (#5320) extends the conclusion of
        # `repulsiveSpinZSector_ground_unique` with the transported ground state's
        # number-operator eigenvalue; the row's prose gains one sentence recording it.
        .replace(
            "Half-integer `m` (odd `Ne`) is out of scope (Theorem 10.2 requires `Even Ne`). "
            "**PR #4955 (general-sector PR-1)**. | "
            "`Fermion/JordanWigner/Hubbard/LiebRepulsiveBalancedGround.lean` |",
            "Half-integer `m` (odd `Ne`) is out of scope (Theorem 10.2 requires `Even Ne`). "
            "**Number-operator eigenvalue** (Issue #5320, PR #5321 PR-1): because Theorem 10.2's "
            "attractive ground state is a spin singlet, its transport lands in the fixed "
            "`(N+1)`-electron (half-filling) sector on every spin-`z` sector — `N̂ φ = (N+1)·φ` — "
            "independently of `Ne`. **PR #4955 (general-sector PR-1)**. | "
            "`Fermion/JordanWigner/Hubbard/LiebRepulsiveBalancedGround.lean` |",
        )
        # The §10.1 arc (#5313) proved Lemma 10.1, so the total-spin caveat of the Theorem 10.4
        # spin-`z`-sector row no longer points at a deferred axiom: what is still missing is the
        # application of the (now proved) finite-dimensional degenerate perturbation theory.
        .replace(
            "identifying it needs the deferred degenerate perturbation axiom.",
            "identifying it needs the (finite-dimensional) degenerate perturbation theory of "
            "Lemma 10.1 (`tasaki_lemma_10_1_degenerate_perturbation`, proved axiom-free).",
        )
        # PR-15c of the Theorem 10.4 discharge arc (#5320) discharges the axiom itself; the
        # row's status/proof-sketch prose is rewritten to reflect the completed theorem.
        .replace(
            "| `theorem_10_4_lieb_repulsive_half_filling` | **Theorem 10.4** (Tasaki §10.2.2, "
            "p. 350, **AXIOM**): at half-filling `N = \\|Λ\\|`, the ground subspace is nonzero, "
            "energy-minimal, consists entirely of total-spin `S₀ = \\|\\|A\\|−\\|B\\|\\|/2` "
            "states (Casimir `S₀(S₀+1)`), and has dimension exactly `\\|A\\|−\\|B\\|+1` (the "
            "unavoidable SU(2) multiplet degeneracy). Lieb's reflection positivity via the Shiba "
            "transformation → faithful documented axiom. | "
            "`Fermion/JordanWigner/Hubbard/LiebRepulsive.lean` |",
            "| `theorem_10_4_lieb_repulsive_half_filling` | **Theorem 10.4** (Tasaki §10.2.2, "
            "p. 350, **now PROVED — axiom discharged**, Issue #5320, PR #5346 PR-15c; "
            "`#print axioms` = std3): for a bipartite real symmetric connected hopping matrix "
            "`T` and a repulsive Hubbard Hamiltonian `H` in either form (uniform eq. (10.2.5) or "
            "symmetric eq. (10.2.6)), at half-filling `N = \\|Λ\\|` the ground subspace is "
            "nonzero, energy-minimal, consists entirely of total-spin "
            "`S₀ = \\|\\|A\\|−\\|B\\|\\|/2` states (Casimir `S₀(S₀+1)`), and has dimension "
            "exactly `\\|A\\|−\\|B\\|+1` (the unavoidable SU(2) multiplet degeneracy). "
            "**Proof**: the capstone splits `IsLiebRepulsiveModel`'s "
            "`IsLiebRepulsiveHamiltonian` disjunction. The **symmetric disjunct** is "
            "`liebRepulsive_symmetric_halfFilling`, which combines the conditional capstone "
            "`liebRepulsive_symmetric_halfFilling_conditional` "
            "(`LiebRepulsiveWeightConfinement.lean`, the `1 ≤ \\|A\\|`/`1 ≤ \\|B\\|` case "
            "reached through the Shiba-transformed reflection-positivity ground state, Casimir "
            "sector pinning, SU(2) weight transport and weight confinement) with the degenerate "
            "case `\\|A\\| = 0 ∨ \\|B\\| = 0`, which forces `T = 0` and hence — by connectedness "
            "of the now edgeless hopping support graph — `N = 0`, a single-site model whose "
            "ground submodule is one diagonal eigenspace (Casimir `3/4`, `finrank 2`, matching "
            "`liebRepulsiveSpinCasimir`/`liebRepulsiveGroundMultiplicity` at the one-point "
            "bipartition). The **uniform disjunct** is `liebRepulsive_uniform_of_symmetric`, "
            "transporting the constant-`U` symmetric-form conjuncts across the energy shift of "
            "`symmetricRepulsiveHubbardHamiltonian_groundSubmodule_eq_uniform`. The model "
            "hypotheses `IsLiebRepulsiveModel` / `IsLiebRepulsiveHamiltonian` and the Hamiltonian "
            "definitions stay in `LiebRepulsive.lean`, strictly upstream of the discharge chain. "
            "| `Fermion/JordanWigner/Hubbard/LiebRepulsiveHalfFillingDischarge.lean` |",
        )
        # PR-8 of the Theorem 10.6 discharge arc (#5347) discharges the axiom itself; the row's
        # status/proof-sketch prose is rewritten to reflect the completed theorem, the page-number
        # correction (p. 354 → p. 356) is folded in, and the "reflection positivity" proof-method
        # claim is replaced by the actual Theorem 10.4 + Theorem 10.5 route.
        .replace(
            "| `fermionStaggeredCasimirOp` / `theorem_10_6_lieb_ferrimagnetism` | **Theorem "
            "10.6** (Shen–Qiu–Tian ferrimagnetism; Tasaki §10.2.3, p. 354, "
            "eqs. (10.2.16)/(10.2.17), **AXIOM**): every normalized repulsive-Hubbard ground "
            "state satisfies `⟨v\\| (Ô_L)² \\|v⟩ ≥ ((\\|A\\|−\\|B\\|)/2)²`, where "
            "`(Ô_L)² = Σ_{x,y} ε_xε_y Ŝ_x·Ŝ_y` (staggered sign `ε_x=±1` per sublattice) — "
            "ferrimagnetic long-range order. Reuses `IsLiebRepulsiveModel`. Reflection positivity "
            "→ faithful documented axiom. | "
            "`Fermion/JordanWigner/Hubbard/LiebFerrimagnetism.lean` |",
            "| `fermionStaggeredCasimirOp` / `theorem_10_6_lieb_ferrimagnetism` | **Theorem "
            "10.6** (Shen–Qiu–Tian ferrimagnetism; Tasaki §10.2.3, p. 356, "
            "eqs. (10.2.16)/(10.2.17), **now PROVED — axiom discharged**, Issue #5347, "
            "PR #5356 PR-8; `#print axioms` = std3): every normalized repulsive-Hubbard ground "
            "state satisfies `⟨v\\| (Ô_L)² \\|v⟩ ≥ ((\\|A\\|−\\|B\\|)/2)²`, where "
            "`(Ô_L)² = Σ_{x,y} ε_xε_y Ŝ_x·Ŝ_y` (staggered sign `ε_x=±1` per sublattice) — "
            "ferrimagnetic long-range order. Reuses `IsLiebRepulsiveModel`. **Proof**: via "
            "Theorem 10.4 and Theorem 10.5 (inequality (10.2.7)), exactly as Theorem 4.4, and "
            "not by reflection positivity — a ground-multiplet lowering-tower argument "
            "transports the centered-sector bound (Theorem 10.5's correlation-sign step) to "
            "every tower member and every normalized ground vector. | "
            "`Fermion/JordanWigner/Hubbard/LiebFerrimagnetismDischarge.lean` |",
        )
        # PR-5 of the Theorem 10.8 discharge arc (#5357) discharges the axiom itself; the
        # row's status/proof-sketch prose is rewritten to reflect the completed theorem.
        .replace(
            "| `totalPairAnnihilationOperator` / `totalPairCreationOperator` / "
            "`totalPairCorrelationOperator` / `symmetricAttractiveHubbardHamiltonian` / "
            "`liebShenQiuPairLowerBound` / `theorem_10_8_lieb_shen_qiu_superconductivity` | **Theorem "
            "10.8** (Lieb–Shen–Qiu superconductivity; Tasaki §10.2.3, p. 359, eq. (10.2.22), "
            "**AXIOM**): for the **symmetric** attractive Hubbard model `Ĥhop − Σ_x "
            "U_x(n̂_↑−½)(n̂_↓−½)` (eq. (10.2.21)) on a bipartite lattice with even `N`, `2\\|B\\| ≤ N ≤ "
            "2\\|A\\|`, the unique ground state satisfies `⟨φ\\| b̂† b̂ \\|φ⟩ ≥ (\\|A\\|−N/2)(N/2−\\|B\\|)` "
            "with `b̂ = Σ_x ĉ_{x↓}ĉ_{x↑}` — off-diagonal long-range order (fermion-pair condensation "
            "/ superconductivity). Reflection positivity + Theorem 10.2 uniqueness → faithful "
            "documented axiom. | `Fermion/JordanWigner/Hubbard/LiebShenQiu.lean` |",
            "| `totalPairAnnihilationOperator` / `totalPairCreationOperator` / "
            "`totalPairCorrelationOperator` / `symmetricAttractiveHubbardHamiltonian` / "
            "`liebShenQiuPairLowerBound` / `theorem_10_8_lieb_shen_qiu_superconductivity` | **Theorem "
            "10.8** (Lieb–Shen–Qiu superconductivity; Tasaki §10.2.3, p. 359, eq. (10.2.22), **now "
            "PROVED — axiom discharged**, Issue #5357, PR #5362 PR-5; `#print axioms` = std3): for "
            "the **symmetric** attractive Hubbard model `Ĥhop − Σ_x U_x(n̂_↑−½)(n̂_↓−½)` (eq. "
            "(10.2.21)) on a bipartite lattice with even `Ne`, `2\\|B\\| ≤ Ne ≤ 2\\|A\\|`, the unique "
            "ground state satisfies `⟨φ\\| b̂† b̂ \\|φ⟩ ≥ (\\|A\\|−Ne/2)(Ne/2−\\|B\\|)` with `b̂ = Σ_x "
            "ĉ_{x↓}ĉ_{x↑}` — off-diagonal long-range order (fermion-pair condensation / "
            "superconductivity). **Proof**: below the top of the band (`Ne < 2(N+1)`), centring away "
            "the interaction (`liebShenQiu_attractiveGround_of_symmetric`) turns the ground state "
            "into a plain-attractive one, whose singlet property (Theorem 10.2) and Theorem 10.3's "
            "pair-transfer positivity drive the Shiba transport of §10.2.3 onto the spin-`z` sector "
            "`Ŝ³ = (Ne−(N+1))/2` of the symmetric repulsive model at half filling, where Theorem 10.4 "
            "fixes the Casimir value; the ladder identity `Ŝ⁺Ŝ⁻ = Ŝ² − Ŝ³(Ŝ³−1)` and the Shiba "
            "identity (eq. (10.2.13)) convert that into the sublattice-signed pair sum, whose signs "
            "can only decrease the strictly positive terms. At the top of the band (`Ne = 2(N+1)`) "
            "the bound degenerates to `0` and follows from `⟨φ\\|b̂ᴴb̂\\|φ⟩ ≥ 0` alone. Theorem 10.5 is "
            "**not** used — the sign step is re-derived directly from the Shiba identity plus Theorem "
            "10.3's strict positivity. | `Fermion/JordanWigner/Hubbard/LiebShenQiu.lean`; "
            "`Fermion/JordanWigner/Hubbard/LiebShenQiuDischarge.lean` |",
        )
        # Corollary 4.3 no longer runs through a susceptibility bound (#5416 replaced that route
        # by Tasaki's own contraposition against Theorem 3.2, p. 77), so neither the conditional
        # reduction `no_long_range_order_1d_of_susceptibility` nor the Shastry susceptibility
        # axiom it consumed is a declaration this repository has. The catalogue rows of the two
        # are removed rather than repaired, and a removal is spelt the only way one can be: the
        # row's exact frozen text, trailing newline included, rewritten to the empty string, so
        # that what leaves the published catalogue is legible in this diff and pinned by
        # APPROVED_CHANGES_SHA256. The Corollary 4.3 row between them survives; it is repaired
        # here and again below, `#print axioms` output included, for the route that replaced this
        # one.
        .replace(
            "| `no_long_range_order_1d_of_susceptibility` | **Cor 4.3 / conditional reduction** "
            "(`NoLongRangeOrderConditional.lean`, Tasaki §4.1, toward Corollary 4.3): the exact "
            "`ε`–`δ` statement of Corollary 4.3 *modulo the susceptibility bound* — if there is `C ≥ "
            "0` such that every normalized ground state of an even zero-field ring (`L≥2, Even L`) "
            "has a potential `y` for `ÔΦ` with `Re⟨y,ÔΦ⟩ ≤ C·L`, then for every `ε > 0` there is "
            "`L₀` beyond which every normalized ground state has `\\|⟨Φ,Ô²Φ⟩.re/L²\\| < ε` (assembling "
            "the `O(L)` oscillator bound + susceptibility reduction + ground-state bridge + an "
            "Archimedean `ε`–`δ`). This isolates the unconditional Cor 4.3 to the susceptibility "
            "bound `Re⟨y,ÔΦ⟩ ≤ C·L`; that bound is now supplied by the documented Shastry axiom "
            "`shastry_staggered_susceptibility_bound`, discharging `no_long_range_order_1d` into a "
            "theorem (PR #5003) | `Quantum/SpinS/NoLongRangeOrderConditional.lean` |\n",
            "",
        )
        .replace(
            "| `no_long_range_order_1d` | **Corollary 4.3** (§4.1, THEOREM; eq. (4.1.11)): absence "
            "of LRO in 1D on **even** rings. For the zero-field 1D AFM Heisenberg ring on **even** "
            "`L` sites (`Even L`, bipartite — faithful to Tasaki §3.1/§4.1.1 which define the "
            "lattice for even `L` only), the squared staggered order parameter per site vanishes in "
            "the thermodynamic limit `lim_{L↑∞} ⟨Φ_GS\\|(Ô_L^(3)/L)²\\|Φ_GS⟩ = 0` (ε–δ form). "
            "Discharged (PR #5003) by feeding the documented Shastry susceptibility axiom "
            "`shastry_staggered_susceptibility_bound` (χ(k*)≤C·L) into the conditional reduction "
            "`no_long_range_order_1d_of_susceptibility` for `N ≥ 1`; the degenerate spin-0 case `N = "
            "0` is unconditional (the staggered order operator vanishes). `#print axioms` = "
            "`[propext, Classical.choice, Quot.sound, shastry_staggered_susceptibility_bound]` | "
            "`Quantum/SpinS/NoLongRangeOrder1D.lean` |",
            "| `no_long_range_order_1d` | **Corollary 4.3** (§4.1, THEOREM; eq. (4.1.11)): absence "
            "of LRO in 1D on **even** rings. For the zero-field 1D AFM Heisenberg ring on **even** "
            "`L` sites (`Even L`, bipartite — faithful to Tasaki §3.1/§4.1.1 which define the "
            "lattice for even `L` only), the squared staggered order parameter per site vanishes in "
            "the thermodynamic limit `lim_{L↑∞} ⟨Φ_GS\\|(Ô_L^(3)/L)²\\|Φ_GS⟩ = 0` (ε–δ form). "
            "Discharged (PR #5003) by feeding the documented Shastry susceptibility axiom "
            "`shastry_staggered_susceptibility_subcubic` (χ(k*)=o(L³)) into the conditional "
            "reduction `no_long_range_order_1d_of_susceptibility` for `N ≥ 1`; the degenerate spin-0 "
            "case `N = 0` is unconditional (the staggered order operator vanishes). `#print axioms` "
            "= `[propext, Classical.choice, Quot.sound, shastry_staggered_susceptibility_subcubic]` "
            "| `Quantum/SpinS/NoLongRangeOrder1D.lean` |",
        )
        .replace(
            "| `shastry_staggered_susceptibility_bound` | **Shastry susceptibility bound χ(k*)≤C·L** "
            "(§4.1, DOCUMENTED AXIOM; toward Corollary 4.3): for the zero-field 1D AFM Heisenberg "
            "ring on **even** `L ≥ 2` sites (`Even L`, bipartite) there is a size-uniform `C ≥ 0` "
            "with every normalized ground state admitting a potential `y` for `ÔΦ` (`(Ĥ−E₀)y=ÔΦ`) of "
            "`O(L)` static staggered susceptibility `Re⟨y,ÔΦ⟩ ≤ C·L` (physically "
            "`χ(k*)=L·f_L^(-1)(k*)`). Tasaki does **not** prove this in the book — footnote 3 (p. "
            "76) cites Shastry [58] / the rigorous formulation of Tanaka–Takeda–Idogaki [63], and "
            "footnote 9 (p. 83) singles out the `f_L^(-1)(k*)` bound as the only \"nontrivial part "
            "that requires some hard analysis\". Per the project's explicit instruction this "
            "genuinely external hard-analysis estimate (massive-Green / inverse-Fourier `k*=π` "
            "control) based on Shastry J.Phys.A 25 L249 (1992) [58] and Tanaka–Takeda–Idogaki JMMM "
            "272–276 908 (2004) [63] is a documented axiom; it discharges `no_long_range_order_1d` "
            "(PR #5003) | `Quantum/SpinS/NoLongRangeOrder1D.lean` |\n",
            "",
        )
        # The same repair updates the two neighbouring rows that quote the retired `χ ≤ C·L`
        # target: the Falk-Bruch reduction row and the χ2b sum-rule row (whose `hsusc` wording
        # named a hypothesis shape the consumer no longer has).
        .replace(
            "reduces Cor 4.3 to the susceptibility bound `χ ≤ C·L` (PR #4846)",
            "reduces Cor 4.3 to the sub-cubic susceptibility bound `χ = o(L³)` (PR #4846)",
        )
        .replace(
            "Phrased in `hsusc` shape (the hypothetical-susceptibility carrier from "
            "`no_long_range_order_1d_of_susceptibility`) for general field `h`; staggered "
            "specialisation and the Green-function `≤ C·L` bound belong to χ3 (next stage).",
            "Phrased as the resolvent/susceptibility conjunct for general field `h`; "
            "`no_long_range_order_1d_of_susceptibility` consumes a sub-cubic form of it (`≤ δ·L³` "
            "beyond a threshold), so the staggered specialisation still has to turn `C(h)` into such "
            "a bound — that belongs to χ3 (next stage).",
        )
        # Two catalogue rows presented Corollary 4.3 as discharged. It is a conditional reduction:
        # the axiom fed into it is strictly stronger than the corollary, so the row must not read
        # as a completed result. (The second entry is applied after the row rewrite above that
        # inserts the sentence it matches, so its position in the chain is load-bearing.)
        .replace(
            "**Corollary 4.3** (§4.1, THEOREM; eq. (4.1.11)): absence of LRO in 1D on **even** "
            "rings.",
            "**Corollary 4.3** (§4.1, CONDITIONAL THEOREM; eq. (4.1.11)): absence of LRO in 1D on "
            "**even** rings.",
        )
        .replace(
            "Discharged (PR #5003) by feeding the documented Shastry susceptibility axiom "
            "`shastry_staggered_susceptibility_subcubic` (χ(k*)=o(L³)) into the conditional "
            "reduction `no_long_range_order_1d_of_susceptibility` for `N ≥ 1`; the degenerate "
            "spin-0 case `N = 0` is unconditional (the staggered order operator vanishes).",
            "**Conditional, not a discharge of Corollary 4.3** (PR #5003): for `N ≥ 1` it is the "
            "conditional reduction `no_long_range_order_1d_of_susceptibility` fed with the "
            "documented Shastry susceptibility axiom `shastry_staggered_susceptibility_subcubic` "
            "(χ(k*)=o(L³)), which is **strictly stronger** than the corollary — the crude bounds "
            "already reach exactly `O(L³)` once the gap obeys `Δ ≳ 1/L`, and via "
            "`staggeredOrder_sq_le_susceptibility` it holds "
            "only if `⟨Ô²⟩ = o(L²)`, the corollary's own conclusion; only the degenerate spin-0 "
            "case `N = 0` is unconditional (the staggered order operator vanishes).",
        )
        # The Theorem 4.2 grouped detail record (former line 560) carried the same claim in prose,
        # and additionally described the closed issue #4777 in the present tense.
        .replace(
            "The **reflection-positivity infrastructure project** (#4777) formalizes supporting "
            "finite-dim RP layers for Cor 4.3 (susceptibility no-LRO, discharged) and related "
            "Thm 4.2 RP auxiliary results, not a re-proof of Thm 4.2 itself.",
            "The **reflection-positivity infrastructure project** (#4777, closed 2026-07-11 and "
            "historical) formalized supporting finite-dim RP layers for the Cor 4.3 "
            "**conditional reduction** (susceptibility no-LRO) and related Thm 4.2 RP auxiliary "
            "results — not a re-proof of Thm 4.2 itself, and not a discharge of Cor 4.3: that "
            "reduction consumes the documented axiom "
            "`shastry_staggered_susceptibility_subcubic`, which is strictly stronger than the "
            "corollary, holding via `staggeredOrder_sq_le_susceptibility` only if "
            "`⟨Ô²⟩ = o(L²)` — the corollary's own conclusion. The successor discharge issue is "
            "#5413.",
        )
        # PR-2 of the same arc (#5416) replaces the susceptibility route by Tasaki's own proof of
        # Corollary 4.3 (contraposition against Theorem 3.2, p. 77). The axiom row and the
        # reduction row are removed outright by the two literal rewrites above; the four entries
        # below repair every remaining row that described that route. (Applied last: each matches
        # text an earlier replacement inserts.)
        .replace(
            "**Conditional, not a discharge of Corollary 4.3** (PR #5003): for `N ≥ 1` it is the "
            "conditional reduction `no_long_range_order_1d_of_susceptibility` fed with the "
            "documented Shastry susceptibility axiom `shastry_staggered_susceptibility_subcubic` "
            "(χ(k*)=o(L³)), which is **strictly stronger** than the corollary — the crude bounds "
            "already reach exactly `O(L³)` once the gap obeys `Δ ≳ 1/L`, and via "
            "`staggeredOrder_sq_le_susceptibility` it holds "
            "only if `⟨Ô²⟩ = o(L²)`, the corollary's own conclusion; only the degenerate spin-0 "
            "case `N = 0` is unconditional (the staggered order operator vanishes). "
            "`#print axioms` = "
            "`[propext, Classical.choice, Quot.sound, shastry_staggered_susceptibility_subcubic]`",
            "**Conditional, and a discharge of nothing** (PR #5420): for `N ≥ 1` it is Tasaki's own "
            "proof of the corollary, `no_long_range_order_1d_of_theorem_4_2` — contraposition "
            "against Theorem 3.2 at a single volume (eq. (3.4.16) plus the per-volume eq. (3.4.21) "
            "bound), with condition (3.4.4) supplied by Marshall–Lieb–Mattis — applied to "
            "Theorem 4.2 (`shastry_no_symmetry_breaking_1d`), which is itself conditional on the "
            "documented axiom `shastryEnergyGain`. Both Corollary 4.3 and Theorem 4.2 remain open: "
            "Tasaki does not prove Theorem 4.2 (footnote 3, p. 76) and nothing here reconstructs "
            "the argument he cites. Only the degenerate spin-0 case `N = 0` is unconditional (the "
            "staggered order operator vanishes). `#print axioms` = "
            "`[propext, Classical.choice, Quot.sound, shastryEnergyGain]`",
        )
        .replace(
            "; reduces Cor 4.3 to the sub-cubic susceptibility bound `χ = o(L³)` (PR #4846)",
            "; the sub-cubic susceptibility bound `χ = o(L³)` it would reduce Cor 4.3 to is not "
            "carried here — Cor 4.3 follows Tasaki's own contraposition from Theorem 4.2 instead "
            "(PR #4846)",
        )
        .replace(
            "Phrased as the resolvent/susceptibility conjunct for general field `h`; "
            "`no_long_range_order_1d_of_susceptibility` consumes a sub-cubic form of it (`≤ δ·L³` "
            "beyond a threshold), so the staggered specialisation still has to turn `C(h)` into such "
            "a bound — that belongs to χ3 (next stage).",
            "Phrased as the resolvent/susceptibility conjunct for general field `h`; turning `C(h)` "
            "into a sub-cubic staggered bound (`≤ δ·L³` beyond a threshold) belongs to χ3, a stage "
            "this repository does not carry out — Cor 4.3 follows Tasaki's own contraposition from "
            "Theorem 4.2 instead.",
        )
        .replace(
            "and not a discharge of Cor 4.3: that "
            "reduction consumes the documented axiom "
            "`shastry_staggered_susceptibility_subcubic`, which is strictly stronger than the "
            "corollary, holding via `staggeredOrder_sq_le_susceptibility` only if "
            "`⟨Ô²⟩ = o(L²)` — the corollary's own conclusion. The successor discharge issue is "
            "#5413.",
            "and not a discharge of Cor 4.3: that "
            "reduction and the documented axiom it consumed have since been deleted, Cor 4.3 now "
            "following Tasaki's own contraposition from Thm 4.2, which leaves both open. Issue "
            "#5413, previously named as the successor discharge issue, is closed as not planned; "
            "#5416 is open and covers Cor 4.3's route rather than the discharge.",
        )
        # #5426 strengthens the recorded Corollary 4.3 statement from `α = 3` alone to
        # `∀ α : Fin 3`, reading off Tasaki's own fourth sentence on p. 77 (SU(2) invariance of the
        # unique ground state), and closes #5416. (Applied last: matches text the pair above
        # inserts.)
        .replace(
            "and not a discharge of Cor 4.3: that "
            "reduction and the documented axiom it consumed have since been deleted, Cor 4.3 now "
            "following Tasaki's own contraposition from Thm 4.2, which leaves both open. Issue "
            "#5413, previously named as the successor discharge issue, is closed as not planned; "
            "#5416 is open and covers Cor 4.3's route rather than the discharge.",
            "and not a discharge of Cor 4.3: that "
            "reduction and the documented axiom it consumed have since been deleted, Cor 4.3 now "
            "following Tasaki's own contraposition from Thm 4.2 for all three Cartesian axes, "
            "which leaves both open. Issue "
            "#5413, previously named as the successor discharge issue, is closed as not planned.",
        )
        .replace(
            "the squared staggered order parameter per site vanishes in "
            "the thermodynamic limit `lim_{L↑∞} ⟨Φ_GS\\|(Ô_L^(3)/L)²\\|Φ_GS⟩ = 0` (ε–δ form). "
            "**Conditional, and a discharge of nothing** (PR #5420): for `N ≥ 1` it is Tasaki's own "
            "proof of the corollary, `no_long_range_order_1d_of_theorem_4_2`",
            "the squared staggered order parameter per site vanishes in "
            "the thermodynamic limit for all three Cartesian axes, "
            "`lim_{L↑∞} ⟨Φ_GS\\|(Ô_L^(α)/L)²\\|Φ_GS⟩ = 0` for `∀ α : Fin 3` (ε–δ form; Lean's "
            "index is Tasaki's `α` minus one). "
            "**Conditional, and a discharge of nothing** (PR #5427): for `N ≥ 1` the `α = 3` "
            "instance is Tasaki's own proof of the corollary, `no_long_range_order_1d_of_theorem_4_2`",
        )
        .replace(
            "which is itself conditional on the "
            "documented axiom `shastryEnergyGain`. Both Corollary 4.3 and Theorem 4.2 remain open: "
            "Tasaki does not prove Theorem 4.2 (footnote 3, p. 76) and nothing here reconstructs "
            "the argument he cites. Only the degenerate spin-0 case `N = 0` is unconditional (the "
            "staggered order operator vanishes). `#print axioms` = "
            "`[propext, Classical.choice, Quot.sound, shastryEnergyGain]`",
            "which is itself conditional on the "
            "documented axiom `shastryEnergyGain`; the other two axes are transported from it by "
            "`afmRing_groundState_totalSpin_annihilate` and the generic su(2) bridge "
            "`totalSpinSOpVec_mulVec_eq_zero_of_unique_ground`. Both Corollary 4.3 and Theorem 4.2 "
            "remain open: "
            "Tasaki does not prove Theorem 4.2 (footnote 3, p. 76) and nothing here reconstructs "
            "the argument he cites. Only the degenerate spin-0 case `N = 0` is unconditional (the "
            "staggered order operator vanishes on every axis). `#print axioms` = "
            "`[propext, Classical.choice, Quot.sound, shastryEnergyGain]`",
        )
    )


def approved_changes(text: str) -> str:
    # Removals are entries of the audited rewrite chain like any other, each at its own row's
    # site, so there is no pass ordering to reason about; `APPROVED_CHANGES_SHA256` is what
    # proves no later entry depended on text an earlier entry had already removed.
    return _drop_private_instructions_ref(_approved_replacements(text))


def published_catalogue_rows() -> list[str]:
    """The published catalogue rows, in order, exactly as `main()` compares the pages against.

    Spelled once for the same reason as `CATALOGUE_BASELINE_SLICE`: `PUBLISHED_ROWS_SHA256` pins
    this list and `main()` consumes it, so the row extractor cannot be narrowed for the
    comparison while the pin keeps hashing the wider one.
    """
    return table_data_rows(approved_changes(catalogue_baseline_text()).splitlines())


def approved_changes_byte_parity_self_test() -> None:
    """Both pins must still hash the published catalogue exactly.

    Called first among the self-tests, so a transformation that moved is reported once, as a pin
    mismatch naming both hashes, rather than as the thousands of row differences the page
    comparison reports much later in the run. `APPROVED_CHANGES_SHA256` covers the transformed
    text and `PUBLISHED_ROWS_SHA256` the row sequence derived from it, because the comparison
    consumes the rows and the text pin alone leaves the extractor between them unguarded.
    """
    published = approved_changes(catalogue_baseline_text())
    actual = hashlib.sha256(published.encode("utf-8")).hexdigest()
    if actual != APPROVED_CHANGES_SHA256:
        fail(
            "approved-changes byte-parity pin mismatch: expected "
            f"{APPROVED_CHANGES_SHA256}, got {actual}. Recompute with: python3 -c 'import sys, "
            "hashlib; sys.path.insert(0, \"scripts\"); import check_docs_hierarchy as c; "
            "print(hashlib.sha256(c.approved_changes(c.catalogue_baseline_text())."
            "encode(\"utf-8\")).hexdigest())' -- a passing pin recompute is never on its own an "
            "authorization for the content change."
        )
    rows_actual = hashlib.sha256(
        "\n".join(published_catalogue_rows()).encode("utf-8")
    ).hexdigest()
    if rows_actual != PUBLISHED_ROWS_SHA256:
        fail(
            "published-rows byte-parity pin mismatch: expected "
            f"{PUBLISHED_ROWS_SHA256}, got {rows_actual}. Recompute with: python3 -c 'import sys, "
            "hashlib; sys.path.insert(0, \"scripts\"); import check_docs_hierarchy as c; "
            "print(hashlib.sha256(\"\\n\".join(c.published_catalogue_rows())."
            "encode(\"utf-8\")).hexdigest())' -- a passing pin recompute is never on its own an "
            "authorization for the content change."
        )


# The row count of the frozen baseline catalogue slice at BASELINE_COMMIT, before any audited
# rewrite. Never moves for a content edit -- only a narrowing of CATALOGUE_BASELINE_SLICE or a
# change of BASELINE_COMMIT itself moves it -- so
# `BASELINE_CATALOGUE_ROW_COUNT - (rows the audited chain drops) == len(published_catalogue_rows())`
# is an identity no pin recompute can satisfy.
BASELINE_CATALOGUE_ROW_COUNT = 2052

# sha256 over the source text of the row-derivation machinery named in
# `_ROW_PATH_SOURCE_NAMES`, deliberately excluding `_approved_replacements`, whose shape the
# chain rule pins more precisely than a hash would and whose literals a sanctioned removal is
# supposed to move. Machinery rather than content: no legitimate catalogue edit moves this pin.
ROW_PATH_SOURCE_SHA256 = "9f787c0a1575ee1854704418927ec0d3c5a72a5bbcaaf05754048c35268ad3f2"

# sha256 over the ordered `(a, b)` literal pairs `_approved_replacements` chains, so that
# surgery inside the reviewed literal list that leaves the published bytes alone -- dropping an
# entry that no longer matches anything, say -- is a moved pin rather than a silent edit.
APPROVED_ENTRIES_SHA256 = "f2ff5401993d12ccf7cbdf3b837910f89eb928feb0cd10f12cd04311858c92c8"

# The nodes `ROW_PATH_SOURCE_SHA256` hashes: everything the published rows are derived through,
# from the frozen blob to the row sequence `main()` compares the legacy pages against.
_ROW_PATH_SOURCE_NAMES = (
    "CATALOGUE_BASELINE_SLICE",
    "BASELINE_COMMIT",
    "_WORKING_NOTE_CITATION",
    "_WORKING_NOTE_SECTION_REF",
    "_PRIVATE_INSTRUCTIONS_REF",
    "baseline_index",
    "catalogue_baseline_text",
    "is_separator",
    "table_data_rows",
    "approved_changes",
    "published_catalogue_rows",
    "_drop_working_note_citations",
    "_drop_private_instructions_ref",
)


def _own_source() -> str:
    """This file's own source text: what the chain rule parses and the machinery pin hashes."""
    return Path(__file__).read_text()


def _approved_replacements_function_node(source: str) -> ast.FunctionDef:
    """The `_approved_replacements` `FunctionDef` of `source`, this file's own text or a copy."""
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, ast.FunctionDef) and node.name == "_approved_replacements":
            return node
    fail("_approved_replacements: not found in the parsed source")


def _approved_replacements_chain(source: str) -> tuple[list[tuple[str, str]], list[str]]:
    """The ordered `(a, b)` literal pairs of `_approved_replacements`'s `.replace` chain.

    Returns `(chain, violations)`. `violations` is non-empty, and `chain` a possibly-partial
    prefix, whenever the function is not exactly: a single `return`, wrapped in exactly
    `_drop_working_note_citations(...)`, of a left-nested chain of two-positional-argument
    `.replace` calls rooted at the parameter `text`, every argument an `ast.Constant` string.
    """
    func = _approved_replacements_function_node(source)
    violations: list[str] = []
    body = func.body
    if (
        body
        and isinstance(body[0], ast.Expr)
        and isinstance(body[0].value, ast.Constant)
        and isinstance(body[0].value.value, str)
    ):
        body = body[1:]
    if len(body) != 1 or not isinstance(body[0], ast.Return):
        return [], [
            "_approved_replacements body is not a docstring plus single return "
            f"({len(func.body)} statements)"
        ]
    value = body[0].value
    wrapper_names: list[str] = []
    while isinstance(value, ast.Call) and isinstance(value.func, ast.Name):
        wrapper_names.append(value.func.id)
        if len(value.args) != 1 or value.keywords:
            violations.append(f"{value.func.id}(...) call is not single-argument")
            return [], violations
        value = value.args[0]
    if wrapper_names != ["_drop_working_note_citations"]:
        violations.append(f"unpinned wrapper chain {tuple(wrapper_names)}")
        return [], violations
    chain: list[tuple[str, str]] = []
    while isinstance(value, ast.Call):
        if (
            not isinstance(value.func, ast.Attribute)
            or value.func.attr != "replace"
            or value.keywords
            or len(value.args) != 2
        ):
            violations.append("chain entry is not a two-positional-argument .replace call")
            return chain, violations
        a_node, b_node = value.args
        if not (
            isinstance(a_node, ast.Constant)
            and isinstance(a_node.value, str)
            and isinstance(b_node, ast.Constant)
            and isinstance(b_node.value, str)
        ):
            violations.append(
                f"non-literal replace() argument: {type(a_node).__name__}, "
                f"{type(b_node).__name__}"
            )
            return chain, violations
        chain.append((a_node.value, b_node.value))
        value = value.func.value
    if not (isinstance(value, ast.Name) and value.id == "text"):
        violations.append("chain is not rooted at the parameter `text`")
        return chain, violations
    chain.reverse()
    return chain, violations


def _row_path_source_sha256() -> str:
    """sha256 over the source text of each `_ROW_PATH_SOURCE_NAMES` top-level node of this file,
    in `_ROW_PATH_SOURCE_NAMES` order.

    A node contributes the lines it spans, its first decorator line through `end_lineno`, with
    trailing whitespace stripped and its byte length framed in ahead of it under its own name,
    so that no two spellings of the machinery share a digest. The parser locates those line
    ranges and nothing else: `ast.dump` renders one tree differently on different interpreters
    -- measured, three distinct digests over this file across 3.9, 3.12 and 3.13 -- which makes
    a pin taken over it a report of which Python ran rather than of what the machinery is, red
    on any runner whose version differs from the one that recomputed it. Line numbers and source
    text are the same everywhere.

    The nodes are covered verbatim, their docstrings and inline comments included; prose outside
    them, this module's own docstring among it, stays free to change.
    """
    source = _own_source()
    lines = source.splitlines()
    top_level: dict[str, ast.AST] = {}
    for node in ast.parse(source).body:
        if isinstance(node, ast.FunctionDef):
            top_level[node.name] = node
        elif isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(
            node.targets[0], ast.Name
        ):
            top_level[node.targets[0].id] = node
    digest = hashlib.sha256()
    for name in _ROW_PATH_SOURCE_NAMES:
        node = top_level.get(name)
        if node is None:
            fail(f"row-path source pin: {name} not found at this file's own module top level")
        start = node.lineno
        for decorator in getattr(node, "decorator_list", []):
            start = min(start, decorator.lineno)
        segment = "\n".join(line.rstrip() for line in lines[start - 1 : node.end_lineno])
        encoded = segment.encode("utf-8")
        digest.update(f"{name} {len(encoded)}\n".encode("utf-8"))
        digest.update(encoded)
    return digest.hexdigest()


def _approved_entries_sha256(chain: list[tuple[str, str]]) -> str:
    """sha256 over the ordered `(a, b)` literal pairs of the audited `.replace` chain.

    Each literal is hashed as its own UTF-8 bytes behind their byte length rather than through
    `repr`, for the same reason `_row_path_source_sha256` stays off `ast.dump`: many of these
    literals carry non-ASCII text, and how `repr` escapes it follows the Unicode database the
    running interpreter was built with.
    """
    digest = hashlib.sha256()
    for a, b in chain:
        for literal in (a, b):
            encoded = literal.encode("utf-8")
            digest.update(f"{len(encoded)}\n".encode("utf-8"))
            digest.update(encoded)
    return digest.hexdigest()


def _is_full_row_removal(text: str, a: str, b: str, delta: int) -> bool:
    """Whether a row-count-changing chain entry has the one sanctioned shape: a whole row out.

    `b` empty, `a` a complete line of `text` -- the chain-intermediate text this entry runs
    against -- carried with its trailing newline and no other, and exactly one row fewer
    afterwards. The complete-line requirement is what separates a sanctioned removal from a
    rewrite keyed on a fragment of the row's own body, which ends at the same newline and also
    costs one row, by merging what precedes it into the following line.

    An entry that adds a row (`delta < 0`) is refused here too, fail-closed: the identity this
    feeds subtracts drops and carries no term for an addition, so admitting one takes a reviewed
    generalization of the identity rather than a passing run.
    """
    return (
        b == ""
        and delta == 1
        and a.endswith("\n")
        and "\n" not in a[:-1]
        and a[:-1] in text.splitlines()
    )


def _chain_row_drops(text: str, chain: list[tuple[str, str]]) -> tuple[str, int, list[str]]:
    """Replay `chain` over `text`; return the transformed text, rows dropped, ill-shaped entries.

    Rows are counted only around an entry whose two literals carry different numbers of newlines,
    since that is the only way `str.replace` can change the line count (measured: 2 of the 50
    entries, against 2.3 s for counting rows around all of them). The screen exonerates nothing:
    an entry it skips could still cost a row with no line delta, by rewriting a row into a
    separator, say. Such a loss is attributed to no entry and left to the global identity, which
    subtracts attributed drops only and so fails.
    """
    dropped = 0
    ill_shaped: list[str] = []
    for a, b in chain:
        if a.count("\n") == b.count("\n"):
            text = text.replace(a, b)
            continue
        rows_before = len(table_data_rows(text.splitlines()))
        replaced = text.replace(a, b)
        delta = rows_before - len(table_data_rows(replaced.splitlines()))
        if delta and not _is_full_row_removal(text, a, b, delta):
            ill_shaped.append(f"{a[:80]!r} -> {b[:40]!r} (delta={delta})")
        dropped += delta
        text = replaced
    return text, dropped, ill_shaped


def _row_conservation_violations(
    source: str, published_rows: Callable[[], list[str]]
) -> list[str]:
    """Parts B and A against `source`'s literal chain and `published_rows`' row sequence.

    Both are parameters only so that the positive controls below can drive this with a mutated
    copy of this file's own `_approved_replacements`, and with a row sequence a rewrite outside
    the chain has thinned, which is the defect class the identity exists to refuse.
    """
    chain, violations = _approved_replacements_chain(source)
    if violations:
        return ["_approved_replacements shape violation: " + "; ".join(violations)]
    baseline_text = catalogue_baseline_text()
    baseline_rows = len(table_data_rows(baseline_text.splitlines()))
    if baseline_rows != BASELINE_CATALOGUE_ROW_COUNT:
        return [
            "BASELINE_CATALOGUE_ROW_COUNT is stale: expected "
            f"{BASELINE_CATALOGUE_ROW_COUNT}, the frozen baseline slice has {baseline_rows} "
            "rows. Recompute with: python3 -c 'import sys; sys.path.insert(0, \"scripts\"); "
            "import check_docs_hierarchy as c; "
            "print(len(c.table_data_rows(c.catalogue_baseline_text().splitlines())))'"
        ]
    after_chain, dropped, ill_shaped = _chain_row_drops(baseline_text, chain)
    if ill_shaped:
        violations.append(
            "row-count-changing chain entry is not a full-row removal: " + "; ".join(ill_shaped)
        )
    after_citations = _drop_working_note_citations(after_chain)
    after_private = _drop_private_instructions_ref(after_citations)
    rows_after_chain = len(table_data_rows(after_chain.splitlines()))
    rows_after_citations = len(table_data_rows(after_citations.splitlines()))
    rows_after_private = len(table_data_rows(after_private.splitlines()))
    if rows_after_chain != rows_after_citations or rows_after_citations != rows_after_private:
        violations.append(
            "structural pass dropped a row: _drop_working_note_citations left "
            f"{rows_after_citations} rows of {rows_after_chain} and "
            f"_drop_private_instructions_ref {rows_after_private} of {rows_after_citations}, "
            "where a row leaves only by a literal of the audited chain"
        )
    published = len(published_rows())
    if BASELINE_CATALOGUE_ROW_COUNT - dropped != published:
        violations.append(
            "row conservation identity failed: BASELINE_CATALOGUE_ROW_COUNT "
            f"({BASELINE_CATALOGUE_ROW_COUNT}) - rows the audited chain drops ({dropped}) != "
            f"published rows ({published}), so a row left the catalogue somewhere other than a "
            "full-row literal of that chain"
        )
    return violations


def approved_replacements_shape_and_row_identity_self_test() -> None:
    """Refuse any row loss that is not a full-row literal of the audited `.replace` chain.

    The row-conservation identity replays that chain entry by entry over the frozen baseline
    slice and requires `BASELINE_CATALOGUE_ROW_COUNT - (rows the chain drops) ==
    len(published_catalogue_rows())`, with every row-count-changing entry a full-row removal in
    the sense of `_is_full_row_removal` and with the two structural passes
    (`_drop_working_note_citations`, `_drop_private_instructions_ref`) dropping no row at all.
    Unlike the two pins of `approved_changes_byte_parity_self_test`, an identity between three
    quantities is not satisfiable by recomputing anything: a rewrite keyed on a Lean name, at any
    narrowing and at any depth, leaves the published catalogue short of what the chain accounts
    for.

    The shape rule requires `_approved_replacements` to keep the form
    `_approved_replacements_chain` parses, which is what makes that attribution a legible diff
    rather than a runtime accident. The last two pins cover machinery rather than content.
    `ROW_PATH_SOURCE_SHA256` hashes the row-derivation nodes, which no catalogue content edit
    touches, so a commit that moves it is machinery surgery and has to be reviewed as such
    rather than accepted on a recompute. `APPROVED_ENTRIES_SHA256` hashes the reviewed literal
    list, which a sanctioned removal is supposed to move; what it catches is surgery inside that
    list which leaves the published bytes alone.
    """
    source = _own_source()

    # Positive controls: a check whose subject is an absence has to be shown firing on the defect
    # it exists to refuse. Each control injects one defect into the same functions the real check
    # below drives -- a mutated copy of this file's own `_approved_replacements`, a row sequence
    # thinned outside the chain, the attribution predicate itself. The two AST mutations are
    # re-spelled from the parsed function, so they stay exact under any later edit of the chain.
    def mutated_chain_source(mutate: Callable[[ast.FunctionDef], None]) -> str:
        """`_approved_replacements` alone, re-spelled from its own AST after `mutate` edits it."""
        node = _approved_replacements_function_node(source)
        mutate(node)
        return ast.unparse(node)

    def key_one_entry_on_a_call(node: ast.FunctionDef) -> None:
        """Re-key one rewrite on a call instead of a literal: a name-keyed drop, spelled inside
        the chain."""
        for call in ast.walk(node):
            if (
                isinstance(call, ast.Call)
                and isinstance(call.func, ast.Attribute)
                and call.func.attr == "replace"
            ):
                call.args[0] = ast.Call(
                    func=ast.Name(id="_row_for", ctx=ast.Load()),
                    args=[ast.Constant(value="x"), ast.Name(id="text", ctx=ast.Load())],
                    keywords=[],
                )
                return
        fail("shape/row-identity control setup: no .replace call to re-key on a call")

    def wrap_chain_in_extra_pass(node: ast.FunctionDef) -> None:
        """Wrap the audited chain in a pass outside it, where an unaudited rewrite could sit."""
        node.body[-1].value = ast.Call(
            func=ast.Name(id="_extra_pass", ctx=ast.Load()),
            args=[node.body[-1].value],
            keywords=[],
        )

    for label, mutate, expected in (
        ("a rewrite keyed on a call", key_one_entry_on_a_call, "non-literal replace() argument"),
        ("an extra pass around the chain", wrap_chain_in_extra_pass, "unpinned wrapper chain"),
    ):
        refusals = _row_conservation_violations(
            mutated_chain_source(mutate), published_catalogue_rows
        )
        if not any(expected in refusal for refusal in refusals):
            fail(
                f"shape/row-identity control did not fire: {label} was accepted, so the shape "
                f"rule cannot detect what it exists to refuse (got {refusals})"
            )

    published = published_catalogue_rows()
    if not published:
        fail(
            "shape/row-identity self-test found no published catalogue rows, so the identity "
            "below would hold vacuously"
        )
    control_cell = published[0].removeprefix("| ").split(" | ")[0]
    thinned = [row for row in published if not row.startswith(f"| {control_cell} |")]
    if len(thinned) == len(published):
        fail(
            "shape/row-identity control setup: the name-keyed shim dropped no row, so its "
            f"control below would be probing the published sequence itself ({control_cell})"
        )
    refusals = _row_conservation_violations(source, lambda: thinned)
    if not any("row conservation identity failed" in refusal for refusal in refusals):
        fail(
            "shape/row-identity control did not fire: a row dropped by name outside the audited "
            f"chain ({control_cell}) was accepted, so the identity cannot detect the defect "
            f"class it exists to refuse (got {refusals})"
        )

    body_fragment = published[0].split(" | ", 1)[-1] + "\n"
    if body_fragment == published[0] + "\n":
        fail(
            "shape/row-identity control setup: the first published row carries no body cell to "
            "key a fragment removal on"
        )
    if _is_full_row_removal(catalogue_baseline_text(), body_fragment, "", 1):
        fail(
            "shape/row-identity control did not fire: a removal keyed on a fragment of a row's "
            "body was attributed as a full-row removal, so the identity's attribution admits "
            "the rewrite it exists to refuse"
        )

    violations = _row_conservation_violations(source, published_catalogue_rows)
    if violations:
        fail("; ".join(violations))
    source_actual = _row_path_source_sha256()
    if source_actual != ROW_PATH_SOURCE_SHA256:
        fail(
            "row-path source pin mismatch, which is machinery surgery rather than a content "
            f"edit: expected {ROW_PATH_SOURCE_SHA256}, got {source_actual}. Recompute with: "
            "python3 -c 'import sys; sys.path.insert(0, \"scripts\"); "
            "import check_docs_hierarchy as c; print(c._row_path_source_sha256())' -- a passing "
            "pin recompute is never on its own an authorization for what moved."
        )
    entries_actual = _approved_entries_sha256(_approved_replacements_chain(source)[0])
    if entries_actual != APPROVED_ENTRIES_SHA256:
        fail(
            f"approved-entries pin mismatch: expected {APPROVED_ENTRIES_SHA256}, got "
            f"{entries_actual}. Recompute with: python3 -c 'import sys; "
            "sys.path.insert(0, \"scripts\"); import check_docs_hierarchy as c; "
            "print(c._approved_entries_sha256(c._approved_replacements_chain(c._own_source())"
            "[0]))' -- a passing pin recompute is never on its own an authorization for what "
            "moved."
        )


MOVED_PROSE_LINK_REWRITES = (
    ("(refactoring-conventions.html)", "(/lattice-system/refactoring-conventions/)"),
    (
        "(deprecations.html#remaining-linter-suppressions)",
        "(/lattice-system/deprecations/#remaining-linter-suppressions)",
    ),
    ("(deprecations.html)", "(/lattice-system/deprecations/)"),
    ("(jordan-wigner-overview.html)", "(/lattice-system/jordan-wigner-overview/)"),
    (
        "](#deleted-routes-what-this-index-used-to-document)",
        "](/lattice-system/history/deleted-routes/#deleted-routes-what-this-index-used-to-document)",
    ),
)
MOVED_PROSE_LINK_REWRITE_COUNTS = (1, 1, 1, 1, 3)


def whitespace_normalized(text: str) -> str:
    """Normalize whitespace only; preserve punctuation, operators, Markdown, and Unicode."""
    return re.sub(r"\s+", " ", text).strip()


def apply_moved_prose_link_rewrites(text: str, counts: list[int] | None = None) -> str:
    """Apply only the seven audited old-public-link migrations to baseline prose."""
    for index, (old, new) in enumerate(MOVED_PROSE_LINK_REWRITES):
        if counts is not None:
            counts[index] += text.count(old)
        text = text.replace(old, new)
    return text


def reconstruct_roadmap_prose(current: str, baseline_line: str) -> str:
    """Invert the known heading/list layout used for one former roadmap row."""
    cells = baseline_line.removeprefix("| ").removesuffix(" |\n").split(" | ", 2)
    phase, scope, _status = (cells[0], "", cells[1]) if len(cells) == 2 else cells
    lines = current.splitlines()
    heading = f"## {phase}: {scope}" if scope else f"## {phase}"
    if lines and lines[0] == heading:
        lines = lines[1:]
    payload = []
    for line in lines:
        payload.append(line[2:] if line.startswith("- ") else line)
    return " ".join(part for part in (phase, scope, "\n".join(payload)) if part)


def normalize_current_moved_prose(start: int, end: int, current: str, old_lines: list[str]) -> str:
    """Invert only documented presentation wrappers and three governance corrections."""
    if start == end and 114 <= start <= 153:
        current = reconstruct_roadmap_prose(current, old_lines[start - 1])
    current = current.replace(
        "The catalogue below includes proved results, conditional results, and documented axioms as recorded, with **zero `sorry`**.",
        "All items below are formally proved with **zero `sorry`**.",
    )
    current = current.replace(
        "**Phase A (historical scaffold; implementation recorded at the time)**",
        "**Phase A (current, this PR)**",
    )
    # The §10.1 arc (#5313) discharges Lemma 10.1, so the documented-axiom policy preamble stops
    # naming it as a perturbation-theoretic axiom and delimits that class by the analytic
    # machinery it needs instead.  The ledger paragraph is hard-wrapped, so unlike the two
    # corrections above this one is inverted after whitespace normalization.
    #
    # PR-15c (#5320) then discharges Theorem 10.4 itself: the closing parenthetical grows from
    # "Lemma 10.1 and ... Theorem A.12 are both axiom-free" to "..., and Theorem 10.4 are all
    # axiom-free", and the sentence recording Theorem 10.4 as fully axiomatized is deleted outright
    # (rather than edited), so it must be reinstated here — with the still-open tracker issue,
    # which the next .replace folds back to the closed #5004 to match the historical baseline.
    return whitespace_normalized(current).replace(
        "- **Perturbation-theoretic results** (e.g., the singular-perturbation and "
        "adiabatic-continuation arguments in Chapter 10, the cluster expansions behind **Theorem "
        "7.3** and **Theorem 8.1**, and the quasi-adiabatic continuation behind **Theorem 8.9**): "
        "the analytic proofs of weak-coupling continuation and adiabatic following for eigenstate "
        "families are **not undertaken** as an active project goal; such techniques naturally "
        "belong to a separate analytic-perturbation development. The class is delimited by the "
        "*machinery* it needs — analytic eigenvalue-branch (Rellich–Kato) continuation, "
        "cluster/polymer expansions, volume-uniform estimates — and does **not** cover "
        "finite-dimensional degenerate perturbation theory at fixed finite volume, which is "
        "ordinary linear algebra and is proved (**Lemma 10.1**, the strong-coupling **Theorem "
        "A.12**, and **Theorem 10.4** are all axiom-free).",
        "- **Perturbation-theoretic results** (e.g., **Lemma 10.1** (Tasaki §10.1, degenerate "
        "perturbation theory) and singular-perturbation arguments in Chapter 10): the analytic "
        "proofs of weak-coupling continuation and adiabatic following for eigenstate families are "
        "**not undertaken** as an active project goal; such techniques naturally belong to a "
        "separate analytic-perturbation development. **Theorem 10.4** (Lieb's repulsive-Hubbard "
        "half-filling ground state) currently has its entire content axiomatized: the global "
        "minimum energy, ground-state degeneracy, and total-spin values are all undischarged. "
        "(The fixed-Ŝ³-sector ground-state uniqueness has been proved; full theorem discharge is "
        "tracked in Issue #5320.)",
    ).replace(
        # Issue #5004 was closed; the Theorem 10.4 discharge is now tracked in Issue #5320, so the
        # ledger's pointer follows the open tracker.  Hard-wrapped, hence inverted after
        # whitespace normalization like the correction above.
        "full theorem discharge is tracked in Issue #5320.",
        "full theorem discharge is tracked in Issue #5004.",
    )


def moved_prose_negative_self_tests() -> None:
    baseline = "**Moved prose:** a ≤ b = c → d; [link](/stable/)"
    if whitespace_normalized(baseline) != whitespace_normalized(baseline.replace("  ", "\n")):
        fail("moved-prose positive whitespace self-test failed")
    for mutated in (
        baseline.replace("≤", "≥"),
        baseline.replace("=", "≠", 1),
        baseline.replace("→", "←"),
    ):
        if whitespace_normalized(baseline) == whitespace_normalized(mutated):
            fail("moved-prose punctuation/operator mutation was not rejected")


def long_record_fidelity(
    baseline_cells: list[str],
    compact_cells: list[str],
    detail_lean: str,
    detail_file: str,
    detail_statement: str,
) -> bool:
    baseline_file = baseline_cells[2] if len(baseline_cells) == 3 else ""
    compact_file = compact_cells[2] if len(compact_cells) == 3 else ""
    return (
        len(baseline_cells) == len(compact_cells)
        and compact_cells[0] == baseline_cells[0]
        and compact_file == baseline_file
        and detail_lean == baseline_cells[0]
        and detail_file == baseline_file
        and whitespace_normalized(detail_statement) == whitespace_normalized(baseline_cells[1])
    )


def long_record_negative_self_tests() -> None:
    baseline = ["`lean_name`", "**Result:** a ≤ b = c → d", "`Path/File.lean`"]
    compact = [baseline[0], "See the grouped detail record.", baseline[2]]
    if not long_record_fidelity(baseline, compact, baseline[0], baseline[2], baseline[1]):
        fail("long-record fidelity positive self-test failed")
    mutations = (
        (baseline[1].replace("≤", "≥"), baseline[0], baseline[2], compact),
        (baseline[1].replace("=", "≠", 1), baseline[0], baseline[2], compact),
        (baseline[1].replace("→", "←"), baseline[0], baseline[2], compact),
        (baseline[1], "`lean_name_drift`", baseline[2], compact),
        (baseline[1], baseline[0], "`Path/Other.lean`", compact),
        (baseline[1], baseline[0], baseline[2], ["`compact_name_drift`", compact[1], compact[2]]),
    )
    for statement, detail_lean, detail_file, compact_cells in mutations:
        if long_record_fidelity(baseline, compact_cells, detail_lean, detail_file, statement):
            fail("long-record fidelity negative mutation self-test was not rejected")


def public_target(
    target: str,
    source: Path,
    permalink_to_page: dict[str, Path],
    file_aliases: dict[str, Path],
) -> tuple[Path | None, str]:
    target = target.replace(r"\#", "#")
    parsed = urlsplit(target)
    if parsed.scheme:
        if parsed.scheme != "https" or parsed.netloc != "phasetr.github.io":
            return None, ""
        route = parsed.path.removeprefix("/lattice-system") or "/"
    elif parsed.path.startswith("/lattice-system"):
        route = parsed.path.removeprefix("/lattice-system") or "/"
    elif parsed.path.startswith("/"):
        return None, ""
    else:
        if not parsed.path:
            return source, parsed.fragment
        direct_alias = file_aliases.get("/" + parsed.path)
        if direct_alias is not None:
            return direct_alias, parsed.fragment
        candidate = (source.parent / unquote(parsed.path)).resolve()
        if candidate in file_aliases.values():
            return candidate, parsed.fragment
        source_route = next(
            (route for route, page in permalink_to_page.items() if page == source),
            "/",
        )
        route = posixpath.normpath(posixpath.join(posixpath.dirname(source_route), parsed.path))
        if not route.startswith("/"):
            route = "/" + route
    target_page = permalink_to_page.get(route) or file_aliases.get(route)
    return target_page, parsed.fragment


CLONE_BASED_SELF_TEST_CALLS = (
    "    frozen_row_drop_negative_self_test()\n",
    "    absent_name_row_drop_negative_self_test()\n",
    "    unrecognized_argument_self_test()\n",
)


def _without_clone_based_self_tests(script_text: str, probe: str) -> str:
    """Return this script's text with every clone-based self-test call removed from `main()`.

    Each of those self-tests runs a copy of this script inside a disposable clone, so a copy
    that still reached one of their calls would clone a mirror of its own; git halts the descent
    only at its alternate-object nesting limit, and a nested probe's failure would be reported as
    the outer fixture's setup error. Every call is required to be found rather than removed where
    present, because a rename that silently stopped being stripped is precisely the way this
    protection would be lost without any test failing.
    """
    for call in CLONE_BASED_SELF_TEST_CALLS:
        if call not in script_text:
            fail(
                f"{probe} could not locate {call.strip()} in main(): a mirror must have every "
                "clone-based self-test call removed before it is run"
            )
        script_text = script_text.replace(call, "")
    return script_text


def frozen_row_drop_negative_self_test() -> None:
    """A published catalogue row must not vanish from a legacy page without a refusal.

    A row leaves the published catalogue only when `_approved_replacements` rewrites that row's
    exact frozen baseline text away, so a page that quietly stops carrying a row is the edit the
    comparison against the transformed baseline exists to catch. This probes that boundary in a
    disposable clone using the row of a declaration the tree still carries
    (`oscillatorStrength_abs_le`, `LatticeSystem/Quantum/SpinS/OscillatorStrengthBound.lean`),
    the same edit an incautious future PR could make by hand, and requires the refusal to account
    for exactly the one row that went missing.
    """
    with tempfile.TemporaryDirectory(prefix="frozen-row-drop-") as scratch:
        mirror = Path(scratch) / "mirror"
        subprocess.run(
            ["git", "clone", "--quiet", "--shared", str(ROOT), str(mirror)], check=True
        )
        script_path = mirror / "scripts" / "check_docs_hierarchy.py"
        script_path.write_text(
            _without_clone_based_self_tests(
                script_path.read_text(), "frozen-row-drop self-test"
            )
        )

        baseline = subprocess.run(
            [sys.executable, "scripts/check_docs_hierarchy.py"],
            cwd=mirror,
            capture_output=True,
            text=True,
        )
        if baseline.returncode != 0:
            fail(
                "frozen-row-drop self-test setup failed: the mirror does not pass before its "
                f"legacy page is edited (exit={baseline.returncode}): {baseline.stderr}"
            )

        legacy_page = (
            mirror
            / "docs"
            / "formalization"
            / "legacy"
            / "16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-01.md"
        )
        legacy_text = legacy_page.read_text()
        row_pattern = re.compile(r"^\| `oscillatorStrength_abs_le` \|.*\n", re.MULTILINE)
        mutated_legacy, row_drops = row_pattern.subn("", legacy_text)
        if row_drops != 1:
            fail(
                "frozen-row-drop self-test could not find exactly one live "
                f"oscillatorStrength_abs_le row (found {row_drops})"
            )
        legacy_page.write_text(mutated_legacy)

        probe = subprocess.run(
            [sys.executable, "scripts/check_docs_hierarchy.py"],
            cwd=mirror,
            capture_output=True,
            text=True,
        )
        if probe.returncode == 0:
            fail(
                "frozen-row-drop fail-open: dropping the published row of a still-declared "
                "name (oscillatorStrength_abs_le, "
                "LatticeSystem/Quantum/SpinS/OscillatorStrengthBound.lean) from its legacy page "
                "must be refused, but the checker exited 0"
            )
        difference = re.search(
            r"legacy catalogue row order/content differs: expected=(\d+), actual=(\d+)",
            probe.stderr,
        )
        if difference is None:
            fail(
                "frozen-row-drop probe failed for the wrong reason: expected the legacy "
                f"catalogue row comparison to refuse the edit, got: {probe.stderr}"
            )
        else:
            missing = int(difference.group(1)) - int(difference.group(2))
            if missing != 1:
                fail(
                    "frozen-row-drop probe refused the edit over a different quantity than the "
                    f"single row removed: expected one row missing, got {missing}"
                )


def absent_name_row_drop_negative_self_test() -> None:
    """A row must never be droppable merely because its Lean-name cell is already absent.

    Published catalogue rows routinely name declarations the Lean tree no longer spells: at the
    revision this was measured, 91 of the 2050 published catalogue rows (4.4%) name at least one
    such identifier -- 64 of them name nothing else -- across 148 distinct absent identifier
    tokens, against the two rows the catalogue actually retires. Absence is the ordinary
    condition of a historical catalogue, not evidence that a row may go. This probes that
    boundary end to end in a disposable clone by re-creating the shape that would make absence
    sufficient -- a name-keyed drop wired into `approved_changes` for an arbitrary already-absent
    name (`pauli_decomposition`) -- and hand-dropping that row from the live legacy page so that
    both halves of the fail-open are present at once. The checker must refuse, and the
    byte-parity pin is what refuses: a name-keyed drop is not a rewrite of the row's frozen text,
    so the transformed catalogue stops hashing to the audited value. The shape itself, wherever
    it sits and however narrowly it is bounded, is what
    `approved_replacements_shape_and_row_identity_self_test` refuses, by the row that goes
    missing from the identity rather than by any spelling; the anchor this fixture matches below
    is only its own wiring.
    """
    with tempfile.TemporaryDirectory(prefix="absent-name-row-drop-") as scratch:
        mirror = Path(scratch) / "mirror"
        subprocess.run(
            ["git", "clone", "--quiet", "--shared", str(ROOT), str(mirror)], check=True
        )
        script_path = mirror / "scripts" / "check_docs_hierarchy.py"
        script_text = _without_clone_based_self_tests(
            script_path.read_text(), "absent-name row drop self-test"
        )
        script_path.write_text(script_text)

        baseline = subprocess.run(
            [sys.executable, "scripts/check_docs_hierarchy.py"],
            cwd=mirror,
            capture_output=True,
            text=True,
        )
        if baseline.returncode != 0:
            fail(
                "absent-name row drop self-test setup failed: the mirror does not pass before "
                f"it is mutated (exit={baseline.returncode}): {baseline.stderr}"
            )

        legacy_page = (
            mirror
            / "docs"
            / "formalization"
            / "legacy"
            / "07-pauli-basis-decomposition-tasaki-2-1-problem-2-1-a-s-1-2.md"
        )
        legacy_text = legacy_page.read_text()
        row_pattern = re.compile(r"^\| `pauli_decomposition` \|.*\n", re.MULTILINE)
        mutated_legacy, row_drops = row_pattern.subn("", legacy_text)
        if row_drops != 1:
            fail(
                "absent-name row drop self-test could not find exactly one live "
                f"pauli_decomposition row (found {row_drops})"
            )
        legacy_page.write_text(mutated_legacy)

        # Dropping the row from the page alone is already refused, so the fixture must also give
        # the mirror the authorization it is being probed for: a drop keyed on the name rather
        # than on the row's frozen text, which is what makes absence look sufficient. Only this
        # fixture's own wiring depends on the exact spelling below; the shape itself is refused
        # by `approved_replacements_shape_and_row_identity_self_test`.
        anchor = "    return _drop_private_instructions_ref(_approved_replacements(text))\n"
        if anchor not in script_text:
            fail(
                "absent-name row drop self-test could not locate approved_changes' return "
                "statement, so it cannot wire the name-keyed drop it exists to refuse"
            )
        name_keyed_drop = (
            "    return re.sub(\n"
            '        r"^\\| `pauli_decomposition` \\|.*\\n?",\n'
            '        "",\n'
            "        _drop_private_instructions_ref(_approved_replacements(text)),\n"
            "        flags=re.MULTILINE,\n"
            "    )\n"
        )
        script_path.write_text(script_text.replace(anchor, name_keyed_drop))

        probe = subprocess.run(
            [sys.executable, "scripts/check_docs_hierarchy.py"],
            cwd=mirror,
            capture_output=True,
            text=True,
        )
        if probe.returncode == 0:
            fail(
                "absent-name row drop fail-open: pauli_decomposition is absent from the Lean "
                "tree, but a name-keyed drop of its catalogue row was accepted (mirror exited 0)"
            )
        if "byte-parity pin mismatch" not in probe.stderr:
            fail(
                "absent-name row drop probe failed for the wrong reason: expected the "
                "approved-changes byte-parity pin to refuse the name-keyed drop, got: "
                f"{probe.stderr}"
            )


def unrecognized_argument_self_test() -> None:
    """`main()` must refuse argv it does not accept instead of running as if it were bare.

    This checker takes no options, so an invocation written like its four sibling checkers'
    `--self-test` would otherwise produce a PASS that the argument had no part in. The probe
    runs a copy of this working-tree file inside a disposable clone with its own call removed,
    because a copy that still ignored argv would re-enter this self-test and clone without end.
    """
    with tempfile.TemporaryDirectory(prefix="unrecognized-argument-") as scratch:
        mirror = Path(scratch) / "mirror"
        subprocess.run(
            ["git", "clone", "--quiet", "--shared", str(ROOT), str(mirror)], check=True
        )
        script_path = mirror / "scripts" / "check_docs_hierarchy.py"
        script_path.write_text(
            _without_clone_based_self_tests(
                Path(__file__).resolve().read_text(), "unrecognized-argument self-test"
            )
        )

        for argument in ("--self-test", "--bogus-flag-xyz", "bogus-positional"):
            probe = subprocess.run(
                [sys.executable, "scripts/check_docs_hierarchy.py", argument],
                cwd=mirror,
                capture_output=True,
                text=True,
            )
            if probe.returncode == 0:
                fail(
                    f"argv fail-open: {argument} must be refused, but the checker exited 0 and "
                    "answered with a PASS the argument had no part in"
                )
            if "unrecognized arguments" not in probe.stderr:
                fail(
                    f"argv probe failed for the wrong reason with {argument}: expected an "
                    f"argparse rejection, got (exit={probe.returncode}): {probe.stderr}"
                )
            if probe.stdout:
                fail(
                    f"argv fail-open: {argument} must be refused before the hierarchy checks "
                    "run, so a rejected run must write nothing to standard output, but this "
                    f"one wrote: {probe.stdout!r}"
                )


def main() -> None:
    # This checker has no modes: every run performs the same self-tests and the same hierarchy
    # checks, so the parser deliberately declares no options. Its only job is to refuse argv that
    # a caller believed selected behaviour -- the sibling checkers' --self-test above all -- which
    # would otherwise be ignored and answered with a PASS the argument had no part in.
    argparse.ArgumentParser(description=__doc__).parse_args()
    approved_changes_byte_parity_self_test()
    approved_replacements_shape_and_row_identity_self_test()
    long_record_negative_self_tests()
    moved_prose_negative_self_tests()
    frozen_row_drop_negative_self_test()
    absent_name_row_drop_negative_self_test()
    unrecognized_argument_self_test()
    generated_records = DOCS / "formalization" / "records"
    if generated_records.exists() or generated_records.is_symlink():
        fail(
            "docs/formalization/records is generator-owned and must not be committed"
        )
    old_text = baseline_index()
    old_lines = old_text.splitlines(keepends=True)
    permalink_to_page: dict[str, Path] = {}
    file_aliases: dict[str, Path] = {}
    bodies: dict[Path, str] = {}
    all_anchors: dict[Path, set[str]] = {}
    warnings: list[str] = []
    max_bytes = (0, Path())
    max_lines = (0, Path())
    max_rows = (0, Path())

    for page in ALL_DOC_PAGES:
        text = page.read_text()
        validate_pipe_blocks(page, text)
        if not text.startswith("---\n"):
            continue
        metadata, body = front_matter(page)
        route = metadata["permalink"]
        if route in permalink_to_page:
            fail(f"duplicate permalink {route}: {permalink_to_page[route]} and {page}")
        permalink_to_page[route] = page
        relative = page.relative_to(DOCS).with_suffix("")
        file_aliases["/" + str(relative) + ".html"] = page
        file_aliases["/" + str(page.relative_to(DOCS))] = page
        anchor_values = anchor_list(body)
        duplicates = [key for key, count in Counter(anchor_values).items() if count > 1]
        if duplicates:
            fail(f"duplicate explicit/heading anchor in {page.relative_to(ROOT)}: {duplicates}")
        all_anchors[page] = set(anchor_values)

    for page in PAGES:
        _, body = front_matter(page)
        bodies[page] = body
        validate_pipe_blocks(page, body)
        raw = page.read_bytes()
        if not raw.endswith(b"\n"):
            fail(f"missing final newline: {page.relative_to(ROOT)}")
        for number, line in enumerate(raw.splitlines(), 1):
            if line.rstrip() != line:
                fail(f"trailing whitespace: {page.relative_to(ROOT)}:{number}")
        line_count = raw.count(b"\n")
        row_count = len(table_data_rows(body.splitlines()))
        max_bytes = max(max_bytes, (len(raw), page), key=lambda item: item[0])
        max_lines = max(max_lines, (line_count, page), key=lambda item: item[0])
        max_rows = max(max_rows, (row_count, page), key=lambda item: item[0])
        if len(raw) > HARD_BYTES or line_count > HARD_LINES:
            fail(f"hard page-size threshold exceeded: {page.relative_to(ROOT)} ({len(raw)} bytes, {line_count} lines)")
        if len(raw) > SOFT_BYTES or line_count > SOFT_LINES or row_count > SOFT_ROWS:
            warnings.append(
                f"soft threshold: {page.relative_to(ROOT)}: {len(raw)} bytes, {line_count} lines, {row_count} rows"
            )

    root = DOCS / "index.md"
    if root.read_text().count("\n") > 250:
        fail("docs/index.md exceeds 250 lines")
    expected_headings = [
        (line_number, match.group(1))
        for line_number, line in enumerate(old_text.splitlines(), 1)
        if (match := re.match(r"^#{2,4} (.+)$", line))
    ]
    fixture_lines = tuple(line for line, _anchor in FORMER_ROOT_IDS)
    if fixture_lines != tuple(line for line, _heading in expected_headings):
        fail("fixed former-root anchor fixture no longer matches the 68 old heading lines")
    expected_ids = {anchor for _line, anchor in FORMER_ROOT_IDS}
    fixture_by_line = dict(FORMER_ROOT_IDS)
    if fixture_by_line[244] != "spin-12-operators-tasaki-21" or not fixture_by_line[297].startswith("d-rotation-"):
        fail("fixed Kramdown compatibility examples differ")
    explicit_root = set(re.findall(r'<a\s+id="([^"]+)"\s*></a>', bodies[root]))
    if explicit_root != expected_ids:
        fail(f"root compatibility IDs differ: missing={sorted(expected_ids-explicit_root)}, extra={sorted(explicit_root-expected_ids)}")

    ledger = DOCS / "limitations" / "documented-axioms.md"
    ledger_headings = [
        (line_number, match.group(1))
        for line_number, line in enumerate(baseline_ledger().splitlines(), 1)
        if (match := re.match(r"^#{1,6} (.+)$", line))
    ]
    if FORMER_LEDGER_IDS != tuple(
        (line_number, heading_anchor(heading)) for line_number, heading in ledger_headings
    ):
        fail("fixed former-ledger anchor fixture no longer matches the pre-split ledger headings")
    ledger_ids = {anchor for _line, anchor in FORMER_LEDGER_IDS}
    unreachable = ledger_ids - all_anchors[ledger]
    if unreachable:
        fail(f"pre-split ledger IDs no longer resolve on the ledger page: {sorted(unreachable)}")
    invented = set(re.findall(r'<a\s+id="([^"]+)"\s*></a>', bodies[ledger])) - ledger_ids
    if invented:
        fail(f"ledger compatibility anchors are not pre-split Kramdown IDs: {sorted(invented)}")

    # Resolve Markdown links in every docs page plus repository-facing prose.
    markdown_sources = ALL_DOC_PAGES + [ROOT / "README.md", ROOT / "AGENTS.md"]
    link_pattern = re.compile(
        r"\[[^\]\n]+\]\(((?:https?://|/|#|(?:\.\.?/)?[\w./-]+\.(?:md|html|tex|pdf))[^ )]*)(?:\s+[^)]*)?\)"
    )
    for source in markdown_sources:
        if not source.exists():
            continue
        text = source.read_text()
        for target in link_pattern.findall(text):
            if target.startswith("mailto:"):
                continue
            target_page, fragment = public_target(target, source, permalink_to_page, file_aliases)
            parsed = urlsplit(target)
            is_internal = (
                target.startswith(("#", "/lattice-system"))
                or (parsed.scheme == "https" and parsed.netloc == "phasetr.github.io")
                or (not parsed.scheme and not parsed.path.startswith("/"))
            )
            if target_page is None:
                if is_internal and not (source.parent / unquote(parsed.path)).exists():
                    fail(f"unresolved internal link {target} from {source.relative_to(ROOT)}")
                continue
            if fragment and fragment not in all_anchors.get(target_page, set()):
                fail(f"unresolved fragment #{fragment} on {target_page.relative_to(ROOT)} from {source.relative_to(ROOT)}")

    # Audit published project URLs embedded in Lean and TeX comments/prose.
    public_url = re.compile(r"https://phasetr\.github\.io/lattice-system/[^\s)\]}]*")
    for source in [*ROOT.glob("*.md"), *ROOT.rglob("*.lean"), *ROOT.rglob("*.tex")]:
        if any(part in {".lake", ".git"} for part in source.parts):
            continue
        for target in public_url.findall(source.read_text(errors="replace")):
            target_page, fragment = public_target(target.rstrip(">}.,;"), source, permalink_to_page, file_aliases)
            if target_page is None:
                fail(f"unresolved published project URL {target} in {source.relative_to(ROOT)}")
            if fragment and fragment not in all_anchors.get(target_page, set()):
                fail(f"unresolved published fragment #{fragment} in {source.relative_to(ROOT)}")

    # Catalogue rows must retain exact global order after the two evidenced status corrections.
    # Long cells are reconstructed from one compact table reference and one grouped detail record.
    catalogue_baseline = catalogue_baseline_text()
    private_instructions_removals = len(
        _PRIVATE_INSTRUCTIONS_REF.findall(_approved_replacements(catalogue_baseline))
    )
    if private_instructions_removals != PRIVATE_INSTRUCTIONS_REMOVAL_COUNT:
        fail(
            "audited private project-instructions removal count differs: "
            f"expected={PRIVATE_INSTRUCTIONS_REMOVAL_COUNT}, actual={private_instructions_removals}"
        )
    working_note_counts = [
        len(_WORKING_NOTE_CITATION.findall(catalogue_baseline)),
        len(_WORKING_NOTE_SECTION_REF.findall(catalogue_baseline)),
        0,
    ]
    expected_rows = published_catalogue_rows()
    expected_by_line: dict[int, str] = {}
    expected_long_lines: set[int] = set()
    catalogue_lines = range(CATALOGUE_BASELINE_SLICE.start + 1, CATALOGUE_BASELINE_SLICE.stop + 1)
    for line_number in catalogue_lines:
        line = approved_changes(old_lines[line_number - 1]).rstrip("\n")
        if not line.startswith("|") or is_separator(line):
            continue
        cells = line.removeprefix("| ").removesuffix(" |").split(" | ")
        if not cells or cells[0] == "Lean name":
            continue
        expected_by_line[line_number] = line
        if len(line.encode()) > LONG_CELL_BYTES or (len(cells) >= 2 and len(cells[1].encode()) > LONG_CELL_BYTES):
            expected_long_lines.add(line_number)
    actual_rows: list[str] = []
    compact_long_cells: dict[int, list[str]] = {}
    chapter_anchor_rows: dict[int, list[str]] = defaultdict(list)
    legacy_pages = sorted((DOCS / "formalization" / "legacy").glob("*.md"))
    for page in legacy_pages:
        if page.name == "index.md":
            continue
        _, body = front_matter(page)
        marker_text = "".join(match.group(3) for match in SOURCE_MARKER.finditer(body))
        for row in table_data_rows(marker_text.splitlines()):
            for source_line, anchor in CHAPTER_ROW_ANCHORS.items():
                if f'<a id="{anchor}"></a>' in row:
                    chapter_anchor_rows[source_line].append(row)
            row = re.sub(r'<a id="tasaki-chapter-[^"]+"></a> ', "", row)
            detail_ref = re.search(r"<!-- legacy-detail-ref:(\d+) -->", row)
            if detail_ref:
                source_line = int(detail_ref.group(1))
                if source_line not in expected_long_lines:
                    fail(f"unexpected long-record reference for former line {source_line}")
                compact_long_cells[source_line] = row.removeprefix("| ").removesuffix(" |").split(" | ")
                row = expected_by_line[source_line]
            actual_rows.append(row)
        for number, row in enumerate(marker_text.splitlines(), 1):
            if not row.startswith("|") or is_separator(row):
                continue
            cells = row.removeprefix("| ").removesuffix(" |").split(" | ")
            if len(row.encode()) > LONG_CELL_BYTES or any(len(cell.encode()) > LONG_CELL_BYTES for cell in cells):
                fail(f"legacy table row/cell exceeds 2 KiB: {page.relative_to(ROOT)}:{number}")
        if "[Interim catalogue]" not in body or " · [Catalogue]" not in body:
            fail(f"missing breadcrumb or previous/next navigation: {page.relative_to(ROOT)}")
    if expected_rows != actual_rows:
        first = next((i for i, pair in enumerate(zip(expected_rows, actual_rows)) if pair[0] != pair[1]), None)
        fail(f"legacy catalogue row order/content differs: expected={len(expected_rows)}, actual={len(actual_rows)}, first_difference={first}")
    for source_line, anchor in CHAPTER_ROW_ANCHORS.items():
        rows = chapter_anchor_rows[source_line]
        if len(rows) != 1:
            fail(f"chapter anchor {anchor} is not attached exactly once to former row {source_line}")
        row = re.sub(r'<a id="tasaki-chapter-[^"]+"></a> ', "", rows[0])
        detail_ref = re.search(r"<!-- legacy-detail-ref:(\d+) -->", row)
        reconstructed = expected_by_line[int(detail_ref.group(1))] if detail_ref else row
        if reconstructed != expected_by_line[source_line]:
            fail(f"chapter anchor {anchor} moved away from exact former row {source_line}")

    detail_records: dict[int, list[tuple[Path, str]]] = defaultdict(list)
    detail_lean: dict[int, list[str]] = defaultdict(list)
    detail_file: dict[int, list[str]] = defaultdict(list)
    for page in sorted((DOCS / "formalization" / "legacy" / "details").glob("*.md")):
        detail_text = page.read_text()
        for match in LEGACY_DETAIL.finditer(detail_text):
            detail_records[int(match.group(1))].append((page, match.group(2)))
        for match in LEGACY_DETAIL_LEAN.finditer(detail_text):
            detail_lean[int(match.group(1))].append(match.group(2))
        for match in LEGACY_DETAIL_FILE.finditer(detail_text):
            detail_file[int(match.group(1))].append(match.group(2))
    if set(detail_records) != expected_long_lines:
        fail(
            "long-record detail coverage differs: "
            f"missing={sorted(expected_long_lines-set(detail_records))}, "
            f"extra={sorted(set(detail_records)-expected_long_lines)}"
        )
    for line_number, entries in detail_records.items():
        if len(entries) != 1 or len(detail_lean[line_number]) != 1 or len(detail_file[line_number]) != 1:
            fail(f"former line {line_number} does not have exactly one statement/Lean-name/File detail record")
        expected_cells = expected_by_line[line_number].removeprefix("| ").removesuffix(" |").split(" | ")
        if not long_record_fidelity(
            expected_cells,
            compact_long_cells[line_number],
            detail_lean[line_number][0],
            detail_file[line_number][0],
            entries[0][1],
        ):
            fail(f"long-record whitespace-normalized exact parity differs at former line {line_number}")

    # Every source-derived non-table block is marked and preserves normalized content/order.
    markers: dict[tuple[int, int], list[tuple[Path, str]]] = defaultdict(list)
    for page in PAGES:
        for match in SOURCE_MARKER.finditer(page.read_text()):
            markers[(int(match.group(1)), int(match.group(2)))].append((page, match.group(3)))
    expected_marker_ranges = {(6, 71), (72, 109), (155, 216), (217, 228), (2732, 2779), (2780, 3037), (3038, 3051)}
    expected_marker_ranges.update((line, line) for line in range(114, 154))
    expected_marker_ranges.update((start, end) for start, end in markers if 229 <= start <= end <= 2731)
    if set(markers) != expected_marker_ranges:
        fail(f"source-marker coverage differs: missing={sorted(expected_marker_ranges-set(markers))}, extra={sorted(set(markers)-expected_marker_ranges)}")
    catalogue_ranges = sorted((start, end) for start, end in markers if 229 <= start <= end <= 2731)
    cursor = 229
    for start, end in catalogue_ranges:
        if start != cursor:
            fail(f"catalogue source-marker gap/overlap before old line {start}; expected {cursor}")
        cursor = end + 1
    if cursor != 2732:
        fail(f"catalogue source-marker coverage ends at {cursor - 1}, expected 2731")
    expected_prose_stream: list[str] = []
    actual_prose_stream: list[str] = []
    rewrite_counts = [0] * len(MOVED_PROSE_LINK_REWRITES)
    for source_range in sorted(markers):
        start, end = source_range
        expected = "".join(old_lines[start - 1 : end])
        if 217 <= start <= 2731:
            # Catalogue tables have a stronger exact-row check; prose still participates here.
            expected = "\n".join(line for line in expected.splitlines() if not line.startswith("|"))
        if start == end and 114 <= start <= 153:
            cells = old_lines[start - 1].removeprefix("| ").removesuffix(" |\n").split(" | ", 2)
            phase, scope, status = (cells[0], "", cells[1]) if len(cells) == 2 else cells
            expected = f"{phase} {scope} {status}"
        current = "".join(text for _page, text in sorted(markers[source_range], key=lambda item: str(item[0])))
        if 217 <= start <= 2731:
            current = "\n".join(line for line in current.splitlines() if not line.startswith("|"))
        normalized_expected = whitespace_normalized(
            apply_moved_prose_link_rewrites(expected, rewrite_counts)
        )
        working_note_counts[2] += len(_WORKING_NOTE_PROSE_CITATION.findall(normalized_expected))
        expected_prose_stream.append(_drop_working_note_prose_citation(normalized_expected))
        actual_prose_stream.append(normalize_current_moved_prose(start, end, current, old_lines))
    if tuple(rewrite_counts) != MOVED_PROSE_LINK_REWRITE_COUNTS:
        fail(
            "audited moved-prose link rewrite counts differ: "
            f"expected={MOVED_PROSE_LINK_REWRITE_COUNTS}, actual={tuple(rewrite_counts)}"
        )
    if tuple(working_note_counts) != WORKING_NOTE_REMOVAL_COUNTS:
        fail(
            "audited working-note removal counts differ: "
            f"expected={WORKING_NOTE_REMOVAL_COUNTS}, actual={tuple(working_note_counts)}"
        )
    if expected_prose_stream != actual_prose_stream:
        first = next(
            (i for i, pair in enumerate(zip(expected_prose_stream, actual_prose_stream)) if pair[0] != pair[1]),
            None,
        )
        fail(
            "whitespace-normalized exact moved-prose parity differs: "
            f"segments={len(expected_prose_stream)}, first_difference={first}"
        )
    prose_chars = sum(len(item) for item in actual_prose_stream)
    prose_digest = hashlib.sha256("\0".join(actual_prose_stream).encode()).hexdigest()

    # Migration map must reproduce anchor, old line, verbatim heading, and a real destination.
    migration = (DOCS / "formalization" / "migration-map.md").read_text()
    map_pattern = re.compile(r"^\| `([^`]+)` \| `(\d+)` \| (.*?) \| `(docs/[^`]+)` \|$", re.MULTILINE)
    mapped = map_pattern.findall(migration)
    if len(mapped) != len(expected_headings):
        fail(f"migration map count differs: expected={len(expected_headings)}, actual={len(mapped)}")
    for ((line_number, heading), (fixture_line, fixture_anchor), (anchor, mapped_line, mapped_heading, destination)) in zip(expected_headings, FORMER_ROOT_IDS, mapped):
        if fixture_line != line_number or (anchor, int(mapped_line), html.unescape(mapped_heading)) != (fixture_anchor, line_number, heading):
            fail(f"migration map mismatch at old line {line_number}")
        if not (ROOT / destination).is_file():
            fail(f"migration destination does not exist: {destination}")
        owners = {
            str(page.relative_to(ROOT))
            for (start, end), entries in markers.items()
            if start <= line_number <= end
            for page, _text in entries
        }
        if owners and destination not in owners:
            fail(f"migration destination {destination} does not own old heading line {line_number}: {sorted(owners)}")

    # Source/topic leaf projections must navigate to the interim authority now.
    projection_pages = [
        page for page in PAGES
        if ("formalization/sources/" in str(page) or "formalization/topics/" in str(page))
        and page.name != "index.md"
        and page.name not in {"tasaki-2020.md", "other-literature.md"}
    ]
    source_links = topic_links = 0
    projected_routes: set[str] = set()
    for page in projection_pages:
        routes = re.findall(
            r"\]\(/lattice-system(/formalization/legacy/[^)#]+/)(?:#[^)]+)?\)",
            page.read_text(),
        )
        count = len(routes)
        if count == 0:
            fail(f"empty source/topic projection: {page.relative_to(ROOT)}")
        projected_routes.update(routes)
        if "/sources/" in str(page):
            source_links += count
        else:
            topic_links += count
    catalogue_routes = {
        front_matter(page)[0]["permalink"]
        for page in legacy_pages
        if page.name != "index.md"
    }
    if projected_routes != catalogue_routes:
        fail(
            "source/topic leaf coverage differs: "
            f"missing={sorted(catalogue_routes-projected_routes)}, "
            f"extra={sorted(projected_routes-catalogue_routes)}"
        )
    chapter_root = DOCS / "formalization" / "sources" / "tasaki-2020"
    expected_chapters = {f"chapter-{chapter:02d}.md" for chapter in range(2, 12)} | {"appendix-a.md"}
    actual_chapters = {page.name for page in chapter_root.glob("*.md")}
    if actual_chapters != expected_chapters:
        fail(f"Tasaki chapter coverage differs: missing={sorted(expected_chapters-actual_chapters)}, extra={sorted(actual_chapters-expected_chapters)}")
    for chapter_key, expected_targets in CHAPTER_EXPECTED_TARGETS.items():
        filename = "appendix-a.md" if chapter_key == "appendix-a" else f"chapter-{chapter_key:02d}.md"
        page = chapter_root / filename
        actual_targets = tuple(
            target
            for target in re.findall(r"\]\(/lattice-system([^)]*)\)", page.read_text())
            if target.startswith("/formalization/legacy/") and target != "/formalization/legacy/"
        )
        if actual_targets != expected_targets:
            fail(
                f"Tasaki {chapter_key} exact projection fixture differs: "
                f"expected={expected_targets}, actual={actual_targets}"
            )
        for target in expected_targets:
            route, fragment = target.split("#", 1)
            target_page = permalink_to_page.get(route)
            if target_page is None or fragment not in all_anchors.get(target_page, set()):
                fail(f"Tasaki {chapter_key} fixture target does not resolve exactly: {target}")
    if "PR pending" in "\n".join(page.read_text() for page in legacy_pages):
        fail("stale PR pending remains in interim legacy catalogue")

    stale_rules = {
        "docs/index.md theorem catalogue": "root landing page is no longer the theorem catalogue",
        "only `docs/index.md` references": "declaration references belong in the interim legacy catalogue",
        "docs/index.md` and this `deprecations.md`": "deprecation updates belong in the interim legacy catalogue",
        "lattice-system/#continuum-limit-roadmap": "continuum roadmap has its own route",
    }
    prose_sources = [*ALL_DOC_PAGES, ROOT / "README.md", ROOT / "AGENTS.md", *ROOT.rglob("*.lean")]
    for source in prose_sources:
        if any(part in {".lake", ".git"} for part in source.parts) or not source.is_file():
            continue
        text = source.read_text(errors="replace")
        for stale, reason in stale_rules.items():
            if stale in text:
                fail(f"forbidden stale authority prose in {source.relative_to(ROOT)} ({reason}): {stale}")

    for warning in warnings:
        print(f"WARNING: {warning}")
    print(
        "OK: docs hierarchy; "
        f"{len(PAGES)} pages, {len(permalink_to_page)} permalinks, "
        f"{len(expected_rows)} catalogue rows in exact order, "
        f"{len(expected_long_lines)} long records in whitespace-normalized exact parity, "
        f"{prose_chars} whitespace-normalized moved-prose characters sha256={prose_digest}, "
        f"{len(expected_headings)} exact migration entries/root stubs, "
        f"source/topic legacy links={source_links}/{topic_links}, "
        f"max={max_bytes[0]} bytes ({max_bytes[1].relative_to(ROOT)}), "
        f"{max_lines[0]} lines ({max_lines[1].relative_to(ROOT)}), "
        f"{max_rows[0]} rows ({max_rows[1].relative_to(ROOT)})"
    )


if __name__ == "__main__":
    main()
