#!/usr/bin/env python3
"""Validate the staged human-documentation hierarchy with the Python stdlib."""

from __future__ import annotations

import hashlib
import html
import posixpath
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
BASELINE_COMMIT = "6519099024bf156b87ac0c807c6633c513792581"
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
        "/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-01/#legacy-catalogue-horschvon-der-linden-low-lying-states-tasaki-34-theorem-31-part-1-of-2",
        "/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-02/#legacy-catalogue-horschvon-der-linden-low-lying-states-tasaki-34-theorem-31-part-2-of-2",
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
    ),
    11: (
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02/#tasaki-chapter-11-part-01",
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03/#tasaki-chapter-11-part-02",
        "/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/#tasaki-chapter-11-part-03",
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


def approved_changes(text: str) -> str:
    return (
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
    """Invert only documented presentation wrappers and two governance corrections."""
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
    return whitespace_normalized(current)


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


def main() -> None:
    long_record_negative_self_tests()
    moved_prose_negative_self_tests()
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
    expected_rows = table_data_rows(approved_changes("".join(old_lines[216:2731])).splitlines())
    expected_by_line: dict[int, str] = {}
    expected_long_lines: set[int] = set()
    for line_number in range(217, 2732):
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
        expected_prose_stream.append(
            whitespace_normalized(apply_moved_prose_link_rewrites(expected, rewrite_counts))
        )
        actual_prose_stream.append(normalize_current_moved_prose(start, end, current, old_lines))
    if tuple(rewrite_counts) != MOVED_PROSE_LINK_REWRITE_COUNTS:
        fail(
            "audited moved-prose link rewrite counts differ: "
            f"expected={MOVED_PROSE_LINK_REWRITE_COUNTS}, actual={tuple(rewrite_counts)}"
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
