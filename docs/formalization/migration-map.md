---
layout: page
title: "docs/index.md migration map"
permalink: /formalization/migration-map/
---

# `docs/index.md` migration map

This map accounts for every former level-2 through level-4 section block in
`main:docs/index.md` at commit `6519099024bf156b87ac0c807c6633c513792581`.
The move preserved source order and did not infer or reclassify mixed-source
headings.

## Split policy

- A normal page should remain at or below 64 KiB, 500 lines, and 100 catalogue
  data rows. Exceeding one is a review warning.
- A page must remain at or below 128 KiB and 1,000 lines. Any unavoidable
  legacy exception must be named in the checker with a written reason.
- Large tables split deterministically before 96 data rows or 120,000 bytes,
  whichever comes first. Continued chunks repeat only the table header and
  separator for readability; these are not catalogue data rows.
- A legacy table row and each of its cells must remain at or below 2 KiB.
  Longer authoritative statement/chronicle cells move to grouped detail pages;
  the original table position retains one compact reference, and the checker
  reconstructs and compares the original ordered record. Lean-name and File
  cells remain byte-for-byte equal to the baseline; statement/detail parity
  normalizes whitespace only, preserving every punctuation mark, operator,
  Markdown delimiter, Unicode character, and their exact order.
- All 68 former level-2 through level-4 root anchors remain explicit stubs on
  the landing page and link to their new homes. The table below is the fixed
  compatibility fixture. Its IDs use Kramdown `basic_generate_id`: strip
  inline markup, remove the leading run before the first ASCII letter, remove
  characters other than ASCII letters, digits, spaces, and hyphens, replace
  spaces with hyphens, and lowercase.
- The complete interim authority is the legacy catalogue tree, not the landing
  page and not the prototype JSON. Issue #5228 owns the only authority cutover.

## Section destinations

| Former anchor | Former line | Verbatim heading | Destination |
|---|---:|---|---|
| `lattice-system` | `6` | lattice-system | `docs/history/legacy-landing-content.md` |
| `design-axis-graphs-not-lattices` | `14` | Design axis: graphs, not lattices | `docs/history/legacy-landing-content.md` |
| `scope` | `42` | Scope | `docs/history/legacy-landing-content.md` |
| `refactoring-conventions-and-review-criteria` | `53` | Refactoring conventions and review criteria | `docs/history/legacy-landing-content.md` |
| `deleted-routes-what-this-index-used-to-document` | `72` | Deleted routes: what this index used to document | `docs/history/deleted-routes.md` |
| `roadmap` | `110` | Roadmap | `docs/history/roadmap.md` |
| `appendix-a-status-and-axiomatization-policy` | `155` | Appendix A: status and axiomatization policy | `docs/limitations/documented-axioms.md` |
| `formalized-theorems` | `217` | Formalized theorems | `docs/formalization/legacy/index.md` |
| `single-site-pauli-operators` | `229` | Single-site Pauli operators | `docs/formalization/legacy/01-single-site-pauli-operators.md` |
| `spin-12-operators-tasaki-21` | `244` | Spin-1/2 operators (Tasaki §2.1) | `docs/formalization/legacy/02-spin-1-2-operators-tasaki-2-1.md` |
| `spin-12-rotation-operators-tasaki-21-eq-2126` | `259` | Spin-1/2 rotation operators (Tasaki §2.1 eq. (2.1.26)) | `docs/formalization/legacy/03-spin-1-2-rotation-operators-tasaki-2-1-eq-2-1-26.md` |
| `d-rotation-matrices-r-general--tasaki-21-eq-2111` | `297` | 3D rotation matrices `R^(α)_θ` (general θ, Tasaki §2.1 eq. (2.1.11)) | `docs/formalization/legacy/04-3d-rotation-matrices-general-tasaki-2-1-eq-2-1-11.md` |
| `z--z-representation-tasaki-21-eqs-2127-2134` | `305` | Z₂ × Z₂ representation (Tasaki §2.1 eqs. (2.1.27)-(2.1.34)) | `docs/formalization/legacy/05-z-z-representation-tasaki-2-1-eqs-2-1-27-2-1-34.md` |
| `d-rotation-matrices-r-tasaki-21-eq-2128` | `313` | 3D rotation matrices `R^(α)_π` (Tasaki §2.1 eq. (2.1.28)) | `docs/formalization/legacy/06-3d-rotation-matrices-tasaki-2-1-eq-2-1-28.md` |
| `pauli-basis-decomposition-tasaki-21-problem-21a-s--12` | `325` | Pauli-basis decomposition (Tasaki §2.1 Problem 2.1.a, S = 1/2) | `docs/formalization/legacy/07-pauli-basis-decomposition-tasaki-2-1-problem-2-1-a-s-1-2.md` |
| `polynomial-basis-decomposition-for-s--1-tasaki-21-problem-21a-s--1` | `337` | Polynomial-basis decomposition for S = 1 (Tasaki §2.1 Problem 2.1.a, S = 1) | `docs/formalization/legacy/08-polynomial-basis-decomposition-for-s-1-tasaki-2-1-problem-.md` |
| `s--1-matrix-representations-tasaki-21-eq-219` | `353` | S = 1 matrix representations (Tasaki §2.1 eq. (2.1.9)) | `docs/formalization/legacy/09-s-1-matrix-representations-tasaki-2-1-eq-2-1-9.md` |
| `spin-s-operators-general-s--0-parameterised-by-n--2s--` | `365` | Spin-`S` operators (general S ≥ 0, parameterised by `N = 2S : ℕ`) | `docs/formalization/legacy/10-spin-operators-general-s-0-parameterised-by.md` |
| `basis-states-and-raisinglowering-tasaki-21` | `410` | Basis states and raising/lowering (Tasaki §2.1) | `docs/formalization/legacy/11-basis-states-and-raising-lowering-tasaki-2-1.md` |
| `basis-states-and-raisinglowering-for-s--1-tasaki-21` | `425` | Basis states and raising/lowering for S = 1 (Tasaki §2.1) | `docs/formalization/legacy/12-basis-states-and-raising-lowering-for-s-1-tasaki-2-1.md` |
| `time-reversal-map-for-s--12-tasaki-23` | `467` | Time-reversal map for `S = 1/2` (Tasaki §2.3) | `docs/formalization/legacy/13-time-reversal-map-for-tasaki-2-3.md` |
| `multi-body-operator-space-abstract-lattice` | `506` | Multi-body operator space (abstract lattice) | `docs/formalization/legacy/14-multi-body-operator-space-abstract-lattice.md` |
| `generic-matrix-analysis-helpers-mathmatrixanalysis` | `525` | Generic matrix-analysis helpers (`Math/MatrixAnalysis/`) | `docs/formalization/legacy/15-generic-matrix-analysis-helpers.md` |
| `horschvon-der-linden-low-lying-states-tasaki-34-theorem-31` | `549` | Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1) | `docs/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-01.md` |
| `boseeinstein-condensation-of-hard-core-bosons-tasaki-5152` | `730` | Bose–Einstein condensation of hard-core bosons (Tasaki §5.1–§5.2) | `docs/formalization/legacy/17-bose-einstein-condensation-of-hard-core-bosons-tasaki-5-1-.md` |
| `antiferromagnetic-heisenberg-chains-and-the-haldane-conjecture-tasaki-61` | `739` | Antiferromagnetic Heisenberg chains and the Haldane conjecture (Tasaki §6.1) | `docs/formalization/legacy/18-antiferromagnetic-heisenberg-chains-and-the-haldane-conjec.md` |
| `the-aklt-model-tasaki-71` | `752` | The AKLT model (Tasaki §7.1) | `docs/formalization/legacy/19-the-aklt-model-tasaki-7-1.md` |
| `total-spin-operator-tasaki-22-eq-227-228` | `784` | Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8)) | `docs/formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-01.md` |
| `two-site-spin-inner-product-tasaki-22-eq-2216` | `1256` | Two-site spin inner product (Tasaki §2.2 eq. (2.2.16)) | `docs/formalization/legacy/21-two-site-spin-inner-product-tasaki-2-2-eq-2-2-16.md` |
| `one-dimensional-open-chain-quantum-ising` | `1301` | One-dimensional open-chain quantum Ising | `docs/formalization/legacy/22-one-dimensional-open-chain-quantum-ising.md` |
| `testing-infrastructure` | `1325` | Testing infrastructure | `docs/formalization/legacy/23-testing-infrastructure.md` |
| `gibbs-state-tasaki-33` | `1349` | Gibbs state (Tasaki §3.3) | `docs/formalization/legacy/24-gibbs-state-tasaki-3-3.md` |
| `heisenberg-chain-tasaki-35` | `1444` | Heisenberg chain (Tasaki §3.5) | `docs/formalization/legacy/25-heisenberg-chain-tasaki-3-5-part-01.md` |
| `perron-frobenius-theorem-mathperronfrobeniuslean-mathperronfrobeniusprimitivelean-mathcollatzwielandtlean-mathperronfrobeniusmainlean` | `1562` | Perron-Frobenius theorem (`Math/PerronFrobenius.lean`, `Math/PerronFrobeniusPrimitive.lean`, `Math/CollatzWielandt.lean`, `Math/PerronFrobeniusMain.lean`) | `docs/formalization/legacy/26-perron-frobenius-theorem.md` |
| `spin-s-marshallliebmattis-on-the-magnetization-sector-tasaki-25-theorem-22-generic-s-sector-form` | `1588` | Spin-`S` Marshall–Lieb–Mattis on the magnetization sector (Tasaki §2.5 Theorem 2.2 generic S, sector form) | `docs/formalization/legacy/27-spin-marshall-lieb-mattis-on-the-magnetization-sector-tasa-part-01.md` |
| `spin-s-saturated-ferromagnetic-state-tasaki-24-generalised` | `2017` | Spin-`S` saturated ferromagnetic state (Tasaki §2.4 generalised) | `docs/formalization/legacy/28-spin-saturated-ferromagnetic-state-tasaki-2-4-generalised-part-01.md` |
| `single-mode-fermion-p2-skeleton` | `2149` | Single-mode fermion (P2 skeleton) | `docs/formalization/legacy/29-single-mode-fermion-p2-skeleton.md` |
| `multi-mode-fermion-via-jordanwigner-p2-backbone` | `2246` | Multi-mode fermion via Jordan–Wigner (P2 backbone) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-01.md` |
| `fock-space-representation-and-slater-determinants-tasaki-923` | `2364` | Fock space representation and Slater determinants (Tasaki §9.2.3) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02.md` |
| `hubbard-spin-symmetry--full-su2-invariance-tasaki-933` | `2379` | Hubbard spin symmetry — full SU(2) invariance (Tasaki §9.3.3) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02.md` |
| `hubbard-all-up-spin-state-and-saturated-ferromagnetism-tasaki-1111` | `2400` | Hubbard all-up-spin state and saturated ferromagnetism (Tasaki §11.1.1) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02.md` |
| `hubbard-hard-core-subspace-tasaki-112` | `2425` | Hubbard hard-core subspace (Tasaki §11.2) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02.md` |
| `hubbard-hard-core-projection-tasaki-112` | `2435` | Hubbard hard-core projection (Tasaki §11.2) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02.md` |
| `hubbard-one-hole-hard-core-basis-states-tasaki-112` | `2452` | Hubbard one-hole hard-core basis states (Tasaki §11.2) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02.md` |
| `jordanwigner-string-action-on-basis-states-tasaki-112-infrastructure` | `2464` | Jordan–Wigner string action on basis states (Tasaki §11.2 infrastructure) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02.md` |
| `span-of-the-one-hole-hard-core-sector-tasaki-112-footnote-8` | `2476` | Span of the one-hole hard-core sector (Tasaki §11.2, footnote 8) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02.md` |
| `hole-filling-hop-configuration-tasaki-112-eq-1124-spatial-content` | `2487` | Hole-filling hop configuration (Tasaki §11.2, eq. (11.2.4) spatial content) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03.md` |
| `degenerate-perturbation-theory-second-order-effective-hamiltonian-tasaki-101-lemma-101` | `2496` | Degenerate perturbation theory: second-order effective Hamiltonian (Tasaki §10.1, Lemma 10.1) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03.md` |
| `liebs-theorem-for-the-attractive-hubbard-model-tasaki-1021-theorems-102--103` | `2505` | Lieb's theorem for the attractive Hubbard model (Tasaki §10.2.1, Theorems 10.2 & 10.3) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03.md` |
| `spin-reflection-positivity-foundation-for-liebs-theorem-tasaki-1021-pr1-toward-discharging-theorem-102` | `2514` | Spin-reflection-positivity foundation for Lieb's theorem (Tasaki §10.2.1, PR1 toward discharging Theorem 10.2) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03.md` |
| `liebs-theorem-for-the-repulsive-hubbard-model-at-half-filling-tasaki-1022-theorem-104` | `2598` | Lieb's theorem for the repulsive Hubbard model at half-filling (Tasaki §10.2.2, Theorem 10.4) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03.md` |
| `kubokishi-finite-temperature-susceptibility-bound-tasaki-1025-theorem-1011-axiom` | `2619` | Kubo–Kishi finite-temperature susceptibility bound (Tasaki §10.2.5, Theorem 10.11, AXIOM) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04.md` |
| `hubbard-effective-hamiltonian-on-the-hard-core-sector-tasaki-112` | `2629` | Hubbard effective Hamiltonian on the hard-core sector (Tasaki §11.2) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04.md` |
| `tasaki-ordered-creation-basis-tasaki-112-eq-1123` | `2639` | Tasaki ordered-creation basis (Tasaki §11.2, eq. (11.2.3)) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04.md` |
| `uniform-sign-hole-filling-action-tasaki-112-eq-1124` | `2651` | Uniform-sign hole-filling action (Tasaki §11.2, eq. (11.2.4)) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04.md` |
| `effective-hamiltonian-matrix-element-tasaki-112-eq-1125` | `2661` | Effective-Hamiltonian matrix element (Tasaki §11.2, eq. (11.2.5)) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04.md` |
| `cauchyschwarz-energy-bound-tasaki-112-eq-1129` | `2668` | Cauchy–Schwarz energy bound (Tasaki §11.2, eq. (11.2.9)) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04.md` |
| `su2-symmetry-of-the-effective-hamiltonian-tasaki-112` | `2681` | SU(2) symmetry of the effective Hamiltonian (Tasaki §11.2) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04.md` |
| `weak-nagaoka-spin-multiplet-tasaki-1121-theorem-115-core` | `2689` | Weak Nagaoka spin multiplet (Tasaki §11.2.1, Theorem 11.5 core) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04.md` |
| `nagaokas-theorem-on-a-magnetization-sector-tasaki-1122-theorem-117--lemma-119` | `2718` | Nagaoka's theorem on a magnetization sector (Tasaki §11.2.2, Theorem 11.7 / Lemma 11.9) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04.md` |
| `general-flat-band-ground-states-the-annihilation-peel-behind-eq-11346-tasaki-1134` | `2725` | General flat-band ground states: the annihilation peel behind eq. (11.3.46) (Tasaki §11.3.4) | `docs/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04.md` |
| `continuum-limit-roadmap` | `2732` | Continuum-limit roadmap | `docs/roadmap/continuum-limit.md` |
| `open-items--axioms` | `2780` | Open items / axioms | `docs/history/open-items.md` |
| `todo-p1d--problem-21a-for-general-s--1-done` | `2786` | ~~TODO (P1d''') — Problem 2.1.a for general `S ≥ 1`~~ **DONE** | `docs/history/open-items.md` |
| `todo--tasaki-problem-22c-su2-non-invariance--averaged-state-done` | `2808` | ~~TODO — Tasaki Problem 2.2.c (SU(2) non-invariance / averaged state)~~ **DONE** | `docs/history/open-items.md` |
| `tasaki-25-antiferromagnetic-status-issues-240-412` | `2828` | Tasaki §2.5 antiferromagnetic status (issues [#240](https://github.com/phasetr/lattice-system/issues/240), [#412](https://github.com/phasetr/lattice-system/issues/412)) | `docs/history/open-items.md` |
| `todo--remove-remaining-7-per-theorem-linter-suppressions-issue-377` | `3028` | TODO — remove remaining 7 per-theorem linter suppressions (issue [#377](https://github.com/phasetr/lattice-system/issues/377)) | `docs/history/open-items.md` |
| `links` | `3038` | Links | `docs/history/project-links.md` |
