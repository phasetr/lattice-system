---
layout: default
title: lattice-system
permalink: /
---

# Project overview

`lattice-system` is a Lean 4 and mathlib formalization of lattice models.
Its primary abstraction is a graph: finite lattices are graph instances, while
infinite graphs remain available for the thermodynamic and continuum limits.

## Browse the project

- [Formalization catalogue](/lattice-system/formalization/) — browse by source
  or topic and find the complete interim catalogue.
- [Formalization-status publication](/lattice-system/formalization-publication/)
  — stable human/machine paths, generation architecture, and reproduction.
- [Current roadmap](/lattice-system/roadmap/) — active direction and the
  authoritative tracking Issues.
- [Limitations and documented axioms](/lattice-system/limitations/) — current
  trust boundaries and deferred mathematical infrastructure.
- [Historical records](/lattice-system/history/) — cumulative implementation
  history and deleted proof routes.
- [Mathematical proof guide](https://github.com/phasetr/lattice-system/blob/main/tex/proof-guide.tex)
  — statements, motivation, and proof sketches.
- [Refactoring conventions](/lattice-system/refactoring-conventions/)

## Formalization-status authority during migration

The complete hand-maintained catalogue under
[`formalization/legacy/`](/lattice-system/formalization/legacy/) is the interim
authority for formalization status and capstone identification. The
[version 1 data contract](/lattice-system/formalization-status-contract/) and
its JSON catalogue are a **non-authoritative prototype**. Issue
[#5228](https://github.com/phasetr/lattice-system/issues/5228) alone performs
the structured-data cutover after full migration and audit. Do not combine the
prototype and legacy pages into competing ledgers.

## Present coverage

The present implementation covers finite-volume classical and quantum spin
systems, fermions and Hubbard-model infrastructure, and reusable finite
matrix-analysis foundations. Infinite-volume, thermodynamic-limit, and
continuum-limit work remains a central long-term goal rather than an excluded
topic. The limitations page explains the policy for documented axioms; complete
declaration-level axiom occurrences remain in the interim legacy catalogue
until #5228.

API documentation generation with doc-gen4 remains disabled because its former
CI job was prohibitively slow. Formalization-status publication is a separate
project tracked by [#5229](https://github.com/phasetr/lattice-system/issues/5229).

## Project resources

- [Source repository](https://github.com/phasetr/lattice-system)
- [mathlib](https://github.com/leanprover-community/mathlib4)
- [Lean](https://lean-lang.org/)


## Former index fragments

Every former section fragment remains an explicit landing-page stub. Each stub
links to the section's new purpose-specific home.

<a id="lattice-system"></a> [lattice-system](/lattice-system/history/legacy-landing-content/)

<a id="design-axis-graphs-not-lattices"></a> [Design axis: graphs, not lattices](/lattice-system/history/legacy-landing-content/)

<a id="scope"></a> [Scope](/lattice-system/history/legacy-landing-content/)

<a id="refactoring-conventions-and-review-criteria"></a> [Refactoring conventions and review criteria](/lattice-system/history/legacy-landing-content/)

<a id="deleted-routes-what-this-index-used-to-document"></a> [Deleted routes: what this index used to document](/lattice-system/history/deleted-routes/)

<a id="roadmap"></a> [Roadmap](/lattice-system/history/roadmap/)

<a id="appendix-a-status-and-axiomatization-policy"></a> [Appendix A: status and axiomatization policy](/lattice-system/limitations/documented-axioms/)

<a id="formalized-theorems"></a> [Formalized theorems](/lattice-system/formalization/legacy/)

<a id="single-site-pauli-operators"></a> [Single-site Pauli operators](/lattice-system/formalization/legacy/01-single-site-pauli-operators/)

<a id="spin-12-operators-tasaki-21"></a> [Spin-1/2 operators (Tasaki §2.1)](/lattice-system/formalization/legacy/02-spin-1-2-operators-tasaki-2-1/)

<a id="spin-12-rotation-operators-tasaki-21-eq-2126"></a> [Spin-1/2 rotation operators (Tasaki §2.1 eq. (2.1.26))](/lattice-system/formalization/legacy/03-spin-1-2-rotation-operators-tasaki-2-1-eq-2-1-26/)

<a id="d-rotation-matrices-r-general--tasaki-21-eq-2111"></a> [3D rotation matrices `R^(α)_θ` (general θ, Tasaki §2.1 eq. (2.1.11))](/lattice-system/formalization/legacy/04-3d-rotation-matrices-general-tasaki-2-1-eq-2-1-11/)

<a id="z--z-representation-tasaki-21-eqs-2127-2134"></a> [Z₂ × Z₂ representation (Tasaki §2.1 eqs. (2.1.27)-(2.1.34))](/lattice-system/formalization/legacy/05-z-z-representation-tasaki-2-1-eqs-2-1-27-2-1-34/)

<a id="d-rotation-matrices-r-tasaki-21-eq-2128"></a> [3D rotation matrices `R^(α)_π` (Tasaki §2.1 eq. (2.1.28))](/lattice-system/formalization/legacy/06-3d-rotation-matrices-tasaki-2-1-eq-2-1-28/)

<a id="pauli-basis-decomposition-tasaki-21-problem-21a-s--12"></a> [Pauli-basis decomposition (Tasaki §2.1 Problem 2.1.a, S = 1/2)](/lattice-system/formalization/legacy/07-pauli-basis-decomposition-tasaki-2-1-problem-2-1-a-s-1-2/)

<a id="polynomial-basis-decomposition-for-s--1-tasaki-21-problem-21a-s--1"></a> [Polynomial-basis decomposition for S = 1 (Tasaki §2.1 Problem 2.1.a, S = 1)](/lattice-system/formalization/legacy/08-polynomial-basis-decomposition-for-s-1-tasaki-2-1-problem-/)

<a id="s--1-matrix-representations-tasaki-21-eq-219"></a> [S = 1 matrix representations (Tasaki §2.1 eq. (2.1.9))](/lattice-system/formalization/legacy/09-s-1-matrix-representations-tasaki-2-1-eq-2-1-9/)

<a id="spin-s-operators-general-s--0-parameterised-by-n--2s--"></a> [Spin-`S` operators (general S ≥ 0, parameterised by `N = 2S : ℕ`)](/lattice-system/formalization/legacy/10-spin-operators-general-s-0-parameterised-by/)

<a id="basis-states-and-raisinglowering-tasaki-21"></a> [Basis states and raising/lowering (Tasaki §2.1)](/lattice-system/formalization/legacy/11-basis-states-and-raising-lowering-tasaki-2-1/)

<a id="basis-states-and-raisinglowering-for-s--1-tasaki-21"></a> [Basis states and raising/lowering for S = 1 (Tasaki §2.1)](/lattice-system/formalization/legacy/12-basis-states-and-raising-lowering-for-s-1-tasaki-2-1/)

<a id="time-reversal-map-for-s--12-tasaki-23"></a> [Time-reversal map for `S = 1/2` (Tasaki §2.3)](/lattice-system/formalization/legacy/13-time-reversal-map-for-tasaki-2-3/)

<a id="multi-body-operator-space-abstract-lattice"></a> [Multi-body operator space (abstract lattice)](/lattice-system/formalization/legacy/14-multi-body-operator-space-abstract-lattice/)

<a id="generic-matrix-analysis-helpers-mathmatrixanalysis"></a> [Generic matrix-analysis helpers (`Math/MatrixAnalysis/`)](/lattice-system/formalization/legacy/15-generic-matrix-analysis-helpers/)

<a id="horschvon-der-linden-low-lying-states-tasaki-34-theorem-31"></a> [Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1)](/lattice-system/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-01/)

<a id="boseeinstein-condensation-of-hard-core-bosons-tasaki-5152"></a> [Bose–Einstein condensation of hard-core bosons (Tasaki §5.1–§5.2)](/lattice-system/formalization/legacy/17-bose-einstein-condensation-of-hard-core-bosons-tasaki-5-1-/)

<a id="antiferromagnetic-heisenberg-chains-and-the-haldane-conjecture-tasaki-61"></a> [Antiferromagnetic Heisenberg chains and the Haldane conjecture (Tasaki §6.1)](/lattice-system/formalization/legacy/18-antiferromagnetic-heisenberg-chains-and-the-haldane-conjec/)

<a id="the-aklt-model-tasaki-71"></a> [The AKLT model (Tasaki §7.1)](/lattice-system/formalization/legacy/19-the-aklt-model-tasaki-7-1/)

<a id="total-spin-operator-tasaki-22-eq-227-228"></a> [Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8))](/lattice-system/formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-01/)

<a id="two-site-spin-inner-product-tasaki-22-eq-2216"></a> [Two-site spin inner product (Tasaki §2.2 eq. (2.2.16))](/lattice-system/formalization/legacy/21-two-site-spin-inner-product-tasaki-2-2-eq-2-2-16/)

<a id="one-dimensional-open-chain-quantum-ising"></a> [One-dimensional open-chain quantum Ising](/lattice-system/formalization/legacy/22-one-dimensional-open-chain-quantum-ising/)

<a id="testing-infrastructure"></a> [Testing infrastructure](/lattice-system/formalization/legacy/23-testing-infrastructure/)

<a id="gibbs-state-tasaki-33"></a> [Gibbs state (Tasaki §3.3)](/lattice-system/formalization/legacy/24-gibbs-state-tasaki-3-3/)

<a id="heisenberg-chain-tasaki-35"></a> [Heisenberg chain (Tasaki §3.5)](/lattice-system/formalization/legacy/25-heisenberg-chain-tasaki-3-5-part-01/)

<a id="perron-frobenius-theorem-mathperronfrobeniuslean-mathperronfrobeniusprimitivelean-mathcollatzwielandtlean-mathperronfrobeniusmainlean"></a> [Perron-Frobenius theorem (`Math/PerronFrobenius.lean`, `Math/PerronFrobeniusPrimitive.lean`, `Math/CollatzWielandt.lean`, `Math/PerronFrobeniusMain.lean`)](/lattice-system/formalization/legacy/26-perron-frobenius-theorem/)

<a id="spin-s-marshallliebmattis-on-the-magnetization-sector-tasaki-25-theorem-22-generic-s-sector-form"></a> [Spin-`S` Marshall–Lieb–Mattis on the magnetization sector (Tasaki §2.5 Theorem 2.2 generic S, sector form)](/lattice-system/formalization/legacy/27-spin-marshall-lieb-mattis-on-the-magnetization-sector-tasa-part-01/)

<a id="spin-s-saturated-ferromagnetic-state-tasaki-24-generalised"></a> [Spin-`S` saturated ferromagnetic state (Tasaki §2.4 generalised)](/lattice-system/formalization/legacy/28-spin-saturated-ferromagnetic-state-tasaki-2-4-generalised-part-01/)

<a id="single-mode-fermion-p2-skeleton"></a> [Single-mode fermion (P2 skeleton)](/lattice-system/formalization/legacy/29-single-mode-fermion-p2-skeleton/)

<a id="multi-mode-fermion-via-jordanwigner-p2-backbone"></a> [Multi-mode fermion via Jordan–Wigner (P2 backbone)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-01/)

<a id="fock-space-representation-and-slater-determinants-tasaki-923"></a> [Fock space representation and Slater determinants (Tasaki §9.2.3)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02/)

<a id="hubbard-spin-symmetry--full-su2-invariance-tasaki-933"></a> [Hubbard spin symmetry — full SU(2) invariance (Tasaki §9.3.3)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02/)

<a id="hubbard-all-up-spin-state-and-saturated-ferromagnetism-tasaki-1111"></a> [Hubbard all-up-spin state and saturated ferromagnetism (Tasaki §11.1.1)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02/)

<a id="hubbard-hard-core-subspace-tasaki-112"></a> [Hubbard hard-core subspace (Tasaki §11.2)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02/)

<a id="hubbard-hard-core-projection-tasaki-112"></a> [Hubbard hard-core projection (Tasaki §11.2)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02/)

<a id="hubbard-one-hole-hard-core-basis-states-tasaki-112"></a> [Hubbard one-hole hard-core basis states (Tasaki §11.2)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02/)

<a id="jordanwigner-string-action-on-basis-states-tasaki-112-infrastructure"></a> [Jordan–Wigner string action on basis states (Tasaki §11.2 infrastructure)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02/)

<a id="span-of-the-one-hole-hard-core-sector-tasaki-112-footnote-8"></a> [Span of the one-hole hard-core sector (Tasaki §11.2, footnote 8)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02/)

<a id="hole-filling-hop-configuration-tasaki-112-eq-1124-spatial-content"></a> [Hole-filling hop configuration (Tasaki §11.2, eq. (11.2.4) spatial content)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03/)

<a id="degenerate-perturbation-theory-second-order-effective-hamiltonian-tasaki-101-lemma-101"></a> [Degenerate perturbation theory: second-order effective Hamiltonian (Tasaki §10.1, Lemma 10.1)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03/)

<a id="liebs-theorem-for-the-attractive-hubbard-model-tasaki-1021-theorems-102--103"></a> [Lieb's theorem for the attractive Hubbard model (Tasaki §10.2.1, Theorems 10.2 & 10.3)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03/)

<a id="spin-reflection-positivity-foundation-for-liebs-theorem-tasaki-1021-pr1-toward-discharging-theorem-102"></a> [Spin-reflection-positivity foundation for Lieb's theorem (Tasaki §10.2.1, PR1 toward discharging Theorem 10.2)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03/)

<a id="liebs-theorem-for-the-repulsive-hubbard-model-at-half-filling-tasaki-1022-theorem-104"></a> [Lieb's theorem for the repulsive Hubbard model at half-filling (Tasaki §10.2.2, Theorem 10.4)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03/)

<a id="kubokishi-finite-temperature-susceptibility-bound-tasaki-1025-theorem-1011-axiom"></a> [Kubo–Kishi finite-temperature susceptibility bound (Tasaki §10.2.5, Theorem 10.11, AXIOM)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/)

<a id="hubbard-effective-hamiltonian-on-the-hard-core-sector-tasaki-112"></a> [Hubbard effective Hamiltonian on the hard-core sector (Tasaki §11.2)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/)

<a id="tasaki-ordered-creation-basis-tasaki-112-eq-1123"></a> [Tasaki ordered-creation basis (Tasaki §11.2, eq. (11.2.3))](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/)

<a id="uniform-sign-hole-filling-action-tasaki-112-eq-1124"></a> [Uniform-sign hole-filling action (Tasaki §11.2, eq. (11.2.4))](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/)

<a id="effective-hamiltonian-matrix-element-tasaki-112-eq-1125"></a> [Effective-Hamiltonian matrix element (Tasaki §11.2, eq. (11.2.5))](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/)

<a id="cauchyschwarz-energy-bound-tasaki-112-eq-1129"></a> [Cauchy–Schwarz energy bound (Tasaki §11.2, eq. (11.2.9))](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/)

<a id="su2-symmetry-of-the-effective-hamiltonian-tasaki-112"></a> [SU(2) symmetry of the effective Hamiltonian (Tasaki §11.2)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/)

<a id="weak-nagaoka-spin-multiplet-tasaki-1121-theorem-115-core"></a> [Weak Nagaoka spin multiplet (Tasaki §11.2.1, Theorem 11.5 core)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/)

<a id="nagaokas-theorem-on-a-magnetization-sector-tasaki-1122-theorem-117--lemma-119"></a> [Nagaoka's theorem on a magnetization sector (Tasaki §11.2.2, Theorem 11.7 / Lemma 11.9)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/)

<a id="general-flat-band-ground-states-the-annihilation-peel-behind-eq-11346-tasaki-1134"></a> [General flat-band ground states: the annihilation peel behind eq. (11.3.46) (Tasaki §11.3.4)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/)

<a id="continuum-limit-roadmap"></a> [Continuum-limit roadmap](/lattice-system/continuum-limit-roadmap/)

<a id="open-items--axioms"></a> [Open items / axioms](/lattice-system/history/open-items/)

<a id="todo-p1d--problem-21a-for-general-s--1-done"></a> [~~TODO (P1d''') — Problem 2.1.a for general `S ≥ 1`~~ **DONE**](/lattice-system/history/open-items/)

<a id="todo--tasaki-problem-22c-su2-non-invariance--averaged-state-done"></a> [~~TODO — Tasaki Problem 2.2.c (SU(2) non-invariance / averaged state)~~ **DONE**](/lattice-system/history/open-items/)

<a id="tasaki-25-antiferromagnetic-status-issues-240-412"></a> [Tasaki §2.5 antiferromagnetic status (issues #240, #412)](/lattice-system/history/open-items/)

<a id="todo--remove-remaining-7-per-theorem-linter-suppressions-issue-377"></a> [TODO — remove remaining 7 per-theorem linter suppressions (issue #377)](/lattice-system/history/open-items/)

<a id="links"></a> [Links](/lattice-system/history/project-links/)
