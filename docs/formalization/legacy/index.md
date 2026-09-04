---
layout: page
title: "Complete interim formalization catalogue"
permalink: /formalization/legacy/
---

# Complete interim formalization catalogue

> **Interim authority.** These pages are a lossless partition of the former
> `docs/index.md` theorem catalogue. They remain authoritative for
> formalization status and capstone identification until Issue #5228 performs
> the audited structured-data cutover. The version 2 JSON records are still a
> non-authoritative prototype.

The partition is source-neutral where the old heading mixed Tasaki results,
external references, and project-original infrastructure. No item was
reclassified during this mechanical move. Each original catalogue data row
occurs in exactly one chunk; repeated table headers are presentation only.

<!-- legacy-source:start:217:228 -->
## Formalized theorems

The catalogue below includes proved results, conditional results, and documented axioms as recorded, with **zero `sorry`**. Full
mathematical statements and proof sketches are in
[`tex/proof-guide.tex`](https://github.com/phasetr/lattice-system/blob/main/tex/proof-guide.tex).

The [formalization-status data contract](/lattice-system/formalization-status-contract/) and
its representative version 1 catalogue are available for review. The catalogue
is a non-authoritative prototype until the governance cutover tracked by issue
[#5228](https://github.com/phasetr/lattice-system/issues/5228); this page remains
the current formalization-status and capstone authority during migration.

<!-- legacy-source:end:217:228 -->

## Catalogue groups

<a id="group-spin-foundations"></a>
### Spin foundations and Tasaki Chapter 2

- [Single-site Pauli operators](/lattice-system/formalization/legacy/01-single-site-pauli-operators/)
- [Spin-1/2 operators (Tasaki §2.1)](/lattice-system/formalization/legacy/02-spin-1-2-operators-tasaki-2-1/)
- [Spin-1/2 rotation operators (Tasaki §2.1 eq. (2.1.26))](/lattice-system/formalization/legacy/03-spin-1-2-rotation-operators-tasaki-2-1-eq-2-1-26/)
- [3D rotation matrices `R^(α)_θ` (general θ, Tasaki §2.1 eq. (2.1.11))](/lattice-system/formalization/legacy/04-3d-rotation-matrices-general-tasaki-2-1-eq-2-1-11/)
- [Z₂ × Z₂ representation (Tasaki §2.1 eqs. (2.1.27)-(2.1.34))](/lattice-system/formalization/legacy/05-z-z-representation-tasaki-2-1-eqs-2-1-27-2-1-34/)
- [3D rotation matrices `R^(α)_π` (Tasaki §2.1 eq. (2.1.28))](/lattice-system/formalization/legacy/06-3d-rotation-matrices-tasaki-2-1-eq-2-1-28/)
- [Pauli-basis decomposition (Tasaki §2.1 Problem 2.1.a, S = 1/2)](/lattice-system/formalization/legacy/07-pauli-basis-decomposition-tasaki-2-1-problem-2-1-a-s-1-2/)
- [Polynomial-basis decomposition for S = 1 (Tasaki §2.1 Problem 2.1.a, S = 1)](/lattice-system/formalization/legacy/08-polynomial-basis-decomposition-for-s-1-tasaki-2-1-problem-/)
- [S = 1 matrix representations (Tasaki §2.1 eq. (2.1.9))](/lattice-system/formalization/legacy/09-s-1-matrix-representations-tasaki-2-1-eq-2-1-9/)
- [Spin-`S` operators (general S ≥ 0, parameterised by `N = 2S : ℕ`)](/lattice-system/formalization/legacy/10-spin-operators-general-s-0-parameterised-by/)
- [Basis states and raising/lowering (Tasaki §2.1)](/lattice-system/formalization/legacy/11-basis-states-and-raising-lowering-tasaki-2-1/)
- [Basis states and raising/lowering for S = 1 (Tasaki §2.1)](/lattice-system/formalization/legacy/12-basis-states-and-raising-lowering-for-s-1-tasaki-2-1/)
- [Time-reversal map for `S = 1/2` (Tasaki §2.3)](/lattice-system/formalization/legacy/13-time-reversal-map-for-tasaki-2-3/)
- [Multi-body operator space (abstract lattice)](/lattice-system/formalization/legacy/14-multi-body-operator-space-abstract-lattice/)
- [Generic matrix-analysis helpers (`Math/MatrixAnalysis/`)](/lattice-system/formalization/legacy/15-generic-matrix-analysis-helpers/)
- [Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8)) — part 1 of 5](/lattice-system/formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-01/)
- [Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8)) — part 2 of 5](/lattice-system/formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-02/)
- [Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8)) — part 3 of 5](/lattice-system/formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-03/)
- [Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8)) — part 4 of 5](/lattice-system/formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-04/)
- [Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8)) — part 5 of 5](/lattice-system/formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-05/)
- [Two-site spin inner product (Tasaki §2.2 eq. (2.2.16))](/lattice-system/formalization/legacy/21-two-site-spin-inner-product-tasaki-2-2-eq-2-2-16/)
- [Spin-`S` Marshall–Lieb–Mattis on the magnetization sector (Tasaki §2.5 Theorem 2.2 generic S, sector form) — part 1 of 4](/lattice-system/formalization/legacy/27-spin-marshall-lieb-mattis-on-the-magnetization-sector-tasa-part-01/)
- [Spin-`S` Marshall–Lieb–Mattis on the magnetization sector (Tasaki §2.5 Theorem 2.2 generic S, sector form) — part 2 of 4](/lattice-system/formalization/legacy/27-spin-marshall-lieb-mattis-on-the-magnetization-sector-tasa-part-02/)
- [Spin-`S` Marshall–Lieb–Mattis on the magnetization sector (Tasaki §2.5 Theorem 2.2 generic S, sector form) — part 3 of 4](/lattice-system/formalization/legacy/27-spin-marshall-lieb-mattis-on-the-magnetization-sector-tasa-part-03/)
- [Spin-`S` Marshall–Lieb–Mattis on the magnetization sector (Tasaki §2.5 Theorem 2.2 generic S, sector form) — part 4 of 4](/lattice-system/formalization/legacy/27-spin-marshall-lieb-mattis-on-the-magnetization-sector-tasa-part-04/)
- [Spin-`S` saturated ferromagnetic state (Tasaki §2.4 generalised) — part 1 of 2](/lattice-system/formalization/legacy/28-spin-saturated-ferromagnetic-state-tasaki-2-4-generalised-part-01/)
- [Spin-`S` saturated ferromagnetic state (Tasaki §2.4 generalised) — part 2 of 2](/lattice-system/formalization/legacy/28-spin-saturated-ferromagnetic-state-tasaki-2-4-generalised-part-02/)

<a id="group-spin-models"></a>
### Spin models, Chapters 3–7, and spectral tools

- [Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1) — part 1 of 4](/lattice-system/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-01/)
- [Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1) — part 2 of 4](/lattice-system/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-02/)
- [Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1) — part 3 of 4](/lattice-system/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-03/)
- [Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1) — part 4 of 4](/lattice-system/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-04/)
- [Bose–Einstein condensation of hard-core bosons (Tasaki §5.1–§5.2)](/lattice-system/formalization/legacy/17-bose-einstein-condensation-of-hard-core-bosons-tasaki-5-1-/)
- [Antiferromagnetic Heisenberg chains and the Haldane conjecture (Tasaki §6.1)](/lattice-system/formalization/legacy/18-antiferromagnetic-heisenberg-chains-and-the-haldane-conjec/)
- [The AKLT model (Tasaki §7.1)](/lattice-system/formalization/legacy/19-the-aklt-model-tasaki-7-1/)
- [One-dimensional open-chain quantum Ising](/lattice-system/formalization/legacy/22-one-dimensional-open-chain-quantum-ising/)
- [Gibbs state (Tasaki §3.3)](/lattice-system/formalization/legacy/24-gibbs-state-tasaki-3-3/)
- [Heisenberg chain (Tasaki §3.5) — part 1 of 2](/lattice-system/formalization/legacy/25-heisenberg-chain-tasaki-3-5-part-01/)
- [Heisenberg chain (Tasaki §3.5) — part 2 of 2](/lattice-system/formalization/legacy/25-heisenberg-chain-tasaki-3-5-part-02/)
- [Perron-Frobenius theorem (`Math/PerronFrobenius.lean`, `Math/PerronFrobeniusPrimitive.lean`, `Math/CollatzWielandt.lean`, `Math/PerronFrobeniusMain.lean`)](/lattice-system/formalization/legacy/26-perron-frobenius-theorem/)

<a id="group-project-infrastructure"></a>
### Project infrastructure

- [Testing infrastructure](/lattice-system/formalization/legacy/23-testing-infrastructure/)

<a id="group-fermions-hubbard"></a>
### Fermions and Hubbard models

- [Single-mode fermion (P2 skeleton)](/lattice-system/formalization/legacy/29-single-mode-fermion-p2-skeleton/)
- [Multi-mode fermion via Jordan–Wigner (P2 backbone) — part 1 of 9](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-01/)
- [Multi-mode fermion via Jordan–Wigner (P2 backbone) — part 2 of 9](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02/)
- [Multi-mode fermion via Jordan–Wigner (P2 backbone) — part 3 of 9](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03/)
- [Multi-mode fermion via Jordan–Wigner (P2 backbone) — part 4 of 9](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-04/)
- [Multi-mode fermion via Jordan–Wigner (P2 backbone) — part 5 of 9](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-05/)
- [Multi-mode fermion via Jordan–Wigner (P2 backbone) — part 6 of 9](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-06/)
- [Multi-mode fermion via Jordan–Wigner (P2 backbone) — part 7 of 9](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-07/)
- [Multi-mode fermion via Jordan–Wigner (P2 backbone) — part 8 of 9](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-08/)
- [Multi-mode fermion via Jordan–Wigner (P2 backbone) — part 9 of 9](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-09/)
