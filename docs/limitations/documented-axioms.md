---
layout: page
title: "Documented-axiom status and axiomatization policy"
permalink: /limitations/documented-axioms/
---

# Documented-axiom status and axiomatization policy

> This current policy text was moved losslessly from the former monolithic index.

<!-- legacy-source:start:155:216 -->
### Appendix A: status and axiomatization policy

Tasaki's **Appendix A is fully formalized in book order (A.1–A.28)**, and the
entire Tasaki text up to and including Chapter 11 (§11.5) plus this appendix is
now covered. The appendix splits into two kinds of items:

- **Proved (axiom-free)** — the linear-algebra and angular-momentum core that
  `mathlib` supports directly: **A.1** (the Lie product / Trotter formula, proved
  from scratch in a complete normed `ℝ`-algebra), **A.12** (the strong-coupling
  effective Hamiltonian limit, by the `v⁻¹`-squeeze + kernel-pairing continuity
  argument), **A.4–A.6**
  (positive-semidefinite basics + unique
  PSD square root), **A.7–A.8** (Weyl eigenvalue monotonicity via Courant–Fischer,
  and the trace-exp monotonicity through the spectral mapping for `exp`),
  **A.9–A.11** (frustration-free Hamiltonians, energy-form
  kernels), **A.13–A.16** (angular-momentum quantization `J = n/2`, the ladder,
  and SU(2)-multiplet degeneracy), **A.17** (spin-0/half sector via the common
  eigenvector of commuting Hermitians), **A.18** (Perron–Frobenius for a real
  symmetric matrix, via the project's Collatz–Wielandt development and the
  variational `|w|`-argument), and **A.19–A.20** (polar + singular-value
  decompositions from the spectral theorem).
- **Documented axioms (faithful statements, deferred proofs)** — the
  operator-algebraic **A.21–A.28** (Wigner's
  theorem, states, Banach–Alaoglu, ground states of infinite systems, the GNS
  construction).

**Value judgment / policy.** The documented axioms above are kept as *faithful,
book-order statements* — they record exactly what Tasaki proves — but they are
**not active proof targets** of this project. They fall into two categories:

- **Operator-algebraic results** (Appendix A.21–A.28): the heavy functional-analytic and
operator-algebraic structures (states on the quasi-local C\*-algebra, weak-∗
compactness, ground states, GNS, Wigner) belong to a dedicated operator-algebra /
functional-analysis development; such a development may well be carried out
**separately** (for instance contributed to `mathlib`), and these axioms simply
**wait for that implementation**.

- **Perturbation-theoretic results** (e.g., the singular-perturbation and
adiabatic-continuation arguments in Chapter 10, the cluster expansions behind
**Theorem 7.3** and **Theorem 8.1**, and the quasi-adiabatic continuation behind
**Theorem 8.9**): the analytic proofs of weak-coupling continuation and adiabatic
following for eigenstate families are **not undertaken** as an active project goal;
such techniques naturally belong to a separate analytic-perturbation development.
The class is delimited by the *machinery* it needs — analytic eigenvalue-branch
(Rellich–Kato) continuation, cluster/polymer expansions, volume-uniform estimates —
and does **not** cover finite-dimensional degenerate perturbation theory at fixed
finite volume, which is ordinary linear algebra and is proved (**Lemma 10.1**, the
strong-coupling **Theorem A.12**, and **Theorem 10.4** are all axiom-free).

- **Book theorems that Tasaki states without proof** (results he quotes from the
external literature rather than proving in the text): **Theorem 10.11** (Kubo–Kishi
finite-temperature charge/pairing susceptibility bound, Tasaki §10.2.5, citing
Kubo–Kishi, *Phys. Rev. B* **41**, 4866 (1990)) and **Theorem 11.13** (Mielke's
flat-band ferromagnetism, `mielke_theorem_11_13`) are recorded as **faithful documented
axioms** on the concrete finite-volume operators (here the Duhamel susceptibilities),
matching the "Tasaki states it without proof" policy — the reproving of the cited
external work is not an active project goal.

Accordingly the project's policy is to **axiomatize only the appendix and
perturbation-theory results that Tasaki's formalized main development actually uses**,
to **prove** the remaining ones where `mathlib` provides the tools, and otherwise to
leave a faithful axiom in place rather than invest in large bespoke developments whose
natural home is elsewhere. The `#print axioms` of every theorem in the repository makes
the precise dependency on these documented axioms auditable.

<!-- legacy-source:end:155:216 -->

## Entry pages

The per-declaration entries are recorded on the chapter pages below; this page keeps the
policy text only.

- [Tasaki Chapter 7](/lattice-system/limitations/documented-axioms/chapter-07/) — <a id="theorem-77-hexagonal-aklt-correlation-decay-and-infinite-volume-uniqueness"></a>[Theorem 7.7](/lattice-system/limitations/documented-axioms/chapter-07/#entry-theorem-7-7), <a id="theorem-72-aklt-infinite-chain-unique-ground-state-with-a-nonzero-gap"></a>[Theorem 7.2](/lattice-system/limitations/documented-axioms/chapter-07/#entry-theorem-7-2), <a id="theorem-73-stability-of-the-aklt-gap-under-small-local-perturbations"></a>[Theorem 7.3](/lattice-system/limitations/documented-axioms/chapter-07/#entry-theorem-7-3)
- [Tasaki Chapter 8 (part 1 of 3)](/lattice-system/limitations/documented-axioms/chapter-08-part-01/) — <a id="theorem-81-large-d-phase-of-the-anisotropic-s--1-chain-l-uniform-gap-and-clustering"></a>[Theorem 8.1](/lattice-system/limitations/documented-axioms/chapter-08-part-01/#entry-theorem-8-1), <a id="theorem-83--d-model-nel-order-bounded-by-string-order"></a>[Theorem 8.3](/lattice-system/limitations/documented-axioms/chapter-08-part-01/#entry-theorem-8-3), <a id="eq-833-oshikawa-parity-dependence-of-the-spin-s-vbs-string-order"></a>[Eq. (8.3.3)](/lattice-system/limitations/documented-axioms/chapter-08-part-01/#entry-eq-8-3-3)
- [Tasaki Chapter 8 (part 2 of 3)](/lattice-system/limitations/documented-axioms/chapter-08-part-02/) — <a id="spt-phase-markers-isshortrangegappeduniquegs-isproductstatehamiltonian"></a>[§8.3.2 SPT-phase markers](/lattice-system/limitations/documented-axioms/chapter-08-part-02/#entry-spt-markers-8-3-2), <a id="general-s-bond-inversion-parity-of-the-vbs-state-p-259-unnumbered-display"></a>[General-`S` bond-inversion parity](/lattice-system/limitations/documented-axioms/chapter-08-part-02/#entry-general-s-bond-inversion-parity), <a id="entanglement-entropy-marker-entanglemententropys"></a>[§8.3.3 entanglement-entropy marker](/lattice-system/limitations/documented-axioms/chapter-08-part-02/#entry-entanglement-entropy-8-3-3)
- [Tasaki Chapter 8 (part 3 of 3)](/lattice-system/limitations/documented-axioms/chapter-08-part-03/) — <a id="theorem-86-lieb-schultz-mattis-type-theorem-without-continuous-symmetry"></a>[§8.3.5 Theorem 8.6](/lattice-system/limitations/documented-axioms/chapter-08-part-03/#entry-theorem-8-6), <a id="theorem-88-rigorous-index-theorem-and-the-spt-phase-transition"></a>[§8.3.6 Theorem 8.8](/lattice-system/limitations/documented-axioms/chapter-08-part-03/#entry-theorem-8-8), <a id="theorem-89-stability-of-the-toric-codes-topological-order-under-arbitrary-local-perturbations"></a>[§8.4 Theorem 8.9](/lattice-system/limitations/documented-axioms/chapter-08-part-03/#entry-theorem-8-9)
- [Tasaki Chapter 4](/lattice-system/limitations/documented-axioms/chapter-04/) — [Theorem 4.2](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-2), [Corollary 4.3 support](/lattice-system/limitations/documented-axioms/chapter-04/#entry-corollary-4-3-support), [Lemma 4.15 / Theorem 4.11 support](/lattice-system/limitations/documented-axioms/chapter-04/#entry-lemma-4-15-theorem-4-11-support), [Theorem 4.20](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-20), [§4.3 thermodynamic-limit bridge](/lattice-system/limitations/documented-axioms/chapter-04/#entry-section-4-3-thermodynamic-limit-bridge), [Theorem 4.22](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-22), [Theorem 4.23](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-23), [Theorem 4.24](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-24), [Theorem 4.25](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-25), [Theorem 4.26](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-26), [Theorem 4.27](/lattice-system/limitations/documented-axioms/chapter-04/#entry-theorem-4-27)
- [Tasaki Chapter 5](/lattice-system/limitations/documented-axioms/chapter-05/) — [Theorem 5.1](/lattice-system/limitations/documented-axioms/chapter-05/#entry-theorem-5-1), [Theorem 5.2](/lattice-system/limitations/documented-axioms/chapter-05/#entry-theorem-5-2), [Theorem 5.3](/lattice-system/limitations/documented-axioms/chapter-05/#entry-theorem-5-3), [Theorem 5.4](/lattice-system/limitations/documented-axioms/chapter-05/#entry-theorem-5-4)
- [Tasaki Chapter 10](/lattice-system/limitations/documented-axioms/chapter-10/) — [Theorem 10.11](/lattice-system/limitations/documented-axioms/chapter-10/#entry-theorem-10-11)
- [Tasaki Chapter 11](/lattice-system/limitations/documented-axioms/chapter-11/) — [Theorem 11.8](/lattice-system/limitations/documented-axioms/chapter-11/#entry-theorem-11-8), [Theorem 11.13](/lattice-system/limitations/documented-axioms/chapter-11/#entry-theorem-11-13), [Theorem 11.18](/lattice-system/limitations/documented-axioms/chapter-11/#entry-theorem-11-18), [Theorem 11.19](/lattice-system/limitations/documented-axioms/chapter-11/#entry-theorem-11-19), [Lemma 11.22/11.23](/lattice-system/limitations/documented-axioms/chapter-11/#entry-lemma-11-22-11-23), [Lemma 11.25](/lattice-system/limitations/documented-axioms/chapter-11/#entry-lemma-11-25), [Theorem 11.27](/lattice-system/limitations/documented-axioms/chapter-11/#entry-theorem-11-27)

Each `<a id="…">` above is the id Kramdown generated for that entry's heading while this page
still carried the entries, so links published against the former single-page ledger keep
resolving. Entries written after the split were never addressable here and get no such id.

A new entry is written on the page of its Tasaki chapter (`chapter-NN.md`, created on first
use and added to this list). When a page would exceed 48 KiB, start the next `-part-NN` page
so that the 64 KiB soft page-size threshold of `scripts/check_docs_hierarchy.py` stays an
early warning rather than the first signal of the 128 KiB hard failure.
