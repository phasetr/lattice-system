---
layout: page
title: "Documented axioms: Tasaki Chapter 11 (part 1 of 2)"
permalink: /limitations/documented-axioms/chapter-11-part-01/
---

# Documented axioms: Tasaki Chapter 11 (part 1 of 2)

[Documented-axiom policy and entry index](/lattice-system/limitations/documented-axioms/)

<a id="entry-theorem-11-8"></a>

## Theorem 11.8 (Nagaoka connectivity classification)

**Tasaki §11.2.2, Theorem 11.8** (pp. 386-388) is a **documented axiom**,
`nagaoka_theorem_11_8`
(`LatticeSystem/Fermion/JordanWigner/Hubbard/NagaokaConnectivityClassification.lean`,
declaration line 60).

- **Proved (axiom-free):** Theorem 11.7 (`nagaoka_theorem_11_7`,
  `NagaokaConnectivity.lean`) is `sorry`-free and does not depend on this
  axiom; companion **Lemma 11.9** (`nagaoka_lemma_11_9`, same module) was
  initially axiomatized but is now a proved theorem via the full
  "15-puzzle" hole-motion machinery in `NagaokaStateQuiver.lean` — a
  precedent that "cite-only" is the correct class for Theorem 11.8 itself,
  not evidence the whole file is provable the same way.
- **What the axiom statement literally asserts:** a Hubbard model with
  `U = ∞`, `N = |Λ| − 1` and `t ≥ 0` satisfies the connectivity condition
  (Definition 11.6, `nagaokaConnectivity`) **if and only if** its bond graph
  is biconnected and is not a simple loop (periodic chain) with more than
  four sites.
- **Axiom reason (documented):** Tasaki's text explicitly leaves the proof
  to the original papers — Bobrow, Stubis and Li, and Wilson's
  graph-theoretic analysis of the "15-puzzle" (§11.2.2, p. 387, refs [4],
  [81]); the book itself provides no proof, so this is a cited external
  classification theorem.
- **Re-check condition:** would change only if a math-before-code
  transcription of the Bobrow–Stubis–Li / Wilson "15-puzzle" classification
  argument is completed in this repository.
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.

<a id="entry-theorem-11-13"></a>

## Theorem 11.13 (Mielke's flat-band ferromagnetism)

**Tasaki §11.3.2, Theorem 11.13** is a **documented axiom**,
`mielke_theorem_11_13`
(`LatticeSystem/Fermion/JordanWigner/Hubbard/MielkeTheorems.lean`,
declaration line 104).

- **Proved (axiom-free):** Theorem 11.12 (the flat-band dimension count),
  which Tasaki likewise defers to §11.3.3, is now proved in
  `MielkeIncidenceMatrix.lean` via the incidence-matrix construction
  (`mielke_theorem_11_12`); the companion §11.3.1 classification,
  Theorem 11.11, is also proved axiom-free in
  `TasakiFlatBandClassification.lean`. Only Theorem 11.13 itself remains
  axiomatized.
- **What the axiom statement literally asserts:** for a biconnected base
  lattice `(Λ̃,B̃)`, the Hubbard model on its line graph at half-filling
  `N = D(Λ̃,B̃)` (with `t, U > 0`) has ground states that all carry total
  spin `S_tot = S_max = N/2`, unique apart from the
  `2S_max + 1 = N + 1`-fold multiplet degeneracy — i.e. the ground subspace
  has `finrank = N + 1` and every ground state is an `(Ŝ_tot)²` eigenvector
  at `S_max(S_max + 1)`.
- **Axiom reason (documented):** Tasaki states this "without a proof" ("We
  state it without a proof"), the project's external-cite-only documented
  axiom class, the same class as Theorem 10.11 (Kubo–Kishi).
- **Re-check condition:** would change only if a math-before-code
  transcription of Mielke's flat-band ferromagnetism argument is completed
  in this repository.
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.

<a id="entry-lemma-11-22-11-23"></a>

## Lemma 11.22 and Lemma 11.23 (positivity of the frustration-free local Hamiltonian)

**Tasaki §11.4.3, Lemma 11.22 and Lemma 11.23** (eqs. (11.4.46)-(11.4.50),
pp. 429-435) are two **documented axioms** in
`LatticeSystem/Fermion/JordanWigner/Hubbard/NonsingularLocalHamiltonian.lean`:
`nonsingular_lemma_11_22` (declaration line 129) and
`nonsingular_lemma_11_23` (declaration line 141).

- **Proved (axiom-free):** the local Hamiltonian `nonsingularLocalHamiltonian`
  (eq. (11.4.48)) is a real definition, and the fact that it annihilates the
  all-up flat-band state
  (`nonsingularLocalHamiltonian_mulVec_alphaAllUpState`) is proved
  axiom-free in the same file. Underlying **Lemma 11.21** (`ĥ_p ≥ 0 ⇒`
  ferromagnetism, via Theorem 11.11) is proved as
  `nonsingular_exhibitsFerromagnetism`, and **Theorem 11.20** is assembled
  as `tasaki_theorem_11_20`, both in `NonsingularFerromagnetism.lean`,
  consuming Lemma 11.22 as a hypothesis.
- **What the axiom statements literally assert:** `nonsingular_lemma_11_22`
  states that for `ν > 0` there are thresholds `T, V, clam, cκ > 0` such that
  once `t/s ≥ T` and `U/s ≥ V` (with `lam = clam·s`, `κ = cκ`), the local
  Hamiltonian `ĥ_p` is positive semidefinite for every external site `p`.
  `nonsingular_lemma_11_23` states, underlying Lemma 11.22, that for the same
  `ν` and thresholds, any state with total spin `twoS < K+1` (below
  `S_max`) has strictly positive sector-minimum energy of `ĥ_p` in the
  `t, U ↑ ∞` regime.
- **Axiom reason (documented):** both genuinely need eigenvalue-continuity
  degenerate-perturbation-theory machinery in the `t, U ↑ ∞` limit that
  mathlib lacks and this repository has not built for this model; this is
  the volume-uniform perturbative-estimate documented-axiom class (`∃ T, V`
  independent of the system size `K`, `∀ K, …`), not finite-fixed-`K` linear
  algebra.
- **Re-check condition:** would change only if a math-before-code
  transcription of the `t, U ↑ ∞` degenerate-perturbation-theory argument
  for `ĥ_p`'s positivity (Lemma 11.22) and its zero-mode characterization
  (Lemma 11.23) is completed in this repository.
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.
