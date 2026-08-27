---
layout: page
title: "Documented axioms: Tasaki Chapter 11"
permalink: /limitations/documented-axioms/chapter-11/
---

# Documented axioms: Tasaki Chapter 11

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

<a id="entry-theorem-11-18"></a>

## Theorem 11.18 (local stability of ferromagnetic ground states)

**Tasaki §11.4, Theorem 11.18** (eqs. (11.4.24)-(11.4.29), pp. 422-423) is a
**documented axiom**, `nonsingular_theorem_11_18`
(`LatticeSystem/Fermion/JordanWigner/Hubbard/NonsingularLocalStability.lean`,
declaration line 49).

- **Proved (axiom-free):** the non-singular hopping regularity predicate
  `IsNonsingularHopping` and the Hamiltonian `nonsingularHubbardHamiltonian`
  it quantifies over are real definitions.
- **What the axiom statement literally asserts:** there are constants
  `ν₀, η₀, ξ₀ > 0` — depending only on the dimension (`d = 1`) and the
  hopping range `R`, uniformly in the system size `K` — such that for the
  non-singular Hubbard model with `0 < ν ≤ ν₀`, `|ζ| ≤ ν³η₀`, and
  `U ≥ ξ₀t|ζ|/ν²` (eqs. (11.4.27)-(11.4.28)), the maximal-spin sector lies
  strictly below the once-flipped sector,
  `E_min(S_max) < E_min(S_max − 1)` (eq. (11.4.29)) — ferromagnetic
  stability against a single spin flip.
- **Axiom reason (documented):** proved by Tasaki via an elementary but
  rigorous perturbation theory (§11.4); the constants are volume-uniform
  (`∀ K`, outside the `∃ ν₀, η₀, ξ₀`) rather than finite-fixed-`K` linear
  algebra, matching the standing perturbation-theory documented-axiom class.
- **Re-check condition:** would change only if a math-before-code
  transcription of Tasaki's local-stability perturbation-theory argument
  (§11.4) is completed in this repository.
- **Tracking:** master tracker #4718; Issue #4189 recorded this documented
  axiom's policy (matching the Theorem 11.8 / 11.13 / 11.15 policy). No
  dedicated discharge issue exists or is to be opened while the re-check
  condition above is unmet.

<a id="entry-theorem-11-19"></a>

## Theorem 11.19 (spin-wave excitation energy bounds)

**Tasaki §11.4.2, Theorem 11.19** (eqs. (11.4.30)-(11.4.35), pp. 423-424) is
a **documented axiom**, `nonsingular_theorem_11_19`
(`LatticeSystem/Fermion/JordanWigner/Hubbard/SpinWaveExcitation.lean`,
declaration line 64).

- **Proved (axiom-free):** the spin-wave excitation energy `spinWaveEnergy`
  and the crystal-momentum phase `momentumPhase` it quantifies over are real
  definitions.
- **What the axiom statement literally asserts:** there are constants
  `ν₁, η₁, ξ₁, ξ₂` and `a₁,a₂,a₃,b₁,b₂,b₃ > 0` (depending only on `d = 1` and
  the hopping range `R`, uniform in the system size) such that, under the
  parameter conditions `0 < ν ≤ ν₁`, `|ζ| ≤ ν²η₁`, `ξ₁t|ζ|/ν² ≤ U ≤ ξ₂tν`
  (eqs. (11.4.31)-(11.4.32)), the spin-wave dispersion
  `E_SW(k) − E_min(S_max)` is two-sided bounded between
  `F₂·2ν⁴U(1−cos k)` and `F₁·2ν⁴U(1−cos k)` (eq. (11.4.33)), with `F₁, F₂`
  as in (11.4.34)/(11.4.35).
- **Axiom reason (documented):** proved by Tasaki via rigorous perturbation
  theory (§11.4.2); the same volume-uniform perturbative-estimate
  documented-axiom class as Theorem 11.18 (which this theorem's proof
  builds on).
- **Re-check condition:** would change only if a math-before-code
  transcription of Tasaki's spin-wave dispersion perturbation-theory
  argument (§11.4.2) is completed in this repository.
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
  states that for `ν > 0` there are thresholds `T, V, clam > 0` and `cκ ≥ 0`
  (`clam` strictly positive, `cκ` merely nonnegative) such that once
  `t/s ≥ T` and `U/s ≥ V` (with `lam = clam·s`, `κ = cκ`), the local
  Hamiltonian `ĥ_p` is positive semidefinite for every external site `p`.
  `nonsingular_lemma_11_23` states, underlying Lemma 11.22, the analogous
  fact for the sector-minimum energy: for `ν > 0` there are its **own**
  thresholds `T, V, clam > 0, cκ ≥ 0` such that once `t/s ≥ T` and
  `U/s ≥ V`, any state with total spin `twoS < K+1` (below `S_max`) has
  strictly positive sector-minimum energy of `ĥ_p`. The two axioms
  existentially quantify their threshold constants **independently** — the
  statements do not assert that the same `T, V, clam, cκ` witnesses work for
  both, even though both are read together as one "Lemma 11.22" bound
  underlying Theorem 11.20's positivity argument.
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

<a id="entry-lemma-11-25"></a>

## Lemma 11.25 (Hubbard–t-J equivalence in the strong-coupling limit)

**Tasaki §11.5.3, Lemma 11.25** is a **documented axiom**, `lemma_11_25`
(`LatticeSystem/Fermion/JordanWigner/Hubbard/MetallicFerroModel.lean`,
declaration line 151).

- **Proved (axiom-free):** the `d = 1` decorated Hubbard model
  `decHubbardHamiltonian` (eqs. (11.5.13)-(11.5.14)) and the ferromagnetic
  t-J model side it relates to are real definitions; the underlying
  strong-coupling effective-Hamiltonian identification machinery
  (Theorem A.12 / Lemma A.11) that Tasaki's proof uses is itself proved
  axiom-free.
- **What the axiom statement literally asserts:** there are thresholds
  `T, V, W > 0` such that once `t ≥ T`, `U ≥ V`, `J ≥ W`, the `t, U ↑ ∞`
  limit of the decorated Hubbard model at electron number `Ne` is equivalent
  to the `J ↑ ∞` limit of the ferromagnetic t-J model (eq. (11.5.4)) on the
  external chain with the same electron number and hopping amplitude
  `τ = (1 + 4ν²)s`: the Hubbard ground subspace at filling `Ne` is the
  maximal-spin `(Ne + 1)`-fold multiplet **iff** the t-J ground subspace is
  (spin-structure transfer, faithfully rendered rather than the full
  ground-space identification).
- **Axiom reason (documented):** Tasaki's proof identifies both
  finite-energy subspaces with hard-core electrons carrying the same
  effective Hamiltonian via Theorem A.12/Lemma A.11, but the technical
  transfer itself is the original paper's argument (Tanaka–Tasaki [63]),
  not reproduced in the book; this is the project's external-cite-only
  documented-axiom class.
- **Re-check condition:** would change only if a math-before-code
  transcription of the Tanaka–Tasaki [63] strong-coupling spin-structure
  transfer argument is completed in this repository.
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.

<a id="entry-theorem-11-27"></a>

## Theorem 11.27 (Tanaka–Tasaki metallic ferromagnetism)

**Tasaki §11.5.4, Theorem 11.27** (eqs. (11.5.19)-(11.5.24)) is a
**documented axiom**, `theorem_11_27`
(`LatticeSystem/Fermion/JordanWigner/Hubbard/TanakaTasakiModel.lean`,
declaration line 194).

- **Proved (axiom-free):** the `d = 1` Tanaka–Tasaki model's special
  single-particle states (`â_p`, `b̂_p`, `d̂_p`, `d̂_{(u,ζ)}`, eqs.
  (11.5.19)-(11.5.22)) and the `u₂, U ↑ ∞` effective Hamiltonian
  `ttEffectiveHamiltonian` it is stated on are real definitions.
- **What the axiom statement literally asserts:** for the `d = 1`
  Tanaka–Tasaki model, if `u₁ > 2(|s| + 2|t|)` (Tasaki's
  `u₁ > 2d(|s|+2|t|)`) and the electron number satisfies
  `K + 1 ≤ Ne ≤ 2(K + 1)` (Tasaki's `L^d ≤ N ≤ 2L^d`), then **in the limit**
  `u₂, U ↑ ∞` — taken faithfully, not as finite "large enough" thresholds —
  every ground state of the effective Hamiltonian restricted to the
  finite-energy subspace (`d̂` modes empty) is an `(Ŝ_tot)²` eigenvector at
  the maximum possible total spin `(Ne/2)(Ne/2 + 1)`. (Tasaki states only
  the maximal spin, not the precise degeneracy, so this is weaker than
  `IsMaximalSpinMultipletSubmodule`.)
- **Axiom reason (documented):** Tasaki cites the original paper
  (Tanaka–Tasaki [63]) for the technical proof, and explicitly warns the
  result is not expected to hold at finite `u₂, U` (unlike the §11.4.3
  insulating model) — a genuine faithfully-taken `u₂, U ↑ ∞` limit, the
  project's external-cite-only-plus-genuine-limit documented-axiom class
  (the same limit-taking caveat as Theorem 5.4's iterated
  `lim_{ε↓0}lim_{L↑∞}`).
- **Re-check condition:** would change only if a math-before-code
  transcription of the Tanaka–Tasaki [63] metallic-ferromagnetism argument
  (including the faithful `u₂, U ↑ ∞` limit) is completed in this
  repository.
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.
