---
layout: page
title: "Documented axioms: Tasaki Chapter 4 (part 2 of 3)"
permalink: /limitations/documented-axioms/chapter-04-part-02/
---

# Documented axioms: Tasaki Chapter 4 (part 2 of 3)

[Documented-axiom policy and entry index](/lattice-system/limitations/documented-axioms/)

<a id="entry-theorem-4-20"></a>

## Theorem 4.20 (infinite-volume ground states `ω₀`, `ω_n`)

**Tasaki §4.3, Theorem 4.20** (eqs. (4.3.7)-(4.3.10), around p. 91) is carried
by two **documented axioms** in
`LatticeSystem/Quantum/SpinS/InfiniteVolumeGroundState.lean`:
`theorem_4_20_omega0` (declaration line 210) and `theorem_4_20_omegaN`
(declaration line 223).

- **Proved (axiom-free):** the finite-volume ground-state machinery these
  states are the `L↑∞` limit of, and the surrounding
  `IsInfiniteVolumeGroundState` / `InfiniteSpinSystem` layer, are real
  definitions; only the existence of the limit states is axiomatized.
- **What the axiom statements literally assert:** `theorem_4_20_omega0`
  states — conditional on `εGS` being the genuine ground-state energy
  density of the model (`IsGroundStateEnergyDensity`, itself an
  uninterpreted documented predicate) — that there exists a state `ω₀`
  (`WeakDual ℂ A`) that is an infinite-volume ground state at energy density
  `εGS` (`IsInfiniteVolumeGroundState`) with vanishing single-site
  magnetization `ω₀(Ŝ_x^{(α)}) = 0` (eq. (4.3.9)). The axiom itself is a bare
  existential; it does **not** encode the `L↑∞` limit construction
  (eq. (4.3.7)) that motivates it — the module doc comment describes that
  construction informally, but only the existence and the two stated
  properties are part of the formal statement. `theorem_4_20_omegaN` states
  that, additionally assuming staggered long-range order with parameter
  `mStar > 0` (`HasStaggeredLRO`, also an uninterpreted documented
  predicate), for every unit direction `n` there exists a state `ω_n`,
  likewise an infinite-volume ground state at energy density `εGS`, with
  Néel magnetization `ω_n(Ŝ_x^{(α)}) = (−1)^x mStar n_α` (eq. (4.3.10)); the
  `L↑∞` limit motivation (eq. (4.3.8)) is again informal, not part of the
  formal existential.
- **Axiom reason (documented):** both statements assert existence of a
  weak-* limit state on the quasi-local C*-algebra of the infinite spin
  system (via Banach–Alaoglu, Theorem A.24) — genuine operator-algebraic /
  thermodynamic-limit content, the same policy class as Appendix A.21-A.28.
- **Re-check condition:** would change only when all of the following exist
  in reviewed form in this repository (or are usable from mathlib): (a) a
  concrete weak-* compactness / state-space layer for `InfiniteSpinSystem`
  strong enough to construct the `L↑∞` limit of the finite-volume ground
  states; (b) a real (non-uninterpreted) definition of
  `IsGroundStateEnergyDensity` tied to the model's actual finite-volume
  energy density; and, for `theorem_4_20_omegaN` specifically, (c) a real
  definition of `HasStaggeredLRO` tied to the model's actual finite-volume
  order-parameter limit, together with a proof that the constructed `ω_n`
  satisfies the stated properties.
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.

<a id="entry-theorem-4-22"></a>

## Theorem 4.22 (no SSB and exponential clustering in one dimension)

**Tasaki §4.4, Theorem 4.22** (eqs. (4.4.5)-(4.4.6), around p. 95, with
footnote 41) is carried by two **documented axioms** in
`LatticeSystem/Quantum/SpinS/HeisenbergEquilibrium.lean`:
`tasaki_4_22_magnetization_vanishes` (declaration line 152) and
`tasaki_4_22_exponential_clustering` (declaration line 168).

- **Proved (axiom-free):** the finite- and infinite-volume magnetization and
  two-spin correlation observables (`finiteVolMagnetizationS`,
  `finiteVolSpinCorrS`, `infiniteVolSpinCorrLiminf`) they quantify over are
  real definitions.
- **What the axiom statements literally assert:**
  `tasaki_4_22_magnetization_vanishes` states that for the one-dimensional
  ferromagnetic or antiferromagnetic Heisenberg model at any spin and any
  `β ∈ [0, ∞)`, the magnetization vanishes in the iterated limit
  `lim_{h↓0} lim_{L↑∞} ⟨Ŝ_x^{(3)}⟩_{β,h}^L = 0` (eq. (4.4.5)), stated
  soundly per footnote 41 as: for every `ε > 0` there is a field threshold
  `δ > 0` such that for every `0 < h < δ` the finite-volume magnetization is
  within `ε` of `0` along arbitrarily large even volumes.
  `tasaki_4_22_exponential_clustering` states that at vanishing field there
  exist a correlation length `ξ(β) > 0` and constant `C(β) > 0` such that the
  infinite-volume two-spin correlation decays exponentially,
  `|⟨Ŝ_x^{(α)} Ŝ_y^{(α)}⟩_{β,0}^∞| ≤ C(β) exp(−|x−y|/ξ(β))`, for every axis
  `α` (eq. (4.4.6)).
- **Axiom reason (documented):** both are proved by one-dimensional
  cluster-expansion methods (Tasaki [4]); the repository contains no
  polymer/cluster-expansion framework with volume-uniform convergence
  estimates, the standing perturbation-theory documented-axiom class (the
  same class as the Chapter 7/8 cluster-expansion entries and the Chapter 10
  singular-perturbation arguments).
- **Re-check condition:** would change only when a general, reviewed
  cluster/polymer-expansion framework with volume-uniform convergence
  estimates exists in this repository (or is usable from mathlib), together
  with a math-before-code transcription of the one-dimensional
  cluster-expansion argument (Tasaki [4]) sufficient to derive both the
  vanishing-magnetization and the exponential-clustering conclusions.
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.

<a id="entry-theorem-4-23"></a>

## Theorem 4.23 (high-temperature disorder in two or higher dimensions)

**Tasaki §4.4, Theorem 4.23** (eqs. (4.4.7)-(4.4.8), around p. 96) is a
**documented axiom**, `tasaki_4_23_high_temperature_disorder`
(`LatticeSystem/Quantum/SpinS/HeisenbergEquilibrium.lean`, declaration
line 192).

- **Proved (axiom-free):** as with Theorem 4.22, the finite-volume
  magnetization and infinite-volume correlation observables the statement
  quantifies over are real definitions.
- **What the axiom statement literally asserts:** for the ferromagnetic or
  antiferromagnetic Heisenberg model on the `d`-dimensional hypercubic
  lattice with `d ≥ 2` and any spin, there is a high-temperature threshold
  `β₀ > 0` — depending only on `d` and the spin, shared by both the
  ferromagnetic and antiferromagnetic models — such that for every
  `β ∈ [0, β₀]` the model is disordered: the magnetization vanishes in the
  same iterated-limit sense as Theorem 4.22 (eq. (4.4.7)), and the
  infinite-volume correlation decays exponentially with `β`-dependent
  constants `ξ(β), C(β) > 0` (eq. (4.4.8)).
- **Axiom reason (documented):** proved by the cluster-expansion technique,
  valid at sufficiently high temperature in any dimension for any
  short-ranged interaction (Tasaki [21, 50, 61]); the same
  absent-cluster-expansion-framework documented-axiom class as Theorem 4.22.
- **Re-check condition:** would change only when a general, reviewed
  cluster/polymer-expansion framework with volume-uniform, high-temperature
  convergence estimates exists in this repository (or is usable from
  mathlib), together with a math-before-code transcription of the
  high-temperature cluster-expansion argument (Tasaki [21, 50, 61]).
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.
