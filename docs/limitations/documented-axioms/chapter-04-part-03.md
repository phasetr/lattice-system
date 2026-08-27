---
layout: page
title: "Documented axioms: Tasaki Chapter 4 (part 3 of 3)"
permalink: /limitations/documented-axioms/chapter-04-part-03/
---

# Documented axioms: Tasaki Chapter 4 (part 3 of 3)

[Documented-axiom policy and entry index](/lattice-system/limitations/documented-axioms/)

<a id="entry-theorem-4-24"></a>

## Theorem 4.24 (improved Hohenberg–Mermin–Wagner theorem)

**Tasaki §4.4, Theorem 4.24** (eq. (4.4.22), around p. 97, with footnote 48)
is a **documented axiom**, `improved_hohenberg_mermin_wagner`
(`LatticeSystem/Quantum/SpinS/HeisenbergEquilibrium.lean`, declaration
line 238).

- **Proved (axiom-free):** the generalized field Hamiltonian
  `generalizedFieldHamiltonianS` (eq. (4.4.21)) and the finite-volume
  magnetization observable `finiteVolMagnetizationGenS` it quantifies over
  are real definitions.
- **What the axiom statement literally asserts:** for the generalized field
  Heisenberg model in **two dimensions** with any spin, either coupling sign
  `J ∈ {−1, +1}`, and *any* fixed field-direction family `ξ` with
  `|ξ_x| ≤ 1`, the magnetization in every component vanishes in the iterated
  limit `lim_{h↓0} lim_{L↑∞} ⟨Ŝ_x^{(α)}⟩_{β,h}^L = 0`, for any `β ≥ 0`
  (eq. (4.4.22)); stated per footnote 48 in the `limsup`-eventual sense (the
  inner limit is rigorously a `lim sup_{L↑∞}`).
- **Axiom reason (documented):** proved by McBryan–Spencer's
  complex-translation method [33, 44] — an external analytic technique
  (not cluster expansion) that Tasaki reports without reproducing;
  recorded as a documented axiom in the same "Tasaki states an external
  analytic-technique proof" class as Theorem 7.7's correlation-decay proof
  and Theorem 4.26/4.27 below.
- **Re-check condition:** would change only if a math-before-code
  transcription of the McBryan–Spencer complex-translation method is
  completed in this repository.
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.

<a id="entry-theorem-4-25"></a>

## Theorem 4.25 (McBryan–Spencer, Koma–Tasaki power-law bound)

**Tasaki §4.4, Theorem 4.25** (eqs. (4.4.23)-(4.4.24), around p. 98) is a
**documented axiom**, `mcbryan_spencer_koma_tasaki`
(`LatticeSystem/Quantum/SpinS/HeisenbergEquilibrium.lean`, declaration
line 262).

- **Proved (axiom-free):** the finite-volume spin correlation observable
  `finiteVolSpinCorrS` it quantifies over is a real definition.
- **What the axiom statement literally asserts:** for the ferromagnetic or
  antiferromagnetic Heisenberg model in **two dimensions** at vanishing
  field, there is an `L`-independent, `β`-decreasing exponent `η(β) > 0`
  (shared by both signs) such that the finite-volume two-point correlation
  obeys the power-law bound
  `|⟨Ŝ_x^{(α)} Ŝ_y^{(α)}⟩_{β,0}^L| ≤ 2 S² |x−y|^{−η(β)}` for every axis
  `α` and every pair of distinct sites with `0 < |x−y| < L/2` (eq. (4.4.23)).
- **Axiom reason (documented):** proved by the McBryan–Spencer
  complex-translation method extended to quantum systems by Koma–Tasaki;
  the same external analytic-technique documented-axiom class as
  Theorem 4.24.
- **Re-check condition:** would change only if a math-before-code
  transcription of the Koma–Tasaki extension of the McBryan–Spencer method
  is completed in this repository.
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.

<a id="entry-theorem-4-26"></a>

## Theorem 4.26 (Dyson–Lieb–Simon long-range order in three or higher dimensions)

**Tasaki §4.4, Theorem 4.26** (eq. (4.4.52), around p. 108) is a
**documented axiom**, `theorem_4_26_staggered_lro`
(`LatticeSystem/Quantum/SpinS/HeisenbergEquilibrium.lean`, declaration
line 296).

- **Proved (axiom-free):** the per-axis staggered order operator
  `staggeredOrderOpAxisS` it quantifies over is a real definition.
- **What the axiom statement literally asserts:** for the antiferromagnetic
  Heisenberg model on the `d`-dimensional hypercubic lattice with `d ≥ 3` and
  any spin (`N ≥ 1`), there exist a low-temperature threshold `β₀ > 0` and a
  function `q(β) > 0` for `β > β₀` such that the squared staggered
  order-parameter density stays bounded below by `q(β)` for sufficiently
  large even volumes, `⟨(Ô_L^{(α)}/L^d)²⟩_{β,0}^L ≥ q(β)`, for every axis
  `α` and every `β > β₀` (eq. (4.4.52)) — genuine Néel long-range order at
  sufficiently low temperature in `d ≥ 3`.
- **Axiom reason (documented):** proved by Dyson, Lieb and Simon [12] via
  reflection positivity (the `d = 3`, `S = 1/2` case by Kennedy–Lieb–Shastry
  [29]); this is the `d`-dimensional reflection-positivity/IR-bound
  documented-axiom class, matching the "d-dim RP/IR-bound intractable at
  project scale" carve-out already recorded for Theorem 5.1 below (the
  repository's existing RP infrastructure is 1D-ring-only).
- **Re-check condition:** would change if a `d`-dimensional
  reflection-positivity / infrared-bound infrastructure is built in this
  repository and a math-before-code transcription of the Dyson–Lieb–Simon
  argument is completed.
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.

<a id="entry-theorem-4-27"></a>

## Theorem 4.27 (Griffiths, Koma–Tasaki finite-temperature symmetry breaking)

**Tasaki §4.4, Theorem 4.27** (eq. (4.4.53), around p. 109) is a
**documented axiom**, `theorem_4_27_griffiths_koma_tasaki_ssb`
(`LatticeSystem/Quantum/SpinS/HeisenbergEquilibrium.lean`, declaration
line 319).

- **Proved (axiom-free):** as with Theorem 4.26, the staggered order and
  field-dependent thermal-average observables it quantifies over are real
  definitions.
- **What the axiom statement literally asserts:** under the same conditions
  as Theorem 4.26 (antiferromagnetic Heisenberg model, `d ≥ 3`, `N ≥ 1`),
  bundling the *same* threshold `β₀` and function `q(β)` as Theorem 4.26,
  the staggered moment survives the iterated limit
  `lim_{h↓0} lim_{L↑∞} ⟨Ô_L^{(3)}⟩_{β,h}^L / L^d ≥ √(3 q(β))`, for every
  `β > β₀` (eq. (4.4.53)) — genuine symmetry breaking accompanying the
  long-range order.
- **Axiom reason (documented):** proved by Koma–Tasaki [34], extending
  Griffiths' [23] argument for commuting order operators; bundled with the
  same reflection-positivity / `d`-dim-intractable-at-scale class as
  Theorem 4.26, since it shares the same `β₀, q`.
- **Re-check condition:** would change under the same condition as
  Theorem 4.26 (a `d`-dimensional RP/IR-bound infrastructure plus a
  transcription of the Griffiths/Koma–Tasaki argument), since this entry's
  `β₀, q` are literally Theorem 4.26's.
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.
