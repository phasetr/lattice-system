---
layout: page
title: "Documented axioms: Tasaki Chapter 5"
permalink: /limitations/documented-axioms/chapter-05/
---

# Documented axioms: Tasaki Chapter 5

[Documented-axiom policy and entry index](/lattice-system/limitations/documented-axioms/)

<a id="entry-theorem-5-1"></a>

## Theorem 5.1 (off-diagonal long-range order of hard-core bosons at half filling)

**Tasaki §5.1-§5.2, Theorem 5.1** (eq. (5.2.5), pp. 135-139) is a
**documented axiom**, `tasaki_5_1_xy_odlro_half_filling`
(`LatticeSystem/Quantum/SpinS/BoseEinsteinCondensate.lean`, declaration
line 81).

- **Proved (axiom-free):** the spin-`1/2` XY Hamiltonian `xyHamiltonianS`
  (eq. (5.1.5), realized as the XXZ Hamiltonian at anisotropy `λ = 0` and
  single-ion term `D = 0`) and the staggered order operators it quantifies
  over are real definitions.
- **What the axiom statement literally asserts:** for the spin-`1/2` XY model
  (the `u ↑ ∞` hard-core boson model) on the `d`-dimensional hypercubic
  torus with `d ≥ 2`, at half filling (`Ŝ_tot^{(3)} = 0`), there is a
  constant `q₀ > 0` depending only on `d` such that every ground state `Φ_GS`
  exhibits ODLRO for sufficiently large even `L`:
  `⟨Φ_GS|(Ô_L^{(α)})²Φ_GS⟩/⟨Φ_GS|Φ_GS⟩/(L^d)² ≥ q₀`, for the two XY-plane
  staggered order operators (`α = 1, 2`) (eq. (5.2.5)).
- **Axiom reason (documented):** proved by Kennedy–Lieb–Shastry and
  Kubo–Kishi via the reflection-positivity method of Dyson–Lieb–Simon.
  Despite invoking `d`-dimensional reflection positivity, this statement is
  **uniform-in-`L` finite-dimensional** (like Theorems 4.6/4.8/4.9/4.11); it
  is a documented axiom because the `d`-dim RP/IR-bound proof technique is
  intractable at project scale (the existing RP infrastructure is
  1D-ring-only), **not** because the subject is infinite-volume. It returns
  to a prove-target if a `d`-dim RP/IR-bound infrastructure is ever built.
- **Re-check condition:** would change if a `d`-dimensional
  reflection-positivity / infrared-bound infrastructure is built in this
  repository and a math-before-code transcription of the
  Kennedy–Lieb–Shastry / Kubo–Kishi argument is completed.
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.

<a id="entry-theorem-5-2"></a>

## Theorem 5.2 (low-lying tower states of hard-core bosons, general `μ`)

**Tasaki §5.3, Theorem 5.2** (eq. (5.3.4), around p. 141) is a
**documented axiom**, `tasaki_5_2_bec_tower`
(`LatticeSystem/Quantum/SpinS/BoseEinsteinCondensate.lean`, declaration
line 193).

- **Proved (axiom-free):** the **half-filling** (`μ = 0`) kernel is proved
  axiom-free as the theorem `tasaki_5_2_bec_tower_half_filling`
  (`BoseEinsteinCondensateTower.lean`, predicate
  `IsBECTowerConstantsHalfFilling`), whose `#print axioms` is `propext`,
  `Classical.choice`, `Quot.sound` only; the chemical-potential Hamiltonian
  `xyChemicalPotentialHamiltonianS` and the tower-state constructor
  `towerState` are real definitions in both cases.
- **What the axiom statement literally asserts:** assuming the ground state
  of the chemical-potential XY Hamiltonian `Ĥ_μ` (eq. (5.3.2)) exhibits
  ODLRO with some `q₀ > 0` (Theorem 5.1), there are constants `C₁, C₂ > 0` —
  depending only on `d`, the density selected by `μ`, and `q₀` — such that
  the bosonic tower states `Γ_M` (`|M| ≤ C₁ L^{d/2}`) are nonvanishing and
  low-lying with cubic energy increment,
  `⟨Γ_M,Ĥ_μΓ_M⟩/⟨Γ_M,Γ_M⟩ ≤ E₀ + C₂|M|³/L^d` (eq. (5.3.4)).
- **Axiom reason (documented):** proved in Tasaki [21] (H. Tasaki,
  *Long-range order, "tower" of states, and symmetry breaking in lattice
  quantum systems*, J. Stat. Phys. **174**, 735-761, 2019). The
  general-`μ` statement stays a documented axiom because at `μ ≠ 0` a ground
  state has `Ŝ_tot^{(3)}Φ = s₀ ≠ 0`, so the reused half-filling variational
  bricks no longer close, and the general-`μ` bound rests on Tasaki
  [21]'s `d`-dimensional reflection-positivity/infrared machinery — the same
  RP-intractability-at-project-scale class as Theorem 5.1.
- **Re-check condition:** would change under the same condition as
  Theorem 5.1 (a `d`-dimensional RP/IR-bound infrastructure plus a
  transcription of the Tasaki [21] general-`μ` argument).
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.

<a id="entry-theorem-5-3"></a>

## Theorem 5.3 (U(1) symmetry-breaking states of hard-core bosons, general `μ`)

**Tasaki §5.3, Theorem 5.3** (eqs. (5.3.6)-(5.3.8), around p. 141) is carried
by two **documented axioms** in
`LatticeSystem/Quantum/SpinS/BoseEinsteinCondensate.lean` and
`.../BoseEinsteinCondensateCoherentConcentration.lean`:
`tasaki_5_3_bec_u1_ssb` (`BoseEinsteinCondensate.lean`, declaration line 421)
and `becMStar_ge_sqrt_twoQ`
(`BoseEinsteinCondensateCoherentConcentration.lean`, declaration line 112).

- **Proved (axiom-free):** the **half-filling** (`μ = 0`) kernel is
  discharged *conditionally* as the theorem `tasaki_5_3_bec_u1_ssb_half_filling`
  (`BoseEinsteinCondensateCoherentAssembly.lean`), whose `#print axioms` is
  `std3 + becMStar_ge_sqrt_twoQ` and which additionally requires an explicit
  `hRealizing` hypothesis (the Tasaki [66] uniform window-ratio
  concentration input); the U(1) coherent state constructor
  `becCoherentState` and the coherent-SSB constants predicate
  `IsBECCoherentSSBConstants` are real definitions.
- **What the axiom statements literally assert:** `tasaki_5_3_bec_u1_ssb`
  states that, if the slow-window cutoff `M_max(L)` diverges not too
  rapidly, the `U(1)` coherent state `Ξ_θ` (eq. (5.3.5)) fully breaks the
  phase symmetry — the order-operator density behaves as a classical planar
  vector of length `mStar` in direction `θ`, with vanishing fluctuation
  (eqs. (5.3.6)-(5.3.8)) — and `mStar ≥ √(2 q₀)`. `becMStar_ge_sqrt_twoQ`
  states the order-parameter lower bound `mStar ≥ √(2 q₀)` alone, for `mStar`
  **pinned** to its genuine value by `IsRealizingBECCoherentFamily`: the
  uniform window-ratio concentration forces every one-step ratio `r_M → mStar`
  in the slow window, ruling out the unsound free-parameter reading
  (`mStar := 0` would otherwise satisfy a `hFamily`-free statement while
  `q₀ > 0`).
- **Axiom reason (documented):** proved in Tasaki [21]/[66];
  `becMStar_ge_sqrt_twoQ` is the BEC half-filling counterpart of the `SU(2)`
  concentration axioms `orderSqMoment_ratio_le_mStarSq_family` and the
  `p̂`-mirror `mStar_eq_phat_ratio_limit` (Chapter 4 Lemma 4.15 entry): per
  the 2026-07-12 no-overreach boundary, the Tasaki [66] concentration
  mechanism is deferred with parity to those axioms rather than rebuilt. The
  general-`μ` statement `tasaki_5_3_bec_u1_ssb` stays a documented axiom for
  the same reason as Theorem 5.2 general-`μ`: at `μ ≠ 0` the reused
  half-filling variational bricks no longer close, and the general-`μ` bound
  rests on the same RP-intractability-at-project-scale class as Theorem 5.1.
- **Re-check condition:** would change (for `tasaki_5_3_bec_u1_ssb`) under
  the same condition as Theorem 5.1/5.2 general-`μ`; and (for
  `becMStar_ge_sqrt_twoQ`) when a math-before-code transcription of the
  Tasaki [66] concentration argument is completed with parity to the
  Chapter 4 Lemma 4.15 / Theorem 4.11 concentration axioms.
- **Tracking:** master tracker #4718; shares the "2026-07-12 no-overreach
  boundary" decision with the Chapter 4 Lemma 4.15 / Theorem 4.11 entry. No
  dedicated discharge issue exists or is to be opened while the re-check
  condition above is unmet.

<a id="entry-theorem-5-4"></a>

## Theorem 5.4 (symmetry breaking in coupled Bose–Einstein condensates)

**Tasaki §5.5, Theorem 5.4** (eqs. (5.5.5)-(5.5.6), around p. 148) is a
**documented axiom**, `tasaki_5_4_coupled_bec_ssb`
(`LatticeSystem/Quantum/SpinS/BoseEinsteinCondensate.lean`, declaration
line 496).

- **Proved (axiom-free):** the two-species coupled lattice `CoupledSite` and
  the inter-condensate correlation operators `coupledCrossCorrelation` /
  `coupledCrossCorrelationConj` it quantifies over are real definitions.
- **What the axiom statement literally asserts:** for two hard-core boson
  condensates on copies of the torus, weakly coupled by a tunneling
  Hamiltonian of strength `ε`, at fixed doubled half filling and assuming the
  single uncoupled system has ODLRO with parameter `q₀ > 0` (Theorem 5.1),
  and given a *supplied* family `Φ` of nonzero minimal-real-eigenvalue
  eigenvectors of the coupled Hamiltonian at half filling for every `ε > 0`
  and sufficiently large even `L` (`hΦ` — a hypothesis on the given family,
  not a proved uniqueness/existence conclusion), there exists an order
  parameter `m̃` with `√(2 q₀) ≤ m̃` such that
  `lim_{ε↓0} lim_{L↑∞} ⟨Φ^ε,â†_{(x,a)}â_{(x,b)}Φ^ε⟩/⟨Φ^ε,Φ^ε⟩ = m̃²e^{−iφ}`
  (eq. (5.5.5)) and the conjugate limit is `m̃²e^{+iφ}` (eq. (5.5.6)), stated
  soundly in eventual-`ε` form (outer `ε↓0`, inner `L↑∞`). The axiom does
  **not** name or bound an intermediate `mStar`; `m̃` is the only order
  parameter the statement introduces.
- **Axiom reason (documented):** proved in Tasaki [22] (H. Tasaki,
  *Spontaneous symmetry breaking in coupled Bose-Einstein condensates*,
  J. Stat. Phys. **178**, 379-391, 2019). Unlike
  Theorem 5.1, this is a **genuine iterated thermodynamic limit**
  `lim_{ε↓0} lim_{L↑∞}`: Tasaki states in a footnote that the existence of
  the limit itself is unproven (open in the source literature), so this
  falls under the open-conjecture exclusion of the
  externally-cited-theorem-must-be-proved policy, rather than being a
  tractable finite-dimensional cite-only case.
- **Re-check condition:** would change only if the existence of the
  `lim_{ε↓0} lim_{L↑∞}` iterated limit is established in the source
  literature (or independently) and a math-before-code transcription of the
  Tasaki [22] argument is completed.
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.
