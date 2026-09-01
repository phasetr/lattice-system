---
layout: page
title: "Documented axioms: Tasaki Chapter 4"
permalink: /limitations/documented-axioms/chapter-04/
---

# Documented axioms: Tasaki Chapter 4

[Documented-axiom policy and entry index](/lattice-system/limitations/documented-axioms/)

<a id="entry-theorem-4-2"></a>

## Theorem 4.2 support (Shastry: staggered-field energy gain)

**Tasaki §4.1, Theorem 4.2** (eqs. (4.1.9)-(4.1.10), pp. 76-77) rests on one
**documented axiom**, `shastryEnergyGain`
(`LatticeSystem/Quantum/SpinS/ShastryNoSSBReduction.lean`, declaration line 158).

- **Proved (axiom-free):** the whole reduction chain that consumes it. For
  Tasaki's field family `Ĥ_h = Ĥ − h Ô_L` (eq. (3.4.19), p. 69) the abstract
  ground energy `chainGroundEnergy` is even (`chainGroundEnergy_neg`), concave
  (`chainGroundEnergy_concave`), maximised at `h = 0`
  (`chainGroundEnergy_le_zero_field`) and obeys the sandwich
  `0 ≤ E(0) − E(h) ≤ h⟨Ô⟩_h ≤ E(0) − E(2h)` (`chainGroundState_order_mean_sandwich`)
  — all in `ReversalSymmetricGroundEnergy.lean`. The ring instance adds
  `staggeredFieldChainHamiltonianS_isHermitian` and `Θ Ĥ_h Θ = Ĥ_{−h}`
  (`staggeredFieldChainHamiltonianS_conj_manyBodyReversalS`). Feeding the axiom
  into `shastry_no_symmetry_breaking_1d_of_energy_gain` (same file, line 182) makes
  `shastry_no_symmetry_breaking_1d` (line 264) a `theorem`, statement unchanged.
- **This records where the axiom now sits; it is not a discharge and not a policy
  change.** `#print axioms shastry_no_symmetry_breaking_1d` names
  `shastryEnergyGain`, which is **equivalent in strength to an `L`-uniform form of
  Theorem 4.2**: the capstone derives Theorem 4.2 from it, and conversely the sandwich
  `E_L(0) − E_L(η) ≤ η⟨Ô⟩_η` turns a per-site staggered-moment bound back into an
  energy-gain bound of the same order. What Tasaki does not prove is as unproved as
  before; the class and override recorded below are unchanged.
- **What the axiom statement literally asserts:** writing
  `E_L(c) = hermitianMinEigenvalue (Ĥ_c)` for the minimum eigenvalue of
  `staggeredFieldChainHamiltonianS L c N` (eq. (4.1.9)): for every `ε > 0` there is
  `η₀ > 0` such that for each `0 < η < η₀` there is a size threshold `L₀` beyond
  which `E_L(0) − E_L(2η) ≤ ε · η · L`. The linear shape is the weakest the reduction
  needs (a `C·η²·L` bound would imply it); the expected `≍ L·η^{4/3}` response of the
  gapless half-integer chains, not formalised here, is why it is not strengthened.
- **Why the `∃ L₀` is part of the statement:** a bare `∀ L` would be false at small
  rings for every `N ≥ 1` (at `N = 0` it is true), hence over-quantified. At `L = 1`
  the coupling degenerates to the self-loop `J 0 0 = 1` and `E_1(0) − E_1(2η) = η·N`
  exactly, exceeding `ε·η·1` for every `ε < N`; at `L = 3`, `N = 1` the frustrated
  triangle gives `E_3(0) − E_3(2η) ≥ (5/3)·η`, exceeding `ε·η·3` for every `ε < 5/9`.
  Both are hand computations, not Lean witnesses, and both are `O(1)` effects the
  factor `L` absorbs once `L` is large — as is the wrap-around sign defect of odd
  rings. `N = 0` and `L = 0` are *not* excluded and hold outright; the declaration's
  doc comment has the full case-by-case derivation.
- **Axiom reason (documented):** Tasaki §4.1 footnote 3 (p. 76) reports
  Shastry's original argument (B. S. Shastry, *J. Phys. A* **25**, L249,
  1992) and its rigorous formulation in Tanaka–Takeda–Idogaki (*J. Magn.
  Magn. Mater.* **272-276**, 908, 2004) [63], both via one-dimensional
  reflection positivity. Per the 2026-07-05 policy override
  (externally-cited theorems the book merely quotes must still be proved,
  not deferred as external-cite-only), this is **not** classified as a
  won't-do citation. It belongs to its own **"1D-ring RP infrastructure
  incomplete"** class, distinct from Theorem 5.1's "`d`-dimensional RP/IR-bound
  intractable at project scale" class below: Theorem 5.1 needs a
  `d`-dimensional reflection-positivity infrastructure the project does not
  have and is not building, whereas this axiom needs exactly the 1D-ring
  reflection-positivity / Gibbs-decomposition infrastructure that issue
  #4777 scoped; #4777 closed (2026-07-11) without completing that
  infrastructure or discharging the axiom, and no successor tracking issue is
  currently open.
- **Re-check condition:** would change once 1D-ring reflection-positivity
  infrastructure (1D-ring Gibbs decomposition) is built and a math-before-code
  transcription of the Shastry / Tanaka–Takeda–Idogaki argument on top of it
  discharges the scalar `shastryEnergyGain` inequality.
- **Tracking:** master tracker #4718; Issue #4777 recorded and then closed
  (2026-07-11) this axiom's 1D-ring RP-infrastructure scoping without
  discharging it. No successor discharge issue exists or is to be opened
  while the re-check condition above is unmet.

<a id="entry-corollary-4-3-support"></a>

## Corollary 4.3 support (Shastry staggered susceptibility bound)

**Tasaki §4.1, Corollary 4.3** (eq. (4.1.11), p. 77, with footnotes 3 (p. 76)
and 9 (p. 83)) rests on one **documented axiom**,
`shastry_staggered_susceptibility_bound`
(`LatticeSystem/Quantum/SpinS/NoLongRangeOrder1D.lean`, declaration line 64).

- **Proved (axiom-free):** Corollary 4.3 itself, `no_long_range_order_1d`
  (`NoLongRangeOrder1D.lean:109`), is a genuine **theorem**, obtained by
  feeding this axiom as the single quantitative input into the conditional
  reduction `no_long_range_order_1d_of_susceptibility`
  (`NoLongRangeOrderConditional.lean:37`); only the susceptibility estimate
  below remains axiomatized.
- **What the axiom statement literally asserts:** for the zero-field
  one-dimensional spin-`S` antiferromagnetic Heisenberg ring on an **even**
  number `L ≥ 2` of sites, there is a size-uniform constant `C ≥ 0` such that
  every normalized ground state `Φ` admits a potential `y` for `ÔΦ` (i.e.
  `(Ĥ − E₀) y = ÔΦ`) with static staggered susceptibility `Re⟨y, ÔΦ⟩ ≤ C·L`
  (physically `χ(k*) = L · f_L^{(-1)}(k*)` at the antiferromagnetic wavevector
  `k* = π`). Restricted to even `L` because only bipartite rings have a
  balanced staggered sublattice (`Σ_x ε_x = 0`), which is what makes the
  ground state an SU(2)-singlet with `⟨Φ, ÔΦ⟩ = 0` and hence `ÔΦ` orthogonal
  to the ground space, so the resolvent potential `y` genuinely exists; odd
  rings lie outside Tasaki's §4.1 setting.
- **Axiom reason (documented):** Tasaki's footnote 9 (§4.1, p. 83) singles out
  exactly this bound on `f_L^{(-1)}(k*)` as "the only nontrivial part that
  requires some hard analysis," deferring it to Shastry's original bound
  (B. S. Shastry, *J. Phys. A: Math. Gen.* **25**, L249, 1992) and its
  rigorous formulation in Tanaka–Takeda–Idogaki (*J. Magn. Magn. Mater.*
  **272-276**, 908, 2004) [63], cited by Tasaki's footnote 3 (p. 76), via a
  massive-Green-function / inverse-Fourier reflection-positivity analysis
  with `O(L)` control of the `k* = π` singularity. As with Theorem 4.2 above,
  per the 2026-07-05 policy override this is classified in the same
  "1D-ring RP infrastructure incomplete" class (not Theorem 5.1's
  "`d`-dimensional RP/IR-bound intractable" class, and not an
  external-cite-only deferral): it needs the 1D-ring RP/Gibbs-decomposition
  infrastructure issue #4777 scoped; #4777 closed (2026-07-11) without
  completing that infrastructure or discharging this axiom, and no successor
  tracking issue is currently open. It returns to a discharged theorem once
  that infrastructure is built.
- **Re-check condition:** would change once 1D-ring reflection-positivity
  infrastructure (1D-ring Gibbs decomposition) is built and a math-before-code
  transcription of the Shastry / Tanaka–Takeda–Idogaki susceptibility
  estimate on top of it is finished.
- **Tracking:** master tracker #4718; Issue #4777 recorded and then closed
  (2026-07-11) this axiom's 1D-ring RP-infrastructure scoping without
  discharging it. No successor discharge issue exists or is to be opened
  while the re-check condition above is unmet.

<a id="entry-lemma-4-15-theorem-4-11-support"></a>

## Lemma 4.15 and Theorem 4.11 support (order-parameter concentration estimates)

Three **documented axioms** record the Tasaki [66] volume-uniform
concentration mechanism underlying Tasaki §4.2.2 Lemma 4.15 (eq. (4.2.38)) and
the still-open Conjecture 4.12 that Theorem 4.11 (eq. (4.2.23)) would need for
an unconditional equality:

- `mStar_eq_phat_ratio_limit` (`LatticeSystem/Quantum/SpinS/OrderOperatorAlgebra.lean`,
  declaration line 812) — the `p̂`/`U(1)` mirror.
- `orderSqMoment_ratio_le_mStarSq` (`LatticeSystem/Quantum/SpinS/AndersonTowerOrderSqConcentration.lean`,
  declaration line 56) — the `ô²`/`SU(2)` mirror, conditional on the explicit
  hypothesis `IsConjecture412Equality` (never asserted true).
- `orderSqMoment_ratio_le_mStarSq_family` (same file, declaration line 111) —
  the `n = 0` instance of the same mirror, `hFamily`-pinned and
  `Conjecture 4.12`-independent (this is the axiom Theorem 4.11's proved
  "easy half" consumes).

- **Proved (axiom-free):** the surrounding realizing-family machinery
  (`IsRealizingTanakaGroundStateFamily`, the base-ratio log-convexity squeeze
  `orderSqMoment_baseRatio_tendsto`) and the finite-volume order operators
  they quantify over are real definitions, not axioms.
- **What the axiom statements literally assert:** `mStar_eq_phat_ratio_limit`
  states that for a realizing ground-state family `Φ` with exact staggered
  moment `mStar` and LRO limit `q₀`, the bare `p̂`-moment ratio has iterated
  limit `lim_n liminf_L ⟨p̂^{n+1}⟩/⟨p̂^n⟩ ≥ (mStar)²`, together with the bound
  `√(2 q₀) ≤ mStar` (eq. (4.2.39)). `orderSqMoment_ratio_le_mStarSq` states
  the `limsup`-upper direction `∀ n ε, eventually in L, s_n < (mStar)² + ε`
  for the `V²`-normalized `ô²`-moment ratio `s_n`, conditional on
  `IsConjecture412Equality mStar qStar` (`hconj`). Dropping `hconj` while
  leaving `mStar` free would be **unsound** (`mStar := 0` with a genuine LRO
  family makes the claimed bound false), so
  `orderSqMoment_ratio_le_mStarSq_family` instead pins `mStar` to the true
  order parameter via `IsRealizingTanakaGroundStateFamily` and states only the
  `hconj`-free `n = 0` instance, `s₀ ≤ (mStar)² + ε` eventually — the "easy
  half" (`(mStar)² ≥ 3 q₀`) of Theorem 4.11, not the equality `(mStar)² = 3 q₀`
  that Conjecture 4.12 would supply.
- **Axiom reason (documented):** Tasaki §4.2.2 eq. (4.2.40) states the `p̂`-ratio
  concentration is "elementary, proof omitted; see [66]" (H. Tasaki, *Long-range
  order, "tower" of states, and symmetry breaking in lattice quantum systems*,
  J. Stat. Phys. **174**, 735-761, 2019), and eqs. (4.2.59)-(4.2.61) instruct
  the reader to repeat the same argument for the `ô²` field. Per the
  2026-07-12 no-overreach boundary decision, the `ô²` mirror is deferred with
  exact parity to the `p̂` axiom rather than rebuilding the multi-PR [66]
  concentration machinery; Conjecture 4.12 is kept an explicit hypothesis,
  never asserted.
- **Re-check condition:** would change only if a math-before-code
  transcription of the Tasaki [66] concentration argument is completed
  for both the `p̂` and `ô²` fields (proving, not assuming, the volume-uniform
  moment-ratio limits); Conjecture 4.12 itself would additionally require an
  independent proof of the matching equality, which is a strictly stronger,
  still-open statement.
- **Tracking:** master tracker #4718; two of the three axioms
  (`orderSqMoment_ratio_le_mStarSq` and `orderSqMoment_ratio_le_mStarSq_family`,
  both in `AndersonTowerOrderSqConcentration.lean`) share the "2026-07-12
  no-overreach boundary" decision recorded in their doc comments;
  `mStar_eq_phat_ratio_limit`'s doc comment (`OrderOperatorAlgebra.lean`)
  does not carry that marker. No dedicated discharge issue exists or is to be
  opened while the re-check condition above is unmet.

<a id="entry-theorem-4-20"></a>

## Theorem 4.20 (infinite-volume ground states `ω₀`, `ω_n`)

**Tasaki §4.3, Theorem 4.20** (eqs. (4.3.7)-(4.3.10), around p. 115) is carried
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
  density of the model (`IsGroundStateEnergyDensity`,
  `InfiniteVolumeGroundState.lean:188`, itself an uninterpreted documented
  predicate) — that there exists a state `ω₀`
  (`WeakDual ℂ A`) that is an infinite-volume ground state at energy density
  `εGS` (`IsInfiniteVolumeGroundState`) with vanishing single-site
  magnetization `ω₀(Ŝ_x^{(α)}) = 0` (eq. (4.3.9)). The axiom itself is a bare
  existential; it does **not** encode the `L↑∞` limit construction
  (eq. (4.3.7)) that motivates it — the module doc comment describes that
  construction informally, but only the existence and the two stated
  properties are part of the formal statement. `theorem_4_20_omegaN` states
  that, additionally assuming staggered long-range order with parameter
  `mStar > 0` (`HasStaggeredLRO`, `InfiniteVolumeGroundState.lean:198`, also
  an uninterpreted documented predicate), for every unit direction `n` there
  exists a state `ω_n`,
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

<a id="entry-section-4-3-thermodynamic-limit-bridge"></a>

## §4.3 thermodynamic-limit bridge (box AFM model on `ℤᵈ`)

Two **documented axioms** and one **documented predicate** connect the
concrete finite-volume antiferromagnetic Heisenberg model on the hypercubic
boxes `Λ_n ⊂ ℤᵈ` to the abstract §4.3 infinite-volume system:

- `boxGroundEnergyDensityS_tendsto`
  (`LatticeSystem/Quantum/SpinS/HypercubicBoxModel.lean`, declaration
  line 151) — existence of the `n → ∞` limit of the box ground-state energy
  density (Tasaki eq. (4.3.4)).
- `IsAFMThermodynamicLimit` (`LatticeSystem/Quantum/SpinS/HypercubicBoxThermodynamicLimit.lean`,
  declaration line 66) — the uninterpreted predicate "`S` is the `L↑∞` limit
  of the box AFM model", kept conditional rather than a construction.
- `afmThermodynamicLimit_energyDensity` (same file, declaration line 76) —
  under `IsAFMThermodynamicLimit`, the abstract ground-state energy density
  of `S` equals the concrete finite-box limit (Tasaki eq. (4.3.4)).

- **Proved (axiom-free):** the box AFM Hamiltonian
  `boxAFMHeisenbergHamiltonianS` and the box ground-energy-density observable
  `boxGroundEnergyDensityS` (`HypercubicBoxModel.lean`) are real definitions;
  the named limit `boxGroundEnergyDensitySLimit` and the fact that it *is*
  the limit (`boxGroundEnergyDensityS_tendsto_limit`) are proved from the
  first axiom. Given the two axioms above, the existence of an
  infinite-volume ground state for the box model's thermodynamic limit
  (`afmThermodynamicLimit_exists_omega0`) is a **proved theorem**, assembled
  from `theorem_4_20_omega0`.
- **What the axiom statements literally assert:**
  `boxGroundEnergyDensityS_tendsto` states that for `0 < d` and `0 < N`, the
  sequence of box ground-state energy densities `boxGroundEnergyDensityS d n N`
  converges as `n → ∞` to some limit `εGS`; the limit's existence is
  axiomatized (the deep analytic/thermodynamic-limit content), not its
  identity. `IsAFMThermodynamicLimit S N` is a bare uninterpreted proposition
  relating an abstract `InfiniteSpinSystem S` to the concrete box model at
  spin `N/2`; it asserts nothing and makes the bridge genuinely conditional.
  `afmThermodynamicLimit_energyDensity` states that, given
  `IsAFMThermodynamicLimit S N`, the abstract predicate
  `IsGroundStateEnergyDensity S (boxGroundEnergyDensitySLimit d N)` holds,
  i.e. the concrete box limit is the correct value to feed into Theorem 4.20.
- **Axiom reason (documented):** the existence of the finite-box
  thermodynamic limit and the identification of an abstract infinite-volume
  system with that concrete limit are genuine operator-algebraic /
  thermodynamic-limit content, the same policy class as Theorem 4.20 and
  Appendix A.21-A.28.
- **Re-check condition:** would change only when a real (non-uninterpreted)
  construction of the quasi-local C*-algebra inductive limit exists in this
  repository, strong enough to both prove the box energy-density limit and
  identify a concrete `InfiniteSpinSystem` instance satisfying
  `IsAFMThermodynamicLimit` for the box model.
- **Tracking:** master tracker #4718; Issue #4564 recorded the infinite-volume
  foundation this bridge builds on.
  No dedicated discharge issue exists or is to be opened while the re-check
  condition above is unmet.

<a id="entry-theorem-4-22"></a>

## Theorem 4.22 (no SSB and exponential clustering in one dimension)

**Tasaki §4.4, Theorem 4.22** (eqs. (4.4.5)-(4.4.6), around p. 119, with
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

**Tasaki §4.4, Theorem 4.23** (eqs. (4.4.7)-(4.4.8), around pp. 119-120) is a
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

<a id="entry-theorem-4-24"></a>

## Theorem 4.24 (improved Hohenberg–Mermin–Wagner theorem)

**Tasaki §4.4, Theorem 4.24** (eq. (4.4.22), around p. 124, with footnote 48)
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

**Tasaki §4.4, Theorem 4.25** (eqs. (4.4.23)-(4.4.24), around p. 125) is a
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

**Tasaki §4.4, Theorem 4.26** (eq. (4.4.52), around p. 130) is a
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

**Tasaki §4.4, Theorem 4.27** (eq. (4.4.53), around p. 131) is a
**documented axiom**, `theorem_4_27_griffiths_koma_tasaki_ssb`
(`LatticeSystem/Quantum/SpinS/HeisenbergEquilibrium.lean`, declaration
line 319).

- **Proved (axiom-free):** as with Theorem 4.26, the staggered order and
  field-dependent thermal-average observables it quantifies over are real
  definitions.
- **What the axiom statement literally asserts:** under the same conditions
  as Theorem 4.26 (antiferromagnetic Heisenberg model, `d ≥ 3`, `N ≥ 1`), a
  single `∃ β₀, ∃ q` bundles **two** conjuncts sharing that `β₀, q`: (i) the
  Theorem 4.26 long-range-order bound itself,
  `⟨(Ô_L^{(α)}/L^d)²⟩_{β,0}^L ≥ q(β)` for every axis `α` and every `β > β₀`
  (eq. (4.4.52)), and (ii) the staggered moment surviving the iterated limit,
  `lim_{h↓0} lim_{L↑∞} ⟨Ô_L^{(3)}⟩_{β,h}^L / L^d ≥ √(3 q(β))`, for every
  `β > β₀` (eq. (4.4.53)) — genuine symmetry breaking accompanying the
  long-range order. The relationship is two-level: **within** Theorem 4.27
  itself the LRO conjunct (i) and the SSB conjunct (ii) share the *same*
  `β₀, q` witnesses (the Lean doc comment states this explicitly); **across**
  Theorem 4.26 and Theorem 4.27 the two axioms are logically independent —
  `theorem_4_26_staggered_lro` and `theorem_4_27_griffiths_koma_tasaki_ssb`
  each existentially quantify their own `β₀, q`, and nothing forces the
  witness used by 4.26 to coincide with the one inside 4.27's shared pair,
  even though both are read together as one long-range-order-plus-SSB
  package at sufficiently low temperature in `d ≥ 3`.
- **Axiom reason (documented):** proved by Koma–Tasaki [34], extending
  Griffiths' [23] argument for commuting order operators; the same
  reflection-positivity / `d`-dim-intractable-at-scale class as
  Theorem 4.26.
- **Re-check condition:** would change under the same condition as
  Theorem 4.26 (a `d`-dimensional RP/IR-bound infrastructure plus a
  transcription of the Griffiths/Koma–Tasaki argument).
- **Tracking:** master tracker #4718. No dedicated discharge issue exists or
  is to be opened while the re-check condition above is unmet.
