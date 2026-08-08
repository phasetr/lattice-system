---
layout: page
title: "Roadmap history: P3 through Appendix A"
permalink: /history/roadmap/future-and-appendix/
---

# Roadmap history: P3 through Appendix A

> Historical implementation record normalized from the former roadmap table. Active work is governed by tracking Issues.

<!-- legacy-source:start:150:150 -->
## P3: CAR algebras, quasi-local C*-algebras, KMS states

Not started
<!-- legacy-source:end:150:150 -->

<!-- legacy-source:start:151:151 -->
## P4: Thermodynamic limit, phase transitions

Not started
<!-- legacy-source:end:151:151 -->

<!-- legacy-source:start:152:152 -->
## P5: Lattice QCD

Not started
<!-- legacy-source:end:152:152 -->

<!-- legacy-source:start:153:153 -->
## Appendix A (Tasaki Mathematical Appendices)

The book-order content after Chapter 11; foundations for the deferred Chapter-11 proof discharges
(frustration-free A.9/A.10, limit A.11/A.12, Perron–Frobenius A.17/A.18 — the last largely already
in `Math/PerronFrobenius*`/`CollatzWielandt*`). **Complete — A.1–A.28 all formalized in book order**
(Issues [#4205](https://github.com/phasetr/lattice-system/issues/4205) +
[#4224](https://github.com/phasetr/lattice-system/issues/4224), both closed; see the **status &
axiomatization policy** note below the Roadmap): **Theorem A.1 (Lie product formula)** `e^{A+B} =
lim_N (e^{A/N}e^{B/N})^N` **now proved (axiom-free)** (`Math/MatrixAnalysis/LieProduct.lean`,
`lieProductFormula` — mathlib has only the commuting case): generic `trotterProductFormula` in a
complete normed `ℝ`-algebra via exponential-series tail bounds (`‖e^X−1−X‖ ≤ ‖X‖²e^{‖X‖}` etc.) +
telescoping power estimate (`‖Cⁿ−Dⁿ‖ ≤ n·M^{n−1}·‖C−D‖`) + `O(s²)` product comparison + the exact
`n`-th-power identity, instantiated for matrices under the scoped operator norm;

- **Lemmas A.4** (Hermitian `Â` is `≥0` iff all eigenvalues `≥0`), **A.5** (`Â,B̂≥0 ⇒ Â+B̂≥0`),
  **A.6** (`B̂†B̂≥0`, and conversely every `Â≥0` is `Ĉ²` for a *unique* PSD square root `Ĉ=√Â` via
  `cfc Real.sqrt`, existence+uniqueness) **proved** (axiom-free, `Math/PosSemidef/Basics.lean`).
  **Theorem A.7** (Weyl monotonicity: Hermitian `Â≤B̂` ⇒ `i`-th sorted eigenvalue `Â.eigenvalues₀ i
  ≤ B̂.eigenvalues₀ i`) **now proved (axiom-free)** via the Courant–Fischer block/pigeonhole
  argument (`Math/MatrixAnalysis/CourantFischer.lean`: spectral Rayleigh-sum `re⟨x,Tx⟩=∑λᵢ‖⟨bᵢ,x⟩‖²`
  + block bounds + the top-`(i+1)`/bottom-`(card−i)` eigenspaces meeting by finrank pigeonhole;
  `EigenvalueMonotone.lean`). **Corollary A.8** (`Â≤B̂ ⇒ Tr e^Â ≤ Tr e^B̂`, eq A.2.31) **now proved
  (axiom-free)** (`Math/MatrixAnalysis/TraceExpMonotone.lean`: spectral mapping `Tr e^Â = Σ e^{a_j}`
  via `Matrix.exp_conj` + `exp_diagonal` + `trace_mul_cycle`, then A.7 Weyl + `Real.exp` monotone).
  **Lemmas A.9/A.10** (frustration-free Hamiltonian `Ĥ=Σĥⱼ`, `ĥⱼ≥εⱼ`: A.9 simultaneous eigenstate ⇒
  ground state at `Σεⱼ`; A.10 converse) **proved** (axiom-free, `FrustrationFree.lean`). **Lemma
  A.11** (`Â≥0 ∧ ⟨Φ|Â|Φ⟩=0 ⇒ ÂΦ=0`; `Â=B̂†B̂ ⇒ B̂Φ=0`; + angular-momentum corollary `Ĵ²Φ=0 ⇒
  Ĵ⁽ᵅ⁾Φ=0`) **proved** (axiom-free, `Math/PosSemidef/Kernel.lean`, over the existing
  `RayleighPosSemidefKernel`). **Theorem A.12** (`Ĥ_v=Ĥ₀+vV̂`, `V̂≥0`: `v↑∞` finite-energy
  eigenstate families converging to nonzero `Φ` satisfy the effective Schrödinger eq `P̂₀Ĥ₀Φ=EΦ` on
  `H₀=ker V̂`) **now proved (axiom-free)** (`EffectiveLimit.lean`, weak-form + Tendsto: the paired
  eigenvalue relation gives `v·⟨Φ_v|V̂|Φ_v⟩ = E_v‖Φ_v‖²−⟨Φ_v|Ĥ₀|Φ_v⟩`, the converging right side
  times `v⁻¹→0` kills the limiting quadratic form, Lemma A.11 kills `V̂Φ`; pairing with `ψ ∈ ker V̂`
  removes the `vV̂` term outright and the limit is the weak equation). **Appendix A.2 complete.**
  **§A.3 angular momentum**: **Lemma A.14** (su(2) ladder) — operator identity `Ĵ⁻Ĵ⁺=Ĵ²−Ĵ³(Ĵ³+1)`
  (eq A.3.7) + ladder non-vanishing (`−J≤M<J`, `Φ≠0` ⇒ `Ĵ⁺Φ≠0`) + raising **membership**
  (`Ĵ⁺Φ∈H_{J,M+1}`, via `[Ĵ³,Ĵ⁺]=Ĵ⁺` + `[Ĵ²,Ĵ⁺]=0`) + **lowering** direction (`Ĵ⁺Ĵ⁻=Ĵ²−Ĵ³(Ĵ³−1)` eq
  A.3.8, `Ĵ⁻Φ≠0` for `−J<M≤J`, `Ĵ⁻Φ∈H_{J,M−1}`) **proved** — A.14 fully done (axiom-free,
  `Math/AngularMomentum/Ladder.lean`). **Lemma A.15 (spin bound, part 1)**: norm identities
  `‖Ĵ±Φ‖²={J(J+1)−M(M±1)}‖Φ‖²` (eq A.3.9, Hermitian Ĵ^α) `angRaise/angLower_normSq` +
  `angMom_abs_le_J` (`−J≤M≤J`, i.e. `J−M,J+M≥0`) **proved** (axiom-free). **Lemma A.15
  (integrality)** + **Theorem A.13 (`J = n/2`)**: ladder-termination `raiseIter` (iterated `Ĵ⁺`)
  with `raiseIter_eigenspace`/`raiseIter_ne_zero` gives `J−M ∈ ℤ≥0` (`angMom_sub_mem_nat`); the
  gauge-reflected `(Ĵ¹,−Ĵ²,−Ĵ³)` gives `J+M ∈ ℤ≥0`, so `2J=(J−M)+(J+M)∈ℤ≥0`, i.e. `J=n/2`
  (`angMom_J_eq_half_nat`) **proved** (axiom-free, `Math/AngularMomentum/Quantization.lean`).
  **Theorem A.16 (SU(2)-multiplet degeneracy)**: for SU(2)-invariant `Ĥ` (`[Ĥ,Ĵᵅ]=0`), a joint
  energy eigenstate in `H_{J,M0}` yields nonzero same-energy companions in every `H_{J,J−k}`
  (`k≤2J`) — `ham_su2_multiplet` (energy `E` is ≥`(2J+1)`-fold degenerate), proved via raise-to-top
  + reflected-lowering ladder + `ham_mulVec_raiseIter` (axiom-free,
  `Math/AngularMomentum/Multiplet.lean`). **Theorem A.17 (spin-0/1-2 sector suffices)**: every
  energy eigenvalue of an SU(2)-invariant `Ĥ` has an eigenstate with `Ĵ³=0` or `Ĵ³=1/2` —
  `ham_eigenstate_spin_zero_or_half` (corollary of A.16+A.13; the lone simultaneous-diagonalization
  step `exists_joint_su2_energy_eigenstate` is **now proved (axiom-free)** via the generic common
  eigenvector of two commuting Hermitian operators on an invariant subspace
  (`Math/CommutingHermitianEigenvector.lean`: `exists_common_eigenvector_of_isHermitian_commute`),
  the Casimir `Ĵ²` being PSD and commuting with `Ĵ³`/`Ĥ`,
  `Math/AngularMomentum/SpinHalfSector.lean`). **Theorem A.18 (Perron–Frobenius, real symmetric)**:
  a real symmetric `M` with `(c·1−M)` irreducible (off-diag `≤0` + connectivity) has a nondegenerate
  lowest eigenvalue with a strictly positive eigenvector — `perronFrobenius_real_symmetric` (reuses
  the project's Collatz–Wielandt PF + eigenspace simplicity; the lowest-eigenvalue identification is
  the variational `|w|`-argument eq A.4.1), proved (axiom-free, `PerronFrobeniusSymmetric.lean`).
  **Theorems A.19/A.20 (polar + SVD)**: `matrix_polar_decomposition` (`A = W C`, `W` unitary, `C`
  PSD) and `matrix_singular_value_decomposition` (`A = U D V†`, `U,V` unitary, `D = diagonal d` with
  `d ≥ 0`) — **now proved (axiom-free)**: SVD built from the spectral theorem of `AᴴA`
  (`eigenvectorUnitary` `V`, eigenvalues `λ_i ≥ 0`, `d_i = √λ_i`), with the normalised images `u_i =
  d_i⁻¹·A v_i` extended to an orthonormal basis (`exists_orthonormalBasis_extension_of_card_eq`)
  giving `U`, and `A V = U D` columnwise; polar follows as `W = U Vᴴ`, `C = V D Vᴴ`
  (`Math/MatrixAnalysis/Decomposition.lean`). **Theorems A.21/A.22 (Wigner)**:
  `wignerAutomorphism_unitary` (linear ∗-automorphism of `M(H)` ⟹ `Γ(Â)=Û†ÂÛ`) +
  `wignerAutomorphism_antiunitary` (antilinear ⟹ `Û†Â̄Û`) + `wignerProjection` (rank-1-projection
  map preserving `Tr[P P′]` ⟹ (anti)unitary `V̂`) — documented axioms over `Matrix D D ℂ`
  (`WignerTheorem.lean`, Issue #4224). **Definition A.23 + Theorem A.24 (states / Banach–Alaoglu)**:
  `IsState` (weak-∗-continuous `φ : WeakDual ℂ A` with `φ 1 = 1`, `0 ≤ φ(a†a)`) over an abstract
  unital C*-algebra + `stateSpace_isCompact` (state space weak-∗ compact, documented axiom) —
  `Math/CStarAlgebra/State.lean`. **Definitions A.25/A.27 + Theorem A.26 (ground states)**: dynamics
  modelled by a derivation `δ=[Ĥ,·]`; `IsGroundState` (`0 ≤ ω(a†·δa)`) + `HasNonzeroGap` (`γ>0`,
  `ω(a†δa) ≥ γω(a†a)` on `ω(a)=0`) + `groundState_variational` (ground state ⟺ `ω(Ĥ_L)` least over
  states agreeing outside Λ_L, documented axiom) — `Math/CStarAlgebra/GroundState.lean`. **Theorem
  A.28 (GNS construction)**: `gns_construction` — every state `ρ` on a C*-algebra has a GNS triple
  `(H_ρ, π_ρ, Ω_ρ)` (`∗`-representation `π : A →⋆ₐ[ℂ] (H→L H)` + cyclic `Ω`) with `ρ(Â)=⟨Ω,π(Â)Ω⟩`
  and `{π(Â)Ω}` dense; documented axiom (mathlib has the GNS machinery),
  `Math/CStarAlgebra/GNS.lean`. **§A.6–§A.7 (Wigner / states / ground states / GNS) complete →
  Appendix A complete.** Prove-first where mathlib supports, axiomatize-first for the heavy analytic
  results, strict book order (see the status & axiomatization-policy note below).
<!-- legacy-source:end:153:153 -->
