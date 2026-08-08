---
layout: page
title: "Roadmap history: P2, part 1"
permalink: /history/roadmap/p2-part-01/
---

# Roadmap history: P2, part 1

> Historical implementation record normalized at semicolon-delimited bold milestones. Active work is governed by tracking Issues.

<!-- legacy-source:start:149:149 -->
## P2: Finite-volume Hubbard / BCS

- In progress (single-mode CAR algebra; multi-mode Jordan–Wigner backbone: JW string + multi-mode
  `c_i`, `c_i†` definitions and Hermiticity, `c_0` reductions, full on-site CAR `c_i² = 0`, `(c_i†)²
  = 0`, `{c_i, c_i†} = 1`, adjoint `(c_i)ᴴ = c_i†`, JW string idempotent `J² = 1`, site-occupation
  number operator `n_i` with Hermiticity and idempotency;
- **full cross-site CAR algebra `{c_i, c_j} = 0`, `{c_i†, c_j†} = 0`, `{c_i, c_j†} = 0`, `{c_i†,
  c_j} = 0` for every `i < j`** (and the abstract general-`Λ` cross-site CAR `{c_i, c_j} = {c_i†,
  c_j†} = {c_i, c_j†} = {c_i†, c_j} = 0` for `i ≠ j` in `Fermion/JWAbstractCrossSite.lean`, plus the
  **smeared** anticommutators `{Ĉ(φ), Ĉ†(ψ)} = (Σ_x φ_x ψ_x)·1` and vacuum-killing `Ĉ(φ)|Φvac⟩ = 0`
  in `Fermion/JordanWigner/SmearedOperators.lean`, and `{Ĉ†(φ), Ĉ†(ψ)} = {Ĉ(φ), Ĉ(ψ)} = 0` in
  `Fermion/JordanWigner/SmearedCAR.lean` — the algebraic foundations behind the now axiom-free
  Tasaki Lemma 9.1, Issue #4593);
- **Hubbard chain (open + periodic BC), Hermiticity + full Gibbs companion family**;
- **U(1)×U(1) spin symmetry: `[N_↑, H] = [N_↓, H] = [S^z_tot, H] = 0` (Tasaki §9.3.3)**;
- **full SU(2) spin symmetry: `[Ŝ^+_tot, H] = [Ŝ^-_tot, H] = 0` (Tasaki §9.3.3)**;
- **all-up-spin state `hubbardAllUpState`: complete kinetic/interaction sector; Casimir `(Ŝ_tot)²`;
  eigenvalue `S_max(S_max+1)`; Definition 11.1 `isSaturatedFerromagnet` (Tasaki §11.1.1 / eq.
  (10.1.5))**;
- **Proposition 11.2** (`hubbard_proposition_11_2`, PROVED, `HubbardFerromagnetismStructure.lean`,
  Issue #4599, PR #4600): for a genuine half-filling ground energy `E₀` of the Hubbard model with
  Hermitian hopping (`hJ`: `star (t i j) = t j i`) and real `U` (`hU`) (nonempty `N+1`-electron
  eigenspace `hne`, minimal `hmin` in real part), if the model is ferromagnetic there (`hferro`:
  every ground state is Ŝ²-max at `S_max=(N+1)/2`), then the ground eigenspace
  `hubbardEigenspaceAtFilling E₀` (eigenspace at `E₀` ∩ `N+1`-electron sector, no hard-core
  constraint) is the `(N+2)`-fold maximal-spin multiplet (Tasaki eq. (11.1.4)) — discharged
  axiom-free: `finrank = N+2` via `le_antisymm` (lower bound = the all-up SU(2) lowering tower
  `highestWeight_spinMultiplet_general`; upper bound = all `N+2` Ŝ³-weight blocks equal-dim by
  both-direction ladder injectivity = the 1-dim top block), the max-spin conjunct being `hferro`
  itself; `hJ`/`hU` added for `Ŝ⁻`-invariance (sound, physical) — E₀ pinned to a real ground energy
  for soundness. **Theorem 11.3** (`hubbard_theorem_11_3`, PROVED, `HubbardImpossibilityLowU.lean` +
  `HubbardImpossibilityLowUVariational.lean` + `HubbardImpossibilityLowUVariationalCore.lean`, Issue
  #4599, PR #4601): impossibility of ferromagnetism for small U — for Hermitian hopping `t` with
  single-particle energies `hubbardSingleParticleEnergies` (= `ht.eigenvalues`) and Fermi gap
  `hubbardFermiGap` (= max ε − min ε, the completely-filled-band specialisation of `ε_N − ε_1`), for
  a pinned genuine ground energy `E₀` (nonempty `hne` + minimal `hmin` at half filling N+1) and `0 ≤
  U < hubbardFermiGap`, the ground states are NOT all max-spin (`¬ ∀ v ∈ hubbardEigenspaceAtFilling
  E₀, Ŝ²v = max•v`) — negating the *pinned* property (not the vacuous `isSaturatedFerromagnet`) for
  soundness; Tasaki variational trial state (11.1.6). **Theorem 11.4** (`hubbard_theorem_11_4`,
  AXIOM, `HubbardImpossibilityLowDensity.lean`, Issue #4477): impossibility at low densities — for
  `d>2`, translation-invariant Hermitian hopping with ascending single-particle spectrum `ε` obeying
  band condition (11.1.8) `hubbardBandCondition` (ε_n−ε_1 ≥ c·((n−n₀)/|Λ|)^{2/d}), a size-uniform
  threshold `ρ₁>0` below which the pinned ground states (`hubbardEigenspaceAt … E₀ Ne`) are NOT all
  max-spin for any U≥0; d>2 explicit (false in d=1), E₀ pinned + genuine transitive translation σ +
  nontrivial 2≤Ne for soundness (Roth/Gutzwiller proof deferred). **Lemma 11.10**
  (`tasaki_lemma_11_10`, **DISCHARGED axiom-free**, `TasakiFlatBandBasisLemma.lean`, Issue #4477):
  the decorated-lattice localized states {α_p}_{p∈E} (metallic) ∪ {β_u}_{u∈I} (oxygen) form a basis
  of the single-electron space — two orthogonal linearly-independent families with |E|+|I|=|Λ| span
  ⊤ (via `isOrtho_span`+`finrank_sup_add_finrank_inf_eq`+`finrank_euclideanSpace`). **Lemma 11.14**
  (`finrank_eigenspace_gram_eq` in `Math/GramEigenspaceCorrespondence.lean`, **DISCHARGED
  axiom-free**, Issue #4477): the Gram matrices T=SᴴS and T̃=SSᴴ have identical positive eigenvalues
  with multiplicities — for λ≠0 the λ-eigenspaces have equal finrank (the injection φ↦Sφ, applied to
  S and Sᴴ); generic SVD fact placed in Math/ by topic per the no-textbook-dir policy. The
  §11.4/§11.5 results 11.4, 11.18, 11.19, Lemmas 11.22, 11.23, 11.25 and Theorem 11.27 are recorded
  as documented axioms with faithful, sound statements, to be discharged in future work; Theorems
  11.8 and 11.13 are stated by Tasaki without proof and remain axioms. **Chapters 3–10 backfill
  STARTED (Issue #4485, book order, infinite systems in scope): Theorem 3.1** (Horsch–von der
  Linden, §3.4, `horsch_vonderLinden_lowLying` in `Quantum/HorschVonderLinden.lean`, **DISCHARGED
  axiom-free**): a normalized trial state orthogonal to the ground eigenvector with Rayleigh energy
  ≤ E₀+δ yields a low-lying energy eigenstate (j≠i₀, orthogonal to the ground eigenvector; possibly
  another ground state if degenerate, as Tasaki notes) with E₀ ≤ E_j ≤ E₀+δ — the finite-dim core
  via the spectral/Rayleigh expansion (rayleighOnVec H Γ = Σ_j‖w_j‖²E_j, min-over-support); the
  C·L^{−d} bound from long-range order is the application context — a Ch.11 book-order backfill;
- **SU(2) algebra: `[Ŝ^z, Ŝ^-] = -Ŝ^-`, eigenvalue preservation and decrement by `Ŝ^-` (Tasaki
  §9.3.3, §11.1.1)**;
- **Nagaoka hard-core subspace: `hubbardHardcoreSubspace`, same-site double-occupancy vanishing, and
  `H_int` vanishing on the subspace (unnumbered infrastructure for Theorems 11.5 and 11.7; Tasaki
  1st ed., §11.2, pp. 381-388)**;
- **Nagaoka hard-core projection: `hubbardHardcoreProjection = ∏_i (1 - n_{i,↑} n_{i,↓})`,
  idempotent, Hermitian, fixing hard-core vectors and projecting onto the no-double-occupancy
  subspace**;
- **Nagaoka one-hole hard-core basis states `|Φ_{x,σ}⟩` (eq. (11.2.3)): definition,
  no-double-occupancy membership, projection-fixed, orthonormality**;
- **one-hole hard-core sector spanned by the basis states (fn. 8): surjectivity of the `(x,σ)`
  parametrization onto one-hole hard-core configurations and `H_hc^N = span{|Φ_{x,σ}⟩}`**;
- **Nagaoka effective Hamiltonian `Ĥ_eff = P̂_hc H P̂_hc`: Hermiticity, `U→∞` reduction to projected
  hopping on the hard-core sector, range in the hard-core subspace**;
- **Tasaki ordered-creation basis (eq. (11.2.3)): `|Φ_{x,σ}⟩ = ĉ_{x,↑} (∏_y ĉ†_{y,σ̄_y}) |vac⟩`
  proven equal to a signed computational basis vector `ε • basisVec(hubbardOneHoleConfig)` via a
  strictly-sorted ordered-creation fold lemma, with orthonormality inherited from `basisVec`;
  uniform-sign hole-filling action (eq. (11.2.4)): `ĉ†_{(x,s)} ĉ_{(z,s)} |Φ_{x,σ}⟩ = -|Φ_{z,
  σ_{z→x}}⟩` with the explicit basis sign `ε = (-1)^x`, the four fermion signs combining to the
  uniform `-1` since the parity exponent `2(x+z)-1` is odd; off-diagonal effective-Hamiltonian
  matrix element (eq. (11.2.5)): `⟨Φ_{y,τ}|Ĥ_eff|Φ_{x,σ}⟩ = -t_{x,y}·[τ=σ_{y→x}]` for `x ≠ y`, only
  the hole-filling channel surviving the hard-core projection;
- **weak Nagaoka spin multiplet (Theorem 11.5 core): SU(2) ladder algebra `[Ŝ^+,Ŝ^-]=2Ŝ^z`,
  `[(Ŝ_tot)²,Ŝ^-]=0`, `Ŝ^+Ŝ^-=(Ŝ_tot)²-Ŝ^z(Ŝ^z-1)`, and `weakNagaoka_spinMultiplet` — a
  highest-weight ferromagnetic GS eigenvector generates `N+1=2S_max+1` linearly independent
  degenerate ground states with `S_tot=S_max=N/2`;
- **Tasaki Theorem 11.5 (weak Nagaoka, effective one-hole sector) `weakNagaoka_theorem_11_5`
  PROVEN**: Tasaki matrix `M=TᴴĤ_eff T` + operator lift + all-up block `M_↑` min eigenvector → `N+1`
  linearly independent degenerate `Ĥ_eff`-eigenvectors at the maximal-spin sector minimum, all
  `S_tot=S_max`;
- **global form `weakNagaoka_theorem_11_5_global`: the all-up minimum equals the global one-hole
  minimum via the Schwarz bound (11.2.9), so these are genuine ground states**;
- **Tasaki §11.2.2 Definition 11.6 + Theorem 11.7 (Nagaoka's theorem) PROVEN**: the `S_z^{(3)}`
  magnetization sectors of the one-hole Tasaki basis (`holeSpinMag`, `Ĥ_eff` block-diagonal across
  them); Definition 11.6 connectivity condition (`nagaokaConnectivity` = per-sector irreducibility
  of `−M`); per-sector Perron–Frobenius → non-degenerate sector ground state (upper bound `finrank ≤
  N+1`); the SU(2) ferromagnetic tower (one-hole supported via `Ŝ^-` preserving the hard-core
  `N`-electron sector) → lower bound `finrank ≥ N+1`; hence `nagaoka_theorem_11_7_degeneracy`
  (ground degeneracy `= N+1 = 2S_max+1`) and `nagaoka_theorem_11_7` (every one-hole ground state has
  `S_tot=S_max`) — Nagaoka's ferromagnetism, sorry-free;
- **Theorem 11.8 (Bobrow–Stubis–Li connectivity ⟺ biconnected ∧ not a simple loop `>4` sites)
  formalized as an `axiom` with its graph predicates (`nagaokaBondGraph`, `IsBiconnected`,
  `IsSimpleLoopGTFour`, `IsExchangeBond`) — its proof is left by Tasaki to external papers; Theorem
  11.7 does not depend on it. **Lemma 11.9 (exchange-bond sufficient condition) PROVED, axiom
  discharged** (`nagaoka_lemma_11_9` at its original path in
  `NagaokaConnectivityClassification.lean`, machinery in `NagaokaStateQuiver.lean` +
  `NagaokaStateQuiverReach.lean` + `NagaokaStateQuiverReachCore.lean` +
  `NagaokaStateQuiverCore.lean`, predicates in `NagaokaBondGraph.lean`): the full 15-puzzle argument
  — `−M` quiver edge characterisation + `StateReach`; length-3 loop transposition and length-4
  once/twice Boolean trips for diagonal *and* adjacent pairs (Figs. 11.8–11.9, fn. 14); controlled
  hole transport with round-trip restoration; E2 routing; the exchange-bond bridge
  `reachSwap_of_isExchangeBond`; swap generation along exchange-bond walks (fn. 13,
  `ReachSwapOff.of_walk`); the farthest-vertex parking lemma `exists_vertex_walks_avoid`; the
  mismatch-reduction induction `StateReach.of_swaps_of_holeSpinMag_eq`; sector irreducibility via
  `nagaokaConnectivity_of_reach`; and the diagonal-zeroing transfer `tasakiEffReMatrix_zeroDiag`**;
- **§11.3.1 Tasaki's flat-band ferromagnetism (model setup + Lemma 11.10)**: the d=1 decorated
  (Delta) chain `Λ = E ∪ I` realized in the spinful Hubbard framework (external `i↦2i`, internal
  `i↦2i+1` in `Fin (2K+2)`); single-particle states `flatBandAlpha`/`flatBandBeta` (11.3.1/11.3.2),
  fermion operators `flatBandA/B{Annihilation,Creation}` (11.3.3/11.3.4) + adjoints, the flat-band
  Hamiltonian `t Σ b̂†b̂ + U Σ n↑n↓` (11.3.5/11.3.6) + Hermiticity;
- **Lemma 11.10**: `{α_p} ∪ {β_u}` is a basis of the single-particle space
  (`flatBand_linearIndependent`, `flatBandBasis`) via the cross-orthogonality `⟨α_p,β_u⟩=0` + the
  even/odd site-split;
- **eq. (11.3.7)** `{b̂_{u,σ}, â†_{p,τ}}=0` (`flatBandBAnnihilation_ACreation_anticomm`, the
  `b̂`/`â†` operators anticommute, via spinful CAR + bilinear expansion + orthogonality);
- **eqs. (11.3.8)/(11.3.9)** the all-up α Slater state `flatBandAlphaAllUpState = (∏_p
  â†_{p,↑})|vac⟩`, a move-through lemma, `b̂_{u,σ}|Φα⟩=0`, and `Ĥ_hop|Φα⟩=0`
  (`flatBandHopping_mulVec_alphaAllUpState` — `|Φα,all↑⟩` is a zero-energy state of the hopping
  Hamiltonian);
- **`Ĥ_int|Φα⟩=0` and `Ĥ|Φα⟩=0`** (`flatBandHamiltonian_mulVec_alphaAllUpState` — the all-up α state
  is a zero-energy state of the full flat-band Hamiltonian, since `ĉ_{x↓}|Φα⟩=0` ⇒ no double
  occupancy), sorry-free;
- **general highest-weight SU(2) lowering tower (toward Thm 11.11 existence,
  `SpinLoweringTowerGeneral.lean`)**: the SU(2) ladder at an *arbitrary* highest weight `m = L/2`
  (the `WeakNagaokaTheorem.lean` tower covers only the chain maximum `N/2`, which the flat-band
  ferromagnet with `Ŝ^z=(K+1)/2 < N/2` violates) — general `Ŝ^z`/`Ŝ^+Ŝ^-`/highest-weight Casimir
  eigenvalue formulas, finite-tower nonvanishing/linear independence, and
  `highestWeight_spinMultiplet_general` packaging a highest-weight state into an `(L+1)`-dimensional
  maximal-spin multiplet;
- **the all-up α state is a highest-weight maximal-spin state (`TasakiFlatBandHighestWeight.lean`,
  eq. (11.3.10))**: `Ŝ^+_tot|Φα⟩=0`, `N̂_↑|Φα⟩=(K+1)|Φα⟩` (charge move-through
  `flatBand_charge_listProd_mulVec_vacuum` + `[N̂_↑,â†_{p,↑}]=â†_{p,↑}`), `N̂_↓|Φα⟩=0`, hence
  `Ŝ^z_tot|Φα⟩=((K+1)/2)|Φα⟩` — the half-filled-band highest weight `m=(K+1)/2=|E|/2 < N/2`,
  matching the hypotheses of `highestWeight_spinMultiplet_general` at `L=K+1`;
- **`|Φα,all↑⟩≠0` (`TasakiFlatBandNonvanishing.lean`)**: the last existence input, proven without
  Slater/Gram machinery — since `α_p(2q)=δ_{pq}` on external sites, the external up annihilation
  `ĉ_{2q,↑}` is the canonical dual `{ĉ_{2q,↑},â†_{p,↑}}=δ_{pq}`, so the ordered dual annihilations
  collapse the creation product to `|vac⟩≠0` (`flatBandAlphaAllUpState_ne_zero`);
- **Theorem 11.11 (existence half, spin content, `TasakiFlatBandMultiplet.lean`)**:
  `flatBand_ferromagnetic_multiplet` — the `K+2=2S_max+1` lowered states `(Ŝ^-_tot)^k|Φα,all↑⟩`
  (`k=0..K+1`) are linearly independent and all carry total spin `S_tot=S_max=(K+1)/2=N_e/2`
  (eigenstates of `(Ŝ_tot)²` at `S_max(S_max+1)`), via `highestWeight_spinMultiplet_general` at
  `L=K+1`;
- **energy tower (`TasakiFlatBandEnergyTower.lean`)**: flat-band SU(2) lowering symmetry
  `[Ŝ^±_tot,Ĥ]=0` (kinetic term SU(2)-invariant since the `b̂` operators are a spin doublet —
  spin-summed mode number commutes with `Ŝ^+`, off-diagonal terms cancel; interaction reuses
  `fermionTotalSpinPlus_commute_hubbardDoubleOccupancy`; `Ŝ^-` by adjoint) ⇒ `Ĥ(Ŝ^-_tot)^k|Φα⟩=0` —
  all K+2 multiplet members are zero-energy;
- **PSD + ground states (`TasakiFlatBandPosSemidef.lean`)**: `Ĥ≥0`
  (`flatBandHamiltonian_posSemidef`, `t,U≥0`) as a nonnegative combination of PSD terms
  (`b̂†b̂=(b̂)ᴴb̂`; `n̂↑n̂↓` Hermitian-idempotent projection), so `rayleighOnVec Ĥ ψ≥0` everywhere
  while the tower attains `0` ⇒ `flatBand_alphaTower_isGroundState`: each `(Ŝ^-_tot)^k|Φα⟩`
  minimizes the energy. **The existence half of Theorem 11.11 is complete**: a `(2S_max+1)`-dim
  maximal-spin degenerate ground-state multiplet, `S_max=(K+1)/2`;
- **frustration-free conditions (`TasakiFlatBandFrustrationFree.lean`, toward uniqueness)**: any
  flat-band ground state `v` (`rayleighOnVec Ĥ v=0`, `t,U>0`) satisfies `b̂_{u,σ}v=0` (eq. 11.3.11)
  and `n̂_{x↑}n̂_{x↓}v=0` (no-double-occupancy form of 11.3.12), since `Ĥ` is a sum of PSD terms
  each of which must annihilate a zero-energy state;
- **number conservation (`TasakiFlatBandNumberConservation.lean`)**: `[Ĥ,N̂]=0`
  (`flatBandHamiltonian_commute_fermionTotalNumber`; `b̂` lowers / `b̂†` raises `N̂` by one), so
  ground states split into fixed-`N` sectors; and any ground state lies in the Hubbard hard-core
  subspace (`flatBand_groundState_mem_hardcoreSubspace`);
- **uniqueness framework subspaces (`TasakiFlatBandSubspaces.lean`)**: `flatBandAlphaFockSubmodule`
  (span of α-Slater states, contains `|Φα⟩`) and `flatBandBKernelSubmodule = ⨅_{u,σ} ker b̂_{u,σ}`
  (contains every ground state, from 11.3.11) — Tasaki's uniqueness is the inclusion `BKernel ⊆
  αFock` + symmetric/maximal-spin classification;
- **rotated-basis Fock-spanning infrastructure toward it (`TasakiFlatBandModeCreation.lean`,
  `TasakiFlatBandModeMonomial.lean`, `Math/ListProdMulVec.lean`, Issue #4346)**: the
  single-particle-mode creation/annihilation maps `Ĉ†_σ(w)`/`Ĉ_σ(w)`
  (`flatBandModeCreation`/`flatBandModeAnnihilation`, with â†/b̂†/â/b̂ as values at α/β), the
  operator-level single-particle change of basis (`flatBandModeCreation_eq_repr_sum`), the generic
  single-particle CAR `{Ĉ_σ(w),Ĉ†_τ(w')}=(∑_x w(x)w'(x))δ_στ·1`
  (`flatBandMode_annihilation_creation_anticomm`, giving the β-Gram and `{b̂,â†}=0`), and
  `flatBandModeFockSubmodule_eq_top` — the rotated-basis Fock monomials `(∏ Ĉ†_σ(basis i))|vac⟩`
  span the whole space (every `basisVec c` is an ordered site-creation product on the vacuum, and
  the span is invariant under each site creation), reindexed by occupation configs (card
  `2^(4K+4)=finrank`) into the **rotated occupation basis** `flatBandOccBasis`;
- **the hard inclusion `BKernel ⊆ AlphaFock` is now PROVED**
  (`flatBandBKernelSubmodule_le_alphaFockSubmodule`, `TasakiFlatBandUniqueness.lean`, axiom-clean):
  the β-Gram is invertible (PosDef, `flatBandBetaGram`), its inverse gives dual annihilators
  `d_{u,σ}=∑_v(G⁻¹)_{uv}b̂_{v,σ}` with `{d,b̂†}=δ`, `{d,â†}=0`, `d|vac⟩=0`; the projector
  `b̂†_{u,σ}d_{u,σ}` kills a b̂-kernel vector (since `d v=0`), forcing every β-occupied
  occupation-basis coordinate to vanish, so the vector is a combination of β-free occ monomials (=
  α-Slater states) ∈ α-Fock; with the easy inclusion, `BKernel = AlphaFock`;
- **dimension-route reduction of the uniqueness `≤` half (`TasakiFlatBandClassification.lean`, Issue
  #4346)**: `finrank(multiplet)=K+2`, `[Ŝ^z_tot,Ĥ_flat]=0`
  (`fermionTotalSpinZ_commute_flatBandHamiltonian`, from `[Ŝ^±,Ĥ]=0` + su(2) `Ŝ⁺Ŝ⁻−Ŝ⁻Ŝ⁺=2Ŝ^z`),
  `Ŝ^z` preserves the ground subspace, the finite `Ŝ^z`-weight decomposition `G=⨆_{a:Fin(K+2)}
  G⊓eigenspace(Ŝ^z, a−(K+1)/2)` (`flatBandHalfFilledGroundSubmodule_eq_iSup_weight`, off-weight
  blocks `⊥` since `N̂=K+1` fixes the half-integer weights), and the capstone
  `flatBand_groundSubmodule_eq_multipletSpan_of_blocks` — IF each `Ŝ^z`-weight block of `G` is
  `≤1`-dimensional THEN `G=multiplet` (via
  `Math/EigenspaceWeightFinrank.finrank_le_of_weight_blocks` + `Submodule.eq_of_le_of_finrank_le`,
  using the proven `multiplet ≤ G`); the residual `finrank(block)≤1` (symmetric/maximal-spin core)
  is proved via `flatBand_block_finrank_le_one`, discharging the axiom;
- **easy inclusion (`TasakiFlatBandAlphaFockKernel.lean`)**: `αFock ≤ BKernel`
  (`flatBandAlphaFockSubmodule_le_BKernelSubmodule`) — every α-Slater state is annihilated by all
  `b̂` via the 11.3.7 anticommutation + move-through; the hard reverse `BKernel ⊆ αFock` needs the
  non-orthogonal-basis Fock factorisation, now PROVED (see above,
  `flatBandBKernelSubmodule_le_alphaFockSubmodule`);
- **Theorem 11.11 CAPSTONE (`TasakiFlatBandClassification.lean`)**:
  `flatBand_theorem_11_11_groundSubmodule_eq_multipletSpan` — the half-filled (`N_e=K+1`)
  zero-energy ground subspace `ker Ĥ ⊓ eigenspace(N̂,K+1)` equals the ferromagnetic multiplet span
  (`2S_max+1`-dim, maximal spin), + maximal-spin corollary;
- **PROVED, axiom-free** (both `≥`, existence, and `≤`, classification via one-dimensional
  `Ŝ^z`-weight blocks);
- **§11.3.2 Mielke's flat-band ferromagnetism (`MielkeHamiltonian.lean`, Issue #4177)**:
  `mielkeHamiltonian` on a graph (uniform hopping + `2t·N̂` shift + `U`) with Hermiticity,
  `[Ĥ,N̂]=0`, SU(2) invariance — model setup; the line-graph structure + Theorems 11.12 (flat-band)
  / 11.13 (Mielke ferromagnetism) (`MielkeTheorems.lean`): `mielkeFlatBandDim` D(Λ̃,B̃),
  `mielkeSingleElectronOp`, line graph via mathlib `SimpleGraph.lineGraph` + `SimpleGraph.Iso`;
- **`mielke_theorem_11_12`** (flat-band, connected base: single-electron kernel finrank = D) and
  **`mielke_theorem_11_13`** (Mielke ferromagnetism: biconnected base, N=D ⇒ ground subspace finrank
  = N+1 + all maximal spin) were documented **axioms**;
- **Theorem 11.12 is now PROVEN** (§11.3.3, see below), leaving only **`mielke_theorem_11_13`** as
  an axiom (Tasaki states it without proof; the Hamiltonian model + symmetries are axiom-free);
- **§11.3.3 incidence-matrix factorisation (`MielkeIncidenceMatrix.lean`, Issue #4180, DISCHARGES
  the 11.12 axiom)**: `mielkeSingleElectronOpOn` (single-electron operator generalised to an
  arbitrary finite vertex type; `mielkeSingleElectronOp` is now the `Fin (M+1)` wrapper),
  `mielkeIncidence` (`S = √t·` mathlib `incMatrix` restricted to genuine edges, eq. (11.3.36)), and
  **`mielkeIncidence_conjTranspose_mul_self`**: `SᴴS = mielkeSingleElectronOpOn (lineGraph G) t` for
  `t ≥ 0` (eqs. (11.3.36)–(11.3.39)) — the line-graph operator presented as a PSD Gram matrix with
  diagonal `2t` (edge degree 2) and off-diagonal `t` on shared-vertex edge pairs, kernel `= ker S`;
  the algebraic core for the rank–nullity + bipartite zero-mode count (11.3.41) discharging Theorem
  11.12, sorry-free;
- **rank step (PR3)**: `mielke_lineGraph_ker_finrank_eq` — for `t≥0`, `dim ker T = |B| − rank S`
  (via mathlib `ker_mulVecLin_conjTranspose_mul_self` giving `ker SᴴS = ker S` + rank–nullity), the
  Lemma 11.14 rank form;
- **zero-mode count + dim (PR4)**: `mielke_conjTranspose_ker_finrank` — for `t>0` and a
  **connected** base, `dim ker(SSᴴ) = dim ker Sᴴ = (Colorable 2 ? 1 : 0)`, proved directly via `ker
  Sᴴ` (`(Sᴴx)_b = √t(x_u+x_v)`; bipartite ⇒ 1-dim span of the alternating ±1 colouring vector,
  non-bipartite ⇒ trivial since a nonzero kernel vector would 2-colour the graph); and
  `mielke_lineGraph_ker_finrank_eq_dim` — the assembled flat-band dimension `D = |B| − (|Λ̃| − bip)`
  (Theorem 11.12 general-base form; inner subtraction keeps it sound under ℕ truncation, = Tasaki's
  `|B|−|Λ̃|+1` once `|Λ̃|≤|B|`). **`mielke_theorem_11_12` (PR5, capstone)** — **now a proved
  theorem** (formerly the §11.3.2 axiom): transports the flat-band dimension to the `Fin (M+1)`
  line-graph realisation along the `SimpleGraph.Iso` via `Matrix.rank_submatrix` (rank/kernel-dim
  invariance under equiv-reindex), with hypothesis `|Λ̃| ≤ |B|` (base has a cycle — exactly where
  Tasaki's `|B|−|Λ̃|+1` is the true dimension). Issue #4180 CLOSED);
<!-- legacy-source:end:149:149 -->
