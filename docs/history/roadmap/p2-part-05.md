---
layout: page
title: "Roadmap history: P2, part 5"
permalink: /history/roadmap/p2-part-05/
---

# Roadmap history: P2, part 5

> Historical implementation record normalized at semicolon-delimited bold milestones. Active work is governed by tracking Issues.

<!-- legacy-source:start:149:149 -->
- **discharge in progress, Issue #4314**: with Prop 11.24 proved, the first step
  `TJHalfFillingKinetic.lean` proves the t-J kinetic term vanishes at half-filling `Ne=K+1` —
  `tJ_kinetic_sandwich_mulVec_tJConfigOf_eq_zero_of_full`, `P̂hc K P̂hc |Φ_s⟩=0` for fully-occupied
  `s`, so `Ĥ_tJ|half` reduces to the ferromagnetic Heisenberg model; PR2
  `TJHalfFillingExchange.lean` completes the reduction `tJHamiltonian_mulVec_tJConfigOf_eq_of_full`:
  `Ĥ_tJ|Φ_s⟩ = J·tJExchange|Φ_s⟩` for fully-occupied `s`; PR3a `TJAllUpSpinDot.lean` computes
  `fermionSpinDot_mulVec_allUpState` `Ŝ_i·Ŝ_j|↑…↑⟩=¼|↑…↑⟩` (i≠j), so the all-up state has exchange
  energy 0; PR3b `TJAllUpGround.lean` then proves `tJHamiltonian_mulVec_allUpState_eq_zero`
  `Ĥ_tJ|↑…↑⟩=0` at half-filling — the maximal-spin `|↑…↑⟩` is a zero-energy eigenstate; PR3c-prep
  `TJSingletAnnihilation.lean` adds the singlet annihilator `Δ_xy=ĉ_{y↓}ĉ_{x↑}−ĉ_{y↑}ĉ_{x↓}`
  (`Δ_xy|↑…↑⟩=0`), towards the bond identity; PR3c `TJExchangeBondPSD.lean` proves the CAR identity
  `tJSingletAnnihilation_conjTranspose_mul_self` `Δ_xy†Δ_xy =
  n̂_{x↑}n̂_{y↓}+n̂_{x↓}n̂_{y↑}−Ŝ⁺_xŜ⁻_y−Ŝ⁻_xŜ⁺_y` (x≠y) + cross-site commutes
  `TJCrossSiteSpinCommute.lean`, the content behind the half-bond identity; PR3d
  `TJExchangeBondHalf.lean` proves `tJExchangeBond_eq_half_singletNormSq`
  `n̂_xn̂_y/4−Ŝ_x·Ŝ_y=½Δ_xy†Δ_xy` (x≠y) and `tJExchangeBond_posSemidef` (the bond is
  positive-semidefinite) — the per-bond PSD input; PR3e `TJExchangePSD.lean` proves
  `tJExchange_posSemidef` `(tJExchange N G).PosSemidef` (graph sum of per-bond PSD terms via
  `Finset.sum_induction`) — the operator nonnegativity behind the half-filling ground energy 0; PR3f
  `TJHalfFillingReduction.lean` extends to the whole sector — `tJFillingSector_full` (Ne=N+1 ⟹ fully
  occupied), `tJ_kinetic_sandwich_mulVec_eq_zero_of_filling`, and
  `tJHamiltonian_mulVec_eq_smul_tJExchange_of_filling` (`Ĥ_tJ v=J·tJExchange v` for hard-core N̂=N+1
  v); PR3g `TJAllUpProperties.lean` (`N̂|↑…↑⟩=(N+1)|↑…↑⟩`, hardcore, ≠0) +
  `TJHalfFillingGroundEnergy.lean` `tJ_groundEnergyAtFilling_eq_zero` (`groundEnergyAtFilling Ĥ_tJ
  (N+1)=0`: all-up at 0, PSD ⇒ rayleigh≥0); axiom-free); PR3h `TJHalfFillingDegeneracyLower.lean`
  `tJ_halfFilling_groundSubmodule_finrank_ge` (`N+2 ≤ finrank` of the half-filling ground subspace:
  the all-up state is a highest-weight ground state, so the SU(2) lowering tower yields `N+2` LI
  ground states `(Ŝ⁻)^k|↑…↑⟩`; mirrors #4305; axiom-free); PR3i `TJHalfFillingBondAction.lean`
  `tJExchangeBond_mulVec_tJConfigOf_full` (the exchange bond is a half spin-swap on the filled
  sector: `(¼ n̂_x n̂_y − Ŝ_x·Ŝ_y)|Φ_s⟩=½(|Φ_s⟩−|Φ_{tJSpinSwap s x y}⟩)` via the sign-free swap over
  the 4 spin cases; ground states of `tJExchange` have spin-swap-invariant bond amplitudes — toward
  the degeneracy upper bound; axiom-free); PR3i-2 `TJHalfFillingBondGround.lean`
  `tJ_ground_bond_mulVec_eq_zero` (a half-filling ground state is annihilated by every adjacent
  bond: `bond_xy v=0` via the PSD sum `⟨v,tJExchange v⟩=0` ⇒ each `⟨v,bond_xy v⟩=0` ⇒ `Δ_xy v=0`;
  axiom-free); PR3i-3a `TJHalfFillingAmplitude.lean` `tJ_ground_amplitude_swap_invariant`
  (half-filling ground amplitudes are spin-swap invariant: `v(tJConfigOf s)=v(tJConfigOf(tJSpinSwap
  s x y))` for adjacent bonds, via filling-basis expansion + the bond half-swap action + `bond_xy
  v=0`; `tJFillingSwap` sector permutation; axiom-free); PR3i-3b `TJHalfFillingUpCount.lean`
  `tJ_ground_amplitude_eq_of_same_upCount` (half-filling ground amplitudes depend only on the
  up-count: equal up-counts ⟹ equal value-counts ⟹ adjacent-swap reachable
  [`adjacentSwapReachable_of_same_counts`] ⟹ amplitudes equal by reachability induction over the
  per-bond swap invariance; axiom-free); PR3i-3c `TJHalfFillingDegeneracyUpper.lean`
  `tJ_halfFilling_groundSubmodule_finrank_le` (**upper bound `finrank G ≤ N+2`**: ground states
  determined by amplitudes constant on the N+2 up-count classes ⟹ injective `G ↪ (Fin(N+2)→ℂ)`; with
  the lower bound #4326 ⟹ `finrank G = N+2`; axiom-free);
- **PR3-cap `TJHalfFillingMaximalSpin.lean` `tJ_halfFilling_isMaximalSpinMultiplet`** (the
  half-filling t-J ground subspace is the maximal-spin `(N+2)`-fold multiplet:
  `IsMaximalSpinMultipletSubmodule N G (N+1)`, assembling `finrank=N+2` with the all-up SU(2) tower
  spanning `G`; boundary case of Theorem 11.26's t-J side; axiom-free, no A.17);
- **PR-unify `TJMaximalSpinUnified.lean` `tJ_isMaximalSpinMultiplet_of_le`** (the d=1 t-J ground
  subspace is the maximal-spin multiplet for ALL odd `Ne ≤ K+1`: metallic `Ne<K+1` via
  `proposition_11_24` + half-filling `Ne=K+1`; the half-filling chain generalized to drop `0<N` so
  `K=0` is covered; t-J input to Theorem 11.26, rests on A.17 via Prop 11.24);
- **PR-final: `theorem_11_26` is now a PROVED theorem** (`MetallicFerroModel.lean`, Issue #4314):
  discharged from `lemma_11_25` (documented strong-coupling-equivalence axiom) +
  `tJ_isMaximalSpinMultiplet_of_le`; `#print axioms theorem_11_26` = `[propext, Classical.choice,
  Quot.sound, lemma_11_25]` (A.17's `exists_joint_su2_energy_eigenstate` now discharged §A.3.2).
  Tasaki §11.5.3 metallic-ferromagnetism Theorem 11.26 complete + **`theorem_11_26` (PROVED, Issue
  #4314)** (d=1, `Ne≤K+1=|E|` odd (Tasaki's `N≤L`) ⇒ `IsMaximalSpinMultipletSubmodule (3K+2)
  (groundSubmoduleAtFilling (decHubbardHamiltonian …) Ne) Ne` for large `t,U` — ground `S_tot=Ne/2`,
  `Ne+1`-fold; metallic when `Ne<K+1`); discharged from `lemma_11_25` (documented axiom) +
  `tJ_isMaximalSpinMultiplet_of_le`, so the model and Theorem 11.26 are proved modulo `lemma_11_25`
  (A.17 now discharged); Theorem 11.27 still a documented axiom);
- **generic single-particle-state operators (`SpinfulVectorOperator.lean`)**:
  `spinfulCreationFromVector`/`spinfulAnnihilationFromVector` (`Ĉ_σ(φ)=Σ_x φ(x)ĉ_{x,σ}`), shared
  helper; axiom-free;
- **§11.5.4 Tanaka–Tasaki model + Theorem 11.27 (AXIOMATIZED, `TanakaTasakiModel.lean`, Issue #4198)
  — §11.5/Chapter 11 capstone**: the heavily-decorated lattice `Λ=E×{1,2,3}∪I×{1,2}` (externals
  triplicated, internals duplicated), d=1 in `Fin(5K+5)` (`ttExtSite`/`ttIntSite`); special states
  `ttAlpha`/`ttBeta`/`ttDeltaP`/`ttDeltaI` (eqs. (11.5.19)–(11.5.22), `â` with `1/√(3+4ν²)`) + ops
  via `spinfulCreationFromVector`; `ttHopping` (`Σ_{⟨p,q⟩}(−s â†â−t b̂†b̂)+u₁Σb̂†b̂+u₂Σd̂†d̂`, eq.
  (11.5.24)) + `ttInteraction` + `ttHamiltonian` (finite); genuine `u₂,U↑∞` limit objects
  `ttDKernel` (`d̂Φ=0`, via Theorem A.12) + `ttEffectiveHamiltonian` (`u₂,U=∞` effective hopping);
- **`axiom theorem_11_27`** (d=1, `u₁>2(|s|+2|t|)`, `K+1≤Ne≤2(K+1)` (Tasaki `L^d≤N≤2L^d`) ⇒ **in the
  limit** every ground state in `groundSubmoduleAtFilling (ttEffectiveHamiltonian …) Ne ⊓ ttDKernel`
  has max spin `S_tot=Ne/2` — taken as a genuine limit, not finite thresholds (Tasaki proves it only
  in the limit, warns finite `u₂,U` is not expected to work); weaker than the multiplet predicate,
  Tasaki claims only the spin; metallic when `1<Ne/L<2`); model axiom-free, `theorem_11_27`
  documented axiom ([63]))
<!-- legacy-source:end:149:149 -->
