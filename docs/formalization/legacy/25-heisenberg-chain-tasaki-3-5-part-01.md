---
layout: page
title: "Legacy catalogue: Heisenberg chain (Tasaki §3.5) (part 1 of 2)"
permalink: /formalization/legacy/25-heisenberg-chain-tasaki-3-5-part-01/
---

# Legacy catalogue: Heisenberg chain (Tasaki §3.5) (part 1 of 2)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin models, Chapters 3–7, and spectral tools](/lattice-system/formalization/legacy/#group-spin-models)

<!-- legacy-source:start:1444:1546 -->
### Heisenberg chain (Tasaki §3.5)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §3.5, p. 89.

| Lean name | Statement | File |
|---|---|---|
| `LatticeSystem.Lattice.couplingOf G J` | the canonical pairwise coupling `Λ → Λ → ℂ` of a `SimpleGraph G` with uniform edge weight `J`: returns `J` on edges of `G`, zero otherwise (graph-centric bridge) | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.couplingOf_symm` / `_self` / `_real` | symmetry (from `G.Adj` symmetry), vanishing on the diagonal (from irreflexivity), and reality (for real edge weight) | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.pathGraph_adj_iff` / `cycleGraph_adj_iff` | path / cycle graph adjacency in the explicit `x.val + 1 = y.val ∨ ...` form used elsewhere in the codebase | `Lattice/Graph.lean` |
| `openChainCoupling N J` | coupling `Fin (N+1) → Fin (N+1) → ℂ`: returns `-J` on nearest-neighbour bonds, zero otherwise | `Quantum/HeisenbergChain.lean` |
| `periodicChainCoupling N J` / `periodicChainCoupling_apply` | coupling `Fin (N+2) → Fin (N+2) → ℂ`: returns `-J` on nearest-neighbour bonds (mod N+2), zero otherwise; `periodicChainCoupling_apply` is the component-wise if-expression unfolding used by the public TeX proof guide (`tex/proof-guide.tex`, `periodicChainCoupling` definition) | `Quantum/HeisenbergChain.lean` |
| `openChainCoupling_eq_couplingOf` | the open-chain coupling is `couplingOf (pathGraph (N+1)) (-J)` | `Quantum/HeisenbergChain.lean` |
| `periodicChainCoupling_eq_couplingOf` | the periodic-chain coupling is `couplingOf (cycleGraph (N+2)) (-J)` | `Quantum/HeisenbergChain.lean` |
| `heisenbergHamiltonian_isHermitian_of_real_symm` | for any real symmetric coupling `J` the Heisenberg Hamiltonian `H = Σ_{x,y} J(x,y) Ŝ_x · Ŝ_y` is Hermitian | `Quantum/HeisenbergChain.lean` |
| `heisenbergHamiltonian_couplingOf_isHermitian` | **graph-centric** Hermiticity: for any `SimpleGraph G` and real edge weight `J : ℂ`, the Heisenberg Hamiltonian `heisenbergHamiltonian (couplingOf G J)` is Hermitian. The chain instances are corollaries via the bridge theorems | `Quantum/HeisenbergChain.lean` |
| `heisenbergHamiltonianOnGraph G J` | named wrapper = `heisenbergHamiltonian (couplingOf G J)` (parallel to `isingHamiltonianOnGraph`) | `Quantum/HeisenbergChain.lean` |
| `heisenbergHamiltonianOnGraph_isHermitian` / `_commute_totalSpinHalfOp{1,2,3}` / `_commute_totalSpinHalfSquared` | corollaries re-exposed under the named wrapper | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsState_eq_onGraph` / `periodicChainHeisenbergGibbsState_eq_onGraph` | rfl bridges: chain Gibbs = graph Gibbs on pathGraph/cycleGraph | `Quantum/HeisenbergChain/Gibbs.lean` |
| `quantumIsingGibbsState_eq_isingGibbsStateOnGraph` | chain Ising Gibbs = `isingGibbsStateOnGraph (pathGraph (N+1)) β (-J/2) h` | `Quantum/IsingChain.lean` |
| `isingCycleGibbsState_commute_hamiltonian` | the periodic Ising Gibbs state commutes with the periodic Ising Hamiltonian (free corollary of `gibbsState_commute_hamiltonian`) | `Quantum/IsingChain.lean` |
| `isingCycleGibbsExpectation_zero` / `_im_of_isHermitian` / `_commutator_hamiltonian` / `_hamiltonian_im` / `_hamiltonian_pow_im` / `isingCycle_partitionFn_im` / `_ofReal_re_eq` / `isingCycleGibbsState_pow_trace` | periodic-Ising expectation companions of the open-chain `quantumIsingGibbsExpectation*` family: β = 0 closed form, real-valuedness for Hermitian observables, conservation `⟨[H, A]⟩ = 0`, energy / energy-power expectations real, partition-function real, real-cast `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β`, Rényi-n trace `Tr(ρ_β^n) = Z(nβ) / Z(β)^n` | `Quantum/IsingChain.lean` |
| `hubbardGibbsStateOnGraph N β G J U` | Gibbs state of the graph-built Hubbard Hamiltonian | `Fermion/JordanWigner.lean` |
| `hubbardGibbsStateOnGraph_isHermitian` / `_commute_hamiltonian` | Hermiticity / commute corollaries | `Fermion/JordanWigner/Hubbard/Graph.lean` |
| `hubbardChainGibbsState_eq_onGraph` | rfl bridge: `hubbardChainGibbsState = hubbardGibbsStateOnGraph (pathGraph (N+1)) (-J) U` | `Fermion/JordanWigner/Hubbard/Graph.lean` |
| `jwStringAbstract i` | Jordan-Wigner string for any `[Fintype Λ] [LinearOrder Λ]` — product of `σ^z_j` over `j < i`; generalises the Fin-specific `jwString` | `Fermion/JWAbstract.lean` |
| `jwStringAbstract_isHermitian` / `jwStringAbstract_sq` / `jwStringAbstract_commute_onSite` | basic structural identities | `Fermion/JWAbstract.lean` |
| `fermionAnnihilationAbstract i` / `fermionCreationAbstract i` / `fermionNumberAbstract i` | abstract-Λ annihilation / creation / number; rfl-bridges to the Fin-specific versions | `Fermion/JWAbstract.lean` |
| `fermionAnnihilationAbstract_conjTranspose` / `fermionCreationAbstract_conjTranspose` / `fermionNumberAbstract_isHermitian` | adjoint relations and Hermiticity in the abstract form | `Fermion/JWAbstract.lean` |
| `fermionAnnihilationAbstract_sq` / `fermionCreationAbstract_sq` | `c_i² = 0`, `c_i†² = 0` (Pauli exclusion) | `Fermion/JWAbstract.lean` |
| `fermionMultiAnticommAbstract_self` / `fermionNumberAbstract_sq` | `{c_i, c_i†} = 1` and `n_i² = n_i` (abstract same-site CAR + idempotency) | `Fermion/JWAbstract.lean` |
| `LatticeSystem.Lattice.boxProd_decidableAdj` | `DecidableRel (G □ H).Adj` for the box product (mathlib provides only the bare definition); enables 2D / nD lattices via `couplingOf` | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.integerChainGraph` | the **infinite** one-dimensional chain `ℤ` as a `SimpleGraph` (= `hasse ℤ`), the infinite-volume analogue of `pathGraph (N+1)` | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.integerChainGraph_adj_iff` | adjacency: `a ~ b ↔ b = a + 1 ∨ a = b + 1` | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.integerSquareLatticeGraph` | the **infinite** 2D square lattice on `ℤ × ℤ` as `integerChainGraph □ integerChainGraph`; infinite analogue of `squareLatticeCoupling` | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.integerSquareLatticeGraph_adj_iff` | adjacency: nearest neighbour in one coordinate, equal in the other | `Lattice/Graph.lean` |
| `LatticeSystem.Lattice.hypercubicLatticeGraph` / `hypercubicLatticeGraph_adj` | the **infinite** `d`-dimensional hypercubic lattice `ℤᵈ` on `Fin d → ℤ` as a `SimpleGraph` (adjacency = differ in exactly one coordinate by `±1`, the nearest-neighbor bond set `B∞`, Tasaki eq. (4.3.1)) + a `DecidableRel` instance; the substrate of the thermodynamic-limit / infinite-volume frontier (Issue #4557) | `Lattice/HypercubicLattice.lean` |
| `LatticeSystem.Lattice.hypercubicBox` / `mem_hypercubicBox` | the centered finite box `Λ_n = {x ∈ ℤᵈ : −n < xᵢ ≤ n}` (even side `2n`, Tasaki eq. (3.1.2)) as a `Finset`, with its coordinatewise membership criterion | `Lattice/HypercubicLattice.lean` |
| `LatticeSystem.Lattice.hypercubicBox_subset_succ` / `hypercubicBox_monotone` / `exists_mem_hypercubicBox` / `iUnion_hypercubicBox` | the **monotone exhaustion** of `ℤᵈ` by the boxes: nesting `Λ_n ⊆ Λ_{n+1}`, monotonicity, every site lies in some box, and `⋃ₙ Λ_n = ℤᵈ`; the increasing-region API for constructing the thermodynamic limit | `Lattice/HypercubicLattice.lean` |
| `LatticeSystem.Lattice.hypercubicBox_card` | the box **volume** `\|Λ_n\| = (2n)ᵈ` (side `2n` in each of `d` directions); the volume normalization `Lᵈ = (2n)ᵈ` of the bulk-density / energy-density limits (Tasaki eqs. (4.3.4), (4.3.6)) | `Lattice/HypercubicLattice.lean` |
| `LatticeSystem.Lattice.hypercubicBoxGraph` / `hypercubicBoxVertex` / `hypercubicBoxGraph_adj` | the **finite-volume graph** on the box `Λ_n` (a `Fintype` subtype of `ℤᵈ`): the induced subgraph `(hypercubicLatticeGraph d).induce ↑Λ_n`, the graph-centric finite-volume substrate `Λ_n ↪ ℤᵈ` of the thermodynamic limit | `Lattice/HypercubicLattice.lean` |
| `LatticeSystem.Lattice.hypercubicBoxCoupling` / `hypercubicBoxParityColoring` / `hypercubicBoxGraph_isBipartite` | the uniform nearest-neighbor coupling `couplingOf` on `Λ_n` (finite-volume many-body Hamiltonian input), and the inherited bipartite structure (parity coloring restricted from `ℤᵈ`) | `Lattice/HypercubicLattice.lean` |
| `boxHeisenbergHamiltonianS` / `boxAFMHeisenbergHamiltonianS` (+ `_isHermitian`, `_eq_heisenbergHamiltonianS_boxCoupling`) | the **concrete finite-volume spin-`S` Heisenberg model** on the box `Λ_n ⊂ ℤᵈ` (`ManyBodyOpS (hypercubicBoxVertex d n) N`), via the graph Hamiltonian on `hypercubicBoxGraph`; the AFM specialization `Ĥ_{Λ_n} = Σ_⟨x,y⟩ Ŝ_x·Ŝ_y` (`J=1/2`, Tasaki unordered-bond convention) is the finite-volume model whose `L↑∞` limit is the §4.3 `InfiniteSpinSystem`. Hermitian for real `J`; ties to PR5's `hypercubicBoxCoupling` by `rfl`. Axiom-free | `Quantum/SpinS/HypercubicBoxModel.lean` |
| `boxGroundEnergyS` / `boxGroundEnergyS_le_eigenvalues` / `boxBondCount` / `boxGroundEnergyDensityS` | **finite-volume ground-state energy** `E_{GS,n}` (least eigenvalue of the Hermitian box AFM Hamiltonian, via `hermitianMinEigenvalue`), the **bond count** `\|B_n\|` (edges of `hypercubicBoxGraph`), and the **energy density** `E_{GS,n}/\|B_n\|` (Tasaki §4.3 eq. (4.3.4)) — the provable finite-volume groundwork for the thermodynamic-limit bridge (Issue #4564). Axiom-free | `Quantum/SpinS/HypercubicBoxModel.lean` |
| `boxBondCount_pos` / `boxGroundEnergyDensityS_tendsto` | `boxBondCount_pos` (**proved**): for `0 < d`, `1 ≤ n` the box has ≥1 bond (origin & `e_i` adjacent), so the energy-density denominator is positive on the tail (non-vacuity). `boxGroundEnergyDensityS_tendsto` (**documented AXIOM**, Tasaki §4.3 eq. (4.3.4)): for `0 < d`, `0 < N` the finite-volume per-bond ground-state energy density converges as `n→∞` to the infinite-volume energy density `ε_GS(d,N)` (existentially pinned to the genuine limit — the thermodynamic-limit existence is the deep analytic content) | `Quantum/SpinS/HypercubicBoxModel.lean` |
| `boxGroundEnergyDensitySLimit` / `boxGroundEnergyDensityS_tendsto_limit` / `IsAFMThermodynamicLimit` / `afmThermodynamicLimit_energyDensity` / `afmThermodynamicLimit_exists_omega0` | **thermodynamic-limit bridge** (Issue #4564 capstone): names the box energy-density limit `ε_GS(d,N)` (`boxGroundEnergyDensitySLimit`, proved to be the limit); the **documented predicate** `IsAFMThermodynamicLimit S N` (`S` is the `L↑∞` limit of the concrete box AFM model — not an identification of matrix algebras with the abstract C*-algebra); the **documented AXIOM** `afmThermodynamicLimit_energyDensity` (such `S`'s abstract energy density = the concrete box limit, Tasaki eq. (4.3.4)); the **PROVED** `afmThermodynamicLimit_exists_omega0` (symmetric infinite-volume ground state `ω_0` exists for the box AFM model's limit, via Theorem 4.20, eqs. (4.3.7)/(4.3.9)); and the **PROVED** `afmThermodynamicLimit_exists_omegaN` (the symmetry-breaking ground states `ω_n` with Néel magnetization `(−1)^x m∗ n_α`, given `HasStaggeredLRO`, eqs. (4.3.8)/(4.3.10) — vacuous in 1D) | `Quantum/SpinS/HypercubicBoxThermodynamicLimit.lean` |
| `LatticeSystem.Lattice.hypercubicLatticeGraph_adj_parity_ne` / `hypercubicEvenSublattice` / `hypercubicOddSublattice` | a nearest-neighbor bond **flips the coordinate-sum parity**; the even sublattice `ℤᵈ_even = {x : Σᵢ xᵢ even}` (A-sublattice, Tasaki eq. (4.3.2)) and its odd complement (B-sublattice) | `Lattice/HypercubicLattice.lean` |
| `LatticeSystem.Lattice.hypercubicLatticeGraph_isBipartiteWith` / `hypercubicParityColoring` / `hypercubicLatticeGraph_isBipartite` | `ℤᵈ` is **bipartite** with the even/odd sublattices as the two parts (`IsBipartiteWith`), via the parity 2-coloring `Coloring (Fin 2)`; hence `IsBipartite` (`Colorable 2`) — the combinatorial structure underlying antiferromagnetic / Néel order | `Lattice/HypercubicLattice.lean` |
| `squareLatticeCoupling N J`, `squareLatticeHeisenberg_isHermitian` | the 2D open-boundary square lattice on `Fin (N+1) × Fin (N+1)` realised as `couplingOf (pathGraph (N+1) □ pathGraph (N+1)) (-J)`; Hermiticity is a one-line corollary of the graph-generic theorem above | `Quantum/HeisenbergLattice.lean` |
| `squareTorusCoupling N J`, `squareTorusHeisenberg_isHermitian` | the 2D periodic square lattice (discrete torus) on `Fin (N+2) × Fin (N+2)` realised as `couplingOf (cycleGraph (N+2) □ cycleGraph (N+2)) (-J)`; Hermiticity is a one-line corollary | `Quantum/HeisenbergLattice.lean` |
| `cubicLatticeCoupling N J`, `cubicLatticeHeisenberg_isHermitian` | the 3D open-boundary cubic lattice on `Fin (N+1)^3` realised as `couplingOf (pathGraph (N+1) □ pathGraph (N+1) □ pathGraph (N+1)) (-J)`; Hermiticity is a one-line corollary | `Quantum/HeisenbergLattice.lean` |
| `squareLatticeHeisenbergGibbsState` / `_isHermitian` / `_commute_hamiltonian` | Gibbs state of the 2D open-boundary square-lattice Heisenberg Hamiltonian + Hermiticity + commute pair | `Quantum/HeisenbergLattice.lean` |
| `squareTorusHeisenbergGibbsState` / `_isHermitian` / `_commute_hamiltonian` | Gibbs state of the 2D torus Heisenberg Hamiltonian + companions | `Quantum/HeisenbergLattice.lean` |
| `cubicLatticeHeisenbergGibbsState` / `_isHermitian` / `_commute_hamiltonian` | Gibbs state of the 3D open-boundary cubic-lattice Heisenberg Hamiltonian + companions | `Quantum/HeisenbergLattice.lean` |
| `squareLatticeHeisenbergGibbsExpectation_hamiltonian_im` / `squareLatticeHeisenberg_partitionFn_im` | 2D open square-lattice Heisenberg energy expectation real / partition function real | `Quantum/HeisenbergLattice.lean` |
| `squareTorusHeisenbergGibbsExpectation_hamiltonian_im` / `squareTorusHeisenberg_partitionFn_im` | 2D torus Heisenberg energy expectation real / partition function real | `Quantum/HeisenbergLattice.lean` |
| `cubicLatticeHeisenbergGibbsExpectation_hamiltonian_im` / `cubicLatticeHeisenberg_partitionFn_im` | 3D cubic-lattice Heisenberg energy expectation real / partition function real | `Quantum/HeisenbergLattice.lean` |
| `squareLatticeHeisenbergGibbsExpectation_{zero, im_of_isHermitian, commutator_hamiltonian, mul_hamiltonian_im, hamiltonian_sq_im, hamiltonian_pow_im, anticommutator_im, commutator_re, ofReal_re_eq}` / `_GibbsHamiltonianVariance_im` / `_GibbsState_pow_trace` | 2D open square-lattice Heisenberg full Gibbs companion family (PR #334, parity with 1D open / periodic chain). Each is a 1-line application of the generic primitive in `GibbsState*.lean` | `Quantum/HeisenbergLattice.lean` |
| `squareTorusHeisenbergGibbsExpectation_{zero, im_of_isHermitian, commutator_hamiltonian, mul_hamiltonian_im, hamiltonian_sq_im, hamiltonian_pow_im, anticommutator_im, commutator_re, ofReal_re_eq}` / `_GibbsHamiltonianVariance_im` / `_GibbsState_pow_trace` | 2D torus Heisenberg full Gibbs companion family (PR #334) | `Quantum/HeisenbergLattice.lean` |
| `cubicLatticeHeisenbergGibbsExpectation_{zero, im_of_isHermitian, commutator_hamiltonian, mul_hamiltonian_im, hamiltonian_sq_im, hamiltonian_pow_im, anticommutator_im, commutator_re, ofReal_re_eq}` / `_GibbsHamiltonianVariance_im` / `_GibbsState_pow_trace` | 3D cubic-lattice Heisenberg full Gibbs companion family (PR #334) | `Quantum/HeisenbergLattice.lean` |
| `heisenbergHamiltonian_couplingOf_commute_totalSpinHalfOp{1,2,3}` | for any `SimpleGraph G` and edge weight `J : ℂ`, the Heisenberg Hamiltonian on `G` commutes with each total-spin component (free corollary of the generic-J theorems) | `Quantum/HeisenbergChain.lean` |
| `heisenbergHamiltonian_couplingOf_commute_totalSpinHalfSquared` | the same Hamiltonian commutes with the total-spin Casimir `Ŝ_tot²` (graph-centric SU(2) invariance) | `Quantum/HeisenbergChain.lean` |
| `heisenbergGibbsStateOnGraph β G J` | Gibbs state `gibbsState β (H_G_J)` for any finite graph `G` and complex edge weight `J` | `Quantum/HeisenbergChain.lean` |
| `heisenbergGibbsStateOnGraph_isHermitian` | Hermiticity when `J` is real | `Quantum/HeisenbergChain.lean` |
| `heisenbergGibbsStateOnGraph_commute_hamiltonian` | `Commute ρ_β H_G_J` (generic for any Gibbs state / Hamiltonian pair) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenberg_isHermitian` | specialization: the open-chain Heisenberg Hamiltonian is Hermitian | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenberg_isHermitian` | specialization: the periodic-chain Heisenberg Hamiltonian is Hermitian | `Quantum/HeisenbergChain.lean` |
| `heisenbergHamiltonian_gibbsExpectation_eq` | generic bond-sum decomposition `⟨H⟩_β = ∑ x, ∑ y, J x y · ⟨Ŝ_x · Ŝ_y⟩_β` (any Gibbs Hamiltonian, any coupling `J`) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsExpectation_self_eq` | open-chain energy expectation as a sum over open-boundary bonds | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsExpectation_self_eq` | periodic-chain energy expectation as a sum over periodic-boundary bonds | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsState β J N` | `gibbsState β (heisenbergHamiltonian (openChainCoupling N J))` (open-chain Gibbs state) | `Quantum/HeisenbergChain.lean` |
| `openChainHeisenbergGibbsState_isHermitian` | the open-chain Heisenberg Gibbs state `ρ_β` is Hermitian | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenbergGibbsState_commute_hamiltonian` | `[ρ_β, H_open] = 0` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenbergGibbsExpectation_zero` | high-temperature closed form `⟨A⟩_0 = (1/dim) · Tr A` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenbergGibbsExpectation_im_of_isHermitian` | for Hermitian `O`, `(⟨O⟩_β).im = 0` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenbergGibbsExpectation_commutator_hamiltonian` | conservation `⟨[H_open, A]⟩_β = 0` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenbergGibbsExpectation_hamiltonian_im` | `(⟨H_open⟩_β).im = 0` (energy expectation is real) | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenbergGibbsExpectation_mul_hamiltonian_im` | for Hermitian `O`, `(⟨H_open · O⟩_β).im = 0` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenbergGibbsExpectation_hamiltonian_sq_im` | `(⟨H_open^2⟩_β).im = 0` (energy-squared expectation real) | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenbergGibbsExpectation_hamiltonian_pow_im` | `(⟨H_open^n⟩_β).im = 0` for any `n : ℕ` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenbergGibbsExpectation_anticommutator_im` | for Hermitian `A, B`, `(⟨A·B + B·A⟩_β).im = 0` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenbergGibbsExpectation_commutator_re` | for Hermitian `A, B`, `(⟨A·B − B·A⟩_β).re = 0` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenbergGibbsHamiltonianVariance_im` | `(Var_β(H_open)).im = 0` (energy variance real) | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenberg_partitionFn_im` | `(partitionFn β H_open).im = 0` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenbergGibbsExpectation_ofReal_re_eq` | for Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenbergGibbsState_pow_trace` | `Tr(ρ_β^n) = Z(nβ) / Z(β)^n` for the open-chain Hamiltonian | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenbergGibbsState β J N` | analogous Gibbs state for the periodic-chain Hamiltonian | `Quantum/HeisenbergChain.lean` |
| `periodicChainHeisenbergGibbsState_isHermitian` | periodic-chain Gibbs state Hermiticity | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenbergGibbsState_commute_hamiltonian` | `[ρ_β, H_periodic] = 0` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenbergGibbsExpectation_zero` | periodic-chain high-temperature closed form | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenbergGibbsExpectation_im_of_isHermitian` | for Hermitian `O`, `(⟨O⟩_β).im = 0` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenbergGibbsExpectation_commutator_hamiltonian` | conservation `⟨[H_periodic, A]⟩_β = 0` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenbergGibbsExpectation_hamiltonian_im` | `(⟨H_periodic⟩_β).im = 0` (energy expectation is real) | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenbergGibbsExpectation_mul_hamiltonian_im` | for Hermitian `O`, `(⟨H_periodic · O⟩_β).im = 0` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenbergGibbsExpectation_hamiltonian_sq_im` | `(⟨H_periodic^2⟩_β).im = 0` (energy-squared expectation real) | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenbergGibbsExpectation_hamiltonian_pow_im` | `(⟨H_periodic^n⟩_β).im = 0` for any `n : ℕ` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenbergGibbsExpectation_anticommutator_im` | for Hermitian `A, B`, `(⟨A·B + B·A⟩_β).im = 0` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenbergGibbsExpectation_commutator_re` | for Hermitian `A, B`, `(⟨A·B − B·A⟩_β).re = 0` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenbergGibbsHamiltonianVariance_im` | `(Var_β(H_periodic)).im = 0` (energy variance real) | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenberg_partitionFn_im` | `(partitionFn β H_periodic).im = 0` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenbergGibbsExpectation_ofReal_re_eq` | for Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β` | `Quantum/HeisenbergChain/Gibbs.lean` |
| `periodicChainHeisenbergGibbsState_pow_trace` | `Tr(ρ_β^n) = Z(nβ) / Z(β)^n` for the periodic-chain Hamiltonian | `Quantum/HeisenbergChain/Gibbs.lean` |
| `openChainHeisenbergHamiltonian_two_site_eq` | for `N = 1` (the 2-site open chain on `Fin 2`), `H_open = -2J · spinHalfDot 0 1` (explicit one-bond reduction; Tasaki §2.4 simplest concrete instance) | `Quantum/HeisenbergChain/EigenvaluesCore.lean` |
<!-- legacy-source:end:1444:1546 -->

## Authoritative supplemental implementation record (2D / 3D Heisenberg lattice Gibbs expectation companions)

This section is maintained by hand, lies outside the migrated catalogue block above, and records
the current implementation of the 2D square-lattice, 2D square-torus and 3D cubic-lattice
Heisenberg Gibbs expectation companions. The migrated catalogue block above is a frozen historical
record — its rows are pinned byte-for-byte by `scripts/check_docs_hierarchy.py` and are never
edited for later relocations or deletions. In particular, the three brace-expansion rows for
`squareLatticeHeisenbergGibbsExpectation_{…}`, `squareTorusHeisenbergGibbsExpectation_{…}` and
`cubicLatticeHeisenbergGibbsExpectation_{…}` name the family members and the file
(`Quantum/HeisenbergLattice.lean`) as they were at migration time; the companions were later moved
out of that file, and most of them have since been retired.

Current locations: the 2D square-lattice and 2D square-torus companions live in
`Quantum/HeisenbergLattice/CompanionsCore.lean`, the 3D cubic-lattice companions in
`Quantum/HeisenbergLattice/Companions.lean`. Current membership is
`squareLatticeHeisenbergGibbsExpectation_zero` / `_im_of_isHermitian` /
`_commutator_hamiltonian` / `_hamiltonian_pow_im` and
`squareLatticeHeisenbergGibbsHamiltonianVariance_im`;
`squareTorusHeisenbergGibbsExpectation_zero` / `_hamiltonian_pow_im` / `_anticommutator_im`;
`cubicLatticeHeisenbergGibbsExpectation_zero` / `_hamiltonian_pow_im` / `_commutator_re` and
`cubicLatticeHeisenbergGibbsState_pow_trace`. The remaining members of each frozen row have been
retired as unreferenced one-line specializations.

The generic primitives those specializations apply — `gibbsExpectation_zero`,
`gibbsExpectation_im_of_isHermitian`, `gibbsExpectation_commutator_hamiltonian`,
`gibbsExpectation_mul_hamiltonian_im`, `gibbsExpectation_sq_im_of_isHermitian`,
`gibbsExpectation_pow_im_of_isHermitian`, `gibbsExpectation_anticommutator_im`,
`gibbsExpectation_commutator_re` and `gibbsState_pow_trace` — are unchanged in
`Quantum/GibbsState.lean` / `Quantum/GibbsState/Covariance.lean` and are exercised directly at the
generic index type by `LatticeSystem/Tests/GibbsState.lean`. The two further primitives
`gibbsVariance_im_of_isHermitian` (`Quantum/GibbsState/Covariance.lean`) and
`gibbsExpectation_ofReal_re_eq_of_isHermitian` (`Quantum/GibbsState.lean`) are unchanged as well,
but they have no direct test in `LatticeSystem/Tests/GibbsState.lean`; they are consumed by the
surviving named-model companions in `Quantum/IsingChain.lean`, `Quantum/HeisenbergChain/Gibbs.lean`
and `Quantum/HeisenbergLattice/CompanionsCore.lean`.

The graph-built Hubbard Gibbs state rows above are frozen in the same sense.
`Fermion/JordanWigner/Hubbard/Graph.lean` currently carries `hubbardGibbsStateOnGraph`, its
Hermiticity corollary `hubbardGibbsStateOnGraph_isHermitian` and the `rfl` bridge
`hubbardChainGibbsState_eq_onGraph`; the commute corollary
`hubbardGibbsStateOnGraph_commute_hamiltonian` has been retired as an unreferenced one-line
specialization of the generic `gibbsState_commute_hamiltonian`.

## Authoritative supplemental implementation record (Heisenberg-on-graph named-wrapper corollaries)

This section is maintained by hand, lies outside the migrated catalogue block above, and records
the current state of the Heisenberg-on-graph named wrapper. The migrated catalogue block above is a
frozen historical record — its rows are pinned byte-for-byte by `scripts/check_docs_hierarchy.py`
and are never edited for later deletions, so the brace-shorthand row
`heisenbergHamiltonianOnGraph_isHermitian` / `_commute_totalSpinHalfOp{1,2,3}` /
`_commute_totalSpinHalfSquared` describes membership as it stood at migration time.

That whole five-member family has since been retired as a duplicate re-exposure: each member was a
one-line restatement of the corresponding `couplingOf` theorem under the wrapper name. What
survives in `Quantum/HeisenbergChain.lean` is the definition
`heisenbergHamiltonianOnGraph G J = heisenbergHamiltonian (couplingOf G J)` together with the
canonical `couplingOf`-form theorems `heisenbergHamiltonian_couplingOf_isHermitian`,
`heisenbergHamiltonian_couplingOf_commute_totalSpinHalfOp1` / `_commute_totalSpinHalfOp2` /
`_commute_totalSpinHalfOp3` and `heisenbergHamiltonian_couplingOf_commute_totalSpinHalfSquared`.

Because the wrapper is definitionally its `couplingOf` right-hand side, those five theorems
discharge Hermiticity and SU(2) invariance for goals stated in wrapper form without any bridge
lemma; `LatticeSystem/Tests/Heisenberg.lean` pins that interoperability by stating the goals for
`heisenbergHamiltonianOnGraph` and proving them with the `couplingOf` theorems. The Gibbs rows for
`heisenbergGibbsStateOnGraph` are unaffected.

---

[← Gibbs state (Tasaki §3.3)](/lattice-system/formalization/legacy/24-gibbs-state-tasaki-3-3/) · [Catalogue](/lattice-system/formalization/legacy/) · [Heisenberg chain (Tasaki §3.5) →](/lattice-system/formalization/legacy/25-heisenberg-chain-tasaki-3-5-part-02/)
