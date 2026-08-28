---
layout: page
title: "Legacy catalogue: One-dimensional open-chain quantum Ising"
permalink: /formalization/legacy/22-one-dimensional-open-chain-quantum-ising/
---

# Legacy catalogue: One-dimensional open-chain quantum Ising

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin models, Chapters 3–7, and spectral tools](/lattice-system/formalization/legacy/#group-spin-models)

<!-- legacy-source:start:1301:1324 -->
### One-dimensional open-chain quantum Ising

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §3.3 eq. (3.3.1), p. 55 (transverse-field Ising on an open
chain). Our formalization uses the Pauli convention `σ = 2·S` and an
explicit bond coupling `J`.

| Lean name | Statement | File |
|---|---|---|
| `quantumIsingHamiltonian N J h` | `H = -J Σ σ^z_i σ^z_{i+1} - h Σ σ^x_i` | `Quantum/IsingChain.lean` |
| `quantumIsingHamiltonian_isHermitian` | `H` is Hermitian for real `J`, `h` | `Quantum/IsingChain.lean` |
| `spinZDot x y` | the Ising bond operator `σ^z_x · σ^z_y` (generic in `Λ`) | `Quantum/IsingChain.lean` |
| `spinZDot_isHermitian` | each bond operator is Hermitian | `Quantum/IsingChain.lean` |
| `isingHamiltonianGeneric (J : Λ → Λ → ℂ) (h : ℂ)` | **graph-friendly** Ising Hamiltonian `Σ J(x,y) σ^z_x σ^z_y − h Σ σ^x_x` for any finite `Λ` and pairwise coupling `J`; specialises to chain / graph / lattice via the choice of `J` | `Quantum/IsingChain.lean` |
| `isingHamiltonianGeneric_isHermitian` | Hermitian for entry-wise real `J` and real `h` | `Quantum/IsingChain.lean` |
| `isingHamiltonianOnGraph G J h` | graph wrapper: `isingHamiltonianGeneric (couplingOf G J) h`; double-sum convention matches Heisenberg-on-graph | `Quantum/IsingChain.lean` |
| `isingHamiltonianOnGraph_isHermitian` | Hermitian for real `J, h` | `Quantum/IsingChain.lean` |
| `isingGibbsStateOnGraph G β J h` | Gibbs state of the graph-built Ising Hamiltonian | `Quantum/IsingChain.lean` |
| `isingGibbsStateOnGraph_isHermitian` / `isingGibbsStateOnGraph_commute_hamiltonian` | Hermiticity (real `J, h`) and commute with the Hamiltonian | `Quantum/IsingChain.lean` |
| `LatticeSystem.Lattice.sum_pathGraph_forward` / `sum_pathGraph_backward` / `sum_pathGraph_adj` | sum-decomposition helpers for `pathGraph (N+1)` adjacency: `Σ_{x,y}` over ordered adjacent pairs = `Σ_{i:Fin N} (f i.cs i.s + f i.s i.cs)` | `Lattice/Graph.lean` |
| `pathGraphParityColoring` / `pathGraph_isBipartite` | parity-based 2-colouring of `pathGraph (N + 1)` (`i ↦ i.val % 2`) and the corresponding `IsBipartite` proof. Underpins the Néel state (`Quantum/NeelState.lean`) and the Marshall-Lieb-Mattis theorem (Tasaki §2.5) | `Lattice/Graph.lean` |
| `cycleGraphEvenParityColoring` / `cycleGraph_even_isBipartite` | parity-based 2-colouring of the even cycle `cycleGraph (2 * K + 2)` and the corresponding `IsBipartite` proof. Wrap-around case `(2K+1) + 1 ≡ 0` still flips parity because the cycle length is even (odd cycles are not bipartite) | `Lattice/Graph.lean` |
| `quantumIsingHamiltonian_eq_isingHamiltonianGeneric` | **generic-N bridge**: `quantumIsingHamiltonian N J h = isingHamiltonianGeneric (couplingOf (pathGraph (N+1)) (-J/2)) h`. The proof itself is the robust regression test | `Quantum/IsingChain.lean` |

<!-- legacy-source:end:1301:1324 -->

## Authoritative supplemental implementation record (page-citation correction)

This note is maintained by hand and lies outside the migrated catalogue block above; it is not
subject to the frozen byte-for-byte parity of the block above. The `p. 55` citation in the frozen
block above is a historical snapshot and is intentionally left unchanged. For the record: Tasaki,
*Physics and Mathematics of Quantum Many-Body Systems*, §3.3 heading appears on p. 55, but the
page breaks mid-paragraph and the numbered Hamiltonian eq. (3.3.1) itself is printed on p. 56
(verified against the rendered PDF).

## Authoritative supplemental implementation record (Problem 3.3.a configuration-basis matrix elements)

This section is maintained by hand, lies outside the migrated catalogue block above, and records
a new capstone added after the migration baseline (PR #5386); it is not subject to the frozen
byte-for-byte parity of the block above.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 3.3.a
(statement p. 59; solution: eqs. (S.24)-(S.26) on p. 498, eq. (S.27) and the "all other matrix
elements are vanishing" clause on p. 499), for the model of eq. (3.3.1), p. 56, with open
boundary conditions. These are **matrix elements, not energies**: with `h ≠ 0` the configuration
basis states are not eigenstates of the Hamiltonian, and this arc deliberately does not identify
any of these matrix elements with the true Hamiltonian's spectrum.

| Lean name | Statement | File |
|---|---|---|
| `quantumIsingHamiltonian_mulVec_apply` | pointwise action of `quantumIsingHamiltonian N J h` on an arbitrary vector `v` at a configuration `τ`: splits into a diagonal `σ^z σ^z` signed-bond-sum part and an off-diagonal `σ^x` single-site-flip sum; the identity all matrix elements below are read off from | `Quantum/IsingChainMatrixElements.lean` |
| `quantumIsingHamiltonian_apply_diag` | **diagonal matrix element** (Tasaki eqs. (S.24)-(S.25)): `⟨Φ_τ\|Ĥ\|Φ_τ⟩` is `-J` times the signed bond sum of `τ`, with no transverse-field contribution | `Quantum/IsingChainMatrixElements.lean` |
| `quantumIsingHamiltonian_apply_siteFlip` | **single-site-flip off-diagonal matrix element** (Tasaki eqs. (S.26)-(S.27)): `⟨Φ_{siteFlipAt τ x}\|Ĥ\|Φ_τ⟩ = -h`, independently of `J`, `τ`, and the flipped site `x` | `Quantum/IsingChainMatrixElements.lean` |
| `quantumIsingHamiltonian_apply_eq_zero` | all other matrix elements vanish (Tasaki p. 499, "all other matrix elements are vanishing"): configurations that are neither equal nor a single-site flip of one another are not connected by `Ĥ` | `Quantum/IsingChainMatrixElements.lean` |

## Authoritative supplemental implementation record (Problem 3.3.a low-energy 2L matrix)

This section is maintained by hand, lies outside the migrated catalogue block above, and records
a new capstone added after the migration baseline (PR #5387); it is not subject to the frozen
byte-for-byte parity of the block above.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 3.3.a
(statement p. 59; solution: eqs. (S.24)-(S.26) on p. 498, eqs. (S.27)-(S.31) and Fig. A.1 on
p. 499), for the model of eq. (3.3.1), p. 56, with open boundary conditions. The spin-`1/2`
convention `σ̂ = 2Ŝ` is §2.1, eqs. (2.1.7)-(2.1.8), p. 15, so the Hamiltonian is
`quantumIsingHamiltonian N (1/4) (λ/2)` on `L = N + 1` sites.

**The `2L` ring of eq. (S.30) is a ring of basis labels, not of lattice sites.** Tasaki's own
Fig. A.1 (p. 499) draws it as a ring of the `2L` basis states `|Φ↓⟩`, `|Φ_j^↑↓⟩`, `|Φ↑⟩`,
`|Φ_j^↓↑⟩` with a spin configuration attached to each site of the ring. Here the labels have type
`ZMod (2 * (N + 1))` while the lattice sites have type `Fin (N + 1)`; the two are never
identified, the chain stays open, and the periodic `isingCycleHamiltonian` is not used. Eq. (S.30)
is printed for `j = 1, …, 2L - 1` but p. 500 uses it at `j = 0`, so the formalization quantifies
over all labels.

These are **matrix elements, not energies**: `Ĥ` does not preserve the span of the `2L`
configurations, so no entry and no eigenvalue of `lowEnergyMatrix` is identified with the true
Hamiltonian's spectrum. Tasaki notes on p. 59 that the analysis of this problem is not
mathematically rigorous.

Every declaration below is **PROVED**; `#print axioms` on each yields only `propext`,
`Classical.choice`, `Quot.sound` (`wallSite` and the two book-form lemmas need even less).

| Lean name | Statement | File |
|---|---|---|
| `lowEnergyConfig`, `wallSite` | the `2L` low-energy configurations indexed by a label in `ZMod (2 * (N + 1))` (site `x` is up iff the label lies in the arc `x + 1, …, x + L`), and the fold of the label ring onto the chain that names the domain wall of a label | `Quantum/IsingLowEnergyProblem33a.lean` |
| `lowEnergyConfig_natCast_le`, `lowEnergyConfig_natCast_add` | book form of the two families: labels `0, …, L` give `\|Φ↓⟩`, `\|Φ_j^↑↓⟩`, `\|Φ↑⟩` (site `x` up iff `x < j`) and labels `L, …, 2L` give the mirror family `\|Φ_m^↓↑⟩` (site `x` down iff `x < m`) | `Quantum/IsingLowEnergyProblem33a.lean` |
| `lowEnergyConfig_injective` | the `2L` labels give `2L` pairwise distinct configurations, i.e. the low-energy space has the dimension `2L` named in the problem statement | `Quantum/IsingLowEnergyProblem33a.lean` |
| `lowEnergyConfig_succ_eq_siteFlipAt` | advancing the label by one step is exactly the single-site flip `siteFlipAt` at the domain wall `wallSite` | `Quantum/IsingLowEnergyProblem33a.lean` |
| `lowEnergyConfig_ne_of_not_adjacent` | labels that are neither equal nor ring-adjacent give configurations that are neither equal nor a single-site flip of one another (Tasaki p. 499, "all other matrix elements are vanishing", at configuration level); needs `1 ≤ N`, i.e. `L ≥ 2` | `Quantum/IsingLowEnergyProblem33a.lean` |
| `lowEnergyMatrix`, `ringPotential`, `tightBindingRing` | the `2L × 2L` array of **matrix elements** `⟨Φ_a\|Ĥ\|Φ_b⟩` in the low-energy configuration basis; the potential `v_j` of eq. (S.30) (`0` at the aligned labels `0` and `L`, `1/2` elsewhere); the tight-binding operator on the labels with hopping `-λ/2` between ring-adjacent labels | `Quantum/IsingLowEnergyProblem33a.lean` |
| `lowEnergyMatrix_eq_add_tightBindingRing` | **capstone of PR #5387**: every entry at once, `lowEnergyMatrix N λ = (-N/4) • 1 + tightBindingRing N λ` for `1 ≤ N` — Tasaki eqs. (S.24)-(S.27) together with "all other matrix elements are vanishing" (p. 499), subsuming the printed index ranges of (S.25) and (S.26) | `Quantum/IsingLowEnergyProblem33a.lean` |

Regression fixtures live in `LatticeSystem/Tests/Problem33aLowEnergy.lean`: the `L = 2` diagonal
entries pin `E_GS^(0) = -(L-1)/4 = -1/4` (a physically periodic chain would give `-1/2`), and the
`L = 3` entry between the labels `0` and `2L - 1 = 5` pins the wrap-around of the label ring.

---

[← Two-site spin inner product (Tasaki §2.2 eq. (2.2.16))](/lattice-system/formalization/legacy/21-two-site-spin-inner-product-tasaki-2-2-eq-2-2-16/) · [Catalogue](/lattice-system/formalization/legacy/) · [Testing infrastructure →](/lattice-system/formalization/legacy/23-testing-infrastructure/)
