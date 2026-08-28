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
Systems*, §3.3 eq. (3.3.1), p. 56 (transverse-field Ising on an open
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

---

[← Two-site spin inner product (Tasaki §2.2 eq. (2.2.16))](/lattice-system/formalization/legacy/21-two-site-spin-inner-product-tasaki-2-2-eq-2-2-16/) · [Catalogue](/lattice-system/formalization/legacy/) · [Testing infrastructure →](/lattice-system/formalization/legacy/23-testing-infrastructure/)
