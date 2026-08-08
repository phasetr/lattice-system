---
layout: page
title: "Legacy catalogue: Testing infrastructure"
permalink: /formalization/legacy/23-testing-infrastructure/
---

# Legacy catalogue: Testing infrastructure

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Project infrastructure](/lattice-system/formalization/legacy/#group-project-infrastructure)

<!-- legacy-source:start:1325:1348 -->
### Testing infrastructure

| Lean name / location | Purpose |
|---|---|
| `LatticeSystem/Tests/Sanity.lean` | sanity-check `example` blocks for concrete small-N instances (Pauli arithmetic, spin-1/2 ladder actions, Heisenberg / Ising Hermiticity on small chains, graph-centric bridge identities) |
| decide-based property tests (in `Tests/Sanity.lean`) | universally-quantified properties verified by `decide` on small finite types (graph adjacency symmetry / irreflexivity / connectivity on `pathGraph n` and `cycleGraph n` for small `n`); real proofs, no `sorry` |
| `quantumIsingGibbsState β J h N` | `gibbsState β (quantumIsingHamiltonian N J h)` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsState_isHermitian` | the Ising-chain Gibbs state `ρ_β` is Hermitian | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsState_commute_hamiltonian` | `[ρ_β, H_Ising] = 0` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_zero` | infinite-temperature closed form `⟨A⟩_0 = (1/dim) · Tr A` (independent of `J, h`) | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_im_of_isHermitian` | for Hermitian `O`, `(⟨O⟩_β).im = 0` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_commutator_hamiltonian` | conservation `⟨[H_Ising, A]⟩_β = 0` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_hamiltonian_im` | `(⟨H_Ising⟩_β).im = 0` (energy expectation is real) | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_mul_hamiltonian_im` | for Hermitian `O`, `(⟨H_Ising · O⟩_β).im = 0` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_hamiltonian_sq_im` | `(⟨H_Ising^2⟩_β).im = 0` (energy-squared expectation real) | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_hamiltonian_pow_im` | `(⟨H_Ising^n⟩_β).im = 0` for any `n : ℕ` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_anticommutator_im` | for Hermitian `A, B`, `(⟨A·B + B·A⟩_β).im = 0` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_commutator_re` | for Hermitian `A, B`, `(⟨A·B − B·A⟩_β).re = 0` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsHamiltonianVariance_im` | `(Var_β(H_Ising)).im = 0` (energy variance real) | `Quantum/IsingChain.lean` |
| `quantumIsing_partitionFn_im` | `(partitionFn β H_Ising).im = 0` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_ofReal_re_eq` | for Hermitian `O`, `((⟨O⟩_β).re : ℂ) = ⟨O⟩_β` | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsState_pow_trace` | `Tr(ρ_β^n) = Z(nβ) / Z(β)^n` for the Ising Hamiltonian | `Quantum/IsingChain.lean` |
| `quantumIsingGibbsExpectation_self_eq` | `⟨H_Ising⟩_β = -J · ∑ ⟨σ^z σ^z⟩_β + (-h) · ∑ ⟨σ^x⟩_β` (energy as bond + transverse-field decomposition) | `Quantum/IsingChain.lean` |

<!-- legacy-source:end:1325:1348 -->

---

[← One-dimensional open-chain quantum Ising](/lattice-system/formalization/legacy/22-one-dimensional-open-chain-quantum-ising/) · [Catalogue](/lattice-system/formalization/legacy/) · [Gibbs state (Tasaki §3.3) →](/lattice-system/formalization/legacy/24-gibbs-state-tasaki-3-3/)
