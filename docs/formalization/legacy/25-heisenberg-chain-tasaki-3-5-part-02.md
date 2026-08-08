---
layout: page
title: "Legacy catalogue: Heisenberg chain (Tasaki §3.5) (part 2 of 2)"
permalink: /formalization/legacy/25-heisenberg-chain-tasaki-3-5-part-02/
---

# Legacy catalogue: Heisenberg chain (Tasaki §3.5) (part 2 of 2)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin models, Chapters 3–7, and spectral tools](/lattice-system/formalization/legacy/#group-spin-models)

<!-- legacy-source:start:1547:1561 -->
| Lean name | Statement | File |
|---|---|---|
| `openChainHeisenbergHamiltonian_two_site_mulVec_basisVec_all_up` | `H_open(N=1) · |↑↑⟩ = -(J/2) · |↑↑⟩` — `|↑↑⟩` lies in the `S = 1` triplet sector and is an exact eigenvector with eigenvalue `-J/2` (this is the ferromagnetic ground state for `J < 0`) | `Quantum/HeisenbergChain/EigenvaluesCore.lean` |
| `openChainHeisenbergHamiltonian_two_site_mulVec_basisVec_singlet` | `H_open(N=1) · (|↑↓⟩ - |↓↑⟩) = (3J/2) · (|↑↓⟩ - |↓↑⟩)` — singlet eigenvalue, the antiferromagnetic ground state for `J > 0` (Tasaki §2.5 concrete instance) | `Quantum/HeisenbergChain/EigenvaluesCore.lean` |
| `openChainHeisenbergHamiltonian_two_site_mulVec_basisVec_all_down` | `H_open(N=1) · |↓↓⟩ = -(J/2) · |↓↓⟩` — all-down state has the same eigenvalue as all-up (both are `S = 1` triplet states) | `Quantum/HeisenbergChain/EigenvaluesCore.lean` |
| `openChainHeisenbergHamiltonian_two_site_mulVec_basisVec_triplet_zero` | `H_open(N=1) · (|↑↓⟩ + |↓↑⟩) = -(J/2) · (|↑↓⟩ + |↓↑⟩)` — triplet `m = 0` state, completing the 3-fold degenerate triplet representation `S = 1` with eigenvalue `-J/2` | `Quantum/HeisenbergChain/EigenvaluesCore.lean` |
| `openChainHeisenbergHamiltonian_three_site_eq` | for `N = 2` (the 3-site open chain on `Fin 3`, 2 bonds), `H_open = -2J · (spinHalfDot 0 1 + spinHalfDot 1 2)` — explicit two-bond reduction | `Quantum/HeisenbergChain/EigenvaluesCore.lean` |
| `openChainHeisenbergHamiltonian_three_site_mulVec_basisVec_all_up` | `H_open(N=2) · |↑↑↑⟩ = -J · |↑↑↑⟩` — confirming the linear scaling `E(|↑..↑⟩) = -N·J/2` (here `N = 2` bonds, `J = 1` per bond) | `Quantum/HeisenbergChain/EigenvaluesCore.lean` |
| `openChainCoupling_sum_eq` | for any `N : ℕ`, `Σ_{x,y ∈ Fin (N+1)} openChainCoupling N J x y = -(2N · J : ℂ)` (the bond-counting lemma: each of the `N` unordered nearest-neighbour bonds is counted in both orientations) | `Quantum/HeisenbergChain/EigenvaluesCore.lean` |
| `openChainHeisenbergHamiltonian_mulVec_basisVec_const` | for any `N : ℕ`, `J : ℝ`, and constant `s : Fin 2`, `H_open · |s..s⟩ = -(N·J/2 : ℂ) · |s..s⟩` — both `s = 0` (all-up) and `s = 1` (all-down) share the same eigenvalue by SU(2) symmetry | `Quantum/HeisenbergChain/EigenvaluesCore.lean` |
| `openChainHeisenbergHamiltonian_mulVec_basisVec_all_up` | `s = 0` specialisation of the above (Tasaki §2.4 (2.4.5)/(2.4.1) ferromagnetic ground-state energy `E_GS = -|B|·S²` for `S = 1/2`, `|B| = N` bonds) | `Quantum/HeisenbergChain/EigenvaluesCore.lean` |
| `openChainHeisenbergHamiltonian_mulVec_basisVec_all_down` | `s = 1` specialisation: same eigenvalue `-(N·J/2)` for the all-down state by SU(2) symmetry | `Quantum/HeisenbergChain/EigenvaluesCore.lean` |
| `openChainHeisenbergHamiltonian_mulVec_totalSpinHalfOpMinus_pow_basisVec_all_up` | for any `N : ℕ`, `J : ℝ`, `k : ℕ`, `H_open · ((Ŝtot^-)^k · |↑..↑⟩) = -(N·J/2 : ℂ) · ((Ŝtot^-)^k · |↑..↑⟩)` — the unnormalised Tasaki §2.4 (2.4.9) ferromagnetic ground states `|Φ_M⟩` made explicit on the chain (combines PRs #82 + #98) | `Quantum/HeisenbergChain/Eigenvalues.lean` |
| `openChainHeisenbergHamiltonian_mulVec_totalSpinHalfOpPlus_pow_basisVec_all_down` | dual ladder from `|↓..↓⟩`, same eigenvalue `-(N·J/2)` | `Quantum/HeisenbergChain/Eigenvalues.lean` |
| `openChainHeisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem` | `H_open` preserves every magnetisation subspace `H_M` (chain specialisation of PR #91) | `Quantum/HeisenbergChain/Eigenvalues.lean` |
| `periodicChainHeisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem` | `H_periodic` preserves every magnetisation subspace `H_M` (chain specialisation of PR #91) | `Quantum/HeisenbergChain/Eigenvalues.lean` |

<!-- legacy-source:end:1547:1561 -->

---

[← Heisenberg chain (Tasaki §3.5)](/lattice-system/formalization/legacy/25-heisenberg-chain-tasaki-3-5-part-01/) · [Catalogue](/lattice-system/formalization/legacy/) · [Perron-Frobenius theorem (`Math/PerronFrobenius.lean`, `Math/PerronFrobeniusPrimitive.lean`, `Math/CollatzWielandt.lean`, `Math/PerronFrobeniusMain.lean`) →](/lattice-system/formalization/legacy/26-perron-frobenius-theorem/)
