---
layout: page
title: "Legacy catalogue: Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8)) (part 1 of 5)"
permalink: /formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-01/
---

# Legacy catalogue: Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8)) (part 1 of 5)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:784:888 -->
### Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8))

> **Pruned rows (PR #5143, issue #5140).** 540 rows of the later γ-4 layers were removed from this section; see [Deleted routes](/lattice-system/history/deleted-routes/#deleted-routes-what-this-index-used-to-document) for what they documented.

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.2 eqs. (2.2.7) and (2.2.8), p. 22.

| Lean name | Statement | File |
|---|---|---|
| `totalSpinHalfOp{1,2,3} Λ` | `Ŝ_tot^(α) := Σ_{x ∈ Λ} onSite x Ŝ^(α)` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp{1,2,3}_isHermitian` | `Ŝ_tot^(α)` is Hermitian | `Quantum/TotalSpin.lean` |
| `spinHalfOp_onSite_comm_of_ne` | S = 1/2 named wrapper of `onSite_mul_onSite_of_ne` | `Quantum/TotalSpin.lean` |
| `spinHalfOp{1,2,3}_onSite_commutator_spinHalfOp{2,3,1}_onSite` | same-site commutator `[Ŝ_x^(α), Ŝ_x^(β)] = i · Ŝ_x^(γ)` (Tasaki (2.2.6), `x = y`) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus`, `totalSpinHalfOpMinus` | `Ŝ^±_tot := Σ_{x ∈ Λ} onSite x Ŝ^±` (Tasaki (2.2.8)) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus_eq_add`, `totalSpinHalfOpMinus_eq_sub` | `Ŝ^±_tot = Ŝ^(1)_tot ± i · Ŝ^(2)_tot` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus/Minus_conjTranspose` | `(Ŝ^±_tot)† = Ŝ^∓_tot` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp{1,2,3}_commutator_totalSpinHalfOp{2,3,1}` | `[Ŝ_tot^(α), Ŝ_tot^(β)] = i · Ŝ_tot^(γ)` (total spin commutation) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp3_commutator_totalSpinHalfOpPlus/Minus` | `[Ŝ_tot^(3), Ŝ^±_tot] = ±Ŝ^±_tot` (Cartan ladder relations) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfSquared` / `_isHermitian` | Casimir operator `(Ŝ_tot)² := Σ_α (Ŝ_tot^(α))²` and its Hermiticity | `Quantum/TotalSpin/Casimir.lean` |
| `totalSpinHalfSquared_commutator_totalSpinHalfOp{1,2,3}` | `[(Ŝ_tot)², Ŝ_tot^(α)] = 0` (Casimir invariance, cf. Tasaki (2.2.12)) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfSquared_commutator_totalSpinHalfOpPlus/Minus` | `[(Ŝ_tot)², Ŝ^±_tot] = 0` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus_commutator_totalSpinHalfOpMinus` | `[Ŝ^+_tot, Ŝ^-_tot] = 2 · Ŝ_tot^(3)` | `Quantum/TotalSpin/Casimir.lean` |
| `magnetization`, `spinSign` | total magnetization `|σ| := Σ_x spinSign(σ_x)` (Tasaki (2.2.2)) | `Quantum/TotalSpin.lean` |
| `spinHalfSign` | half-integer eigenvalue of `Ŝ^(3)` on `Fin 2` basis | `Quantum/TotalSpin.lean` |
| `onSite_spinHalfOp3_mulVec_basisVec` | `Ŝ_x^(3) · |σ⟩ = ±(1/2) · |σ⟩` (single-site eigenvalue) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp3_mulVec_basisVec` | `Ŝ_tot^(3) · |σ⟩ = (Σ_x spinHalfSign(σ_x)) · |σ⟩`, partial (2.2.10) | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp3_mulVec_basisVec_eq_magnetization` | `Ŝ_tot^(3) · |σ⟩ = (|σ| / 2) · |σ⟩` (full Tasaki eq. (2.2.10)) | `Quantum/TotalSpin.lean` |
| `onSite_spinHalfOpPlus/Minus_mulVec_basisVec` | raising/lowering action `Ŝ_x^± · |σ⟩` on a basis state at site `x` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus/Minus_mulVec_basisVec` | total `Ŝ^±_tot · |σ⟩` as a sum of site-wise actions | `Quantum/TotalSpin.lean` |
| `totalSpinHalfRot{1,2,3}Pi` | global π-rotation `Û^(α)_π_tot := ∏_x Û^(α)_π_x` (Tasaki eq. (2.2.11) at θ = π) via `Finset.noncommProd` | `Quantum/TotalSpin/Rotation.lean` |
| `totalSpinHalfRot{1,2,3} θ` | general-θ global rotation `Û^(α)_θ_tot := ∏_x Û^(α)_θ_x` (Tasaki eq. (2.2.11)) | `Quantum/TotalSpin/Rotation.lean` |
| `totalSpinHalfRot{1,2,3}_zero` | `Û^(α)_0_tot = 1` (identity rotation) | `Quantum/TotalSpin/Rotation.lean` |
| `totalSpinHalfRot{1,2,3}Pi_eq` | π-rotation matches the general-θ form at `θ = π` | `Quantum/TotalSpin/Rotation.lean` |
| `totalSpinHalfRot{1,2,3}Pi_mul_totalSpinHalfRot{2,3,1}Pi` | `Û^(α)_π_tot · Û^(β)_π_tot = Û^(γ)_π_tot` (cyclic, Tasaki Problem 2.2.a) | `Quantum/TotalSpin/Rotation.lean` |
| `onSiteRingHom x` / `onSiteLinearMap x` / `continuous_onSite x` | `onSite x` packaged as a `RingHom`, ℂ-linear map, and continuous function | `Quantum/TotalSpin/Rotation.lean` |
| `onSite_pow` | `(onSite x A)^k = onSite x (A^k)` (powers commute with `onSite`) | `Quantum/TotalSpin/Rotation.lean` |
| `totalSpinHalfRot{1,2,3}Pi_two_site` | for `Λ = Fin 2`, the global π-rotation factors as `onSite 0 (Û^(α)_π) * onSite 1 (Û^(α)_π)` (Tasaki Problem 2.2.b) | `Quantum/TotalSpin/Rotation.lean` |
| `totalSpinHalfOp3_mulVec_totalSpinHalfOpMinus_pow_basisVec_all_up` | for any `k : ℕ`, `Ŝtot^(3) · (Ŝtot^-)^k · |↑..↑⟩ = (|Λ|/2 - k) · (Ŝtot^-)^k · |↑..↑⟩` — the magnetic-quantum-number `M = Smax - k` labelling of the unnormalised iterates `(Ŝtot^-)^k · |Φ↑⟩` (Tasaki's `|Φ_M⟩` of eq. (2.4.9), p. 33, up to normalisation). Proof via Nat induction using the Cartan ladder `[Ŝtot^(3), Ŝtot^-] = -Ŝtot^-` | `Quantum/TotalSpin/Casimir.lean` |
| `mulVec_preserves_eigenvalue_of_commute` | generic abstract pattern: for any `A B : ManyBodyOp Λ` with `Commute A B`, if `A · v = λ · v` then `A · (B · v) = λ · (B · v)` — the backbone of all commutator-based eigenvalue propagation | `Quantum/TotalSpin/Casimir.lean` |
| `totalSpinHalfOp3_mulVec_totalSpinHalfOpPlus_pow_basisVec_all_down` | dual ladder: for any `k : ℕ`, `Ŝtot^(3) · (Ŝtot^+)^k · |↓..↓⟩ = (-|Λ|/2 + k) · (Ŝtot^+)^k · |↓..↓⟩` — same Tasaki §2.4 (2.4.9) ladder parameterised from the lowest weight `M = -Smax`, raised by `Ŝtot^+`. Proof: Nat induction using `[Ŝtot^(3), Ŝtot^+] = +Ŝtot^+` | `Quantum/TotalSpin/Casimir.lean` |
| `totalSpinHalfOp3_mulVec_basisVec_const` / `_all_up` / `_all_down` | constant-config Ŝtot^(3) eigenvalue: `Ŝtot^(3) · |s..s⟩ = (|Λ| · spinHalfSign s) · |s..s⟩`; `s = 0` gives eigenvalue `|Λ|/2 = Smax`, `s = 1` gives `-|Λ|/2 = -Smax` | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpMinus_mulVec_basisVec_all_down` | `Ŝtot^- · |↓..↓⟩ = 0`: lowering annihilates the bottom of the ladder | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOpPlus_mulVec_basisVec_all_up` | `Ŝtot^+ · |↑..↑⟩ = 0`: raising annihilates the top of the ladder | `Quantum/TotalSpin.lean` |
| `totalSpinHalfOp{Minus,Plus}_pow_basisVec_all_{up,down}_mem_magnetizationSubspace` | Submodule-form: `(Ŝtot^-)^k · |↑..↑⟩ ∈ H_{Smax - k}` and `(Ŝtot^+)^k · |↓..↓⟩ ∈ H_{-Smax + k}` — Tasaki §2.4 eq. (2.4.9) ladder iterates explicitly placed in the magnetisation sectors of Tasaki eq. (2.2.10) | `Quantum/MagnetizationSubspace.lean` |
| `basisVec_{upDown,basisSwap_upDown}_mem_magnetizationSubspace_zero` | two-site antiparallel states `|↑↓⟩`, `|↓↑⟩` lie in `H_0` (Tasaki §2.5 (2.5.2), p. 37, Néel state for the spin-1/2 Fin 2 instance) | `Quantum/MagnetizationSubspace.lean` |
| `singlet_mem_magnetizationSubspace_zero` / `triplet_zero_mem_magnetizationSubspace_zero` | singlet `|↑↓⟩ - |↓↑⟩` and triplet-`m=0` state `|↑↓⟩ + |↓↑⟩` lie in `H_0` (Tasaki §A.3 decomposition at the `M = 0` sector) | `Quantum/MagnetizationSubspace.lean` |
| `neelChainConfig` / `neelChainState` | Tasaki §2.5 eq. (2.5.2) Néel state at `S = 1/2` on the parity-coloured chain `Fin (2 * K)`: `σ(i) = ↑` if `i.val` even, `↓` if odd | `Quantum/NeelState/Definition.lean` |
| `neelChainConfig_magnetization_zero` / `neelChainState_mem_magnetizationSubspace_zero` | the Néel chain configuration has total magnetisation `0`, so the corresponding basis state lies in the `Ŝ_tot^(3) = 0` eigenspace `H_0` | `Quantum/NeelState/Definition.lean` |
| `heisenbergHamiltonian_mulVec_neelChainState_mem_magnetizationSubspace_zero` | for any coupling `J`, `H · |Φ_Néel⟩` again lies in `H_0` — immediate corollary of SU(2) invariance applied to the Néel state. The Néel state is *not* an H-eigenstate (Tasaki §2.5 (2.5.3)), but it cannot leak into other magnetisation sectors | `Quantum/NeelState/Definition.lean` |
| `spinHalfDot_mulVec_neelChainState_adjacent` | Tasaki §2.5 eq. (2.5.3) per-bond action: for every adjacent pair `(i, i+1)` of the chain `Fin (2 * K)`, `Ŝ_⟨i⟩ · Ŝ_⟨i+1⟩ · |Φ_Néel⟩ = (1/2) · |swap_{i,i+1} Φ_Néel⟩ - (1/4) · |Φ_Néel⟩` (antiparallel case, parity-derived) | `Quantum/NeelState/BondAction/Chain.lean` |
| `spinHalfDot_mulVec_neelChainState_wrap` | wrap-around bond `(2K + 1, 0)` action on the periodic chain `Fin (2 * (K + 1))`: same `(1/2) swap - (1/4) Néel` decomposition as the open-bond case (parities `1` and `0` differ since the cycle length is even). Together with the adjacent lemma, covers every bond of the periodic chain | `Quantum/NeelState/BondAction/Chain.lean` |
| `heisenbergHamiltonian_openChainCoupling_one_mulVec_neelChainState_one` | `K = 1` instance: `H_open(N=1, J) · |Φ_Néel⟩ = -J · |↓↑⟩ + (J/2) · |Φ_Néel⟩`. Lifts the per-bond `spinHalfDot` calculation through `H_open(N=1, J) = -2J · spinHalfDot 0 1`. The non-eigenstate character of the Néel state is plain | `Quantum/NeelState/BondAction/Chain.lean` |
| `neelChainConfig_one_eq_upDown` / `timeReversalSpinHalfMulti_neelChainState_one` | bridges the `K = 1` Néel chain configuration to the existing `upDown` config and computes `Θ̂_tot (neelChainState 1) = -basisVec (basisSwap upDown 0 1)` (the per-down sign convention of `Θ̂` flips the antiparallel pair) | `Quantum/NeelState/TimeReversal.lean` |
| `neelSquareConfig` / `neelSquareState` | 2D checkerboard Néel state on `Fin (2K) × Fin (2L)` (Tasaki §2.5 (2.5.2) bipartite case): `σ(i, j) = ↑` if `(i.val + j.val) % 2 = 0`, `↓` otherwise | `Quantum/NeelState/Definition2D.lean` |
| `neelSquareConfig_magnetization_zero` / `neelSquareState_mem_magnetizationSubspace_zero` | the 2D Néel configuration has total magnetisation `0` and the corresponding state lies in the `Ŝ_tot^(3) = 0` eigenspace `H_0`. Proof: row-by-row column-sum vanishes (helper `sum_alternating_sign_offset` for the 1D parity sum with offset) | `Quantum/NeelState/Definition2D.lean` |
| `spinHalfDot_mulVec_neelSquareState_horizontal_adjacent` / `_vertical_adjacent` | Tasaki §2.5 (2.5.3) per-bond action on the 2D Néel state for the horizontal (`(i,j)~(i+1,j)`) and vertical (`(i,j)~(i,j+1)`) nearest-neighbour bonds: same `(1/2) · |swap⟩ - (1/4) · |Φ_Néel⟩` decomposition as the 1D chain | `Quantum/NeelState/BondAction/Square.lean` |
| `spinHalfDot_mulVec_neelSquareState_horizontal_wrap` / `_vertical_wrap` | wrap-around bond actions on the 2D torus Néel state: horizontal `((2K+1, j), (0, j))` on `Fin (2(K+1)) × Fin (2L)` and vertical `((i, 2L+1), (i, 0))` on `Fin (2K) × Fin (2(L+1))` are antiparallel (parities differ by an odd shift); both inherit the same `(1/2)·|swap⟩ - (1/4)·|Φ_Néel⟩` decomposition. With `_horizontal_adjacent` / `_vertical_adjacent`, covers every nearest-neighbour bond of the 2D torus Néel state | `Quantum/NeelState/BondAction/Square.lean` |
| `neelCubicConfig` / `neelCubicState` / `neelCubicConfig_magnetization_zero` / `neelCubicState_mem_magnetizationSubspace_zero` | 3D cubic checkerboard Néel state on `(Fin (2K) × Fin (2L)) × Fin (2M)`: `σ((i,j),k) = ↑` if `(i+j+k) % 2 = 0`, magnetisation = 0, lies in `H_0` | `Quantum/NeelState/Definition3D.lean` |
| `spinHalfDot_mulVec_neelCubicState_x_adjacent` / `_y_adjacent` / `_z_adjacent` | Tasaki §2.5 (2.5.3) per-bond actions on the 3D cubic Néel state for the three nearest-neighbour bond axes (x, y, z): same `(1/2)·|swap⟩ - (1/4)·|Φ_Néel⟩` decomposition | `Quantum/NeelState/BondAction/Cubic.lean` |
| `spinHalfDot_mulVec_neelCubicState_x_wrap` / `_y_wrap` / `_z_wrap` | wrap-around bond actions on the 3D cubic-torus Néel state: each axis-wrap (`((2K+1, j), k) ~ ((0, j), k)`, `((i, 2L+1), k) ~ ((i, 0), k)`, `((i, j), 2M+1) ~ ((i, j), 0)`) is antiparallel (one coordinate shifts by an odd amount). All three axes inherit the same `(1/2)·|swap⟩ - (1/4)·|Φ_Néel⟩` decomposition. With `_x_adjacent` / `_y_adjacent` / `_z_adjacent`, covers every nearest-neighbour bond of the 3D cubic torus Néel state | `Quantum/NeelState/BondAction/Cubic.lean` |
| `timeReversalSpinHalfMulti_neelSquareState_one_one` | concrete `K = L = 1` (2×2 = 4-site) instance: `Θ̂_tot (neelSquareState 1 1) = basisVec (flipConfig (neelSquareConfig 1 1))` (the equal up/down counts make `(-1)^|A| = 1`, so no overall sign) | `Quantum/NeelState/TimeReversal.lean` |
| `timeReversalSpinHalfMulti_neelCubicState_one_one_one` | concrete `K = L = M = 1` (2×2×2 = 8-site) instance: `Θ̂_tot (neelCubicState 1 1 1) = basisVec (flipConfig (neelCubicConfig 1 1 1))` (4 down spins after flipping → `(-1)^4 = 1`, so no overall sign) | `Quantum/NeelState/TimeReversal.lean` |
| `timeReversalSpinHalfMulti_neelChainState` | general-`K` 1D chain: `Θ̂_tot (neelChainState K) = (-1)^K · basisVec (flipConfig (neelChainConfig K))` (helper `prod_alternating_neg_one` collapses the per-site sign product). Specialisations at K=1 (factor −1), K=2 (factor 1), K=3 (factor −1) provided as tests | `Quantum/NeelState/TimeReversal.lean` |
| `timeReversalSpinHalfMulti_neelSquareState` | general-`K, L` 2D checkerboard: `Θ̂_tot (neelSquareState K L) = basisVec (flipConfig (neelSquareConfig K L))` (no sign because `(-1)^(2KL) = 1`). Helper `prod_alternating_neg_one_offset` reduces the parity-shifted column product to `(-1)^L`, then the row product `((-1)^L)^(2K) = 1` | `Quantum/NeelState/TimeReversal.lean` |
| `timeReversalSpinHalfMulti_neelCubicState` | general-`K, L, M` 3D cubic checkerboard: `Θ̂_tot (neelCubicState K L M) = basisVec (flipConfig (neelCubicConfig K L M))` (no sign because `(-1)^(4KLM) = 1`). Reduces along `k`-axis to `(-1)^M` then collapses the `(2K)·(2L)`-fold product | `Quantum/NeelState/TimeReversal.lean` |
| `basisVec_apply` / `basisVec_self` / `basisVec_of_ne` | foundational evaluation lemmas for the standard basis vectors: explicit `if`-form, diagonal `=1`, and off-diagonal `=0` | `Quantum/ManyBody.lean` |
| `sum_mul_basisVec` / `basisVec_sum_mul` | selector-sum identities `∑ τ, f τ · basisVec σ τ = f σ` (and the symmetric form), the workhorses for inner-product computations on the spin Hilbert space | `Quantum/ManyBody.lean` |
| `basisVec_inner` | basis-vector orthonormality `∑ τ, basisVec σ τ · basisVec ρ τ = if ρ = σ then 1 else 0`. Real bilinear pairing (no complex conjugation needed since `basisVec` values are 0 or 1) | `Quantum/ManyBody.lean` |
| `basisSwap_ne_self` | `σ x ≠ σ y → basisSwap σ x y ≠ σ` (the swap of an antiparallel pair changes the configuration). Useful for orthogonality computations on swapped states | `Quantum/SpinDot/Core.lean` |
| `neelChainState_norm_squared` / `neelSquareState_norm_squared` / `neelCubicState_norm_squared` | the 1D / 2D / 3D Néel states are normalized: `∑ τ, |Φ_Néel(τ)|² = 1` (one-line consequence of `basisVec_inner`) | `Quantum/NeelState/InnerProductCore.lean` |
| `neelChainState_inner_basisVec_basisSwap_adjacent_eq_zero` | the Néel chain state is orthogonal to the swapped basis vector at any adjacent (antiparallel) bond: `∑ τ, Φ_Néel(τ) · basisVec(swap)(τ) = 0`. Direct consequence of `basisVec_inner` + `basisSwap_ne_self` | `Quantum/NeelState/InnerProductCore.lean` |
| `neelChainState_inner_spinHalfDot_adjacent_eq_neg_one_quarter` | the per-adjacent-bond expectation `⟨Φ_Néel, Ŝ_x · Ŝ_y · Φ_Néel⟩ = -1/4` (Tasaki §2.5 (2.5.4) ingredient at S = 1/2). Combines `spinHalfDot_mulVec_neelChainState_adjacent` (bond action) with the orthogonality + norm² lemmas to compute `(1/2)·0 - (1/4)·1 = -1/4` | `Quantum/NeelState/InnerProductCore.lean` |
| `inner_basisVec_spinHalfDot_basisVec_antiparallel` | generic lemma: for any antiparallel `(x, y)` configuration `σ`, `⟨basisVec σ, Ŝ_x · Ŝ_y · basisVec σ⟩ = -1/4`. The 1-line foundation for every Néel-bond expectation | `Quantum/SpinDot/Core.lean` |
| `inner_basisVec_spinHalfDot_basisVec_parallel` | parallel companion: for `σ x = σ y` (and `x ≠ y`), `⟨basisVec σ, Ŝ_x · Ŝ_y · basisVec σ⟩ = +1/4`. Both basis vectors at the parallel pair are eigenvectors of `Ŝ_x · Ŝ_y` (eigenvalue `+1/4`) | `Quantum/SpinDot/Core.lean` |
| `neelChainState_inner_spinHalfDot_parallel_eq_one_quarter` | Néel chain same-sublattice (parallel) bond expectation `+1/4`: for any `x ≠ y` with `x.val % 2 = y.val % 2` (e.g., `(0, 2)`, `(1, 3)`), `⟨Φ_Néel, Ŝ_x · Ŝ_y · Φ_Néel⟩ = +1/4` | `Quantum/NeelState/InnerProduct.lean` |
| `onSite_spinHalfOp3_mul_onSite_spinHalfOp3_mulVec_basisVec` | `(Ŝ^(3)_x · Ŝ^(3)_y) · basisVec σ = (spinHalfSign σ x · spinHalfSign σ y) · basisVec σ`: every basis vector is an eigenvector of the diagonal `Ŝ^z·Ŝ^z` correlator. Composes the single-site action `Ŝ^(3)_x · |σ⟩ = ε_x · |σ⟩` twice | `Quantum/SpinDot/Core.lean` |
| `inner_basisVec_szsz_basisVec` | generic `⟨basisVec σ, Ŝ^(3)_x · Ŝ^(3)_y · basisVec σ⟩ = spinHalfSign σ x · spinHalfSign σ y`. The diagonal-only spin-spin correlator on a basis state | `Quantum/SpinDot/Core.lean` |
| `spinHalfSign_mul_antiparallel` | for antiparallel `s ≠ t : Fin 2`, `spinHalfSign s · spinHalfSign t = -(1/4)`. Made public in PR #332 to power the generic `inner_neelStateOf_szsz_neelStateOf_antiparallel = -(1/4)` Néel correlator | `Quantum/SpinDot/Core.lean` |
| `inner_basisVec_spinHalfDot_sub_szsz_basisVec_antiparallel` | generic off-diagonal correlator: for any antiparallel `(x, y)` configuration `σ`, `⟨basisVec σ, (Ŝ_x · Ŝ_y - Ŝ^(3)_x · Ŝ^(3)_y) · basisVec σ⟩ = 0`. The off-diagonal `(Ŝ^x·Ŝ^x + Ŝ^y·Ŝ^y)` part is entirely supported on swap states (⟂ to the original) | `Quantum/SpinDot/Core.lean` |
| `neelChainState_inner_off_diagonal_correlator_adjacent_eq_zero` | the per-adjacent-bond off-diagonal correlator on the Néel chain vanishes: `⟨Φ_Néel, (Ŝ_x · Ŝ_y - Ŝ^(3)_x · Ŝ^(3)_y) · Φ_Néel⟩ = 0`. Direct application of the generic helper | `Quantum/NeelState/InnerProduct.lean` |
| `neelChainState_inner_szsz_adjacent_eq_neg_one_quarter` | per-adjacent-bond `Ŝ^(3)_x · Ŝ^(3)_y` correlation on the Néel chain: `-1/4`. Matches the full `Ŝ_x · Ŝ_y` expectation since the off-diagonal `Ŝ^x·Ŝ^x + Ŝ^y·Ŝ^y` parts vanish on the diagonal (they map `|σ⟩` to `|swap σ⟩ ⊥ |σ⟩`) | `Quantum/NeelState/InnerProduct.lean` |
| `neelChainState_inner_szsz_wrap_eq_neg_one_quarter` | 1D Néel periodic chain: per-wrap-bond `Ŝ^(3)_x · Ŝ^(3)_y` correlation `-1/4` | `Quantum/NeelState/InnerProduct.lean` |
| `neelSquareState_inner_szsz_{horizontal,vertical}_{adjacent,wrap}_eq_neg_one_quarter` | 2D Néel: per-bond `Ŝ^(3)·Ŝ^(3)` correlation `-1/4` for every horizontal / vertical adjacent and wrap bond | `Quantum/NeelState.lean` |
| `neelCubicState_inner_szsz_{x,y,z}_{adjacent,wrap}_eq_neg_one_quarter` | 3D Néel: per-bond `Ŝ^(3)·Ŝ^(3)` correlation `-1/4` for every x / y / z adjacent and wrap bond. Completes the `Ŝ^z·Ŝ^z` correlation coverage parity with the full `Ŝ·Ŝ` family from #273 | `Quantum/NeelState.lean` |
| `neelChainState_inner_spinHalfDot_wrap_eq_neg_one_quarter` | 1D wrap-bond expectation `-1/4` on the periodic Néel chain `Fin (2(K+1))` | `Quantum/NeelState/InnerProductCore.lean` |
| `neelSquareState_inner_spinHalfDot_{horizontal,vertical}_{adjacent,wrap}_eq_neg_one_quarter` | 2D Néel: per-bond expectation `-1/4` for every horizontal / vertical adjacent and wrap bond | `Quantum/NeelState.lean` |
| `neelCubicState_inner_spinHalfDot_{x,y,z}_{adjacent,wrap}_eq_neg_one_quarter` | 3D Néel: per-bond expectation `-1/4` for every x / y / z adjacent and wrap bond. With the 1D / 2D family this completes per-bond `-1/4` coverage across the full Néel-state bond family of #251 / #261 / #262 | `Quantum/NeelState.lean` |
| `neelChainState_energy_expectation_K1` | `K = 1` (2-site) open-chain Heisenberg energy expectation `⟨Φ_Néel, H_open · Φ_Néel⟩ = J/2`. Combines `openChainHeisenbergHamiltonian_two_site_eq` (`H = -2J · spinHalfDot 0 1`) with the per-bond `-1/4` expectation, giving `-2J · (-1/4) = J/2` | `Quantum/NeelState/Energy.lean` |
| `neelConfigOf` / `neelStateOf` | generic graph-centric Néel state from a sublattice indicator `A : V → Bool`: `neelConfigOf A x := if A x then ↑ else ↓` and `neelStateOf A := basisVec (neelConfigOf A)`. The chain / 2D / 3D `neelXyzConfig` / `neelXyzState` definitions are bridged via `_eq_neelConfigOf` / `_eq_neelStateOf`. Tasaki §2.5 eq. (2.5.2) graph-centric form | `Quantum/NeelState/Definition.lean` |
| `spinHalfDot_mulVec_neelStateOf_antiparallel` | generic per-bond `Ŝ_x · Ŝ_y` action on the canonical Néel state: for any `x ≠ y` with `A x ≠ A y`, `Ŝ_x · Ŝ_y · Φ_Néel(A) = (1/2) · |swap_{x, y} Φ_Néel(A)⟩ - (1/4) · Φ_Néel(A)`. Tasaki §2.5 eq. (2.5.3) graph-centric form. The chain / 2D / 3D `_adjacent` / `_wrap` bond actions are 1-line corollaries via the `_eq_neelStateOf` bridges | `Quantum/NeelState/Definition.lean` |
| `inner_neelStateOf_spinHalfDot_neelStateOf_antiparallel` | generic per-bond `Ŝ_x · Ŝ_y` expectation on the canonical Néel state: for any `x ≠ y` with `A x ≠ A y`, `⟨Φ_Néel(A), Ŝ_x · Ŝ_y · Φ_Néel(A)⟩ = -(1/4)`. Tasaki §2.5 (2.5.4) ingredient (graph-centric form). The chain / 2D / 3D `_eq_neg_one_quarter` companions reduce to this via the `_eq_neelStateOf` bridges | `Quantum/NeelState/Definition.lean` |
| `inner_neelStateOf_szsz_neelStateOf_antiparallel` | generic per-bond `Ŝ^z_x · Ŝ^z_y` correlation on the canonical Néel state: for any `A x ≠ A y`, `⟨Φ_Néel(A), Ŝ^z_x · Ŝ^z_y · Φ_Néel(A)⟩ = -(1/4)`. Diagonal half of Tasaki §2.5 (2.5.4) | `Quantum/NeelState/Definition.lean` |
| `marshallSignOf` | generic graph-centric Marshall sign `∏_{x ∈ A} (-1)^(σ x)` for any finite vertex type `V`, sublattice indicator `A : V → Bool`, and configuration `σ : V → Fin 2`. Aligns with the project-wide graph-centric design (CLAUDE.local.md) | `Quantum/NeelState/MarshallSign.lean` |
| `marshallSignOf_const_zero` | for any sublattice indicator `A`, the all-up Marshall sign is `marshallSignOf A (const 0) = 1`. Generic counterpart of `marshallSignChainConfig_const_zero` etc.; those are now 1-line corollaries via the `_eq_marshallSignOf` bridges | `Quantum/NeelState/MarshallSign.lean` |
| `marshallSignChainConfig` / `marshallSignChainConfig_neelChainConfig` | the Marshall sign `(-1)^(N_A^↓)` for spin-1/2 configurations on the parity-coloured chain `Fin (2K)`, encoded as `∏_{x even} (-1)^(σ x)`; specialisation to the Néel configuration gives sign `+1` (no down spins on sublattice `A`). Foundational definition for the Marshall basis change underpinning the Marshall-Lieb-Mattis theorem (Tasaki §2.5). **Deprecated** as of 2026-04-22 in favour of the generic `marshallSignOf` (the chain / 2D / 3D Marshall sign defs are kept for backward compatibility but new code should prefer the generic form) | `Quantum/NeelState/MarshallSign.lean` |
| `marshallSign{Chain,Square,Cubic}Config_eq_marshallSignOf` | the chain / 2D / 3D parity-coloured Marshall signs are precisely `marshallSignOf` instantiated at the corresponding parity colouring | `Quantum/NeelState.lean` |
| `marshallSignSquareConfig` / `marshallSignSquareConfig_neelSquareConfig` | 2D analogue: Marshall sign `∏_{(i,j) with i+j even} (-1)^(σ (i,j))` on `Fin (2K) × Fin (2L)`; equals `+1` on the 2D checkerboard Néel configuration | `Quantum/NeelState/MarshallSign.lean` |
| `marshallSignCubicConfig` / `marshallSignCubicConfig_neelCubicConfig` | 3D analogue: Marshall sign `∏_{((i,j),k) with i+j+k even} (-1)^(σ ((i,j),k))` on `(Fin (2K) × Fin (2L)) × Fin (2M)`; equals `+1` on the 3D cubic checkerboard Néel configuration | `Quantum/NeelState/MarshallSign.lean` |
| `marshallSignChainConfig_const_zero` / `_const_one` | Marshall sign on the all-up / all-down chain configurations: `marshallSignChainConfig K (const 0) = 1` and `marshallSignChainConfig K (const 1) = (-1)^K` | `Quantum/NeelState/MarshallSign.lean` |
| `marshallSignSquareConfig_const_zero` / `_const_one` | 2D Marshall sign on the all-up / all-down checkerboard: both equal `+1` (the all-down case has `2KL` down spins on `A`, so `(-1)^(2KL) = 1`) | `Quantum/NeelState/MarshallSign.lean` |
| `marshallSignCubicConfig_const_zero` / `_const_one` | 3D Marshall sign on the all-up / all-down cubic: both equal `+1` (the all-down case has `4KLM` down spins on `A`, so `(-1)^(4KLM) = 1`) | `Quantum/NeelState/MarshallSign.lean` |
| `marshallSignChainConfig_flipConfig` | Marshall sign under the global spin-flip on the chain: `marshallSignChainConfig K (flipConfig σ) = (-1)^K · marshallSignChainConfig K σ`. Each of the K even-indexed sites contributes `-1`. Proof: `Finset.prod_mul_distrib` + helper `prod_alternating_neg_one` collapses the contributing factor product to `(-1)^K`, with the per-site identity `(-1)^((1-s).val) = (-1)·(-1)^(s.val)` closed by `fin_cases` | `Quantum/NeelState/MarshallSign.lean` |
| `marshallSignSquareConfig_flipConfig` / `marshallSignCubicConfig_flipConfig` | 2D / 3D Marshall sign invariant under the global spin-flip (the contributing factor product `(-1)^(2KL)` resp. `(-1)^(4KLM)` equals `+1` for all K, L, M) | `Quantum/NeelState/MarshallSign.lean` |
| `marshallChainState` / `_neelChainConfig` | Marshall-rotated chain basis state `marshallSignChainConfig K σ • basisVec σ`; specialisation at the Néel configuration coincides with `neelChainState K` (since the Marshall sign of the Néel state is `+1`) | `Quantum/NeelState/MarshallSign.lean` |
| `marshallSquareState` / `_neelSquareConfig` | 2D Marshall-rotated checkerboard state; coincides with `neelSquareState K L` at the Néel configuration | `Quantum/NeelState/MarshallSign.lean` |
<!-- legacy-source:end:784:888 -->

## Authoritative supplemental implementation record (private, not public API)
This section is maintained by hand, lies outside the migrated catalogue block above, and records
private implementation declarations introduced for the public rotation rows of that block. Every
migrated row above is unchanged.

Source file: `LatticeSystem/Quantum/TotalSpin/Rotation.lean`, section "Internal generic
construction", immediately before `totalSpinHalfRot1Pi`. All four declarations are `private` and
are not public API; no public name, signature, statement or doc comment changed when they were
introduced (issue #5241, PR #5243).

- `private noncomputable def totalSpinHalfRotOf (U : Matrix (Fin 2) (Fin 2) ℂ) : ManyBodyOp Λ`,
  defined as `(Finset.univ : Finset Λ).noncommProd (fun x => onSite x U) …` with the commutation
  side condition discharged by `onSite_mul_onSite_of_ne`. Role: the one generic site-wise product
  of a single-site matrix over the lattice. It implements the public constructors
  `totalSpinHalfRot{1,2,3}Pi` (at `U = spinHalfRot{1,2,3} Real.pi`) and `totalSpinHalfRot{1,2,3} θ`
  (at `U = spinHalfRot{1,2,3} θ`), which are now one-line instantiations.
- `private theorem totalSpinHalfRotOf_one : totalSpinHalfRotOf Λ 1 = 1`. Role: identity value of
  the generic product. It implements the public family `totalSpinHalfRot{1,2,3}_zero`, each proved
  from it together with `spinHalfRot{1,2,3}_zero`.
- `private theorem totalSpinHalfRotOf_mul (U V : Matrix (Fin 2) (Fin 2) ℂ) :
  totalSpinHalfRotOf Λ U * totalSpinHalfRotOf Λ V = totalSpinHalfRotOf Λ (U * V)`.
  Role: site-wise multiplicativity. It implements the public cyclic family
  `totalSpinHalfRot{1,2,3}Pi_mul_totalSpinHalfRot{2,3,1}Pi`, each proved from it together with
  `spinHalfRot{1,2,3}_pi_mul_spinHalfRot{2,3,1}_pi`.
- `private theorem totalSpinHalfRotOf_two_site (U : Matrix (Fin 2) (Fin 2) ℂ) :
  totalSpinHalfRotOf (Fin 2) U = onSite (0 : Fin 2) U * onSite (1 : Fin 2) U`. Role: two-site
  factorisation. It implements the public theorems `totalSpinHalfRot{1,2,3}Pi_two_site` and
  `totalSpinHalfRot{1,2,3}_two_site`, each a one-line application.

The public theorems `totalSpinHalfRot{1,2,3}Pi_eq` keep their `:= rfl` proofs and do not invoke any
of the four private declarations. Of the other public results of the same file, `_commute_of_commute`,
`_conjTranspose_mul_self`, and `_conj_eq_self_of_commute` are unchanged and go through the public
`_eq_exp` seam, not through the private core. `_eq_exp` itself is not exempt from the private core:
it is proved by the (unrelated, pre-existing) private helper `totalRot_eq_exp_aux`, whose statement
still spells the raw `Finset.noncommProd` and which typechecks only by delta-unfolding
`totalSpinHalfRotOf`'s definition.

## Authoritative supplemental implementation record (Néel per-bond correlation direction/wrap variants)

This section is maintained by hand, lies outside the migrated catalogue block above, and records
the current state of the Néel-state per-bond correlation family. The migrated catalogue block above
is a frozen historical record — its rows are pinned byte-for-byte by
`scripts/check_docs_hierarchy.py` and are never edited for later deletions, so the four
brace-shorthand rows
`neelSquareState_inner_szsz_{horizontal,vertical}_{adjacent,wrap}_eq_neg_one_quarter`,
`neelCubicState_inner_szsz_{x,y,z}_{adjacent,wrap}_eq_neg_one_quarter`,
`neelSquareState_inner_spinHalfDot_{horizontal,vertical}_{adjacent,wrap}_eq_neg_one_quarter` and
`neelCubicState_inner_spinHalfDot_{x,y,z}_{adjacent,wrap}_eq_neg_one_quarter`, together with their
"for every … adjacent and wrap bond", "coverage parity" and "full Néel-state bond family" prose,
describe membership as it stood at migration time.

Of those four families only the 2D `szsz` one has been retired in full; the other three each keep a
single representative bond (`horizontal_adjacent` for the 2D `spinHalfDot` family, `x_adjacent` for
the two cubic families, enumerated below), and every other per-direction and per-wrap instance is no
longer present in the library. Retired from `Quantum/NeelState/InnerProductCore.lean`:
`neelSquareState_inner_spinHalfDot_vertical_adjacent_eq_neg_one_quarter`,
`neelSquareState_inner_spinHalfDot_horizontal_wrap_eq_neg_one_quarter`,
`neelSquareState_inner_spinHalfDot_vertical_wrap_eq_neg_one_quarter`,
`neelCubicState_inner_spinHalfDot_y_adjacent_eq_neg_one_quarter`,
`neelCubicState_inner_spinHalfDot_z_adjacent_eq_neg_one_quarter`,
`neelCubicState_inner_spinHalfDot_x_wrap_eq_neg_one_quarter` and
`neelCubicState_inner_spinHalfDot_y_wrap_eq_neg_one_quarter`.
Retired from `Quantum/NeelState/InnerProduct.lean`:
`neelSquareState_inner_szsz_horizontal_adjacent_eq_neg_one_quarter`,
`neelSquareState_inner_szsz_vertical_adjacent_eq_neg_one_quarter`,
`neelSquareState_inner_szsz_horizontal_wrap_eq_neg_one_quarter`,
`neelSquareState_inner_szsz_vertical_wrap_eq_neg_one_quarter`,
`neelCubicState_inner_szsz_y_adjacent_eq_neg_one_quarter`,
`neelCubicState_inner_szsz_z_adjacent_eq_neg_one_quarter`,
`neelCubicState_inner_szsz_x_wrap_eq_neg_one_quarter`,
`neelCubicState_inner_szsz_y_wrap_eq_neg_one_quarter` and
`neelCubicState_inner_szsz_z_wrap_eq_neg_one_quarter`.
Retired from `Quantum/NeelState/Energy.lean`:
`neelCubicState_inner_spinHalfDot_z_wrap_eq_neg_one_quarter`.

The surviving members of the inner-product family are unchanged in statement and proof.
In `Quantum/NeelState/InnerProductCore.lean`: `neelChainState_norm_squared`,
`neelSquareState_norm_squared`, `neelCubicState_norm_squared`,
`neelChainState_inner_basisVec_basisSwap_adjacent_eq_zero`,
`neelChainState_inner_spinHalfDot_adjacent_eq_neg_one_quarter`,
`neelChainState_inner_spinHalfDot_wrap_eq_neg_one_quarter`,
`neelSquareState_inner_spinHalfDot_horizontal_adjacent_eq_neg_one_quarter` and
`neelCubicState_inner_spinHalfDot_x_adjacent_eq_neg_one_quarter`.
In `Quantum/NeelState/InnerProduct.lean`:
`neelChainState_inner_szsz_adjacent_eq_neg_one_quarter`,
`neelChainState_inner_szsz_wrap_eq_neg_one_quarter`,
`neelCubicState_inner_szsz_x_adjacent_eq_neg_one_quarter`,
`neelChainState_inner_off_diagonal_correlator_adjacent_eq_zero` and
`neelChainState_inner_spinHalfDot_parallel_eq_one_quarter`.
`neelChainState_energy_expectation_K1` in `Quantum/NeelState/Energy.lean` is likewise unchanged.

Nothing mathematical is lost. Every antiparallel bond, in every dimension and for both the full
`Ŝ_x · Ŝ_y` expectation and the diagonal `Ŝ^z_x · Ŝ^z_y` correlator, is covered in one line by the
generic `inner_neelStateOf_spinHalfDot_neelStateOf_antiparallel` and
`inner_neelStateOf_szsz_neelStateOf_antiparallel` (`Quantum/NeelState/Definition.lean`), applied
through the `neelChainState_eq_neelStateOf` / `neelSquareState_eq_neelStateOf` /
`neelCubicState_eq_neelStateOf` bridges; the surviving named instances are representatives of that
pattern, not the source of the coverage. Consequently the `szsz` correlator carries no 2D
specialisation by design: the 2D case is obtained from the generic theorem exactly as the retired
2D instances were.

## Authoritative supplemental implementation record (Tasaki §2.2 same-site commutator, total ladder action and total adjoint instances)

This section is maintained by hand, lies outside the migrated catalogue block above, and records
the current state of four rows of that block. The migrated catalogue block is a frozen historical
record — its rows are pinned byte-for-byte by `scripts/check_docs_hierarchy.py` and are never
edited for later deletions — so the rows
`spinHalfOp{1,2,3}_onSite_commutator_spinHalfOp{2,3,1}_onSite`,
`totalSpinHalfOpPlus/Minus_conjTranspose`, `totalSpinHalfOpPlus/Minus_mulVec_basisVec` and
`totalSpinHalfOp3_mulVec_basisVec_const` / `_all_up` / `_all_down` describe membership as it stood
at migration time.

Retired from `Quantum/TotalSpin.lean`:
`spinHalfOp1_onSite_commutator_spinHalfOp2_onSite`,
`spinHalfOp2_onSite_commutator_spinHalfOp3_onSite`,
`spinHalfOp3_onSite_commutator_spinHalfOp1_onSite`,
`totalSpinHalfOp3_mulVec_basisVec_all_up`, `totalSpinHalfOp3_mulVec_basisVec_all_down`,
`totalSpinHalfOpPlus_mulVec_basisVec`, `totalSpinHalfOpMinus_mulVec_basisVec`,
`totalSpinHalfOpPlus_conjTranspose` and `totalSpinHalfOpMinus_conjTranspose`.

Row by row: the same-site commutator row, the total adjoint row and the total ladder-action row
have no member left in the library; the constant-configuration row keeps
`totalSpinHalfOp3_mulVec_basisVec_const`, which is consumed by
`Quantum/SpinDot/HamiltonianCore.lean`. Every other row of the block is untouched — in particular
the site-wise `onSite_spinHalfOpPlus/Minus_mulVec_basisVec`, the definitions
`totalSpinHalfOpPlus` / `totalSpinHalfOpMinus` with their eq. (2.2.8) forms
`totalSpinHalfOpPlus_eq_add` / `totalSpinHalfOpMinus_eq_sub`, the Cartan ladder relations, and
`totalSpinHalfOp3_mulVec_basisVec` / `_eq_magnetization` all keep their statements and consumers.

Nothing mathematical is lost. Each retirement satisfies one criterion: the retired statement was a
one-line specialisation of a declaration that is still present in the library and still consumed.
Concretely:

- the `x = y` case of Tasaki eq. (2.2.6) is the generic `onSite_commutator_same`
  (`Quantum/ManyBody.lean`) composed with the single-site commutators
  `spinHalfOp{1,2,3}_commutator_spinHalfOp{2,3,1}` (`Quantum/SpinHalf.lean`); each retired
  spin specialisation was exactly that one `rw` chain, and both ingredients keep their consumers
  (`onSite_commutator_same` is used in `Quantum/TotalSpin.lean` and
  `Quantum/TotalSpin/Casimir.lean`);
- `_all_up` and `_all_down` were the `s := 0` and `s := 1` instantiations of the surviving
  `totalSpinHalfOp3_mulVec_basisVec_const`;
- `(Ŝ^±_tot)† = Ŝ^∓_tot` is the site-wise sum of the surviving single-site
  `spinHalfOp{Plus,Minus}_conjTranspose` (`Quantum/SpinHalfBasis.lean`, consumed by the
  Jordan–Wigner layer) transported through `onSite_conjTranspose` and `Matrix.conjTranspose_sum`;
- `Ŝ^±_tot · |σ⟩` as a sum of site-wise actions is the `Finset.sum` of the surviving
  `onSite_spinHalfOpPlus/Minus_mulVec_basisVec`, which are the forms the library actually consumes
  (`Quantum/SpinDot/Core.lean`, `Fermion/JordanWigner/AnnihilationCreationBasisVec.lean`).

The criterion is applied only to declarations that carry no numbered book equation of their own. A
statement that is the sole Lean rendering of a numbered Tasaki equation is kept even when no Lean
file references it: `spinHalfOp_onSite_comm_of_ne` (eq. (2.2.6) at `x ≠ y`) and
`totalSpinHalfOp{Minus,Plus}_mulVec_basisVec_all_{down,up}` (the §2.4 eq. (2.4.9) ladder
terminations) are therefore untouched.

The supplemental section on the private rotation core above needs no change: the three public
families it names — `_commute_of_commute`, `_conjTranspose_mul_self` and
`_conj_eq_self_of_commute` — all keep their statements and proofs.

---

[← The AKLT model (Tasaki §7.1)](/lattice-system/formalization/legacy/19-the-aklt-model-tasaki-7-1/) · [Catalogue](/lattice-system/formalization/legacy/) · [Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8)) →](/lattice-system/formalization/legacy/20-total-spin-operator-tasaki-2-2-eq-2-2-7-2-2-8-part-02/)
