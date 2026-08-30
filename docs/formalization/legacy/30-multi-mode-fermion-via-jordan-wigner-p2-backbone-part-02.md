---
layout: page
title: "Legacy catalogue: Multi-mode fermion via Jordan–Wigner (P2 backbone) (part 2 of 9)"
permalink: /formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-02/
---

<a id="legacy-catalogue-multi-mode-fermion-via-jordanwigner-p2-backbone-part-2-of-4"></a>
<a id="legacy-catalogue-multi-mode-fermion-via-jordanwigner-p2-backbone-part-2-of-5"></a>
# Legacy catalogue: Multi-mode fermion via Jordan–Wigner (P2 backbone) (part 2 of 9)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Fermions and Hubbard models](/lattice-system/formalization/legacy/#group-fermions-hubbard)

<!-- legacy-source:start:2346:2481 -->
| Lean name | Statement | File |
|---|---|---|
| `hubbardGibbsState_isHermitian` | Hermiticity (Hermitian `t`, real `U`) | `Fermion/JordanWigner/Hubbard.lean` |
| `hubbardGibbsState_commute_hamiltonian` | `Commute ρ_β H_Hubbard` | `Fermion/JordanWigner/Hubbard.lean` |
| `fermionTotalUpNumber`, `fermionTotalDownNumber` | spinful conserved charges `N_↑ = Σ_i n_{i↑}`, `N_↓ = Σ_i n_{i↓}` | `Fermion/JordanWigner/Hubbard/ChargesCore.lean` |
| `fermionTotalSpinZ` | total spin polarisation `S^z_tot = (1/2)(N_↑ − N_↓)` | `Fermion/JordanWigner/Hubbard/ChargesCore.lean` |
| `fermionTotalUpNumber_commute_fermionTotalDownNumber` | `[N_↑, N_↓] = 0` | `Fermion/JordanWigner/Hubbard/ChargesCore.lean` |
| `fermionTotalUpNumber_commute_fermionTotalNumber` / `fermionTotalDownNumber_commute_fermionTotalNumber` | `[N_↑, N̂] = [N_↓, N̂] = 0` | `Fermion/JordanWigner/Hubbard/ChargesCore.lean` |
| `fermionTotalSpinZ_commute_fermionTotalNumber` | `[S^z_tot, N̂] = 0` (spin polarisation commutes with total number) | `Fermion/JordanWigner/Hubbard/ChargesCore.lean` |
| `fermionTotalUpNumber_commute_hubbardOnSiteInteraction` / `fermionTotalDownNumber_commute_hubbardOnSiteInteraction` | `[N_↑, H_int] = [N_↓, H_int] = 0` | `Fermion/JordanWigner/Hubbard/ChargesCore.lean` |
| `fermionTotalSpinZ_commute_hubbardOnSiteInteraction` | `[S^z_tot, H_int] = 0` (free corollary) | `Fermion/JordanWigner/Hubbard/ChargesCore.lean` |
| `fermionUpAnnihilation_mulVec_vacuum` / `fermionDownAnnihilation_mulVec_vacuum` | every spinful annihilation kills the JW vacuum | `Fermion/JordanWigner/Hubbard/ChargesCore.lean` |
| `fermionUpNumber_mulVec_vacuum` / `fermionDownNumber_mulVec_vacuum` | each spinful site number kills the vacuum | `Fermion/JordanWigner/Hubbard/ChargesCore.lean` |
| `fermionTotalUpNumber_mulVec_vacuum` / `fermionTotalDownNumber_mulVec_vacuum` | `N_↑ · |vac⟩ = N_↓ · |vac⟩ = 0` | `Fermion/JordanWigner/Hubbard/ChargesCore.lean` |
| `fermionTotalSpinZ_mulVec_vacuum` | `S^z_tot · |vac⟩ = 0` (the vacuum is unpolarised) | `Fermion/JordanWigner/Hubbard/ChargesCore.lean` |
| `hubbardKinetic_mulVec_vacuum` / `hubbardOnSiteInteraction_mulVec_vacuum` / `hubbardHamiltonian_mulVec_vacuum` | each annihilates the vacuum (so `|vac⟩` is a 0-energy / 0-particle eigenstate) | `Fermion/JordanWigner/Hubbard/ChargesCore.lean` |
| `spinfulIndex_up_ne_down` | the up-channel position `2 i` is never the down-channel position `2 j + 1` | `Fermion/JordanWigner/Hubbard/Charges.lean` |
| `fermionTotalDownNumber_commute_fermionUp{Creation,Annihilation,Number}` and the dual `fermionTotalUpNumber_commute_fermionDown{Creation,Annihilation,Number}` | the spinful number on one species commutes with every operator of the other species (different JW positions) | `Fermion/JordanWigner.lean` |
| `fermionTotalDownNumber_commute_upHopping` / `fermionTotalUpNumber_commute_downHopping` | the spinful same-σ hopping term `c_{iσ}† c_{jσ}` commutes with the opposite-spin total number `N_{σ'≠σ}` (cross-spin half of `[H_kinetic, N_σ] = 0`) | `Fermion/JordanWigner/Hubbard/Charges.lean` |

#### Fock space representation and Slater determinants (Tasaki §9.2.3)

| Lean name | Statement | File |
|---|---|---|
| <a id="tasaki-chapter-9-part-01"></a> `fermionCreationFromVector` / `fermionAnnihilationFromVector` | smeared creation / annihilation operators `Ĉ†(φ) = Σ_x φ(x) ĉ†_x`, `Ĉ(φ) = Σ_x φ(x) ĉ_x` (Tasaki §9.2.3, eq. (9.2.46), p. 313) | `Fermion/JordanWigner/SmearedOperators.lean` |
| `slaterState` | the Slater determinant state `\|Φ⟩ = Ĉ†(φ⁽¹⁾) ⋯ Ĉ†(φ⁽ᴺ⁾) \|Φvac⟩` (ordered `List.prod`; Tasaki eq. (9.2.52), p. 319) | `Fermion/JordanWigner/FockSpaceRepresentationCore.lean` |
| `slaterGram` / `singleParticleInner` | single-particle overlap (Gram) matrix `(G)_{j,k} = ⟨φ⁽ʲ⁾, ψ⁽ᵏ⁾⟩` and its entry `Σ_x φ(x)* ψ(x)` | `Fermion/JordanWigner/FockSpaceRepresentationCore.lean` |
| `slaterState_nil` / `fockInner_vacuum_self` | empty Slater state is the vacuum; `⟨Φvac, Φvac⟩ = 1` (the `n = 0` instance of Lemma 9.1, proved axiom-free as a consistency guard) | `Fermion/JordanWigner/FockSpaceRepresentationCore.lean` |
| `lemma_9_1_slater_inner_det` / `lemma_9_1_slater_inner_perm_sum` | **Lemma 9.1** (Tasaki §9.2.3, p. 319, eq. (9.2.53), **PROVED axiom-free**): the Slater overlap `⟨Φ, Ψ⟩ = det(⟨φ⁽ʲ⁾, ψ⁽ᵏ⁾⟩) = Σ_p (sign p) ∏_j ⟨φ⁽ʲ⁾, ψ⁽ᵖ⁽ʲ⁾⁾⟩`. Proved by induction on the electron number: the bra's leading creation operator is moved to the ket as a smeared annihilation operator via the adjoint `(Ĉ†(φ₀))ᴴ = Ĉ(φ₀*)`, then anticommuted through the ket's creation string by the smeared mixed CAR `{Ĉ(φ), Ĉ†(ψ)} = (Σ_x φψ)·1` (killing the vacuum at the end). This yields exactly the row-0 cofactor (Laplace) expansion `Matrix.det_succ_row_zero`. The permutation-sum form follows via the Leibniz expansion. (Issue #4593.) | `Fermion/JordanWigner/FockSpaceRepresentationCore.lean` |
| `slaterCoeffMatrix` / `slaterGram_self_eq_conjTranspose_mul_self` / `slaterGram_self_det_ne_zero_iff` | coefficient matrix `A` (columns = wave functions), `G = AᴴA`, and the linear-algebra core `det G ≠ 0 ↔ LinearIndependent ℂ φ` (axiom-free, via `ker(AᴴA)=ker A` + column-injectivity criterion) | `Fermion/JordanWigner/FockSpaceRepresentationCore.lean` |
| `lemma_9_2_slater_ne_zero_iff_linearIndependent` | **Lemma 9.2** (Tasaki §9.2.3, p. 320): the Slater determinant state `slaterState (List.ofFn φ) ≠ 0 ↔ LinearIndependent ℂ φ`. Proved from Lemma 9.1 (`⟨Φ,Φ⟩ = det Gram`) + positive-definiteness of the Fock inner product. Axiom-free (Lemma 9.1 is now proved). | `Fermion/JordanWigner/FockSpaceRepresentationCore.lean` |
| `slaterChangeMatrix` / `slaterChangeMatrix_sum` / `slaterGram_change` / `fockInner_slater_change` | change-of-basis matrix `β` (`ψ⁽ʲ⁾ = Σ_k β_{j,k} φ⁽ᵏ⁾`), the Gram transformation `G(χ,ψ) = G(χ,φ)·βᵀ`, and the overlap identity `⟨Φ_χ,Φ_ψ⟩ = det(β)·⟨Φ_χ,Φ_φ⟩` (via Lemma 9.1) | `Fermion/JordanWigner/FockSpaceRepresentation.lean` |
| `lemma_9_3_slater_proportional_of_span_eq` | **Lemma 9.3** (Tasaki §9.2.3, pp. 320–321): if `φ`, `ψ` span the same subspace then `∃ c ≠ 0, slaterState (List.ofFn ψ) = c • slaterState (List.ofFn φ)`. Proved (`c = det β`) via the overlap identity + Fock positive-definiteness/Hermiticity (`w = |Ψ⟩−c|Φ⟩` has `⟨w,w⟩=0`) + Lemma 9.2 for `c ≠ 0`. Axiom-free (Lemma 9.1 is now proved). | `Fermion/JordanWigner/FockSpaceRepresentation.lean` |
| `spinfulNElectronSubmodule` / `spinfulGeneralBasisState` / `tasaki_lemma_9_4_generalBasis_span` / `tasaki_lemma_9_4_of_linearIndependent` | **Lemma 9.4** (Tasaki §9.2.3, pp. 321–322, eq. (9.2.65), "general basis of `H_N`", **PROVED axiom-free**): for `M+1` linearly independent single-particle states, the up-then-down states `\|Γ_{S↑,S↓}⟩` over subset pairs with `\|S↑\|+\|S↓\|=N` span the `N`-electron sector `H_N` (the `N`-eigenspace of the total number operator). Proof reuses the general-basis Fock-monomial machinery (`generalModeMonomial`, `generalOccBasis`, `N̂` diagonalization, the reordering-sign lemma): each `N`-card occupation monomial equals a nonzero multiple of some `\|Γ⟩` (permutation), and wrong-card coefficients vanish. | `Fermion/JordanWigner/Hubbard/GeneralBasisHN.lean` |

#### Hubbard spin symmetry — full SU(2) invariance (Tasaki §9.3.3)

| Lean name | Statement | File |
|---|---|---|
| `fermionTotalUpNumber_isHermitian` / `fermionTotalDownNumber_isHermitian` | `N_↑` and `N_↓` are Hermitian (sum of Hermitian number operators) | `Fermion/JordanWigner/Hubbard/SpinSymmetryAuxCore.lean` |
| `fermionTotalUpNumber_commutator_fermionUpCreation` | `[N_↑, c†_{i,↑}] = c†_{i,↑}` (up-spin sub-chain analogue of `[N̂, c†_i] = c†_i`) | `Fermion/JordanWigner/Hubbard/SpinSymmetryAuxCore.lean` |
| `fermionTotalDownNumber_commutator_fermionDownCreation` | `[N_↓, c†_{i,↓}] = c†_{i,↓}` | `Fermion/JordanWigner/Hubbard/SpinSymmetryAux.lean` |
| `fermionTotalUpNumber_commute_upHopping` | `[N_↑, c†_{i,↑} c_{j,↑}] = 0` (same-species hopping preserves spin-up count) | `Fermion/JordanWigner/Hubbard/SpinSymmetryAuxCore.lean` |
| `fermionTotalDownNumber_commute_downHopping` | `[N_↓, c†_{i,↓} c_{j,↓}] = 0` | `Fermion/JordanWigner/Hubbard/SpinSymmetryAux.lean` |
| `fermionTotalUpNumber_commute_hubbardKinetic` / `fermionTotalDownNumber_commute_hubbardKinetic` | `[N_↑, H_kin] = [N_↓, H_kin] = 0` (each spin species conserved by kinetic term) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalUpNumber_commute_hubbardHamiltonian` | `[N_↑, H] = 0` (Tasaki §9.3.3, eq. (9.3.35)) | `Fermion/JordanWigner/Hubbard/SpinSymmetryAuxCore.lean` |
| `fermionTotalDownNumber_commute_hubbardHamiltonian` | `[N_↓, H] = 0` (Tasaki §9.3.3, eq. (9.3.35)) | `Fermion/JordanWigner/Hubbard/SpinSymmetryAux.lean` |
| `fermionTotalSpinZ_commute_hubbardHamiltonian` | `[S^z_tot, H] = 0` (Tasaki §9.3.3, p. 333) | `Fermion/JordanWigner/Hubbard/SpinSymmetryAux.lean` |
| `fermionTotalSpinPlus` / `fermionTotalSpinMinus` | `Ŝ^+_tot = Σ_i c†_{i,↑}c_{i,↓}`, `Ŝ^-_tot = (Ŝ^+_tot)†` — SU(2) raising/lowering operators (Tasaki §9.3.3, p. 332) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalSpinPlus_conjTranspose` | `(Ŝ^+_tot)† = Ŝ^-_tot` | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionUpAnnihilation_commutator_fermionTotalSpinPlus` | `[c_{j,↑}, Ŝ^+_tot] = c_{j,↓}` (Tasaki §9.3.3, eq. (9.3.36)) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionDownCreation_commutator_fermionTotalSpinPlus` | `[c†_{j,↓}, Ŝ^+_tot] = −c†_{j,↑}` (Tasaki §9.3.3, eq. (9.3.36)) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionUpCreation_commute_fermionTotalSpinPlus` / `fermionDownAnnihilation_commute_fermionTotalSpinPlus` | `[c†_{i,↑}, Ŝ^+_tot] = 0` and `[c_{j,↓}, Ŝ^+_tot] = 0` (Tasaki §9.3.3, eq. (9.3.36)) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalSpinPlus_commute_hubbardHamiltonian` | `[Ŝ^+_tot, H] = 0` (Tasaki §9.3.3, eq. (9.3.35)) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |
| `fermionTotalSpinMinus_commute_hubbardHamiltonian` | `[Ŝ^-_tot, H] = 0` (Tasaki §9.3.3, eq. (9.3.35), proved by adjoint) | `Fermion/JordanWigner/Hubbard/SpinSymmetry.lean` |

#### Hubbard all-up-spin state and saturated ferromagnetism (Tasaki §11.1.1)

| Lean name | Statement | File |
|---|---|---|
| <a id="tasaki-chapter-11-part-01"></a> `hubbardAllUpState N` | fully spin-polarised basis vector: all spin-up orbitals occupied, spin-down empty (even JW indices = 1, odd = 0) | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `fermionUpNumber_mulVec_allUpState` | `n_{i,↑} · |↑…↑⟩ = |↑…↑⟩` — each spin-up number operator acts as identity on the all-up state | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `fermionDownNumber_mulVec_allUpState` | `n_{i,↓} · |↑…↑⟩ = 0` — no spin-down electrons; key to the vanishing of `H_int` | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `hubbardOnSiteInteraction_mulVec_allUpState` | `H_int · |↑…↑⟩ = 0` — no double occupancy in the fully-polarised state (Tasaki §11.1.1, p. 373; eq. (10.1.5), p. 344) | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `hubbardHamiltonian_mulVec_allUpState` | `H · |↑…↑⟩ = H_hop · |↑…↑⟩` — the Hubbard model in the all-up sector reduces to a non-interacting hopping problem | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `fermionDownAnnihilation_mulVec_allUpState` | `c_{i,↓} · |↑…↑⟩ = 0` — spin-down annihilation kills the all-up state (odd JW index unoccupied, so σ⁺ maps it to 0) (Tasaki §11.1.1, p. 373) | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `fermionUpCreation_mulVec_allUpState` | `c†_{i,↑} · |↑…↑⟩ = 0` — spin-up creation kills the all-up state (even JW index already occupied, so σ⁻ maps it to 0) (Tasaki §11.1.1, p. 373) | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `hubbardKinetic_mulVec_allUpState` | `H_hop · |↑…↑⟩ = (Σ_i t i i) • |↑…↑⟩` — hopping eigenvalue: off-diagonal terms vanish by CAR anticommutation, diagonal terms give 1 each (Tasaki §11.1.1, p. 373) | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `hubbardHamiltonian_mulVec_allUpState_eigenstate` | `H · |↑…↑⟩ = (Σ_i t i i) • |↑…↑⟩` — full Hamiltonian eigenstate: combines `H_hop` eigenvalue and `H_int · |↑…↑⟩ = 0` (Tasaki §11.1.1, p. 373; eq. (10.1.5), p. 344) | `Fermion/JordanWigner/Hubbard/AllUpState.lean` |
| `fermionTotalSpinSquared` | total-spin Casimir `(Ŝ_tot)² = Ŝ⁻Ŝ⁺ + Ŝ_z(Ŝ_z+1)` | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalUpNumber_mulVec_allUpState` | `N_↑ · |↑…↑⟩ = (N+1) • |↑…↑⟩` | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalDownNumber_mulVec_allUpState` | `N_↓ · |↑…↑⟩ = 0` | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalSpinZ_mulVec_allUpState` | `Ŝ^z_tot · |↑…↑⟩ = ((N+1)/2) • |↑…↑⟩` | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalSpinPlus_mulVec_allUpState` | `Ŝ⁺_tot · |↑…↑⟩ = 0` — highest-weight state; no down-spin to raise | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalSpinSquared_mulVec_allUpState` | `(Ŝ_tot)² · |↑…↑⟩ = S_max(S_max+1) • |↑…↑⟩` where `S_max = (N+1)/2` (Tasaki §11.1.1, p. 372) | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalSpinSquared_commute_hubbardHamiltonian` | `[(Ŝ_tot)², H] = 0` — Casimir commutes with H (from SU(2) invariance, Tasaki §9.3.3) | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `isSaturatedFerromagnet` | **Definition 11.1** — Lean predicate: there exists a ground-state energy `E₀` such that every nonzero `H`-eigenvector with eigenvalue `E₀` is a `(Ŝ_tot)²`-eigenvector with eigenvalue `S_max(S_max+1)` (Tasaki §11.1.1, p. 372) | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalSpinZ_commutator_fermionTotalSpinMinus` | `[Ŝ^z_tot, Ŝ^-_tot] = -Ŝ^-_tot` — SU(2) algebra relation; follows from site-wise `[Ŝ_z, c†_{i,↓}c_{i,↑}] = -(c†_{i,↓}c_{i,↑})` (Tasaki §9.3.3, p. 332) | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalSpinMinus_mulVec_preserves_hamiltonian_eigenvalue` | if `H·v = E·v` then `H·(Ŝ^-·v) = E·(Ŝ^-·v)` — applying `Ŝ^-` preserves Hamiltonian eigenvalues; follows from `[Ŝ^-, H] = 0` (Tasaki §11.1.1, p. 373) | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |
| `fermionTotalSpinZ_mulVec_spinMinus_step` | if `Ŝ_z·v = m·v` then `Ŝ_z·(Ŝ^-·v) = (m-1)·(Ŝ^-·v)` — applying `Ŝ^-` decrements `Ŝ_z` eigenvalue by 1; follows from `[Ŝ^z, Ŝ^-] = -Ŝ^-` (Tasaki §2.4, eq. (2.4.9); §11.1.1, p. 373) | `Fermion/JordanWigner/Hubbard/SaturatedFerromagnetism.lean` |

#### Hubbard hard-core subspace (Tasaki §11.2)

| Lean name | Statement | File |
|---|---|---|
| `hubbardDoubleOccupancy N i` | same-site Hubbard double-occupancy operator `n_{i,↑} n_{i,↓}` | `Fermion/JordanWigner/Hubbard/HardcoreSubspace.lean` |
| `hubbardHardcoreSubspace N` | linear subspace of vectors annihilated by every same-site double-occupancy operator, the no-double-occupancy sector used as unnumbered infrastructure for Tasaki Theorems 11.5 and 11.7 (1st ed., §11.2, pp. 381-388) | `Fermion/JordanWigner/Hubbard/HardcoreSubspace.lean` |
| `mem_hubbardHardcoreSubspace_iff` | membership in `hubbardHardcoreSubspace` is equivalent to vanishing of all `hubbardDoubleOccupancy N i` actions | `Fermion/JordanWigner/Hubbard/HardcoreSubspace.lean` |
| `hubbardDoubleOccupancy_mulVec_eq_zero_of_mem_hardcore` | every `hubbardDoubleOccupancy N i` annihilates each hard-core vector | `Fermion/JordanWigner/Hubbard/HardcoreSubspace.lean` |
| `hubbardOnSiteInteraction_mulVec_eq_zero_of_mem_hardcore` / `hubbardOnSiteInteraction_apply_eq_zero_of_mem_hardcore` | the on-site interaction `U Σ_i n_{i,↑} n_{i,↓}` annihilates every hard-core vector, both as a vector equation and pointwise | `Fermion/JordanWigner/Hubbard/HardcoreSubspace.lean` |

#### Hubbard hard-core projection (Tasaki §11.2)

| Lean name | Statement | File |
|---|---|---|
| `hubbardHardcoreFactor N i` | single-site hard-core factor `1 - n_{i,↑} n_{i,↓}` at spinful site `i` | `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean` |
| `hubbardHardcoreFactor_mul_self` | each hard-core factor is idempotent | `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean` |
| `hubbardDoubleOccupancy_mul_hardcoreFactor` | `n_{i,↑} n_{i,↓} · (1 - n_{i,↑} n_{i,↓}) = 0` | `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean` |
| `hubbardHardcoreFactor_commute` | hard-core factors at any two sites commute | `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean` |
| `hubbardDoubleOccupancy_isHermitian` / `hubbardHardcoreFactor_isHermitian` | the double-occupancy operator and each hard-core factor are Hermitian | `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean` |
| `hubbardHardcoreFactor_mulVec_eq_self_of_mem` | every hard-core factor fixes each hard-core vector | `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean` |
| `hubbardHardcoreProjection N` | hard-core projection `P̂_hc = ∏_i (1 - n_{i,↑} n_{i,↓})`, the non-commutative product of pairwise-commuting hard-core factors, unnumbered infrastructure for Tasaki Theorems 11.5 and 11.7 (1st ed., §11.2, pp. 381-388) | `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean` |
| `hubbardHardcoreProjection_mul_self` | the hard-core projection is idempotent | `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean` |
| `hubbardHardcoreProjection_isHermitian` | the hard-core projection is Hermitian | `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean` |
| `hubbardDoubleOccupancy_mul_hardcoreProjection` | every same-site double-occupancy operator annihilates `P̂_hc`: `n_{j,↑} n_{j,↓} · P̂_hc = 0` | `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean` |
| `hubbardHardcoreProjection_mulVec_eq_self_of_mem` | `P̂_hc` fixes every hard-core vector | `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean` |
| `hubbardHardcoreProjection_mulVec_mem` | `P̂_hc · ψ` always lies in `hubbardHardcoreSubspace` | `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean` |

#### Hubbard one-hole hard-core basis states (Tasaki §11.2)

| Lean name | Statement | File |
|---|---|---|
| `hubbardOneHoleConfig N x σ` | occupation configuration with a hole at site `x` and spin `σ` (`true = ↑`) on every other site | `Fermion/JordanWigner/Hubbard/HardcoreBasis.lean` |
| `hubbardOneHoleConfig_apply_up` / `hubbardOneHoleConfig_apply_down` | the up- / down-orbital occupation values of that configuration at each site | `Fermion/JordanWigner/Hubbard/HardcoreBasis.lean` |
| `hubbardHardcoreBasisState N x σ` | one-hole hard-core basis state `\|Φ_{x,σ}⟩`, the computational basis vector of `hubbardOneHoleConfig N x σ` (Tasaki §11.2, eq. (11.2.3); 1st ed., pp. 381-388) | `Fermion/JordanWigner/Hubbard/HardcoreBasis.lean` |
| `hubbardHardcoreBasisState_mem_hardcoreSubspace` | every basis state lies in `hubbardHardcoreSubspace` | `Fermion/JordanWigner/Hubbard/HardcoreBasis.lean` |
| `hubbardHardcoreProjection_mulVec_basisState` | the hard-core projection fixes every basis state | `Fermion/JordanWigner/Hubbard/HardcoreBasis.lean` |
| `hubbardHardcoreBasisState_inner` | orthonormality: `⟨Φ_{x,σ} \| Φ_{x',σ'}⟩ = 1` iff their configurations coincide, else `0` | `Fermion/JordanWigner/Hubbard/HardcoreBasis.lean` |
| `hubbardHardcoreBasisState_self_inner` | each basis state is normalised (self-overlap `1`) | `Fermion/JordanWigner/Hubbard/HardcoreBasis.lean` |

#### Jordan–Wigner string action on basis states (Tasaki §11.2 infrastructure)

| Lean name | Statement | File |
|---|---|---|
| `onSite_pauliZ_mulVec_basisVec` | `σ^z_j · \|c⟩ = (-1)^{c j} \|c⟩` (single `σ^z` acts by the parity sign at `j`) | `Fermion/JordanWigner/StringBasisVecAction.lean` |
| `jwString_mulVec_basisVec` | `jwString N i · \|c⟩ = (∏_{j<i} (-1)^{c j}) \|c⟩` (the JW string acts by the fermion-parity sign of the occupied modes below `i`) | `Fermion/JordanWigner/StringBasisVecAction.lean` |
| `jwSign N j c` | the JW string sign `∏_{k<j} (-1)^{c k}` of a configuration | `Fermion/JordanWigner/AnnihilationCreationBasisVec.lean` |
| `fermionMultiAnnihilation_mulVec_basisVec` | `c_j \|c⟩ = jwSign N j c • \|c with j↦0⟩` if `c j = 1`, else `0` | `Fermion/JordanWigner/AnnihilationCreationBasisVec.lean` |
| `fermionMultiCreation_mulVec_basisVec` | `c†_j \|c⟩ = jwSign N j c • \|c with j↦1⟩` if `c j = 0`, else `0` | `Fermion/JordanWigner/AnnihilationCreationBasisVec.lean` |
| `fermionMultiCreation_mul_Annihilation_mulVec_basisVec` | a single hop `c†_p c_q \|c⟩` = `(jwSign·jwSign) • \|c with q↦0, p↦1⟩` if `c q = 1` and the intermediate config is empty at `p`, else `0` | `Fermion/JordanWigner/HopBasisVec.lean` |
| `jwSign_zero_config` / `fermionMultiCreation_mulVec_vacuum_eq_basisVec` | the string sign of the vacuum is `1`; `c†_j \|vac⟩ = \|single electron at j⟩` (base case for the ordered-`c†` Tasaki basis (11.2.3)) | `Fermion/JordanWigner/VacuumCreationBasisVec.lean` |

#### Span of the one-hole hard-core sector (Tasaki §11.2, footnote 8)

| Lean name | Statement | File |
|---|---|---|
| `IsOneHoleHardcoreConfig N c` | a configuration is one-hole hard-core: no double occupancy and exactly one empty site (the hole) | `Fermion/JordanWigner/Hubbard/HardcoreSpan.lean` |
| `hubbardOneHoleConfig_isOneHoleHardcore` | each parametrized configuration `hubbardOneHoleConfig N x σ` is one-hole hard-core | `Fermion/JordanWigner/Hubbard/HardcoreSpan.lean` |
<!-- legacy-source:end:2346:2481 -->

---

[← Multi-mode fermion via Jordan–Wigner (P2 backbone)](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-01/) · [Catalogue](/lattice-system/formalization/legacy/) · [Multi-mode fermion via Jordan–Wigner (P2 backbone) →](/lattice-system/formalization/legacy/30-multi-mode-fermion-via-jordan-wigner-p2-backbone-part-03/)
