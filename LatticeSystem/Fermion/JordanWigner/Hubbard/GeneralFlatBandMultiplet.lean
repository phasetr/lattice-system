import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandConnectivity
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinLoweringTowerGeneral
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiHopAction
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandGroundAnnihilation
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinChargeCommutation
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandSpinRep

/-!
# The general flat-band maximal-spin multiplet (Tasaki §11.3.4)

The ground subspace of a connected general flat-band Hubbard model is the `(D₀+1)`-fold maximal-spin
multiplet.  The all-up μ-Slater state `Slater(canonical I (fun _ => 0))` is the highest-weight
vector (`Ŝ⁺_tot` annihilates it, `Ŝᶻ_tot` eigenvalue `D₀/2`); the SU(2) lowering tower
`highestWeight_spinMultiplet_general` then produces `D₀+1` linearly independent ground states all
carrying total spin `(D₀/2)(D₀/2+1)`, which (with the `finrank ≤ D₀+1` upper bound
`generalFlatBandGround_finrank_le_of_connected`) pins the ground subspace as the multiplet.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §11.3.4, Theorem 11.17, pp. 410–412.  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators

variable {M : ℕ}

/-- **`Ŝ⁺_tot` annihilates the all-up μ-Slater state**: `Ŝ⁺_tot = Σ_i ĉ†_{i,↑}ĉ_{i,↓}` and each
down-annihilation `ĉ_{i,↓}` kills the all-up Slater (every creation mode carries spin `↑ = 0 ≠ 1`),
so the whole raising operator does.  This is the highest-weight condition `Ŝ⁺ v = 0` for the SU(2)
tower of the general flat-band ferromagnet. -/
theorem generalFlatBand_totalSpinPlus_mulVec_allUpSlater (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (I : Finset (Fin (M + 1))) :
    (fermionTotalSpinPlus M).mulVec
      (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))) = 0 := by
  unfold fermionTotalSpinPlus
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [← Matrix.mulVec_mulVec]
  have hdown : (fermionDownAnnihilation M i).mulVec
      (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))) = 0 := by
    rw [fermionDownAnnihilation]
    refine generalFlatBand_siteAnnihilation_eq_zero μ i 1 _ (fun q hq => Or.inr ?_)
    rw [flatBandSpinConfigList_mem_snd_eq I (fun _ => 0) hq]
    decide
  rw [hdown, Matrix.mulVec_zero]

/-- **The total number operator is diagonal on the general flat-band Slater states**:
`N̂_tot |Slater(μ, qs)⟩ = (length qs) · |Slater(μ, qs)⟩` — every `â†`-creation adds one particle.
List induction via `fermionTotalNumber_mul_spinfulCreationFromVector` (each
`generalFlatBandCreation μ z σ = spinfulCreationFromVector M (μ z) σ`), down to
`N̂_tot|vac⟩ = 0`. -/
theorem fermionTotalNumber_mulVec_generalFlatBandSlaterState
    (μ : Fin (M + 1) → Fin (M + 1) → ℂ) (qs : List (Fin (M + 1) × Fin 2)) :
    (fermionTotalNumber (2 * M + 1)).mulVec (generalFlatBandSlaterState μ qs)
      = (qs.length : ℂ) • generalFlatBandSlaterState μ qs := by
  induction qs with
  | nil =>
    simp only [generalFlatBandSlaterState, List.map_nil, List.prod_nil, Matrix.one_mulVec,
      List.length_nil, Nat.cast_zero, zero_smul]
    exact fermionTotalNumber_mulVec_vacuum (2 * M + 1)
  | cons q qs' ih =>
    obtain ⟨q1, q2⟩ := q
    have hcons : generalFlatBandSlaterState μ ((q1, q2) :: qs')
        = (spinfulCreationFromVector M (μ q1) q2).mulVec (generalFlatBandSlaterState μ qs') := by
      rw [generalFlatBandSlaterState, generalFlatBandSlaterState, List.map_cons, List.prod_cons,
        Matrix.mulVec_mulVec]
      rfl
    rw [hcons, Matrix.mulVec_mulVec, fermionTotalNumber_mul_spinfulCreationFromVector,
      Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, List.length_cons]
    push_cast
    rw [add_smul, one_smul]

/-- **The total number operator splits into spin-up and spin-down totals**:
`N̂_tot = N̂_↑ + N̂_↓` on the spinful `2M+2`-mode chain.  Reindex the `2M+2` Jordan–Wigner modes
into sites `t : Fin (M+1)` and spins `r : Fin 2` via `sum_spinful_reindex`, then split the inner
two-element spin sum (`r = 0 ↦ n_{t,↑}`, `r = 1 ↦ n_{t,↓}`).  This is the standard
`N̂ = N̂_↑ + N̂_↓` charge decomposition; used to read `Ŝᶻ_tot = (N̂_↑ − N̂_↓)/2` off the diagonal
filling `N̂_tot = D₀`, `N̂_↓ = 0` of the all-up flat-band Slater. -/
theorem fermionTotalNumber_eq_up_add_down (N : ℕ) :
    fermionTotalNumber (2 * N + 1) = fermionTotalUpNumber N + fermionTotalDownNumber N := by
  change (∑ k : Fin (2 * N + 2), fermionMultiNumber (2 * N + 1) k)
      = (∑ t : Fin (N + 1), fermionUpNumber N t) + ∑ t : Fin (N + 1), fermionDownNumber N t
  rw [sum_spinful_reindex N (fun k => fermionMultiNumber (2 * N + 1) k), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun t _ => Fin.sum_univ_two _)

/-- **The total spin-down number annihilates the all-up μ-Slater state**: each
`n̂_{i,↓} = ĉ†_{i,↓}ĉ_{i,↓}` and `ĉ_{i,↓}` kills the all-up Slater (every mode carries spin
`↑ = 0 ≠ 1`), so `N̂_↓ |Slater⟩ = 0`.  Together with `N̂_tot |Slater⟩ = D₀ |Slater⟩` this fixes the
filling to be fully spin-polarized. -/
theorem fermionTotalDownNumber_mulVec_allUpSlater (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (I : Finset (Fin (M + 1))) :
    (fermionTotalDownNumber M).mulVec
      (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))) = 0 := by
  unfold fermionTotalDownNumber
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [fermionDownNumber,
    show fermionMultiNumber (2 * M + 1) (spinfulIndex M i 1)
        = fermionMultiCreation (2 * M + 1) (spinfulIndex M i 1)
          * fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M i 1) from rfl,
    ← Matrix.mulVec_mulVec]
  have hann : (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M i 1)).mulVec
      (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))) = 0 :=
    generalFlatBand_siteAnnihilation_eq_zero μ i 1 _ (fun q hq => Or.inr (by
      rw [flatBandSpinConfigList_mem_snd_eq I (fun _ => 0) hq]; decide))
  rw [hann, Matrix.mulVec_zero]

/-- **`Ŝᶻ_tot` eigenvalue `D₀/2` on the all-up μ-Slater state** (`D₀ = |I|`): from
`Ŝᶻ_tot = (N̂_↑ − N̂_↓)/2`, `N̂_tot |Slater⟩ = |I| |Slater⟩`, and `N̂_↓ |Slater⟩ = 0` (hence
`N̂_↑ |Slater⟩ = N̂_tot |Slater⟩ − N̂_↓ |Slater⟩ = |I| |Slater⟩`), the all-up Slater is the
highest-weight vector of the SU(2) tower with `Ŝᶻ` eigenvalue `|I|/2`. -/
theorem generalFlatBand_totalSpinZ_mulVec_allUpSlater (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (I : Finset (Fin (M + 1))) :
    (fermionTotalSpinZ M).mulVec
        (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0)))
      = ((I.card : ℂ) / 2) •
        generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0)) := by
  set v := generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0)) with hv
  have hdown : (fermionTotalDownNumber M).mulVec v = 0 :=
    fermionTotalDownNumber_mulVec_allUpSlater μ I
  have htot : (fermionTotalNumber (2 * M + 1)).mulVec v = (I.card : ℂ) • v := by
    rw [hv, fermionTotalNumber_mulVec_generalFlatBandSlaterState,
      flatBandSpinConfigList_length]
  have hup : (fermionTotalUpNumber M).mulVec v = (I.card : ℂ) • v := by
    have hsplit := fermionTotalNumber_eq_up_add_down M
    have : (fermionTotalUpNumber M).mulVec v + (fermionTotalDownNumber M).mulVec v
        = (I.card : ℂ) • v := by
      rw [← Matrix.add_mulVec, ← hsplit, htot]
    rwa [hdown, add_zero] at this
  rw [fermionTotalSpinZ, Matrix.smul_mulVec, Matrix.sub_mulVec, hup, hdown, sub_zero, smul_smul]
  congr 1
  rw [one_div]
  ring

/-- **The all-up μ-Slater state is nonzero** (`hv` for the SU(2) tower).  Its occupation-basis
coordinate at its own index configuration is nonzero
(`generalFlatBandSlaterState_repr_self_ne_zero`, since the canonical creation list is nodup with all
indices in `I`), so the vector cannot be the zero vector.  This is the nontriviality hypothesis of
`highestWeight_spinMultiplet_general`. -/
theorem generalFlatBandSlaterState_allUp_ne_zero
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (idx : Fin (M + 1) → Fin (M + 1))
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) :
    generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0)) ≠ 0 := by
  intro h
  refine generalFlatBandSlaterState_repr_self_ne_zero hbasis eμ idx hidx
    (flatBandSpinConfigList I (fun _ => 0)) (flatBandSpinConfigList_nodup I _)
    (fun q hq => flatBandSpinConfigList_mem_fst_mem I _ hq) ?_
  rw [h, map_zero]
  rfl

open scoped ComplexOrder in
/-- **The kinetic operator annihilates the all-up μ-Slater state**: the flat-band Slater is a
zero-kinetic-energy state.  Factor `T = Cᴴ C` (`exists_posSemidef_sq_eq_of_posSemidef`); then
`hubbardKinetic M (Cᴴ C) = Σ_σ,k Ĉ_σ(C_k)ᴴ Ĉ_σ(C_k)`
(`hubbardKinetic_conjTranspose_mul_self_eq_gram_sum`).  Each Gram-mode annihilation kills the
Slater: every occupied mode `μ_z` lies in `ker T = ker C` (so `C μ_z = 0`, i.e.
`Σ_x C_k(x) μ_z(x) = 0`), so the orthogonal-kill lemma applies. -/
theorem hubbardKinetic_mulVec_allUpSlater_eq_zero
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) :
    (hubbardKinetic M T).mulVec
        (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))) = 0 := by
  obtain ⟨C, hC, hTC⟩ := LatticeSystem.Math.exists_posSemidef_sq_eq_of_posSemidef hT
  have hTCH : T = Cᴴ * C := by rw [hTC, hC.isHermitian.eq]
  set v := generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0)) with hv
  have hkerC : ∀ z ∈ I, C.mulVec (μ z) = 0 := fun z hz => by
    have hTz : (Cᴴ * C).mulVec (μ z) = 0 := by rw [← hTCH]; exact hbasis.2.1 z hz
    have hmem : μ z ∈ LinearMap.ker (Cᴴ * C).mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hTz
    rw [Matrix.ker_mulVecLin_conjTranspose_mul_self] at hmem
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hmem
  have hCk : ∀ (σ : Fin 2) (k : Fin (M + 1)),
      (spinfulAnnihilationFromVector M (fun j => C k j) σ).mulVec v = 0 := fun σ k =>
    spinfulAnnihilationFromVector_mulVec_generalFlatBandSlaterState_eq_zero_of_orthogonal
      μ (fun j => C k j) σ _ (fun q hq => by
        have hk := congrFun (hkerC q.1 (flatBandSpinConfigList_mem_fst_mem I _ hq)) k
        simpa [Matrix.mulVec, dotProduct] using hk)
  rw [hTCH, hubbardKinetic_conjTranspose_mul_self_eq_gram_sum, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun σ _ => ?_)
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [← Matrix.mulVec_mulVec, hCk σ k, Matrix.mulVec_zero]

/-- **The on-site interaction annihilates the all-up μ-Slater state**: the fully spin-polarized
Slater has no double occupancy, so each term `U • (n̂_{i,↑} n̂_{i,↓})` kills it (the inner
`n̂_{i,↓} = ĉ†_{i,↓}ĉ_{i,↓}` already vanishes, as `ĉ_{i,↓}` annihilates the all-up state). -/
theorem hubbardOnSiteInteraction_mulVec_allUpSlater_eq_zero
    (μ : Fin (M + 1) → Fin (M + 1) → ℂ) (I : Finset (Fin (M + 1))) (U : ℂ) :
    (hubbardOnSiteInteraction M U).mulVec
        (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))) = 0 := by
  unfold hubbardOnSiteInteraction
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hdown : (fermionDownNumber M i).mulVec
      (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))) = 0 := by
    rw [fermionDownNumber,
      show fermionMultiNumber (2 * M + 1) (spinfulIndex M i 1)
          = fermionMultiCreation (2 * M + 1) (spinfulIndex M i 1)
            * fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M i 1) from rfl,
      ← Matrix.mulVec_mulVec]
    have hann : (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M i 1)).mulVec
        (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))) = 0 :=
      generalFlatBand_siteAnnihilation_eq_zero μ i 1 _ (fun q hq => Or.inr (by
        rw [flatBandSpinConfigList_mem_snd_eq I (fun _ => 0) hq]; decide))
    rw [hann, Matrix.mulVec_zero]
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hdown, Matrix.mulVec_zero, smul_zero]

open scoped ComplexOrder in
/-- **The all-up μ-Slater state lies in the general flat-band ground submodule** (`v ∈ ground`):
it is a zero-energy `D₀`-electron state.  `Ĥ = K̂ + U Σ n̂↑n̂↓` annihilates it (kinetic and
interaction kills above), and `N̂_tot v = |I| v = D₀ v` places it in the `D₀`-electron sector.  This
exhibits the highest-weight vector of the SU(2) tower inside the ground subspace, the seed for the
`finrank ≥ D₀+1` lower bound. -/
theorem generalFlatBandSlaterState_allUp_mem_groundSubmodule
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) :
    generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))
      ∈ generalFlatBandGroundSubmodule T U := by
  simp only [generalFlatBandGroundSubmodule, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hubbardHamiltonian, Matrix.add_mulVec,
      hubbardKinetic_mulVec_allUpSlater_eq_zero hbasis hT,
      hubbardOnSiteInteraction_mulVec_allUpSlater_eq_zero μ I (U : ℂ), add_zero]
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
      fermionTotalNumber_mulVec_generalFlatBandSlaterState, flatBandSpinConfigList_length, hbasis.1]

open scoped ComplexOrder in
/-- **The total spin-lowering operator preserves the general flat-band ground submodule**
(`tower ⊆ ground`): if `v` is a ground state then so is `Ŝ⁻_tot v`.  `Ŝ⁻_tot` commutes with both
`Ĥ` (SU(2) symmetry, `fermionTotalSpinMinus_commute_hubbardHamiltonian` — needs `T` Hermitian and
`U` real) and `N̂_tot` (it conserves particle number, `fermionTotalSpinMinus_commute_fermionTotalNumber`),
so it maps `ker Ĥ ∩ {N = D₀}` into itself.  Hence the whole SU(2) lowering tower `(Ŝ⁻_tot)^k v` from
the all-up highest-weight vector lies inside the ground subspace, supplying `D₀+1` independent
ground states for the `finrank ≥ D₀+1` lower bound. -/
theorem fermionTotalSpinMinus_mulVec_mem_generalFlatBandGroundSubmodule
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.PosSemidef) (U : ℝ)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ} (hv : v ∈ generalFlatBandGroundSubmodule T U) :
    (fermionTotalSpinMinus M).mulVec v ∈ generalFlatBandGroundSubmodule T U := by
  simp only [generalFlatBandGroundSubmodule, Submodule.mem_inf, LinearMap.mem_ker,
    Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hv ⊢
  obtain ⟨hH, hN⟩ := hv
  refine ⟨?_, ?_⟩
  · have hcomm : Commute (hubbardHamiltonian M T (U : ℂ)) (fermionTotalSpinMinus M) :=
      (fermionTotalSpinMinus_commute_hubbardHamiltonian M T (U : ℂ)
        (hJ := fun i j => hT.isHermitian.apply j i) (hU := Complex.conj_ofReal U)).symm
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hH, Matrix.mulVec_zero]
  · have hcomm : Commute (fermionTotalNumber (2 * M + 1)) (fermionTotalSpinMinus M) :=
      (fermionTotalSpinMinus_commute_fermionTotalNumber M).symm
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hN, Matrix.mulVec_smul]

open scoped ComplexOrder in
/-- **Unconditional `finrank ≥ D₀+1` lower bound on the general flat-band ground subspace**: the
SU(2) lowering tower of the all-up μ-Slater supplies `D₀+1` linearly independent ground states.
From the highest-weight inputs (`v ≠ 0`, `Ŝ⁺v = 0`, `Ŝᶻv = (D₀/2)v`), `highestWeight_spinMultiplet_general`
gives a linearly independent family `(Ŝ⁻)^k v`, `k : Fin (D₀+1)`; each member stays in the ground
submodule (`Ŝ⁻` commutes with `Ĥ` and `N̂`, applied as a power), so lifting the independence into the
submodule and counting (`LinearIndependent.fintype_card_le_finrank`) gives the bound.  This holds for
*any* special basis (connected or not); equality with `D₀+1` needs connectivity (`generalFlatBandGround_finrank_le_of_connected`). -/
theorem generalFlatBandGround_finrank_ge
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) :
    generalFlatBandDim T + 1 ≤ Module.finrank ℂ ↥(generalFlatBandGroundSubmodule T U) := by
  classical
  obtain ⟨eμ, heμ⟩ := exists_extended_special_basis hbasis
  choose! idx hidx using heμ
  have hvmem : generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))
      ∈ generalFlatBandGroundSubmodule T U :=
    generalFlatBandSlaterState_allUp_mem_groundSubmodule hbasis hT U
  rw [generalFlatBandGroundSubmodule, Submodule.mem_inf, LinearMap.mem_ker,
    Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hvmem
  obtain ⟨hHv, hNv⟩ := hvmem
  have hv : generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0)) ≠ 0 :=
    generalFlatBandSlaterState_allUp_ne_zero hbasis eμ idx hidx
  obtain ⟨hLI, _⟩ := highestWeight_spinMultiplet_general M I.card
    (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))) hv
    (generalFlatBand_totalSpinPlus_mulVec_allUpSlater μ I)
    (generalFlatBand_totalSpinZ_mulVec_allUpSlater μ I)
  set G := generalFlatBandGroundSubmodule T U with hG
  have hmem : ∀ k : Fin (I.card + 1),
      ((fermionTotalSpinMinus M) ^ (k : ℕ)).mulVec
          (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))) ∈ G := by
    intro k
    have hHk : (hubbardHamiltonian M T (U : ℂ)).mulVec
        (((fermionTotalSpinMinus M) ^ (k : ℕ)).mulVec
          (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0)))) = 0 := by
      have hcomm : Commute (hubbardHamiltonian M T (U : ℂ))
          ((fermionTotalSpinMinus M) ^ (k : ℕ)) :=
        ((fermionTotalSpinMinus_commute_hubbardHamiltonian M T (U : ℂ)
          (hJ := fun i j => hT.isHermitian.apply j i) (hU := Complex.conj_ofReal U)).symm).pow_right _
      rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hHv, Matrix.mulVec_zero]
    have hNk : (fermionTotalNumber (2 * M + 1)).mulVec
        (((fermionTotalSpinMinus M) ^ (k : ℕ)).mulVec
          (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0)))) =
        (generalFlatBandDim T : ℂ) • (((fermionTotalSpinMinus M) ^ (k : ℕ)).mulVec
          (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0)))) := by
      have hcomm : Commute (fermionTotalNumber (2 * M + 1)) ((fermionTotalSpinMinus M) ^ (k : ℕ)) :=
        ((fermionTotalSpinMinus_commute_fermionTotalNumber M).symm).pow_right _
      rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hNv, Matrix.mulVec_smul]
    rw [hG, generalFlatBandGroundSubmodule, Submodule.mem_inf, LinearMap.mem_ker,
      Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    exact ⟨hHk, hNk⟩
  have hGLI : LinearIndependent ℂ (fun k : Fin (I.card + 1) =>
      (⟨((fermionTotalSpinMinus M) ^ (k : ℕ)).mulVec
        (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))), hmem k⟩ : G)) :=
    LinearIndependent.of_comp G.subtype hLI
  have hcard := hGLI.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  rwa [hbasis.1] at hcard

open scoped ComplexOrder in
/-- **Connected special basis ⟹ maximal-spin multiplet** (the `⇐` direction of Tasaki
Theorem 11.17): for a *connected* flat-band special basis, the `D₀`-electron Hubbard ground
subspace is the `(D₀+1)`-fold maximal-spin multiplet — `finrank = D₀+1` and every ground state is a
`(Ŝ_tot)²`-eigenvector at `(D₀/2)(D₀/2+1)`.  The dimension is pinned by `le_antisymm` of the
connected upper bound (`generalFlatBandGround_finrank_le_of_connected`) and the unconditional lower
bound (`generalFlatBandGround_finrank_ge`); the SU(2) tower of the all-up μ-Slater, having exactly
`D₀+1` independent members, then spans the ground subspace
(`LinearIndependent.span_eq_top_of_card_eq_finrank`), and `(Ŝ_tot)²` acts as the maximal scalar on
each tower member (`highestWeight_spinMultiplet_general`), hence on every ground state. -/
theorem generalFlatBand_connected_isMaximalSpinMultiplet
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U) (hconn : generalFlatBandBasisConnected I μ) :
    IsMaximalSpinMultipletSubmodule M (generalFlatBandGroundSubmodule T U)
      (generalFlatBandDim T) := by
  classical
  obtain ⟨eμ, heμ⟩ := exists_extended_special_basis hbasis
  choose! idx hidx using heμ
  set G := generalFlatBandGroundSubmodule T U with hG
  have hfin : Module.finrank ℂ ↥G = generalFlatBandDim T + 1 :=
    le_antisymm (generalFlatBandGround_finrank_le_of_connected hbasis hT U hU eμ idx hidx hconn)
      (generalFlatBandGround_finrank_ge hbasis hT U)
  refine ⟨hfin, ?_⟩
  have hvmem : generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0)) ∈ G :=
    hG ▸ generalFlatBandSlaterState_allUp_mem_groundSubmodule hbasis hT U
  have hvmem' := hvmem
  rw [hG, generalFlatBandGroundSubmodule, Submodule.mem_inf, LinearMap.mem_ker,
    Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hvmem'
  obtain ⟨hHv, hNv⟩ := hvmem'
  have hv : generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0)) ≠ 0 :=
    generalFlatBandSlaterState_allUp_ne_zero hbasis eμ idx hidx
  obtain ⟨hLI, hSq⟩ := highestWeight_spinMultiplet_general M I.card
    (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))) hv
    (generalFlatBand_totalSpinPlus_mulVec_allUpSlater μ I)
    (generalFlatBand_totalSpinZ_mulVec_allUpSlater μ I)
  set tower : Fin (I.card + 1) → (Fin (2 * M + 2) → Fin 2) → ℂ :=
    fun k => ((fermionTotalSpinMinus M) ^ (k : ℕ)).mulVec
      (generalFlatBandSlaterState μ (flatBandSpinConfigList I (fun _ => 0))) with htower
  have hmem : ∀ k : Fin (I.card + 1), tower k ∈ G := by
    intro k
    have hHk : (hubbardHamiltonian M T (U : ℂ)).mulVec (tower k) = 0 := by
      have hcomm : Commute (hubbardHamiltonian M T (U : ℂ))
          ((fermionTotalSpinMinus M) ^ (k : ℕ)) :=
        ((fermionTotalSpinMinus_commute_hubbardHamiltonian M T (U : ℂ)
          (hJ := fun i j => hT.isHermitian.apply j i) (hU := Complex.conj_ofReal U)).symm).pow_right _
      rw [htower, Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hHv, Matrix.mulVec_zero]
    have hNk : (fermionTotalNumber (2 * M + 1)).mulVec (tower k) =
        (generalFlatBandDim T : ℂ) • (tower k) := by
      have hcomm : Commute (fermionTotalNumber (2 * M + 1)) ((fermionTotalSpinMinus M) ^ (k : ℕ)) :=
        ((fermionTotalSpinMinus_commute_fermionTotalNumber M).symm).pow_right _
      rw [htower, Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hNv, Matrix.mulVec_smul]
    rw [hG, generalFlatBandGroundSubmodule, Submodule.mem_inf, LinearMap.mem_ker,
      Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    exact ⟨hHk, hNk⟩
  have hGLI : LinearIndependent ℂ (fun k : Fin (I.card + 1) => (⟨tower k, hmem k⟩ : G)) :=
    LinearIndependent.of_comp G.subtype hLI
  have hcard : Fintype.card (Fin (I.card + 1)) = Module.finrank ℂ ↥G := by
    rw [Fintype.card_fin, hfin, hbasis.1]
  have hspan := hGLI.span_eq_top_of_card_eq_finrank hcard
  have htw : ∀ k, (fermionTotalSpinSquared M).mulVec (tower k) =
      (((generalFlatBandDim T : ℂ) / 2) * ((generalFlatBandDim T : ℂ) / 2 + 1)) • tower k := by
    intro k; rw [← hbasis.1]; exact hSq k
  intro w hwG
  have hmemw : (⟨w, hwG⟩ : G) ∈
      Submodule.span ℂ (Set.range fun k => (⟨tower k, hmem k⟩ : G)) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmemw
  have hw_eq : w = ∑ k, a k • tower k := by
    have hc := congrArg Subtype.val ha
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hc.symm
  rw [hw_eq, Matrix.mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mulVec_smul, htw k, smul_comm]

end LatticeSystem.Fermion
