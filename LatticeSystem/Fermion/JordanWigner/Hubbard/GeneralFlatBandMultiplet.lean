import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandTwoHoleCollapse
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinLoweringTowerGeneral
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiHopAction

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

end LatticeSystem.Fermion
