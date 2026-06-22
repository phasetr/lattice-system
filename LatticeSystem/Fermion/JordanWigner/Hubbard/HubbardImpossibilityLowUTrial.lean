import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowUTrialCore

/-!
# Eigenmode kinetic diagonalization (Tasaki §11.1.1, toward Theorem 11.3)

For a Hermitian hopping matrix `t : Matrix (Fin (M+1)) (Fin (M+1)) ℂ`, the spinful kinetic operator
`Ĥ_kin = Σ_σ Σ_{i,j} t_{ij} ĉ†_{iσ}ĉ_{jσ}` is diagonalized by the single-particle eigenbasis of `t`:
in terms of the eigenmode number operators `n̂_{j,σ} = Ĉ†_σ(e_j) Ĉ_σ(ē_j)`
(`eigenNumberOp`, from `GeneralFlatBandSpanning.lean`),

`Ĥ_kin = Σ_σ Σ_j ε_j n̂_{j,σ}`   (`hubbardKinetic_eq_sum_eigenNumberOp`).

Since `n̂_{j,σ}` is diagonal in the eigenmode Fock monomials
(`eigenNumberOp_mulVec_generalModeMonomial`), this gives the kinetic energy of any eigenmode Slater
determinant as the sum of the occupied single-particle energies — the variational input for
Tasaki's spin-flip trial state (eq. (11.1.6)).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer 2020), §11.1.1, Theorem 11.3, eqs. (11.1.5)–(11.1.6), pp. 378–379.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {M : ℕ}

/-! ## Kinetic operator as a sum of eigenmode number operators -/

set_option maxHeartbeats 1000000 in
-- The nested triple `Finset.sum` reindexings over `(σ, j, y, x)` in the eigenbasis expansion
-- push elaboration past the default heartbeat budget.
/-- **Eigenmode diagonalization of the kinetic operator** (Tasaki eq. (11.1.5) in the
single-particle eigenbasis):
`Ĥ_kin = Σ_σ Σ_j ε_j n̂_{j,σ}`.

Both sides expand to `Σ_σ Σ_{y,x} t_{yx} ĉ†_{yσ}ĉ_{xσ}`: the left by definition (renaming `(i,j)`
to `(y,x)`), the right by the site expansion of `n̂_{j,σ}` and the spectral coordinate form
`Σ_j ε_j e_j(y) conj(e_j(x)) = t_{yx}` (`hubbardSpectral_entry`). -/
theorem hubbardKinetic_eq_sum_eigenNumberOp
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian) :
    hubbardKinetic M t
      = ∑ σ : Fin 2, ∑ j : Fin (M + 1), (hT.eigenvalues j : ℂ) • eigenNumberOp hT j σ := by
  rw [hubbardKinetic]
  refine Finset.sum_congr rfl fun σ _ => ?_
  -- RHS for this `σ`: `Σ_j ε_j n̂_{j,σ} = Σ_{y,x} t_{yx} (c†_{yσ} c_{xσ})`.
  calc (∑ i : Fin (M + 1), ∑ j : Fin (M + 1),
          t i j • (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
            fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)))
      = ∑ y : Fin (M + 1), ∑ x : Fin (M + 1), ∑ j : Fin (M + 1),
          ((hT.eigenvalues j : ℂ)
              * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) y
              * star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) x)) •
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M y σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)) := by
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
        rw [← hubbardSpectral_entry hT y x, Finset.sum_smul]
    _ = ∑ j : Fin (M + 1), ∑ y : Fin (M + 1), ∑ x : Fin (M + 1),
          ((hT.eigenvalues j : ℂ)
              * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) y
              * star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) x)) •
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M y σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)) := by
        rw [show (∑ y : Fin (M + 1), ∑ x : Fin (M + 1), ∑ j : Fin (M + 1),
              ((hT.eigenvalues j : ℂ)
                  * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) y
                  * star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) x)) •
                (fermionMultiCreation (2 * M + 1) (spinfulIndex M y σ) *
                  fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)))
            = ∑ y : Fin (M + 1), ∑ j : Fin (M + 1), ∑ x : Fin (M + 1),
              ((hT.eigenvalues j : ℂ)
                  * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) y
                  * star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) x)) •
                (fermionMultiCreation (2 * M + 1) (spinfulIndex M y σ) *
                  fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)) from
          Finset.sum_congr rfl fun y _ => Finset.sum_comm]
        rw [Finset.sum_comm]
    _ = ∑ j : Fin (M + 1), (hT.eigenvalues j : ℂ) • eigenNumberOp hT j σ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [eigenNumberOp_eq_site_sum hT j σ]
        rw [show (∑ x : Fin (M + 1), ∑ y : Fin (M + 1),
              (star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) x)
                  * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) y) •
                (fermionMultiCreation (2 * M + 1) (spinfulIndex M y σ) *
                  fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)))
            = ∑ y : Fin (M + 1), ∑ x : Fin (M + 1),
              (star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) x)
                  * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) y) •
                (fermionMultiCreation (2 * M + 1) (spinfulIndex M y σ) *
                  fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)) from
          Finset.sum_comm]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [smul_smul]
        congr 1
        ring

/-! ## Kinetic energy of an eigenmode Slater determinant -/

/-- **Count of an eigenmode in the subset-pair list**: `(j, σ)` occurs `1` time if its spin tag
selects the matching subset, else `0` (the list is nodup). -/
theorem spinfulSubsetPairList_count (SUp SDown : Finset (Fin (M + 1)))
    (j : Fin (M + 1)) (σ : Fin 2) :
    (spinfulSubsetPairList SUp SDown).count (j, σ)
      = if (σ = 0 ∧ j ∈ SUp) ∨ (σ = 1 ∧ j ∈ SDown) then 1 else 0 := by
  by_cases hmem : (j, σ) ∈ spinfulSubsetPairList SUp SDown
  · rw [List.count_eq_one_of_mem (spinfulSubsetPairList_nodup SUp SDown) hmem]
    rw [mem_spinfulSubsetPairList] at hmem
    rw [if_pos hmem]
  · rw [List.count_eq_zero_of_not_mem hmem]
    rw [mem_spinfulSubsetPairList] at hmem
    rw [if_neg hmem]

/-- The single-particle energy sum over the occupied eigenmodes of the subset pair `(SUp, SDown)`:
`Σ_{j∈SUp} ε_j + Σ_{j∈SDown} ε_j`.  This is the kinetic energy of the eigenmode Slater determinant
filling the up-modes `SUp` and the down-modes `SDown`. -/
noncomputable def occupiedEigenEnergy {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    (hT : t.IsHermitian) (SUp SDown : Finset (Fin (M + 1))) : ℂ :=
  (∑ j ∈ SUp, (hT.eigenvalues j : ℂ)) + ∑ j ∈ SDown, (hT.eigenvalues j : ℂ)

/-- **Kinetic energy of an eigenmode Slater determinant**: the kinetic operator acts on the
eigenmode Slater state `spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp SDown` as the scalar
`occupiedEigenEnergy = Σ_{j∈SUp} ε_j + Σ_{j∈SDown} ε_j`.  From the eigenmode diagonalization
`Ĥ_kin = Σ_σ Σ_j ε_j n̂_{j,σ}` and the count of each eigenmode in the Slater list. -/
theorem hubbardKinetic_mulVec_spinfulGeneralBasisState
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (SUp SDown : Finset (Fin (M + 1))) :
    (hubbardKinetic M t).mulVec (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp SDown)
      = occupiedEigenEnergy hT SUp SDown •
        spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp SDown := by
  set Ψ := spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp SDown with hΨ
  set qs := spinfulSubsetPairList SUp SDown with hqs
  have hΨqs : Ψ = generalModeMonomial (eigenbasisAsBasis hT) qs := rfl
  rw [hubbardKinetic_eq_sum_eigenNumberOp hT, Matrix.sum_mulVec]
  -- evaluate each `ε_j • n̂_{j,σ}` on the Slater list
  have hterm : ∀ σ : Fin 2, ∀ j : Fin (M + 1),
      ((hT.eigenvalues j : ℂ) • eigenNumberOp hT j σ).mulVec Ψ
        = ((hT.eigenvalues j : ℂ) * (qs.count (j, σ) : ℂ)) • Ψ := by
    intro σ j
    rw [Matrix.smul_mulVec, hΨqs, eigenNumberOp_mulVec_generalModeMonomial hT j σ,
      smul_smul]
  calc ∑ σ : Fin 2, (∑ j : Fin (M + 1), (hT.eigenvalues j : ℂ) • eigenNumberOp hT j σ).mulVec Ψ
      = ∑ σ : Fin 2, ∑ j : Fin (M + 1),
          ((hT.eigenvalues j : ℂ) * (qs.count (j, σ) : ℂ)) • Ψ := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Matrix.sum_mulVec]
        exact Finset.sum_congr rfl fun j _ => hterm σ j
    _ = (∑ σ : Fin 2, ∑ j : Fin (M + 1),
          (hT.eigenvalues j : ℂ) * (qs.count (j, σ) : ℂ)) • Ψ := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.sum_smul]
    _ = occupiedEigenEnergy hT SUp SDown • Ψ := by
        congr 1
        rw [occupiedEigenEnergy, Fin.sum_univ_two]
        congr 1
        · -- σ = 0 → up modes
          rw [show (∑ j : Fin (M + 1), (hT.eigenvalues j : ℂ) * (qs.count (j, 0) : ℂ))
              = ∑ j : Fin (M + 1), if j ∈ SUp then (hT.eigenvalues j : ℂ) else 0 from by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hqs, spinfulSubsetPairList_count]
            by_cases hj : j ∈ SUp
            · rw [if_pos (Or.inl ⟨rfl, hj⟩), if_pos hj, Nat.cast_one, mul_one]
            · rw [if_neg (by rintro (⟨_, h⟩ | ⟨h, _⟩); exacts [hj h, by simp at h]),
                if_neg hj, Nat.cast_zero, mul_zero]]
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        · -- σ = 1 → down modes
          rw [show (∑ j : Fin (M + 1), (hT.eigenvalues j : ℂ) * (qs.count (j, 1) : ℂ))
              = ∑ j : Fin (M + 1), if j ∈ SDown then (hT.eigenvalues j : ℂ) else 0 from by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hqs, spinfulSubsetPairList_count]
            by_cases hj : j ∈ SDown
            · rw [if_pos (Or.inr ⟨rfl, hj⟩), if_pos hj, Nat.cast_one, mul_one]
            · rw [if_neg (by rintro (⟨h, _⟩ | ⟨_, h⟩); exacts [by simp at h, hj h]),
                if_neg hj, Nat.cast_zero, mul_zero]]
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

end LatticeSystem.Fermion
