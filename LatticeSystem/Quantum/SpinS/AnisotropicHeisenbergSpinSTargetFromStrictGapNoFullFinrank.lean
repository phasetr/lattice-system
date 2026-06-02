import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSTargetFromStrictGap
import LatticeSystem.Quantum.SpinS.HermitianEigenspaceBotBelowMin

/-!
# General spin-S target uniqueness from strict sector gap without full `finrank <= 2`

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

The PR #4097 strict-gap bridge still kept the full target ground eigenspace
`finrank <= 2` input explicit.  This file removes that input from the
strict-gap target bridge: a strict gap over every non-balanced non-empty
magnetization sector directly forces every full ground vector into the balanced
sector.  Balanced-sector Perron--Frobenius simplicity then gives full target
uniqueness.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Finset

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Strict gap forces full ground vectors into the balanced sector -/

/-- **Ground vectors lie in the balanced magnetization sector under strict
sector gap**.  If the balanced-sector minimum equals the full ground energy and
every non-balanced non-empty sector has strictly larger minimum, then every
full ground eigenvector belongs to `magSubspaceS Λ N 0`. -/
theorem anisotropicHeisenbergS_groundState_mem_balanced_sector_of_strict_gap
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    [Nonempty (Λ → Fin (N + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (h_balanced_eq_full :
      hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) =
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D))
    (h_strict_gap :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) <
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M) hJ_star lam D))
    {Ψ : (Λ → Fin (N + 1)) → ℂ}
    (hΨ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Ψ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Ψ) :
    Ψ ∈ magSubspaceS Λ N 0 := by
  classical
  set μ_full : ℝ := hermitianMinEigenvalue
    (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D)
  set μ_balanced : ℝ := hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D)
  have hμ_eq : μ_balanced = μ_full := by
    simpa [μ_balanced, μ_full] using h_balanced_eq_full
  rw [eq_sum_magSectorEmbedding_magSectorRestriction Ψ]
  refine Submodule.sum_mem _ ?_
  intro M _
  by_cases hM_bal : M = M_balanced
  · subst M
    have hmem : magSectorEmbedding (magSectorRestriction (M := M_balanced) Ψ) ∈
        magSubspaceS Λ N
          (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ)) :=
      magSectorEmbedding_mem_magSubspaceS _
    rw [h_balanced] at hmem
    exact hmem
  · by_cases hM_nonempty : Nonempty (magConfigS Λ N M)
    · letI : Nonempty (magConfigS Λ N M) := hM_nonempty
      have hlt : μ_full <
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ_star lam D) := by
        rw [← hμ_eq]
        exact h_strict_gap M hM_nonempty hM_bal
      have hbot :
          End.eigenspace (Matrix.toLin'
              (anisotropicHeisenbergS_magSector_submatrix
                (Λ := Λ) J (lam : ℂ) (D : ℂ) N M))
              ((μ_full : ℝ) : ℂ) = ⊥ :=
        hermitian_eigenspace_eq_bot_of_real_lt_min
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M) hJ_star lam D) hlt
      have hΨ_gs_mu :
          (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Ψ =
            ((μ_full : ℝ) : ℂ) • Ψ := by
        simpa [μ_full] using hΨ_gs
      have hsec_eig :
          (anisotropicHeisenbergS_magSector_submatrix
              (Λ := Λ) J (lam : ℂ) (D : ℂ) N M).mulVec
            (magSectorRestriction (M := M) Ψ) =
            ((μ_full : ℝ) : ℂ) • magSectorRestriction (M := M) Ψ :=
        anisotropicHeisenbergS_magSector_submatrix_mulVec_magSectorRestriction_of_full_eigen
          (Λ := Λ) (N := N) J (lam : ℂ) (D : ℂ) (M := M) hΨ_gs_mu
      have hmem_eig :
          magSectorRestriction (M := M) Ψ ∈
            End.eigenspace (Matrix.toLin'
              (anisotropicHeisenbergS_magSector_submatrix
                (Λ := Λ) J (lam : ℂ) (D : ℂ) N M))
              ((μ_full : ℝ) : ℂ) := by
        rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
        exact hsec_eig
      have hzero_restrict : magSectorRestriction (M := M) Ψ = 0 :=
        (Submodule.eq_bot_iff _).mp hbot _ hmem_eig
      rw [hzero_restrict, magSectorEmbedding_zero]
      exact (magSubspaceS Λ N 0).zero_mem
    · have hzero : magSectorEmbedding (magSectorRestriction (M := M) Ψ) = 0 := by
        funext σ
        by_cases hσM : magSumS σ = M
        · exact False.elim (hM_nonempty ⟨⟨σ, hσM⟩⟩)
        · exact magSectorEmbedding_apply_of_not_mem (magSectorRestriction (M := M) Ψ) hσM
      rw [hzero]
      exact (magSubspaceS Λ N 0).zero_mem

/-! ## Target wrappers from strict gap alone -/

/-- **General spin-S target ground eigenspace `finrank <= 1` from strict sector
gap, without a full `finrank <= 2` input**. -/
theorem anisotropicHeisenbergS_target_finrank_le_one_of_strict_gap_no_full_le_two
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (Λ → Fin (N + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (h_strict_gap :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) <
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M) hJ_star lam D)) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 := by
  classical
  set μ_full : ℝ := hermitianMinEigenvalue
    (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D)
  set μ_balanced : ℝ := hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D)
  have h_balanced_eq_full :=
    hermitianMinEigenvalue_balanced_eq_full_of_strict_gap
      (Λ := Λ) hJ_star N M_balanced lam D h_strict_gap
  have hpf :=
    anisotropicHeisenbergS_balanced_sector_pf_at_target
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
      M_balanced (lam := lam) (D := D)
  have h_admis_pf : finrank ℂ ↥((End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
        ((μ_full : ℝ) : ℂ)) ⊓ magSubspaceS Λ N 0) ≤ 1 := by
    have h_transfer :=
      anisotropicHeisenbergS_eigenspace_inf_magSubspaceS_finrank_le_one_of_sector
        (Λ := Λ) (N := N) J (lam : ℂ) (D : ℂ) M_balanced
        ((μ_balanced : ℝ) : ℂ)
        (by simpa [μ_balanced] using hpf)
    rw [h_balanced] at h_transfer
    have hμ_eq : ((μ_balanced : ℝ) : ℂ) = ((μ_full : ℝ) : ℂ) := by
      exact congrArg (fun x : ℝ => (x : ℂ))
        (by simpa [μ_balanced, μ_full] using h_balanced_eq_full)
    rw [hμ_eq] at h_transfer
    exact h_transfer
  set E := End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((μ_full : ℝ) : ℂ)
  have h_subset : E ≤ magSubspaceS Λ N 0 := by
    intro Ψ hΨ_mem
    simp only [E, End.mem_eigenspace_iff, Matrix.toLin'_apply] at hΨ_mem
    exact anisotropicHeisenbergS_groundState_mem_balanced_sector_of_strict_gap
      (Λ := Λ) (N := N) (J := J) hJ_star M_balanced h_balanced
      h_balanced_eq_full h_strict_gap hΨ_mem
  have h_inter_eq : E ⊓ magSubspaceS Λ N 0 = E := inf_eq_left.mpr h_subset
  have hbound := h_admis_pf
  rw [h_inter_eq] at hbound
  simpa [E] using hbound

/-- **General spin-S target ground states have zero total magnetization from
strict sector gap, without a full `finrank <= 2` input**. -/
theorem anisotropicHeisenbergS_target_groundState_zero_magnetization_of_strict_gap_no_full_le_two
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (Λ → Fin (N + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (h_strict_gap :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) <
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M) hJ_star lam D))
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  classical
  have huniq :=
    anisotropicHeisenbergS_target_finrank_le_one_of_strict_gap_no_full_le_two
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
      M_balanced h_balanced h_strict_gap
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J (lam : ℂ) (D : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_gs

/-! ## Case-(ii) theorem-surface wrappers -/

/-- **General spin-S case-(ii) target ground eigenspace `finrank <= 1` from
strict sector gap, with no full `finrank <= 2` input**. -/
theorem anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_strict_gap_no_full_le_two
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (Λ → Fin (N + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (_hlam_case_ii : 1 ≤ lam) (_hD_case_ii : D ≤ 0)
    (h_strict_gap :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) <
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M) hJ_star lam D)) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 :=
  anisotropicHeisenbergS_target_finrank_le_one_of_strict_gap_no_full_le_two
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced h_strict_gap

/-- **General spin-S case-(ii) target ground states have zero total
magnetization from strict sector gap, with no full `finrank <= 2` input**. -/
theorem anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_strict_gap_no_full_le_two
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (Λ → Fin (N + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (_hlam_case_ii : 1 ≤ lam) (_hD_case_ii : D ≤ 0)
    (h_strict_gap :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) <
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M) hJ_star lam D))
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  anisotropicHeisenbergS_target_groundState_zero_magnetization_of_strict_gap_no_full_le_two
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced h_strict_gap hΦ_ne hΦ_gs

end LatticeSystem.Quantum
