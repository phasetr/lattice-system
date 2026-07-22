import LatticeSystem.Quantum.SpinS.AnisotropicEigenspaceSectorFinrankEq
import LatticeSystem.Quantum.SpinS.AnisotropicSectorPFAtMin
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergGlobalMinFinrankLeTwo
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfBalancedGSFromMLM
import LatticeSystem.Quantum.SpinS.Theorem24FinrankLeOneFromAdmisPF
import LatticeSystem.Quantum.SpinS.Theorem24ZeroMagnetizationFromUniqueness

/-!
# Spin-1/2 target uniqueness from balanced-sector PF

Issue #3739 — Tasaki §2.5 Theorem 2.4.

This file packages the consumer endpoint after PR #4029.  Once the balanced
sector is known to attain the full ground energy at the target point, target
ground-state uniqueness follows from three existing ingredients:

1. the target global `finrank <= 2` theorem for spin `1/2`;
2. a non-zero balanced-sector ground vector lifted to the full Hilbert space;
3. balanced-sector Perron--Frobenius simplicity at the target point.

The last item remains an explicit hypothesis here.  The theorem then composes
the resulting `finrank <= 1` bound with the existing zero-magnetization theorem.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorems 2.3--2.4, pp. 42--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Spin-1/2 balanced-sector Perron--Frobenius simplicity at the target point**:
the anisotropic target sector matrix has a one-dimensional ground eigenspace in
the balanced magnetization sector. -/
theorem spinHalf_anisotropicHeisenbergS_balanced_sector_pf_at_target
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)]
    {lam' D' : ℝ} :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J (lam' : ℂ) (D' : ℂ)
        1 M_balanced))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M_balanced) hJ_star lam' D') : ℝ) : ℂ)) ≤ 1 := by
  classical
  let c : ℝ :=
    Finset.univ.sup' Finset.univ_nonempty
      (fun σ : magConfigS Λ 1 M_balanced =>
        dressedAnisotropicHeisenbergSReMatrixOnMagSector
          A J (lam' : ℂ) (D' : ℂ) 1 M_balanced σ σ) + 1
  have hc_strict : ∀ σ : magConfigS Λ 1 M_balanced,
      dressedAnisotropicHeisenbergSReMatrixOnMagSector
        A J (lam' : ℂ) (D' : ℂ) 1 M_balanced σ σ < c := by
    intro σ
    have hle :
        dressedAnisotropicHeisenbergSReMatrixOnMagSector
          A J (lam' : ℂ) (D' : ℂ) 1 M_balanced σ σ ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun τ : magConfigS Λ 1 M_balanced =>
            dressedAnisotropicHeisenbergSReMatrixOnMagSector
              A J (lam' : ℂ) (D' : ℂ) 1 M_balanced τ τ) :=
      Finset.le_sup'
        (fun τ : magConfigS Λ 1 M_balanced =>
          dressedAnisotropicHeisenbergSReMatrixOnMagSector
            A J (lam' : ℂ) (D' : ℂ) 1 M_balanced τ τ)
        (Finset.mem_univ σ)
    dsimp [c]
    linarith
  have hJ_bipartite : ∀ x y, A x = A y → J x y = 0 := by
    intro x y hAeq
    by_contra hne
    exact (hJbip x y hne) hAeq
  have hraw :=
    anisotropicHeisenbergS_magSector_submatrix_finrank_le_one_at_hermitianMinEigenvalue
      (Λ := Λ) (N := 1) A (J := J) (lam := (lam' : ℂ)) (D := (D' : ℂ))
      (M := M_balanced) hJim hJnn hJpos hJ_sym hJ_bipartite
      (by simp) (by simp) (c := c) hc_strict hA_ne hB_ne (by omega)
  have hmin_eq :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M_balanced) hJ_star lam' D') =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_of_real
          (Λ := Λ) (N := 1) (M := M_balanced) (lam := (lam' : ℂ)) (D := (D' : ℂ))
          (fun x y => by
            rw [Complex.star_def, Complex.conj_eq_iff_im]
            exact hJim x y)
          (by rw [Complex.star_def, Complex.conj_ofReal])
          (by rw [Complex.star_def, Complex.conj_ofReal])) :=
    hermitianMinEigenvalue_eq_of_spectrum_eq _ _ rfl
  rw [hmin_eq]
  exact hraw

/-- **Spin-1/2 target ground eigenspace `finrank <= 1` from balanced-sector PF**:
assuming Perron--Frobenius simplicity for the balanced sector at the target
point, the PR #4029 balanced-full ground-energy equality, global `finrank <= 2`,
and the admissible-sector bridge give full ground-state uniqueness. -/
theorem spinHalf_aHeisS_target_finrank_le_one_of_balSec_pf_and_MLM_casLadder_t23_pf
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
    (h_balanced_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J (lam' : ℂ) (D' : ℂ)
          1 M_balanced))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := 1) (M := M_balanced) hJ_star lam' D') : ℝ) : ℂ)) ≤ 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam' : ℂ) (D' : ℂ) 1))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') : ℝ) : ℂ)) ≤
      1 := by
  classical
  set μ_sector : ℝ := hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := 1) (M := M_balanced) hJ_star lam' D') with hμ_sector_def
  set μ_full : ℝ := hermitianMinEigenvalue
    (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') with hμ_full_def
  have h_bal_full :=
    spinHalf_anisotropicHeisenbergS_balanced_eq_full_of_MLM_casimir_ladder_t23_pf
      A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced h_balanced h_centered_nonzero hlam'_lb hlam'_ub hD'
  have hμ_eq : ((μ_sector : ℝ) : ℂ) = ((μ_full : ℝ) : ℂ) := by
    rw [hμ_sector_def, hμ_full_def]
    exact congrArg (fun x : ℝ => (x : ℂ)) h_bal_full
  have h_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam' : ℂ) (D' : ℂ) 1))
      ((μ_full : ℝ) : ℂ)) ≤ 2 := by
    have hraw :=
      spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min
        A hJim hJnn hJpos hJself hJbip
        (by simp) hlam'_lb hlam'_ub (by simp) hD'
        (hc_axis_strict (lam' : ℂ) (D' : ℂ)) hA_ne hB_ne hJ_star
        (show star (lam' : ℂ) = (lam' : ℂ) from by
          rw [Complex.star_def, Complex.conj_ofReal])
        (show star (D' : ℂ) = (D' : ℂ) from by
          rw [Complex.star_def, Complex.conj_ofReal])
    simpa [hμ_full_def, anisotropicHeisenbergS_full_isHermitian_real] using hraw
  have h_admis_pf : finrank ℂ ↥((End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J (lam' : ℂ) (D' : ℂ) 1))
        ((μ_full : ℝ) : ℂ)) ⊓ magSubspaceS Λ 1 0) ≤ 1 := by
    have h_transfer :=
      anisotropicHeisenbergS_eigenspace_inf_magSubspaceS_finrank_le_one_of_sector
        (Λ := Λ) (N := 1) J (lam' : ℂ) (D' : ℂ) M_balanced
        ((μ_sector : ℝ) : ℂ) (by simpa [hμ_sector_def] using h_balanced_sector_pf)
    rw [h_balanced] at h_transfer
    rw [hμ_eq] at h_transfer
    exact h_transfer
  obtain ⟨Φ_sector, hΦ_sector_ne, hΦ_eig, hΦ_admis⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS
      (Λ := Λ) hJ_star lam' D' 1 M_balanced
  set Φ : (Λ → Fin (1 + 1)) → ℂ := magSectorEmbedding Φ_sector with hΦ_def
  have hΦ_ne : Φ ≠ 0 := by
    intro hzero
    apply hΦ_sector_ne
    have hres := congrArg
      (magSectorRestriction (V := Λ) (N := 1) (M := M_balanced)) hzero
    simpa [hΦ_def, magSectorRestriction_magSectorEmbedding,
      magSectorRestriction_zero] using hres
  have hΦ_admis0 : Φ ∈ magSubspaceS Λ 1 0 := by
    have h_balanced' : ((Fintype.card Λ : ℂ) / 2 - (M_balanced : ℂ)) = 0 := by
      simpa using h_balanced
    simpa [hΦ_def, h_balanced', zero_smul] using hΦ_admis
  have hΦ_eig_full :
      (anisotropicHeisenbergS J (lam' : ℂ) (D' : ℂ) 1).mulVec Φ =
        ((μ_full : ℝ) : ℂ) • Φ := by
    have h := hΦ_eig
    rw [hΦ_def] at h
    rw [hμ_sector_def] at hμ_eq
    rw [hμ_eq] at h
    exact h
  exact anisotropicHeisenbergS_finrank_le_one_from_admis_pf
    J (lam' : ℂ) (D' : ℂ) ((μ_full : ℝ) : ℂ)
    h_two hΦ_admis0 hΦ_ne hΦ_eig_full h_admis_pf

/-- **Spin-1/2 target ground state has zero magnetization from balanced-sector PF**:
the target uniqueness theorem above composed with the existing
uniqueness-implies-zero-magnetization theorem. -/
theorem spinHalf_aHeisS_target_gState_zeroMag_of_balSec_pf_and_MLM_casLadder_t23_pf
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
    (h_balanced_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J (lam' : ℂ) (D' : ℂ)
          1 M_balanced))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := 1) (M := M_balanced) hJ_star lam' D') : ℝ) : ℂ)) ≤ 1)
    {Φ : (Λ → Fin (1 + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam' : ℂ) (D' : ℂ) 1).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') : ℝ) : ℂ) •
        Φ) :
    (totalSpinSOp3 Λ 1).mulVec Φ = 0 := by
  classical
  have huniq :=
    spinHalf_aHeisS_target_finrank_le_one_of_balSec_pf_and_MLM_casLadder_t23_pf
      A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced h_balanced h_centered_nonzero hlam'_lb hlam'_ub hD' h_balanced_sector_pf
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    J (lam' : ℂ) (D' : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') : ℝ) : ℂ)
    huniq hΦ_ne hΦ_gs

/-- **Spin-1/2 target ground eigenspace `finrank <= 1` without a balanced-sector
PF callback**: the callback is supplied by
`spinHalf_anisotropicHeisenbergS_balanced_sector_pf_at_target`. -/
theorem spinHalf_anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D') :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam' : ℂ) (D' : ℂ) 1))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') : ℝ) : ℂ)) ≤
      1 := by
  classical
  have hpf :=
    spinHalf_anisotropicHeisenbergS_balanced_sector_pf_at_target
      A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne M_balanced
      (lam' := lam') (D' := D')
  exact
    spinHalf_aHeisS_target_finrank_le_one_of_balSec_pf_and_MLM_casLadder_t23_pf
      A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced h_balanced h_centered_nonzero hlam'_lb hlam'_ub hD' hpf

/-- **Spin-1/2 target ground state has zero magnetization without a
balanced-sector PF callback**. -/
theorem spinHalf_aHeisS_target_gState_zeroMag_of_MLM_casLadder_t23_pf
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
    {Φ : (Λ → Fin (1 + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam' : ℂ) (D' : ℂ) 1).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') : ℝ) : ℂ) •
        Φ) :
    (totalSpinSOp3 Λ 1).mulVec Φ = 0 := by
  classical
  have hpf :=
    spinHalf_anisotropicHeisenbergS_balanced_sector_pf_at_target
      A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne M_balanced
      (lam' := lam') (D' := D')
  exact
    spinHalf_aHeisS_target_gState_zeroMag_of_balSec_pf_and_MLM_casLadder_t23_pf
      A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced h_balanced h_centered_nonzero hlam'_lb hlam'_ub hD' hpf
      hΦ_ne hΦ_gs

end LatticeSystem.Quantum
