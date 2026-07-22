import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfTargetUniquenessFromBalancedPF
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfDNonnegBoundaryCore
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.longLine false

/-!
# Spin-1/2 `D >= 0` boundary for Theorem 2.4 parity-block finrank

Issue #412 — Tasaki §2.5 Theorem 2.4.

This file extends the spin-1/2 parity-block Perron--Frobenius route in the
`D` direction.  The generic spin-`S` proof assumes `0 < D.re` because
single-ion `±2` moves need strict single-ion matrix entries.  At spin `1/2`
those single-ion moves are impossible on `Fin (1 + 1)`, so the parity-block
irreducibility and global `finrank <= 2` theorem only need `0 <= D.re`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set LatticeSystem.Math.PerronFrobenius

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
set_option linter.style.longLine false in
/-- Spin-`1/2` obligation (2) under a single SU(2)-point strict-gap axiom,
with target `D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_single_axiom_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M_orig)]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_orig lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 1)
    (axiom_strict_gap_at_SU2 :
      ∀ M' : ℕ, [Nonempty (magConfigS Λ 1 M')] → M' ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star 1 M' lam' D' 0) :
    False := by
  have axiom_GS_at_SU2 :=
    strict_GS_at_path_zero_from_strict_gap_at_SU2 (Λ := Λ) hJ_star 1 M_balanced
      lam' D' (fun M' _ hne => by
        haveI := ‹Nonempty (magConfigS Λ 1 M')›
        have := axiom_strict_gap_at_SU2 M' hne
        unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath at this
        have hpath := anisotropicHeisenbergParametricPath_zero lam' D'
        simp only [hpath] at this
        exact this)
  classical
  have hne_orig : (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M_orig lam' D' ∩
      Icc (0 : ℝ) 1).Nonempty :=
    ⟨1, h_violation_orig, ⟨by norm_num, le_refl _⟩⟩
  obtain ⟨M_chosen, hM_chosen_range, hM_chosen_ne_bal, hM_chosen_NE,
          hM_chosen_cross_total, h_argmin_total⟩ :=
    exists_M_chosen_argmin_per_M_first_crossing
      hJ_star 1 M_balanced M_orig hM_orig_ne lam' D' hne_orig
  haveI := hM_chosen_NE
  have hM_chosen_cross :
      (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M_chosen lam' D' ∩
        Icc (0 : ℝ) 1).Nonempty := by
    rw [← perMCrossingSet_total_eq_perMCrossingSet]
    exact hM_chosen_cross_total
  have hM_chosen_centered_ne : (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) -
      (M_chosen : ℂ)) ≠ 0 :=
    h_centered_nonzero M_chosen hM_chosen_range hM_chosen_ne_bal
  have h_strict_chosen :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 <
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_chosen lam' D' 0 :=
    axiom_strict_gap_at_SU2 M_chosen hM_chosen_ne_bal
  have h_argmin : ∀ M' : ℕ, ∀ _ : Nonempty (magConfigS Λ 1 M'), M' ≠ M_balanced →
      (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M' lam' D' ∩ Icc (0 : ℝ) 1).Nonempty →
      sInf (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M_chosen lam' D' ∩
        Icc (0 : ℝ) 1) ≤
      sInf (perMCrossingSet (Λ := Λ) hJ_star 1 M_balanced M' lam' D' ∩
        Icc (0 : ℝ) 1) := by
    intro M' hNE_M' h_ne_bal_M' h_cross_M'
    haveI := hNE_M'
    have hM'_range : M' ∈ Finset.range (Fintype.card Λ * 1 + 1) := by
      rw [Finset.mem_range]
      obtain ⟨σ⟩ := hNE_M'
      have hbound := magSumS_le σ.val
      rw [σ.property] at hbound
      exact Nat.lt_succ_of_le hbound
    have h_cross_M'_total :
        (perMCrossingSet_total (Λ := Λ) hJ_star 1 M_balanced M' lam' D' ∩
          Icc (0 : ℝ) 1).Nonempty := by
      rw [perMCrossingSet_total_eq_perMCrossingSet]
      exact h_cross_M'
    have h_le_total := h_argmin_total M' hM'_range h_ne_bal_M' hNE_M' h_cross_M'_total
    rw [perMCrossingSet_total_eq_perMCrossingSet,
        perMCrossingSet_total_eq_perMCrossingSet] at h_le_total
    exact h_le_total
  have h_below := balanced_GS_below_sInf_of_argmin
    hJ_star 1 M_balanced M_chosen lam' D' hM_chosen_cross h_argmin
    (strict_gap_all_M_below_sInf_of_argmin hJ_star 1 M_balanced M_chosen lam' D'
      hM_chosen_cross h_argmin)
  exact spinHalf_anisotropicHeisenbergS_obligation_2_axiomatic_sup_crossing_hne_D_nonneg
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
    M_balanced M_chosen h_balanced hM_chosen_centered_ne hlam'_lb hlam'_ub hD'
    hM_chosen_cross h_strict_chosen axiom_GS_at_SU2 h_below

set_option linter.style.longLine false in
/-- Spin-`1/2` obligation (2) from SU(2) global uniqueness with target
`D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M_orig)]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_orig lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 1)
    (h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 1))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0) :
            ℝ) : ℂ)) ≤ 1)
    (h_GS_at_SU2 :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M_balanced) hJ_star 1 0) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0)) :
    False := by
  classical
  have h_strict_gap_at_SU2 :
      ∀ M' : ℕ, [Nonempty (magConfigS Λ 1 M')] → M' ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star 1 M_balanced lam' D' 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star 1 M' lam' D' 0 := by
    intro M' hNE_M' hM'_ne_bal
    haveI := hNE_M'
    have hM'_range : M' ∈ Finset.range (Fintype.card Λ * 1 + 1) := by
      rw [Finset.mem_range]
      obtain ⟨σ⟩ := hNE_M'
      have hbound := magSumS_le σ.val
      rw [σ.property] at hbound
      exact Nat.lt_succ_of_le hbound
    exact strict_gap_at_path_zero_of_global_unique
      (Λ := Λ) hJ_star 1 M_balanced M' lam' D'
      h_balanced (h_centered_nonzero M' hM'_range hM'_ne_bal)
      h_SU2_global_unique h_GS_at_SU2
  exact spinHalf_anisotropicHeisenbergS_obligation_2_single_axiom_D_nonneg
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD' h_violation_orig h_strict_gap_at_SU2

set_option linter.style.longLine false in
/-- Spin-`1/2` obligation (2) from only SU(2) global uniqueness with target
`D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_only_D_nonneg
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M_orig)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_orig lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 1)
    (h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 1))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0) :
            ℝ) : ℂ)) ≤ 1) :
    False := by
  classical
  have h_GS_at_SU2 :=
    hermitianMinEigenvalue_balanced_eq_full_at_SU2_of_global_unique
      (Λ := Λ) hJ_star 1 M_balanced h_balanced h_SU2_global_unique
  exact spinHalf_anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_D_nonneg
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD' h_violation_orig h_SU2_global_unique h_GS_at_SU2

/-- Transport Heisenberg ground-line uniqueness at the SU(2) point to the
anisotropic Hamiltonian written with `(lambda, D) = (1, 0)`. -/
private theorem anisotropicHeisenbergS_SU2_ground_eigenspace_finrank_le_one_of_heisenberg_D_nonneg_aux
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    [Nonempty (Λ → Fin (1 + 1))]
    {μ : ℝ}
    (hμ : hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real (Λ := Λ) hJ_star 1) = μ)
    (huniq :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS (Λ := Λ) J 1))
        (μ : ℂ)) ≤ 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin' (anisotropicHeisenbergS (Λ := Λ) J 1 0 1))
      ((hermitianMinEigenvalue (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0) :
        ℝ) : ℂ)) ≤ 1 := by
  have hmin :
      hermitianMinEigenvalue (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0) =
        μ := by
    simpa [anisotropicHeisenbergS_one_zero] using hμ
  have h_eigsp_eq := anisotropicHeisenbergS_at_SU2_eigenspace_eq_heisenbergHamiltonianS
    (Λ := Λ) (N := 1) J
    (((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0) : ℝ) : ℂ))
  rw [h_eigsp_eq]
  rw [hmin]
  exact huniq

set_option linter.style.longLine false in
/-- Spin-`1/2` obligation (2) from the MLM/Casimir endpoint with target
`D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_of_MLM_casimir_ladder_t23_pf_D_nonneg
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
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M_orig)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_orig lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam' D' 1) :
    False := by
  classical
  have hJ_bipartite_zero : ∀ x y, A x = A y → J x y = 0 := by
    intro x y hAxy
    by_contra hJxy_ne
    exact (hJbip x y hJxy_ne) hAxy
  have hcardA : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card := by
    obtain ⟨a, ha⟩ := hA_ne
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨a, by simp [ha]⟩)
  have hcardB : 1 ≤ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
    obtain ⟨b, hb⟩ := hB_ne
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨b, by simp [hb]⟩)
  have h_sector_pf : ∀ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := Λ) hJ_star 1) = μ →
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J 1
          ((Finset.univ.filter (fun x : Λ => A x = true)).card * 1))) (μ : ℂ)) ≤ 1 :=
    fun μ hmin_eq =>
      tasaki23_balanced_sector_matrix_finrank_le_one_of_common_min
        (V := Λ) A 1 c_mlm hT23 hJim hJ_star hJ_sym hJnn hJ_bipartite_zero
        hJpos hc_heis_strict h_card_eq (by norm_num) hcardA hcardB hmin_eq
  obtain ⟨μ, hμ_min, _hsectors, huniq_heis⟩ :=
    LatticeSystem.Quantum.exists_t23_commonE_and_heisHamS_fullEig_finrank_le_one_of_casLadder
      (V := Λ) A 1 c_mlm c_toy hT23 hJim hJ_star hJ_sym hJnn hJ_bipartite_zero
      hJpos hc_heis_strict hc_toy_strict h_card_eq (by norm_num) hcardA hcardB h_sector_pf
  have h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 1))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 1 0) :
            ℝ) : ℂ)) ≤ 1 :=
    anisotropicHeisenbergS_SU2_ground_eigenspace_finrank_le_one_of_heisenberg_D_nonneg_aux
      (Λ := Λ) hJ_star hμ_min huniq_heis
  exact spinHalf_anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_only_D_nonneg
    A hJim hJnn hJpos hJself hJbip hc_axis_strict hA_ne hB_ne hJ_star
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD' h_violation_orig h_SU2_global_unique

/-- Spin-`1/2` obligation (2) strict-gap form from the MLM/Casimir endpoint and
Theorem 2.3 sector PF, with target `D' >= 0`. -/
theorem spinHalf_aHeisS_oblig2_strict_gap_of_MLM_casLadder_t23_pf_D_nonneg
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
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M_orig)]
    [Nonempty (Λ → Fin (1 + 1))]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * 1 + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D') :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star 1 M_balanced lam' D' 1 <
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star 1 M_orig lam' D' 1 := by
  classical
  exact lt_of_not_ge (by
    intro h_violation_orig
    exact spinHalf_anisotropicHeisenbergS_obligation_2_of_MLM_casimir_ladder_t23_pf_D_nonneg
      A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
      hlam'_lb hlam'_ub hD' h_violation_orig)

/-- Spin-`1/2` strict gap for every non-balanced sector, with target
`D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_strict_gap_all_M_of_MLM_casimir_ladder_t23_pf_D_nonneg
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
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (M : ℕ) [Nonempty (magConfigS Λ 1 M)] (hM_ne : M ≠ M_balanced) :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star 1 M_balanced lam' D' 1 <
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star 1 M lam' D' 1 := by
  classical
  have hM_range : M ∈ Finset.range (Fintype.card Λ * 1 + 1) := by
    rw [Finset.mem_range]
    obtain ⟨σ⟩ := (inferInstance : Nonempty (magConfigS Λ 1 M))
    have hbound := magSumS_le σ.val
    rw [σ.property] at hbound
    exact Nat.lt_succ_of_le hbound
  exact spinHalf_aHeisS_oblig2_strict_gap_of_MLM_casLadder_t23_pf_D_nonneg
    A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
    c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
    M_balanced M h_balanced hM_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD'

set_option linter.style.longLine false in
/-- Spin-`1/2` balanced sector is the full target ground sector, with target
`D' >= 0`. -/
theorem spinHalf_anisotropicHeisenbergS_balanced_eq_full_of_MLM_casimir_ladder_t23_pf_D_nonneg
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
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D') :
    hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M_balanced) hJ_star lam' D') =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') := by
  classical
  have h_strict_gap :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ 1 M), M ≠ M_balanced →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := 1) (M := M_balanced) hJ_star lam' D') <
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := 1) (M := M) hJ_star lam' D') := by
    intro M hM_nonempty hM_ne
    haveI := hM_nonempty
    have hpath :=
      spinHalf_anisotropicHeisenbergS_strict_gap_all_M_of_MLM_casimir_ladder_t23_pf_D_nonneg
        A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
        c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
        M_balanced h_balanced h_centered_nonzero
        hlam'_lb hlam'_ub hD' M hM_ne
    unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath at hpath
    simpa using hpath
  exact hermitianMinEigenvalue_balanced_eq_full_of_strict_gap
    hJ_star 1 M_balanced lam' D' h_strict_gap

set_option linter.style.longLine false in
/-- Spin-`1/2` target ground eigenspace `finrank <= 1` in the case-(i)
`D' >= 0` boundary strip. -/
theorem spinHalf_anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg
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
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D') :
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
    spinHalf_anisotropicHeisenbergS_balanced_eq_full_of_MLM_casimir_ladder_t23_pf_D_nonneg
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
      spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_D_nonneg
        A hJim hJnn hJpos hJself hJbip
        (by simp) hlam'_lb hlam'_ub (by simp) hD'
        (hc_axis_strict (lam' : ℂ) (D' : ℂ)) hA_ne hB_ne hJ_star
        (show star (lam' : ℂ) = (lam' : ℂ) from by
          rw [Complex.star_def, Complex.conj_ofReal])
        (show star (D' : ℂ) = (D' : ℂ) from by
          rw [Complex.star_def, Complex.conj_ofReal])
    simpa [hμ_full_def, anisotropicHeisenbergS_full_isHermitian_real] using hraw
  have h_balanced_sector_pf :=
    spinHalf_anisotropicHeisenbergS_balanced_sector_pf_at_target
      A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne M_balanced
      (lam' := lam') (D' := D')
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

/-- Spin-`1/2` target ground states have zero magnetization in the case-(i)
`D' >= 0` boundary strip. -/
theorem spinHalf_aHeisS_target_gState_zeroMag_of_MLM_casLadder_t23_pf_D_nonneg
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
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    {Φ : (Λ → Fin (1 + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam' : ℂ) (D' : ℂ) 1).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') : ℝ) : ℂ) •
        Φ) :
    (totalSpinSOp3 Λ 1).mulVec Φ = 0 := by
  classical
  have huniq :=
    spinHalf_anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg
      A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced h_balanced h_centered_nonzero hlam'_lb hlam'_ub hD'
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    J (lam' : ℂ) (D' : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam' D') : ℝ) : ℂ)
    huniq hΦ_ne hΦ_gs

end LatticeSystem.Quantum
