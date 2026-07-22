import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfCaseIICore

/-!
# Spin-1/2 Tasaki Theorem 2.4 case-(ii) wrapper

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

This file closes the spin-`1/2` (`N = 1`) case-(ii) packaging gap.  The
general spin-`S` total-reachability wrapper needs `2 <= N` because the
`lambda = 1`, `D < 0` boundary uses ion-only parity reachability.  For a
strict case-(ii) target `1 < lambda`, however, the linear deformation path
from `(1,0)` never meets the `lambda = 1`, `D < 0` branch: the only
`lambda = 1` point is the SU(2) corner.  Thus the strict and `D = 0`
bond-only reachability inputs, both available for `1 <= N`, suffice.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorems 2.3--2.4, pp. 42--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Spin-1/2 target wrappers -/

/-- Spin-`1/2` strict case-(ii) target ground eigenspace `finrank <= 1` from
the MLM/Casimir/Theorem 2.3 endpoint. -/
theorem spinHalf_anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (Λ → Fin (1 + 1))]
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M : ℕ, M ∈ Finset.range (Fintype.card Λ * 1 + 1) → M ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M : ℂ)) ≠ 0)
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    {lam D : ℝ}
    (hlam_gt : 1 < lam) (hD_case_ii : D ≤ 0) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) 1))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam D) :
          ℝ) : ℂ)) ≤ 1 := by
  classical
  have h_SU2_unique :=
    spinHalf_anisotropicHeisenbergS_lambda_one_finrank_le_one_of_MLM_casimir_ladder_t23_pf
      (Λ := Λ) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq 0
  have h_GS_at_SU2_base :=
    hermitianMinEigenvalue_balanced_eq_full_at_SU2_of_global_unique
      (Λ := Λ) hJ_star 1 M_balanced h_balanced h_SU2_unique
  have h_GS_at_SU2 :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star 1 M_balanced lam D 0 =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1
          (anisotropicHeisenbergParametricPath lam D 0).1
          (anisotropicHeisenbergParametricPath lam D 0).2) := by
    have hpath := anisotropicHeisenbergParametricPath_zero lam D
    unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
    simp only [hpath]
    exact h_GS_at_SU2_base
  have h_strict_gap_at_SU2 :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ 1 M), M ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star 1 M_balanced lam D 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star 1 M lam D 0 := by
    intro M hM_nonempty hM_ne_balanced
    haveI := hM_nonempty
    have hM_range : M ∈ Finset.range (Fintype.card Λ * 1 + 1) := by
      rw [Finset.mem_range]
      obtain ⟨σ⟩ := hM_nonempty
      have hbound := magSumS_le σ.val
      rw [σ.property] at hbound
      exact Nat.lt_succ_of_le hbound
    exact strict_gap_at_path_zero_of_global_unique
      (Λ := Λ) hJ_star 1 M_balanced M lam D h_balanced
      (h_centered_nonzero M hM_range hM_ne_balanced)
      h_SU2_unique h_GS_at_SU2_base
  exact anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_path_global_finrank_bound
    (Λ := Λ) (N := 1) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne
    (by norm_num : 1 ≤ 1)
    M_balanced h_balanced (le_of_lt hlam_gt) hD_case_ii h_centered_nonzero
    h_strict_gap_at_SU2 h_GS_at_SU2
    (caseII_path_global_finrank_bound_of_total_reachability_and_su2_unique_lambda_gt_one
      (Λ := Λ) (N := 1) A hJim hJnn hJpos hJself
      (caseII_coupling_eq_zero_of_not_bipartiteCompleteGraph_adj (Λ := Λ) A hJself hJbip)
      hJ_star hA_ne hB_ne (by norm_num : 1 ≤ 1) hlam_gt hD_case_ii h_SU2_unique)

/-- Spin-`1/2` strict case-(ii) target ground states have zero total
magnetization. -/
theorem spinHalf_aHeisS_case_ii_target_zeroMag_of_MLM_casLadder_t23_pf
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (Λ → Fin (1 + 1))]
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M : ℕ, M ∈ Finset.range (Fintype.card Λ * 1 + 1) → M ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M : ℂ)) ≠ 0)
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A 1 J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J 1 σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) 1 σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    {lam D : ℝ}
    (hlam_gt : 1 < lam) (hD_case_ii : D ≤ 0)
    {Φ : (Λ → Fin (1 + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) 1).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ 1).mulVec Φ = 0 := by
  have huniq :=
    spinHalf_anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf
      (Λ := Λ) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hA_ne hB_ne
      M_balanced h_balanced h_centered_nonzero c_mlm c_toy hT23 hc_heis_strict
      hc_toy_strict h_card_eq hlam_gt hD_case_ii
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := 1) J (lam : ℂ) (D : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam D) :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_gs

/-! ## Exact spin-1/2 parameter-region wrapper -/

/-- Spin-`1/2` Tasaki Theorem 2.4 target uniqueness wrapper over the exact
case-(i) and case-(ii) parameter region currently proved for `N = 1`. -/
theorem spinHalf_anisotropicHeisenbergS_tasaki24_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf
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
      ∀ M : ℕ, M ∈ Finset.range (Fintype.card Λ * 1 + 1) → M ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M : ℂ)) ≠ 0)
    {lam D : ℝ}
    (h_region :
      (-1 < lam ∧ lam < 1 ∧ 0 ≤ D) ∨
      (lam = 1 ∧ 0 ≤ D) ∨
      (1 ≤ lam ∧ D ≤ 0)) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) 1))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam D) :
          ℝ) : ℂ)) ≤ 1 := by
  classical
  rcases h_region with h_case_i | h_boundary_or_case_ii
  · rcases h_case_i with ⟨hlam_lb, hlam_ub, hD_nonneg⟩
    exact
      spinHalf_anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg
      (Λ := Λ) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict
      hA_ne hB_ne c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced h_balanced h_centered_nonzero hlam_lb hlam_ub hD_nonneg
  rcases h_boundary_or_case_ii with h_lambda_one | h_case_ii
  · rcases h_lambda_one with ⟨hlam_eq, _hD_nonneg⟩
    subst lam
    exact spinHalf_anisotropicHeisenbergS_lambda_one_finrank_le_one_of_MLM_casimir_ladder_t23_pf
      (Λ := Λ) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq D
  · rcases h_case_ii with ⟨hlam_case_ii, hD_case_ii⟩
    rcases lt_or_eq_of_le hlam_case_ii with hlam_gt | hlam_eq
    · exact
        spinHalf_anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf
        (Λ := Λ) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hA_ne hB_ne
        M_balanced h_balanced h_centered_nonzero c_mlm c_toy hT23 hc_heis_strict
        hc_toy_strict h_card_eq hlam_gt hD_case_ii
    · subst lam
      exact spinHalf_anisotropicHeisenbergS_lambda_one_finrank_le_one_of_MLM_casimir_ladder_t23_pf
        (Λ := Λ) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne
        c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq D

/-- Spin-`1/2` Tasaki Theorem 2.4 zero-magnetization wrapper over the exact
case-(i) and case-(ii) parameter region currently proved for `N = 1`. -/
theorem spinHalf_aHeisS_tasaki24_target_zeroMag_of_MLM_casLadder_t23_pf
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
      ∀ M : ℕ, M ∈ Finset.range (Fintype.card Λ * 1 + 1) → M ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M : ℂ)) ≠ 0)
    {lam D : ℝ}
    (h_region :
      (-1 < lam ∧ lam < 1 ∧ 0 ≤ D) ∨
      (lam = 1 ∧ 0 ≤ D) ∨
      (1 ≤ lam ∧ D ≤ 0))
    {Φ : (Λ → Fin (1 + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) 1).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ 1).mulVec Φ = 0 := by
  have huniq :=
    spinHalf_anisotropicHeisenbergS_tasaki24_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf
      (Λ := Λ) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict
      hA_ne hB_ne c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced h_balanced h_centered_nonzero h_region
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := 1) J (lam : ℂ) (D : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star 1 lam D) :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_gs

end LatticeSystem.Quantum
