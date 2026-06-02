import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfDNonnegBoundary
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfLambdaOneBoundary
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIICorner
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIPathGlobalFinrank
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergStrictGapFromGlobalUniqueness

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

/-! ## Path geometry for strict case (ii) -/

/-- If the target satisfies `1 < lambda`, the case-(ii) linear path has first
coordinate `1` only at `t = 0`. -/
theorem anisotropicHeisenbergParametricPath_eq_zero_of_fst_eq_one_of_one_lt
    {lam D t : ℝ} (hlam : 1 < lam)
    (hfst : (anisotropicHeisenbergParametricPath lam D t).1 = 1) :
    t = 0 := by
  have hpath : (1 - t) + t * lam = 1 := by
    simpa [anisotropicHeisenbergParametricPath] using hfst
  have hrewrite : (1 - t) + t * lam = 1 + t * (lam - 1) := by ring
  rw [hrewrite] at hpath
  have hprod : t * (lam - 1) = 0 := by linarith
  rcases mul_eq_zero.mp hprod with ht_zero | hlam_zero
  · exact ht_zero
  · linarith

/-! ## `N = 1` non-corner path-global input -/

set_option linter.style.longLine false in
/-- Strict case-(ii) non-corner parity-block PF/min callback with only
`1 <= N`.  The `lambda = 1`, `D < 0` branch is impossible because the target
satisfies `1 < lambda`, so the proof never needs the ion-only totality
hypothesis that requires `2 <= N`. -/
theorem axisSwappedParityBlockPFMinAt_of_total_reachability_noncorner_lambda_gt_one
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    {lam D : ℝ}
    (hlam_gt : 1 < lam) (hD_case_ii : D ≤ 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hnot_corner :
      ¬ ((anisotropicHeisenbergParametricPath lam D t).1 = 1 ∧
        (anisotropicHeisenbergParametricPath lam D t).2 = 0))
    (p : ℕ) [Nonempty (parityConfigS Λ N p)] :
    axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
      (anisotropicHeisenbergParametricPath lam D t).1
      (anisotropicHeisenbergParametricPath lam D t).2 p := by
  classical
  have ht_nn : 0 ≤ t := ht.1
  have hlam_ge :
      1 ≤ (anisotropicHeisenbergParametricPath lam D t).1 :=
    anisotropicHeisenbergParametricPath_fst_ge_one_case_ii (le_of_lt hlam_gt) ht_nn
  have hD_le :
      (anisotropicHeisenbergParametricPath lam D t).2 ≤ 0 :=
    anisotropicHeisenbergParametricPath_snd_nonpos_case_ii hD_case_ii ht_nn
  rcases lt_or_eq_of_le hlam_ge with hlam_path_gt | hlam_path_eq
  · rcases lt_or_eq_of_le hD_le with hD_path_lt | hD_path_eq
    · obtain ⟨c, hc_strict⟩ :=
        exists_parityBlock_dressed_diag_strict_upper_bound
          (Λ := Λ) (N := N) A J
          ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
          ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) p
      exact axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_of_caseII_raw_support
        (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
        (lam := ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ))
        (by simp)
        (by
          simp
          linarith)
        (by simpa using hlam_path_gt)
        (D := ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ))
        (by simp)
        (by simpa using hD_path_lt)
        (p := p) hc_strict
        (fun σ' σ _hne =>
          parityReachableSOnBlock_total_bipartiteCompleteGraph
            (Λ := Λ) (N := N) A hA_ne hB_ne hN σ' σ)
    · obtain ⟨c, hc_strict⟩ :=
        exists_parityBlock_dressed_diag_strict_upper_bound
          (Λ := Λ) (N := N) A J
          ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ) 0 p
      change axisSwappedParityBlockPFMinAt (Λ := Λ) (N := N) J hJim
        (anisotropicHeisenbergParametricPath lam D t).1
        (anisotropicHeisenbergParametricPath lam D t).2 p
      rw [hD_path_eq]
      exact
        axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_of_caseII_raw_support_D_zero
          (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp
          (lam := ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ))
          (by simp)
          (by
            simp
            linarith)
          (by simpa using hlam_path_gt)
          (p := p) hc_strict
          (fun σ' σ _hne =>
            bondParityReachableSOnBlock_total_bipartiteCompleteGraph
              (Λ := Λ) (N := N) A hA_ne hB_ne hN σ' σ)
  · rcases lt_or_eq_of_le hD_le with hD_path_lt | hD_path_eq
    · have ht_zero :=
        anisotropicHeisenbergParametricPath_eq_zero_of_fst_eq_one_of_one_lt
          (D := D) hlam_gt hlam_path_eq.symm
      have hD_zero : (anisotropicHeisenbergParametricPath lam D t).2 = 0 := by
        simp [anisotropicHeisenbergParametricPath, ht_zero]
      linarith
    · exact False.elim (hnot_corner ⟨hlam_path_eq.symm, hD_path_eq⟩)

set_option linter.style.longLine false in
/-- Non-corner strict case-(ii) parity-block full-min bound with only
`1 <= N`, using the strict-target path geometry to avoid the ion-only branch. -/
theorem axisSwappedSubmatrix_full_min_finrank_le_one_of_total_reachability_noncorner_lambda_gt_one
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    {lam D : ℝ}
    (hlam_gt : 1 < lam) (hD_case_ii : D ≤ 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hnot_corner :
      ¬ ((anisotropicHeisenbergParametricPath lam D t).1 = 1 ∧
        (anisotropicHeisenbergParametricPath lam D t).2 = 0))
    (p : ℕ) [Nonempty (parityConfigS Λ N p)]
    (hp : p = 0 ∨ p = 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J
        ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
        ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1)))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
          (anisotropicHeisenbergParametricPath lam D t).1
          (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 1 := by
  rcases axisSwappedParityBlockPFMinAt_of_total_reachability_noncorner_lambda_gt_one
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp hA_ne hB_ne hN
      hlam_gt hD_case_ii t ht hnot_corner p with
    ⟨ν, hν_bound, hν_eq_min⟩
  exact axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_full_min_of_pf_min
    (Λ := Λ) (N := N) (J := J) hJim hJself hJ_star
    (lam := (anisotropicHeisenbergParametricPath lam D t).1)
    (D := (anisotropicHeisenbergParametricPath lam D t).2)
    p hp ν hν_bound hν_eq_min

set_option linter.style.longLine false in
/-- Path-global full `finrank <= 2` for strict spin-`S` case-(ii) targets
from reachability available under `1 <= N`, plus the SU(2) corner callback. -/
theorem caseII_path_global_finrank_bound_of_total_reachability_and_corner_lambda_gt_one
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    {lam D : ℝ}
    (hlam_gt : 1 < lam) (hD_case_ii : D ≤ 0)
    (hcorner :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (anisotropicHeisenbergParametricPath lam D t).1 = 1 →
        (anisotropicHeisenbergParametricPath lam D t).2 = 0 →
          finrank ℂ ↥(End.eigenspace (Matrix.toLin'
            (anisotropicHeisenbergS (Λ := Λ) J
              ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
              ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N))
            ((hermitianMinEigenvalue
              (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
                (anisotropicHeisenbergParametricPath lam D t).1
                (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 2) :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 2 := by
  intro t ht
  by_cases hcorner_params :
      (anisotropicHeisenbergParametricPath lam D t).1 = 1 ∧
        (anisotropicHeisenbergParametricPath lam D t).2 = 0
  · exact hcorner t ht hcorner_params.1 hcorner_params.2
  · have h_even :=
      axisSwappedSubmatrix_full_min_finrank_le_one_of_total_reachability_noncorner_lambda_gt_one
        (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp hJ_star
        hA_ne hB_ne hN hlam_gt hD_case_ii t ht hcorner_params
        0 (Or.inl rfl)
    have h_odd :=
      axisSwappedSubmatrix_full_min_finrank_le_one_of_total_reachability_noncorner_lambda_gt_one
        (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp hJ_star
        hA_ne hB_ne hN hlam_gt hD_case_ii t ht hcorner_params
        1 (Or.inr rfl)
    exact anisotropicHeisenbergS_eigenspace_finrank_le_two_of_submatrix_blocks_le_one_general
      (Λ := Λ) (N := N) (J := J) hJself
      ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
      ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ)
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
          (anisotropicHeisenbergParametricPath lam D t).1
          (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)
      h_even h_odd

set_option linter.style.longLine false in
/-- Path-global full `finrank <= 2` for strict case-(ii) targets, using a
single full SU(2)-corner uniqueness callback. -/
theorem caseII_path_global_finrank_bound_of_total_reachability_and_su2_unique_lambda_gt_one
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (Λ → Fin (N + 1))]
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    {lam D : ℝ}
    (hlam_gt : 1 < lam) (hD_case_ii : D ≤ 0)
    (h_SU2_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ)) ≤ 1) :
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (anisotropicHeisenbergS (Λ := Λ) J
            ((anisotropicHeisenbergParametricPath lam D t).1 : ℂ)
            ((anisotropicHeisenbergParametricPath lam D t).2 : ℂ) N))
          ((hermitianMinEigenvalue
            (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N
              (anisotropicHeisenbergParametricPath lam D t).1
              (anisotropicHeisenbergParametricPath lam D t).2) : ℝ) : ℂ)) ≤ 2 :=
  caseII_path_global_finrank_bound_of_total_reachability_and_corner_lambda_gt_one
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJself hJsupp hJ_star hA_ne hB_ne hN
    hlam_gt hD_case_ii
    (fun t _ht hlam hD => by
      rw [hlam, hD]
      exact le_trans h_SU2_unique (by omega))

/-! ## Spin-1/2 target wrappers -/

set_option linter.style.longLine false in
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

set_option linter.style.longLine false in
/-- Spin-`1/2` strict case-(ii) target ground states have zero total
magnetization. -/
theorem spinHalf_anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_MLM_casimir_ladder_t23_pf
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

set_option linter.style.longLine false in
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
    exact spinHalf_anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg
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
    · exact spinHalf_anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf
        (Λ := Λ) A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hA_ne hB_ne
        M_balanced h_balanced h_centered_nonzero c_mlm c_toy hT23 hc_heis_strict
        hc_toy_strict h_card_eq hlam_gt hD_case_ii
    · subst lam
      exact spinHalf_anisotropicHeisenbergS_lambda_one_finrank_le_one_of_MLM_casimir_ladder_t23_pf
        (Λ := Λ) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne
        c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq D

set_option linter.style.longLine false in
/-- Spin-`1/2` Tasaki Theorem 2.4 zero-magnetization wrapper over the exact
case-(i) and case-(ii) parameter region currently proved for `N = 1`. -/
theorem spinHalf_anisotropicHeisenbergS_tasaki24_target_zero_magnetization_of_MLM_casimir_ladder_t23_pf
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
