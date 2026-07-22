import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSDNonnegBoundaryGlobalMin

/-!
# Anisotropic spin-`S` Heisenberg `D ≥ 0` boundary — SU(2)/MLM target endpoints

Continued from `AnisotropicHeisenbergSpinSDNonnegBoundaryGlobalMin.lean` (the
`D ≥ 0` deformation-path wrappers, the global-minimum `finrank ℂ ≤ 2` results,
and the axiomatic / single-axiom obligation-(2) bridges).  This file carries the
final §2.5 Theorem 2.4 target endpoints from SU(2) global uniqueness and from
the MLM Casimir-ladder route: the `D ≥ 0` obligation (2), the strict gap over
all `M`, and the target `finrank ℂ ≤ 1` / zero-magnetization conclusions.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- General spin-`S` obligation (2) from only SU(2) global uniqueness, with
target `D' >= 0`. -/
theorem anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_only_D_nonneg_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced M_orig : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M_orig)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_orig_ne : M_orig ≠ M_balanced)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (h_violation_orig :
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_orig lam' D' 1 ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ_star N M_balanced lam' D' 1)
    (h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ)) ≤ 1) :
    False := by
  classical
  have h_GS_at_SU2 :=
    hermitianMinEigenvalue_balanced_eq_full_at_SU2_of_global_unique
      (Λ := Λ) hJ_star N M_balanced h_balanced h_SU2_global_unique
  have h_strict_gap_at_SU2 :
      ∀ M' : ℕ, [Nonempty (magConfigS Λ N M')] → M' ≠ M_balanced →
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M_balanced lam' D' 0 <
        anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
          (Λ := Λ) hJ_star N M' lam' D' 0 := by
    intro M' hNE_M' hM'_ne_bal
    haveI := hNE_M'
    have hM'_range : M' ∈ Finset.range (Fintype.card Λ * N + 1) := by
      rw [Finset.mem_range]
      obtain ⟨σ⟩ := hNE_M'
      have hbound := magSumS_le σ.val
      rw [σ.property] at hbound
      exact Nat.lt_succ_of_le hbound
    exact strict_gap_at_path_zero_of_global_unique
      (Λ := Λ) hJ_star N M_balanced M' lam' D'
      h_balanced (h_centered_nonzero M' hM'_range hM'_ne_bal)
      h_SU2_global_unique h_GS_at_SU2
  exact anisotropicHeisenbergS_obligation_2_single_axiom_D_nonneg_general
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hN hJ_star
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD' h_violation_orig h_strict_gap_at_SU2

set_option linter.style.longLine false in
/-- General spin-`S` target strict gap from SU(2) global uniqueness, with
target `D' >= 0`. -/
theorem anisotropicHeisenbergS_strict_gap_all_M_of_SU2_global_unique_D_nonneg_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    (h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ)) ≤ 1)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (M : ℕ) [Nonempty (magConfigS Λ N M)] (hM_ne : M ≠ M_balanced) :
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam' D') <
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M) hJ_star lam' D') := by
  classical
  have hpath : anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star N M_balanced lam' D' 1 <
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ_star N M lam' D' 1 := by
    exact lt_of_not_ge (by
      intro h_violation
      exact anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_only_D_nonneg_general
        A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hN hJ_star
        M_balanced M h_balanced hM_ne h_centered_nonzero
        hlam'_lb hlam'_ub hD' h_violation h_SU2_global_unique)
  unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath at hpath
  simp only [anisotropicHeisenbergParametricPath_one] at hpath
  exact hpath

set_option linter.style.longLine false in
/-- General spin-`S` target uniqueness from SU(2) global uniqueness in the
case-(i) `D' >= 0` boundary strip. -/
theorem anisotropicHeisenbergS_target_finrank_le_one_of_SU2_global_unique_D_nonneg_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    (h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ)) ≤ 1)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D') :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam' : ℂ) (D' : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
          ℝ) : ℂ)) ≤ 1 := by
  classical
  have h_global_two :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J (lam' : ℂ) (D' : ℂ) N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
            ℝ) : ℂ)) ≤ 2 := by
    have hraw :=
      anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_D_nonneg_general
        A hJim hJnn hJpos hJself hJbip
        (by simp) hlam'_lb hlam'_ub (by simp) hD'
        (hc_strict (lam' : ℂ) (D' : ℂ)) hA_ne hB_ne hN hJ_star
        (show star (lam' : ℂ) = (lam' : ℂ) from by
          rw [Complex.star_def, Complex.conj_ofReal])
        (show star (D' : ℂ) = (D' : ℂ) from by
          rw [Complex.star_def, Complex.conj_ofReal])
    simpa [anisotropicHeisenbergS_full_isHermitian_real] using hraw
  have h_strict_gap :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam' D') <
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M) hJ_star lam' D') := by
    intro M hM hM_ne
    haveI := hM
    exact anisotropicHeisenbergS_strict_gap_all_M_of_SU2_global_unique_D_nonneg_general
      A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hN hJ_star
      M_balanced h_balanced h_centered_nonzero h_SU2_global_unique
      hlam'_lb hlam'_ub hD' M hM_ne
  exact anisotropicHeisenbergS_target_finrank_le_one_of_strict_gap
    A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced h_strict_gap h_global_two

set_option linter.style.longLine false in
/-- General spin-`S` target ground states have zero magnetization from SU(2)
global uniqueness in the case-(i) `D' >= 0` boundary strip. -/
theorem anisotropicHeisenbergS_target_groundState_zero_magnetization_of_SU2_global_unique_D_nonneg_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    (h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ)) ≤ 1)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hΦ_ne : Φ ≠ 0)
    (hΦ_eig :
      (anisotropicHeisenbergS J (lam' : ℂ) (D' : ℂ) N).mulVec Φ =
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
            ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  classical
  have huniq :=
    anisotropicHeisenbergS_target_finrank_le_one_of_SU2_global_unique_D_nonneg_general
      A hJim hJnn hJpos hJself hJbip hJ_sym hc_strict hA_ne hB_ne hN hJ_star
      M_balanced h_balanced h_centered_nonzero h_SU2_global_unique
      hlam'_lb hlam'_ub hD'
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J (lam' : ℂ) (D' : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_eig

set_option linter.style.longLine false in
/-- General spin-`S` target uniqueness from the MLM/Casimir SU(2) endpoint in
the case-(i) `D' >= 0` boundary strip. -/
theorem anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D') :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam' : ℂ) (D' : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
          ℝ) : ℂ)) ≤ 1 := by
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
  obtain ⟨μ, hμ_min, _hsectors, huniq_heis⟩ :=
    exists_t23_commonE_and_heisHamS_fullEig_finrank_le_one_of_casLadder_t23_pf
      (V := Λ) A N c_mlm c_toy hT23 hJim hJ_star hJ_sym hJnn hJ_bipartite_zero
      hJpos hc_heis_strict hc_toy_strict h_card_eq hN hcardA hcardB
  have h_SU2_global_unique :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J 1 0 N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0) :
            ℝ) : ℂ)) ≤ 1 :=
    anisotropicHeisenbergS_SU2_ground_eigenspace_finrank_le_one_of_heisenberg_general
      (Λ := Λ) (N := N) hJ_star hμ_min huniq_heis
  exact anisotropicHeisenbergS_target_finrank_le_one_of_SU2_global_unique_D_nonneg_general
    A hJim hJnn hJpos hJself hJbip hJ_sym hc_axis_strict hA_ne hB_ne hN hJ_star
    M_balanced h_balanced h_centered_nonzero h_SU2_global_unique
    hlam'_lb hlam'_ub hD'

set_option linter.style.longLine false in
/-- General spin-`S` target zero-magnetization from the MLM/Casimir SU(2)
endpoint in the case-(i) `D' >= 0` boundary strip. -/
theorem anisotropicHeisenbergS_target_zero_magnetization_of_MLM_casimir_ladder_t23_pf_D_nonneg_general
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    {c_axis : ℝ}
    (hc_axis_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (N + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c_axis)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    [Nonempty (Λ → Fin (N + 1))]
    (c_mlm c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c_mlm)
    (hc_heis_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c_mlm)
    (hc_toy_strict : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (h_centered_nonzero :
      ∀ M' : ℕ, M' ∈ Finset.range (Fintype.card Λ * N + 1) → M' ≠ M_balanced →
        (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M' : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 ≤ D')
    (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hΦ_ne : Φ ≠ 0)
    (hΦ_eig :
      (anisotropicHeisenbergS J (lam' : ℂ) (D' : ℂ) N).mulVec Φ =
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
            ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  classical
  have huniq :=
    anisotropicHeisenbergS_target_finrank_le_one_of_MLM_casimir_ladder_t23_pf_D_nonneg_general
      A hJim hJnn hJpos hJself hJbip hJ_star hJ_sym hc_axis_strict hA_ne hB_ne hN
      c_mlm c_toy hT23 hc_heis_strict hc_toy_strict h_card_eq
      M_balanced h_balanced h_centered_nonzero hlam'_lb hlam'_ub hD'
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J (lam' : ℂ) (D' : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_eig

end LatticeSystem.Quantum
