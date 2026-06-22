import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfDNonnegBoundary
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfLambdaOneBoundary
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIICorner
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIPathGlobalFinrank
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergStrictGapFromGlobalUniqueness

/-!
# Anisotropic Heisenberg spin-1/2 case (ii): path-geometry foundation

Foundational layer extracted from `AnisotropicHeisenbergSpinHalfCaseII.lean` for build
speed (Tasaki §2.5 Theorems 2.3–2.4).  This file develops the case-(ii) path geometry —
the axis-swapped parity-block PF-minimum and full-submatrix `finrank ≤ 1` inputs at
total reachability (non-corner, `λ > 1`) and the `N = 1` non-corner path-global finrank
bounds (corner / SU(2)-uniqueness endpoints).

The spin-1/2 target wrappers (`finrank ≤ 1` and zero-magnetization, case-(ii) and
Theorem 2.4) are kept in the capstone module `AnisotropicHeisenbergSpinHalfCaseII.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §2.5 Theorems 2.3–2.4, pp. 42–44.
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

end LatticeSystem.Quantum
