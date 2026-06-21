import LatticeSystem.Quantum.SpinS.AxisSwapUnitarySSpinS
import LatticeSystem.Quantum.SpinS.AxisSwappedBlockMinEq
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergArgminExtraction
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedFromGlobalUniqueness
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedMinEqFullAtSInf
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricPathStaysInRegion
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergPerMCrossingEqualityAtSInf
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSTargetFromStrictGap
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergStrictGapAllMFromArgmin
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergStrictGapFromGlobalUniqueness
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergStrictGSAtSU2FromStrictGap
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSObligation2FromSU2UniqueCore

/-!
# General spin-S obligation (2) from SU(2) global uniqueness

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

This file lifts the spin-`1/2` first-crossing obligation-(2) capstone to a
general spin parameter `N = 2S`.  The public endpoint supplies the strict
target sector gap, and hence the target ground-state uniqueness wrappers, from
the SU(2)-point full ground eigenspace uniqueness input.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **General spin-S obligation (2) from SU(2) global uniqueness**: the
SU(2)-point global one-dimensional ground eigenspace supplies the strict-gap
axiom used by the single-axiom first-crossing capstone. -/
theorem anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_general
    {N : ℕ} (A : Λ → Bool) {J : Λ → Λ → ℂ}
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
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
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
            ℝ) : ℂ)) ≤ 1)
    (h_GS_at_SU2 :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ_star 1 0) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N 1 0)) :
    False := by
  classical
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
  exact anisotropicHeisenbergS_obligation_2_single_axiom_general
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hN hJ_star
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD' h_violation_orig h_strict_gap_at_SU2

/-- **General spin-S obligation (2) from only SU(2) global uniqueness**:
the balanced SU(2)-sector/full-ground equality is derived from the same global
uniqueness input, leaving one public SU(2) endpoint hypothesis. -/
theorem anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_only_general
    {N : ℕ} (A : Λ → Bool) {J : Λ → Λ → ℂ}
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
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
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
  exact anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_general
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hN hJ_star
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD' h_violation_orig h_SU2_global_unique h_GS_at_SU2

/-- **General spin-S target strict gap from SU(2) global uniqueness**: at the
target point of the deformation path, every non-balanced non-empty sector has
strictly larger minimum energy than the balanced sector. -/
theorem anisotropicHeisenbergS_strict_gap_all_M_of_SU2_global_unique_general
    {N : ℕ} (A : Λ → Bool) {J : Λ → Λ → ℂ}
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
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
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
      exact anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_only_general
        A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hN hJ_star
        M_balanced M h_balanced hM_ne h_centered_nonzero
        hlam'_lb hlam'_ub hD' h_violation h_SU2_global_unique)
  unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath at hpath
  simp only [anisotropicHeisenbergParametricPath_one] at hpath
  exact hpath

/-- **General spin-S target uniqueness from SU(2) global uniqueness**: the
SU(2) global uniqueness input supplies the target strict-gap callback consumed
by `anisotropicHeisenbergS_target_finrank_le_one_of_strict_gap`. -/
theorem anisotropicHeisenbergS_target_finrank_le_one_of_SU2_global_unique_general
    {N : ℕ} (A : Λ → Bool) {J : Λ → Λ → ℂ}
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
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D') :
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
    have hlam_im : ((lam' : ℂ)).im = 0 := by simp
    have hD_im : ((D' : ℂ)).im = 0 := by simp
    have hlam_re : ((lam' : ℂ)).re = lam' := by simp
    have hD_re : ((D' : ℂ)).re = D' := by simp
    have hlam_star : star (lam' : ℂ) = (lam' : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    have hD_star : star (D' : ℂ) = (D' : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    exact anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_general
      A hJim hJnn hJpos hJself hJbip
      hlam_im (by simpa [hlam_re] using hlam'_lb) (by simpa [hlam_re] using hlam'_ub)
      hD_im (by simpa [hD_re] using hD') (hc_strict (lam' : ℂ) (D' : ℂ))
      hA_ne hB_ne hN hJ_star hlam_star hD_star
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
    exact anisotropicHeisenbergS_strict_gap_all_M_of_SU2_global_unique_general
      A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hN hJ_star
      M_balanced h_balanced h_centered_nonzero h_SU2_global_unique
      hlam'_lb hlam'_ub hD' M hM_ne
  exact anisotropicHeisenbergS_target_finrank_le_one_of_strict_gap
    A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced h_strict_gap h_global_two

/-- **General spin-S target ground states have zero magnetization from SU(2)
global uniqueness**: the uniqueness wrapper above feeds the existing
zero-magnetization theorem. -/
theorem anisotropicHeisenbergS_target_groundState_zero_magnetization_of_SU2_global_unique_general
    {N : ℕ} (A : Λ → Bool) {J : Λ → Λ → ℂ}
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
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
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
    anisotropicHeisenbergS_target_finrank_le_one_of_SU2_global_unique_general
      A hJim hJnn hJpos hJself hJbip hJ_sym hc_strict hA_ne hB_ne hN hJ_star
      M_balanced h_balanced h_centered_nonzero h_SU2_global_unique
      hlam'_lb hlam'_ub hD'
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J (lam' : ℂ) (D' : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam' D') :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_eig

end LatticeSystem.Quantum
