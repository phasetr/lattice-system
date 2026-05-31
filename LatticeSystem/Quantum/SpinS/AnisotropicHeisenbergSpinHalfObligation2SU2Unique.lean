import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfObligation2SingleAxiom
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergStrictGapFromGlobalUniqueness

/-!
# Spin-1/2 Theorem 2.4 obligation (2) from SU(2) global uniqueness

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

This capstone replaces the remaining strict-gap axiom of
`spinHalf_anisotropicHeisenbergS_obligation_2_single_axiom` by the structural
SU(2)-point inputs:

* the full ground eigenspace of `Ĥ(1, 0)` has `finrank ≤ 1`;
* the balanced sector attains the full ground energy at `(1, 0)`.

Together with the existing centered-magnetization arithmetic hypothesis, these
inputs imply the strict gap for every non-balanced sector, using
`strict_gap_at_path_zero_of_global_unique`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Spin-1/2 obligation (2) from SU(2) global uniqueness**: the deformation
contradiction follows from the SU(2)-point ground eigenspace being
one-dimensional and the balanced sector attaining the SU(2) full ground
energy.  This discharges the strict-gap axiom of the single-axiom capstone. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_of_SU2_global_unique
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
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
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
  exact spinHalf_anisotropicHeisenbergS_obligation_2_single_axiom
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD' h_violation_orig h_strict_gap_at_SU2

end LatticeSystem.Quantum
