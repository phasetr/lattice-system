import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedFromGlobalUniqueness
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfObligation2SU2Unique

/-!
# Spin-1/2 Theorem 2.4 obligation (2) from only SU(2) global uniqueness

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

This file composes the balanced-sector equality bridge from global SU(2)
uniqueness with the PR #4018 capstone. The resulting theorem removes the
separate balanced-sector ground-energy equality hypothesis from the public
obligation-(2) boundary.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Spin-1/2 obligation (2) from only SU(2) global uniqueness**: the
deformation contradiction follows from the full SU(2)-point ground eigenspace
being one-dimensional, without separately assuming balanced-sector equality at
the SU(2) endpoint. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_of_SU2_global_unique_only
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
            ℝ) : ℂ)) ≤ 1) :
    False := by
  classical
  have h_GS_at_SU2 :=
    hermitianMinEigenvalue_balanced_eq_full_at_SU2_of_global_unique
      (Λ := Λ) hJ_star 1 M_balanced h_balanced h_SU2_global_unique
  exact spinHalf_anisotropicHeisenbergS_obligation_2_of_SU2_global_unique
    A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
    M_balanced M_orig h_balanced hM_orig_ne h_centered_nonzero
    hlam'_lb hlam'_ub hD' h_violation_orig h_SU2_global_unique h_GS_at_SU2

end LatticeSystem.Quantum
