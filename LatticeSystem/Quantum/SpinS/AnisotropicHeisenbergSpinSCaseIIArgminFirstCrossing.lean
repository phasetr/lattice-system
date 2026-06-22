import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIArgminFirstCrossingCore
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIStrictGapFromCrossing

/-!
# General spin-S case-(ii) target bridge from an argmin first crossing

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

PR #4102 exposed a callback at the first crossing of each non-balanced
magnetization sector.  This file narrows that callback to the sector selected
by the existing argmin extraction over first-crossing times.  The remaining
case-(ii) mathematical input can therefore assume the chosen sector minimises
the first crossing among all non-balanced sectors with non-empty crossing set.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Case-(ii) target wrappers from an argmin first-crossing callback -/

/-- **General spin-S case-(ii) target ground eigenspace `finrank <= 1` from an
argmin first-crossing callback**. -/
theorem anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_argmin_first_crossing
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
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    (h_argmin_first_crossing_contradiction :
      caseIIArgminFirstCrossingContradiction (Λ := Λ) hJ_star N M_balanced lam D) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 :=
  anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_crossing_contradiction
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii
    (fun M hM_nonempty hM_ne htarget_crossing => by
      letI : Nonempty (magConfigS Λ N M) := hM_nonempty
      exact anisotropicHeisenbergS_case_ii_crossing_contradiction_of_argmin_first_crossing
        (Λ := Λ) (N := N) (J := J) hJ_star M_balanced hlam_case_ii hD_case_ii
        h_argmin_first_crossing_contradiction M hM_ne (by
          simpa [anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath]
            using htarget_crossing))

/-- **General spin-S case-(ii) target ground states have zero total
magnetization from an argmin first-crossing callback**. -/
theorem anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_argmin_first_crossing
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
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    (h_argmin_first_crossing_contradiction :
      caseIIArgminFirstCrossingContradiction (Λ := Λ) hJ_star N M_balanced lam D)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_crossing_contradiction
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii
    (fun M hM_nonempty hM_ne htarget_crossing => by
      letI : Nonempty (magConfigS Λ N M) := hM_nonempty
      exact anisotropicHeisenbergS_case_ii_crossing_contradiction_of_argmin_first_crossing
        (Λ := Λ) (N := N) (J := J) hJ_star M_balanced hlam_case_ii hD_case_ii
        h_argmin_first_crossing_contradiction M hM_ne (by
          simpa [anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath]
            using htarget_crossing))
    hΦ_ne hΦ_gs

end LatticeSystem.Quantum
