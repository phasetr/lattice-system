import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIConditionalBridge
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIStrictGapFromCrossing
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricMinEigenvalue

/-!
# General spin-S case-(ii) target crossing contradiction from a path callback

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

PR #4099 reduced the remaining case-(ii) strict-gap derivation to a target
crossing contradiction callback.  This file shifts that callback one step
closer to the deformation argument: a contradiction for every crossing along
the case-(ii) path implies the target crossing contradiction by evaluating the
path at `t = 1`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Target crossing contradiction from a path callback -/

/-- **General spin-S case-(ii) target crossing contradiction from a path
crossing contradiction callback**.

If every crossing along the path in the case-(ii) region contradicts the path
hypotheses, then the target crossing at `t = 1` is impossible. -/
theorem anisotropicHeisenbergS_case_ii_crossing_contradiction_of_path_crossing_contradiction
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    {lam D : ℝ}
    (hlam_case_ii : 1 ≤ lam) (hD_case_ii : D ≤ 0)
    (h_path_crossing_contradiction :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
          1 ≤ (anisotropicHeisenbergParametricPath lam D t).1 →
          (anisotropicHeisenbergParametricPath lam D t).2 ≤ 0 →
          anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
              hJ_star N M lam D t ≤
            anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
              hJ_star N M_balanced lam D t →
          False)
    (M : ℕ) [Nonempty (magConfigS Λ N M)] (hM_ne : M ≠ M_balanced) :
    hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M) hJ_star lam D) ≤
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) →
      False := by
  intro htarget_crossing
  have hregion :=
    anisotropicHeisenbergParametricPath_in_case_ii_region
      (lam' := lam) (D' := D) hlam_case_ii hD_case_ii
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1)
  exact h_path_crossing_contradiction M inferInstance hM_ne 1
    ⟨by norm_num, by norm_num⟩ hregion.1 hregion.2 (by
      simpa [anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath] using
        htarget_crossing)

/-! ## Case-(ii) target wrappers from a path crossing callback -/

/-- **General spin-S case-(ii) target ground eigenspace `finrank <= 1` from a
path crossing contradiction callback**. -/
theorem anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_path_crossing_contradiction
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
    (h_path_crossing_contradiction :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
          1 ≤ (anisotropicHeisenbergParametricPath lam D t).1 →
          (anisotropicHeisenbergParametricPath lam D t).2 ≤ 0 →
          anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
              hJ_star N M lam D t ≤
            anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
              hJ_star N M_balanced lam D t →
          False) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 :=
  anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_crossing_contradiction
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii
    (fun M hM_nonempty hM_ne => by
      letI : Nonempty (magConfigS Λ N M) := hM_nonempty
      exact anisotropicHeisenbergS_case_ii_crossing_contradiction_of_path_crossing_contradiction
        (Λ := Λ) (N := N) (J := J) hJ_star M_balanced
        hlam_case_ii hD_case_ii h_path_crossing_contradiction M hM_ne)

/-- **General spin-S case-(ii) target ground states have zero total
magnetization from a path crossing contradiction callback**. -/
theorem anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_path_crossing_contradiction
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
    (h_path_crossing_contradiction :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
          1 ≤ (anisotropicHeisenbergParametricPath lam D t).1 →
          (anisotropicHeisenbergParametricPath lam D t).2 ≤ 0 →
          anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
              hJ_star N M lam D t ≤
            anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
              hJ_star N M_balanced lam D t →
          False)
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
    (fun M hM_nonempty hM_ne => by
      letI : Nonempty (magConfigS Λ N M) := hM_nonempty
      exact anisotropicHeisenbergS_case_ii_crossing_contradiction_of_path_crossing_contradiction
        (Λ := Λ) (N := N) (J := J) hJ_star M_balanced
        hlam_case_ii hD_case_ii h_path_crossing_contradiction M hM_ne)
    hΦ_ne hΦ_gs

end LatticeSystem.Quantum
