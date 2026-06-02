import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIICrossingFromPath
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergPerMCrossingSet

/-!
# General spin-S case-(ii) path crossing contradiction from crossing-set non-emptiness

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

PR #4100 reduced the remaining case-(ii) target contradiction to a path crossing
contradiction callback.  This file shifts that input to the first-crossing
set language: a pointwise crossing along the path is a witness that
`perMCrossingSet M ∩ Icc 0 1` is non-empty.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Path crossing contradiction from crossing-set non-emptiness -/

/-- **General spin-S case-(ii) path crossing contradiction from a crossing-set
non-emptiness contradiction**.

If every non-balanced `perMCrossingSet M ∩ Icc 0 1` is contradictory, then any
pointwise crossing along the path is contradictory, because the point itself
witnesses non-emptiness of that crossing set. -/
theorem anisotropicHeisenbergS_case_ii_path_crossing_contradiction_of_set_contradiction
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    {lam D : ℝ}
    (h_crossing_set_contradiction :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩ Icc (0 : ℝ) 1).Nonempty →
          False)
    (M : ℕ) [Nonempty (magConfigS Λ N M)] (hM_ne : M ≠ M_balanced)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (_hlam_path : 1 ≤ (anisotropicHeisenbergParametricPath lam D t).1)
    (_hD_path : (anisotropicHeisenbergParametricPath lam D t).2 ≤ 0) :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        hJ_star N M lam D t ≤
      anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        hJ_star N M_balanced lam D t →
      False := by
  intro hcross
  exact h_crossing_set_contradiction M inferInstance hM_ne
    ⟨t, by simpa [perMCrossingSet] using hcross, ht⟩

/-! ## Case-(ii) target wrappers from crossing-set non-emptiness -/

/-- **General spin-S case-(ii) target ground eigenspace `finrank <= 1` from a
crossing-set non-emptiness contradiction**. -/
theorem anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_set_contradiction
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
    (h_crossing_set_contradiction :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩ Icc (0 : ℝ) 1).Nonempty →
          False) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 :=
  anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_path_crossing_contradiction
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii
    (fun M hM_nonempty hM_ne t ht hlam_path hD_path => by
      letI : Nonempty (magConfigS Λ N M) := hM_nonempty
      exact anisotropicHeisenbergS_case_ii_path_crossing_contradiction_of_set_contradiction
        (Λ := Λ) (N := N) (J := J) hJ_star M_balanced
        h_crossing_set_contradiction M hM_ne t ht hlam_path hD_path)

/-- **General spin-S case-(ii) target ground states have zero total
magnetization from a crossing-set non-emptiness contradiction**. -/
theorem anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_set_contradiction
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
    (h_crossing_set_contradiction :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        (perMCrossingSet (Λ := Λ) hJ_star N M_balanced M lam D ∩ Icc (0 : ℝ) 1).Nonempty →
          False)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_path_crossing_contradiction
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii
    (fun M hM_nonempty hM_ne t ht hlam_path hD_path => by
      letI : Nonempty (magConfigS Λ N M) := hM_nonempty
      exact anisotropicHeisenbergS_case_ii_path_crossing_contradiction_of_set_contradiction
        (Λ := Λ) (N := N) (J := J) hJ_star M_balanced
        h_crossing_set_contradiction M hM_ne t ht hlam_path hD_path)
    hΦ_ne hΦ_gs

end LatticeSystem.Quantum
