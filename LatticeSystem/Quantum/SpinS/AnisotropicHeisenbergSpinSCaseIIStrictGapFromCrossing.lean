import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSTargetFromStrictGapNoFullFinrank

/-!
# General spin-S case-(ii) strict gap from a crossing contradiction callback

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

PR #4098 removed the full target ground eigenspace `finrank <= 2` input once a
strict sector gap is available.  This file exposes the next case-(ii) boundary:
a single crossing-contradiction callback, at the target point, implies the
strict sector gap and therefore the case-(ii) target uniqueness wrappers.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Case-(ii) strict gap from target crossing contradiction -/

/-- **General spin-S case-(ii) strict sector gap from crossing contradiction**.

If every non-balanced sector target crossing `E_M <= E_balanced` contradicts
the case-(ii) hypotheses, then the balanced sector is strictly below every
non-balanced non-empty sector. -/
theorem anisotropicHeisenbergS_case_ii_strict_gap_all_M_of_crossing_contradiction
    {J : Λ → Λ → ℂ} (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    {lam D : ℝ}
    (_hlam_case_ii : 1 ≤ lam) (_hD_case_ii : D ≤ 0)
    (h_crossing_contradiction :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ_star lam D) ≤
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) →
        False)
    (M : ℕ) [Nonempty (magConfigS Λ N M)] (hM_ne : M ≠ M_balanced) :
    hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) <
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M) hJ_star lam D) := by
  exact not_le.mp (by
    intro hle
    exact h_crossing_contradiction M inferInstance hM_ne hle)

/-! ## Case-(ii) target wrappers from crossing contradiction -/

/-- **General spin-S case-(ii) target ground eigenspace `finrank <= 1` from a
crossing contradiction callback**.

The callback supplies the strict sector gap consumed by the PR #4098 no-full
`finrank <= 2` target wrapper. -/
theorem anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_crossing_contradiction
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
    (h_crossing_contradiction :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ_star lam D) ≤
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) →
        False) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 :=
  anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_strict_gap_no_full_le_two
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii
    (fun M hM_nonempty hM_ne => by
      letI : Nonempty (magConfigS Λ N M) := hM_nonempty
      exact anisotropicHeisenbergS_case_ii_strict_gap_all_M_of_crossing_contradiction
        (Λ := Λ) (N := N) (J := J) hJ_star M_balanced hlam_case_ii hD_case_ii
        h_crossing_contradiction M hM_ne)

/-- **General spin-S case-(ii) target ground states have zero total
magnetization from a crossing contradiction callback**. -/
theorem anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_crossing_contradiction
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
    (h_crossing_contradiction :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M) hJ_star lam D) ≤
          hermitianMinEigenvalue
            (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
              (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) →
        False)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_strict_gap_no_full_le_two
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced hlam_case_ii hD_case_ii
    (fun M hM_nonempty hM_ne => by
      letI : Nonempty (magConfigS Λ N M) := hM_nonempty
      exact anisotropicHeisenbergS_case_ii_strict_gap_all_M_of_crossing_contradiction
        (Λ := Λ) (N := N) (J := J) hJ_star M_balanced hlam_case_ii hD_case_ii
        h_crossing_contradiction M hM_ne)
    hΦ_ne hΦ_gs

end LatticeSystem.Quantum
