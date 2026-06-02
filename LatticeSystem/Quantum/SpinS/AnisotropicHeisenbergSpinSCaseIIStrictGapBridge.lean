import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIConditionalBridge
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSTargetFromStrictGap

/-!
# General spin-S case-(ii) strict-gap bridge for Tasaki Theorem 2.4

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

PR #4096 exposed the case-(ii) target wrappers under direct
balanced-sector/full-ground equality plus the still-explicit full
`finrank <= 2` input.  This file replaces the direct equality input by the
standard strict sector gap over all non-balanced non-empty magnetization
sectors.  The case-(ii) full `finrank <= 2` input remains explicit.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Case-(ii) target wrappers from strict sector gap -/

/-- **General spin-S case-(ii) target ground eigenspace `finrank <= 1` from
strict sector gap**.  Under the case-(ii) inequalities `1 <= lambda`,
`D <= 0`, the strict gap over every non-balanced non-empty magnetization
sector supplies balanced-sector/full-ground equality.  The remaining global
input is the full ground eigenspace `finrank <= 2` bound. -/
theorem anisotropicHeisenbergS_case_ii_target_finrank_le_one_of_strict_gap
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
    (_hlam_case_ii : 1 ≤ lam) (_hD_case_ii : D ≤ 0)
    (h_strict_gap :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) <
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M) hJ_star lam D))
    (h_full_le_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
            ℝ) : ℂ)) ≤ 2) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 :=
  anisotropicHeisenbergS_target_finrank_le_one_of_strict_gap
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced h_strict_gap h_full_le_two

/-- **General spin-S case-(ii) target ground states have zero total
magnetization from strict sector gap**.  This case-(ii)-named wrapper first
derives target uniqueness from strict sector gap and the still-explicit full
`finrank <= 2` input, then applies the uniqueness-implies-zero-magnetization
theorem. -/
theorem anisotropicHeisenbergS_case_ii_target_zero_magnetization_of_strict_gap
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
    (_hlam_case_ii : 1 ≤ lam) (_hD_case_ii : D ≤ 0)
    (h_strict_gap :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) <
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M) hJ_star lam D))
    (h_full_le_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
            ℝ) : ℂ)) ≤ 2)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 :=
  anisotropicHeisenbergS_target_groundState_zero_magnetization_of_strict_gap
    (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
    M_balanced h_balanced h_strict_gap h_full_le_two hΦ_ne hΦ_gs

end LatticeSystem.Quantum
