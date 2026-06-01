import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedIsGSAtSU2
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSBalancedSectorPFTarget

/-!
# General spin-S target uniqueness from strict sector gap

Issue #412 — Tasaki §2.5 Theorem 2.4.

This file composes the existing strict-gap-to-balanced/full equality theorem
with the balanced-sector Perron--Frobenius target wrappers.  It does not prove
the strict-gap input; it only replaces the explicit balanced/full equality
hypothesis at the target boundary by the standard strict-gap callback over all
non-balanced non-empty magnetization sectors.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **General spin-S target ground eigenspace `finrank <= 1` from strict sector
gap**: the strict gap over every non-balanced non-empty magnetization sector
supplies balanced/full equality, and the PR #4088 balanced-sector PF target
wrapper supplies full target uniqueness. -/
theorem anisotropicHeisenbergS_target_finrank_le_one_of_strict_gap
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
          ℝ) : ℂ)) ≤ 1 := by
  classical
  have h_balanced_eq_full :=
    hermitianMinEigenvalue_balanced_eq_full_of_strict_gap
      (Λ := Λ) hJ_star N M_balanced lam D h_strict_gap
  exact
    anisotropicHeisenbergS_target_finrank_le_one_of_balanced_eq_full
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
      M_balanced h_balanced h_balanced_eq_full h_full_le_two

/-- **General spin-S target ground states have zero total magnetization from
strict sector gap**: target uniqueness follows from the strict-gap wrapper, then
the existing uniqueness-implies-zero-magnetization theorem applies. -/
theorem anisotropicHeisenbergS_target_groundState_zero_magnetization_of_strict_gap
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
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  classical
  have huniq :=
    anisotropicHeisenbergS_target_finrank_le_one_of_strict_gap
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
      M_balanced h_balanced h_strict_gap h_full_le_two
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J (lam : ℂ) (D : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_gs

end LatticeSystem.Quantum
