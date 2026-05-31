import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergBalancedIsGSAtSU2
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricMinEigenvalue
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricPath
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergFullMinEigenvalueContinuous

/-!
# Strict-GS at `(1, 0)` discharged from strict-gap axiom (axiom 2 from axiom 1)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

Combines PR #3990 (balanced IS GS from path-wise strict gap) applied at the
SU(2) point `(1, 0)` to discharge the strict-GS axiom (axiom 2 of capstone v5
#4010) from the strict-gap axiom (axiom 1).

This is the FINAL reduction: capstone v5's 2 axioms collapse to 1 mathematical
axiom (the strict gap at `(1, 0)`), assuming this brick is composed into the
chain.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Strict-GS at `(1, 0)` from path-wise strict gap (in path-named form)**:
under the strict gap at `(1, 0)` for ALL `M ≠ M_balanced` (non-empty), the
balanced sector IS the GS at `(1, 0)`, i.e., the sector-`M_balanced` min equals
the global `Ĥ(1, 0)` min. -/
theorem strict_GS_at_path_zero_from_strict_gap_at_SU2
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced : ℕ) (lam' D' : ℝ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (Λ → Fin (N + 1))]
    -- ★ Strict gap at (1, 0) for all M ≠ M_balanced (non-empty).
    (h_strict_gap_at_SU2 :
      ∀ M : ℕ, [Nonempty (magConfigS Λ N M)] → M ≠ M_balanced →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ 1 0) <
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M) hJ 1 0)) :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ N M_balanced lam' D' 0 =
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N
        (anisotropicHeisenbergParametricPath lam' D' 0).1
        (anisotropicHeisenbergParametricPath lam' D' 0).2) := by
  -- γ(0) = (1, 0). Apply PR #3990 at (1, 0).
  have hpath := anisotropicHeisenbergParametricPath_zero lam' D'
  unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
  simp only [hpath]
  -- PR #3990 gives the equality given strict gap at (1, 0).
  exact hermitianMinEigenvalue_balanced_eq_full_of_strict_gap
    hJ N M_balanced 1 0 h_strict_gap_at_SU2

end LatticeSystem.Quantum
