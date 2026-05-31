import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergReduction
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricMinEigenvalue
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergFullMinEigenvalueContinuous

/-!
# Strict gap at `(1, 0)` from Heisenberg GS uniqueness (MLM hypothesis)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) — strict gap chain.

A CONDITIONAL strict-gap brick: under the **Marshall-Lieb-Mattis uniqueness
hypothesis** (the Heisenberg GS eigenspace at the SU(2) point `(1, 0)` is
1-dimensional, contained in the admissible/balanced sector), the strict gap
`E_M_balanced(1, 0) < E_M(1, 0)` holds for every `M ≠ M_balanced` (non-empty
sector).

The MLM hypothesis is the OPEN axiom needed to discharge `(2-IVT-c)`. It is
classically known to hold for the bipartite isotropic Heisenberg
antiferromagnet with `|A| = |B|`, via the SU(2) Casimir argument
(`tasaki23PredictedDegeneracy = 1` for `|A| = |B|`). A direct Lean
formalisation of this fact is the remaining open work.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44; Marshall (1955), Lieb-Mattis (1962).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Strict gap at `(1, 0)` from MLM uniqueness (conditional)**: under the
hypothesis that the Heisenberg (= anisotropic at `(1, 0)`) GS eigvec is uniquely
located in sector `M_balanced` (i.e., no non-zero eigvec in any other sector
at the global min energy), the strict gap holds.

The hypothesis is stated as: at the global min eigenvalue of `Ĥ(1, 0)`, any
non-zero eigvec must have a non-zero sector-`M_balanced` restriction. -/
theorem strict_gap_at_SU2_of_GS_uniqueness
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M)]
    [Nonempty (Λ → Fin (N + 1))]
    (hM_ne_balanced : M ≠ M_balanced)
    -- MLM uniqueness hypothesis: GS uniquely located in admissible (balanced) sector.
    -- Equivalent form: sector-M-min eigenvalue > global Ĥ min for M ≠ balanced at (1, 0).
    (h_MLM_uniqueness :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0) <
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M) hJ 1 0))
    -- Strict-GS at (1, 0): balanced sector achieves the global min.
    (h_GS_at_SU2 :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ 1 0) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0)) :
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M_balanced) hJ 1 0) <
    hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M) hJ 1 0) := by
  rw [h_GS_at_SU2]
  exact h_MLM_uniqueness

/-- **Strict gap at γ(0) (path version)**: identical to the above, but stated
in the named parametric-path form needed by the obligation (2) capstones
(PRs #4001, #4010). -/
theorem strict_gap_at_path_zero_of_GS_uniqueness
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced M : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (magConfigS Λ N M)]
    [Nonempty (Λ → Fin (N + 1))]
    (lam' D' : ℝ) (hM_ne_balanced : M ≠ M_balanced)
    (h_MLM_uniqueness :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0) <
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M) hJ 1 0))
    (h_GS_at_SU2 :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ 1 0) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N 1 0)) :
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ N M_balanced lam' D' 0 <
    anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
      (Λ := Λ) hJ N M lam' D' 0 := by
  -- Unfold the named def at t = 0 → γ(0) = (1, 0).
  have hpath := anisotropicHeisenbergParametricPath_zero lam' D'
  unfold anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
  -- Replace γ(0).1 and γ(0).2 by 1 and 0 respectively via simp.
  simp only [hpath]
  exact strict_gap_at_SU2_of_GS_uniqueness hJ N M_balanced M hM_ne_balanced
    h_MLM_uniqueness h_GS_at_SU2

end LatticeSystem.Quantum
