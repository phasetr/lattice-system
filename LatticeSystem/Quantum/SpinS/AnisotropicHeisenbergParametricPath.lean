import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorMinEigenvalueContinuous

/-!
# Parametric path `[0, 1] → ℝ × ℝ` for the obligation (2) IVT crossing argument

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

Defines the linear path
`anisotropicHeisenbergParametricPath λ' D' t := ((1 - t) + t * λ', t * D')`
from the SU(2) point `(1, 0)` to an arbitrary target `(λ', D')` in `ℝ × ℝ`,
proves continuity, and proves continuity of the composed per-sector min
eigenvalue `t ↦ hermitianMinEigenvalue (Ĥ_M(γ(t)))` on `[0, 1]`. This is
the analytic ingredient (2-IVT-a)+(2-IVT-b) of the obligation (2) IVT
crossing argument.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Linear parametric path** from the SU(2) point `(1, 0)` to `(λ', D')` in `ℝ × ℝ`,
parameterised by `t ∈ ℝ`. At `t = 0` returns `(1, 0)`; at `t = 1` returns `(λ', D')`. -/
def anisotropicHeisenbergParametricPath (lam' D' : ℝ) : ℝ → ℝ × ℝ :=
  fun t => ((1 - t) + t * lam', t * D')

/-- The parametric path is continuous in `t`. -/
theorem continuous_anisotropicHeisenbergParametricPath (lam' D' : ℝ) :
    Continuous (anisotropicHeisenbergParametricPath lam' D') := by
  unfold anisotropicHeisenbergParametricPath
  refine Continuous.prodMk ?_ ?_
  · exact ((continuous_const.sub continuous_id).add (continuous_id.mul continuous_const))
  · exact continuous_id.mul continuous_const

/-- At `t = 0` the path is at the SU(2) point `(1, 0)`. -/
@[simp]
theorem anisotropicHeisenbergParametricPath_zero (lam' D' : ℝ) :
    anisotropicHeisenbergParametricPath lam' D' 0 = (1, 0) := by
  unfold anisotropicHeisenbergParametricPath
  simp

/-- At `t = 1` the path is at the target `(λ', D')`. -/
@[simp]
theorem anisotropicHeisenbergParametricPath_one (lam' D' : ℝ) :
    anisotropicHeisenbergParametricPath lam' D' 1 = (lam', D') := by
  unfold anisotropicHeisenbergParametricPath
  simp

/-- **Composed continuity (2-IVT-b)**: `t ↦ hermitianMinEigenvalue (Ĥ_M(γ(t)))` is continuous
on `ℝ`, where `γ` is the parametric path from `(1, 0)` to `(λ', D')`. This composes the
parametric continuity of the per-sector min eigenvalue (PR #3957) with the continuity of
the path. -/
theorem continuous_anisotropicHeisenbergS_magSector_minEigenvalue_along_parametricPath
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M : ℕ) [Nonempty (magConfigS Λ N M)] (lam' D' : ℝ) :
    Continuous (fun t : ℝ => hermitianMinEigenvalue
      (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
        (Λ := Λ) (N := N) (M := M) hJ
        (anisotropicHeisenbergParametricPath lam' D' t).1
        (anisotropicHeisenbergParametricPath lam' D' t).2)) :=
  (continuous_anisotropicHeisenbergS_magSector_minEigenvalue_real (Λ := Λ) hJ N M).comp
    (continuous_anisotropicHeisenbergParametricPath lam' D')

end LatticeSystem.Quantum
