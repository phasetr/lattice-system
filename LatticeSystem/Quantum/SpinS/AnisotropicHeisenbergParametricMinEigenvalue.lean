import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergParametricPath
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergMagSectorMinEigenvalueContinuous

/-!
# `E_M_along_path`: the parametric per-sector min eigenvalue, named definition

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

A short-named abbreviation for the per-sector min eigenvalue along the parametric
path from `(1, 0)` to `(λ', D')`:
`E_M_along_path J hJ N M lam' D' t := hermitianMinEigenvalue (Ĥ_M(γ(t)))`.

Used in downstream capstone statements to avoid the heavy
`anisotropicHeisenbergS_magSector_submatrix_isHermitian_real`-applied-to-
`anisotropicHeisenbergParametricPath` expression triggering `whnf` heartbeat
timeouts during signature elaboration.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Parametric per-sector min eigenvalue along the path from `(1, 0)` to `(λ', D')`**:
`E_M(γ(t)) = hermitianMinEigenvalue (Ĥ_M(γ(t)))` as a `ℝ`-valued function of `t : ℝ`. -/
noncomputable def anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M : ℕ) [Nonempty (magConfigS Λ N M)] (lam' D' : ℝ) (t : ℝ) : ℝ :=
  hermitianMinEigenvalue
    (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
      (Λ := Λ) (N := N) (M := M) hJ
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2)

/-- The parametric per-sector min eigenvalue is continuous in `t`. -/
theorem continuous_anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M : ℕ) [Nonempty (magConfigS Λ N M)] (lam' D' : ℝ) :
    Continuous
      (anisotropicHeisenbergS_magSector_minEigenvalue_alongParametricPath
        (Λ := Λ) hJ N M lam' D') :=
  continuous_anisotropicHeisenbergS_magSector_minEigenvalue_along_parametricPath
    (Λ := Λ) hJ N M lam' D'

end LatticeSystem.Quantum
