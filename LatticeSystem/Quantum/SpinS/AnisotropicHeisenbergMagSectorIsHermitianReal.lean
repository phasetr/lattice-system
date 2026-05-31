import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergContinuity

/-!
# Hermitian instance of `Ĥ_M(λ, D)` for real `(λ, D)` (ℝ-parametrised wrapper)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

Provides the per-sector Hermitian instance for the anisotropic Hamiltonian
`Ĥ_M(λ, D)` viewed as a function of `(λ, D) ∈ ℝ × ℝ` (via the real coercion to
`ℂ`). This is the small "wrapper" needed before applying
`Continuous.hermitianMinEigenvalue_comp` (PR #3953) to obtain parametric
continuity of the min eigenvalue.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- For real `r : ℝ`, `star ((r : ℂ)) = (r : ℂ)`. -/
theorem star_ofReal_eq (r : ℝ) : star ((r : ℂ)) = (r : ℂ) :=
  Complex.conj_ofReal r

/-- Per-sector restriction is Hermitian at each real `(λ, D)`. -/
theorem anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M : ℕ) (lam D : ℝ) :
    (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J ((lam : ℂ)) ((D : ℂ)) N M).IsHermitian :=
  anisotropicHeisenbergS_magSector_submatrix_isHermitian_of_real (Λ := Λ) (N := N) (M := M)
    hJ (star_ofReal_eq lam) (star_ofReal_eq D)

end LatticeSystem.Quantum
