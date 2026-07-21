import LatticeSystem.Quantum.SpinS.ParityBlockSubmatrixHermitian
import LatticeSystem.Quantum.SpinS.SubmatrixMinEigenvalue

/-!
# Bare submatrix `finrank ≤ 1` at `hermitianMinEigenvalue` (conditional)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(j.11): bare-side analogue of (j.5) #3861. Given a specific `ν` with the bare-side PF
bound (from (j.10) #3868) AND `ν = hermitianMinEigenvalue bare.submatrix` (the deferred
PF = min identification), the bound transfers to `(hermitianMinEigenvalue : ℂ)`.

This is the consumer-friendly form directly consumed by (i.7) #3854's `h0`/`h1`
hypotheses for the BARE submatrix.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Bare submatrix `finrank ≤ 1` at `hermitianMinEigenvalue` (conditional)**: given a
specific `ν : ℝ` with the PF bound AND `ν = hermitianMinEigenvalue`, the bound transfers
to `(hermitianMinEigenvalue : ℂ)`. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_min_conditional
    {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hDim : D.im = 0)
    (p : ℕ) [Nonempty (parityConfigS Λ N p)]
    (ν : ℝ)
    (hν_bound : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1))) (ν : ℂ)) ≤ 1)
    (hν_eq_min : ν = hermitianMinEigenvalue
      (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
        (Λ := Λ) (N := N) hJim hlam hDim p)) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1)))
      ((hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) hJim hlam hDim p) : ℂ))) ≤ 1 := by
  rw [← hν_eq_min]
  exact hν_bound

end LatticeSystem.Quantum
