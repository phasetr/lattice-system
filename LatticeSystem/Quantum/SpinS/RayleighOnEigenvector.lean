import LatticeSystem.Quantum.SpinS.RayleighInfMatrix
import LatticeSystem.Quantum.SpinS.SubmatrixMinEigenvalue

/-!
# Rayleigh quotient on an eigenvector

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) foundation.

For an eigenvector `v` of `M` with eigenvalue `μ` (i.e. `M.mulVec v = μ • v`)
that is *unit-normalised* (`dotProduct (star v) v = 1`), the Rayleigh quotient
`rayleighOnVec M v` equals `μ.re`. This is the canonical bridge identifying
the Rayleigh inf with the minimum eigenvalue of a Hermitian matrix.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n]

/-- **Rayleigh quotient on an eigenvector**: if `M.mulVec v = μ • v` and `v` is
unit-normalised, then `rayleighOnVec M v = μ.re`. -/
theorem rayleighOnVec_eq_re_of_eigenvector
    (M : Matrix n n ℂ) (v : n → ℂ) (μ : ℂ)
    (heig : M.mulVec v = μ • v)
    (hunit : dotProduct (star v) v = 1) :
    rayleighOnVec M v = μ.re := by
  unfold rayleighOnVec
  rw [heig, dotProduct_smul, hunit, smul_eq_mul, mul_one]

end LatticeSystem.Quantum
