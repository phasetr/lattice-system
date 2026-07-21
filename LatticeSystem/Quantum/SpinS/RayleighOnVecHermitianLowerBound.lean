import Mathlib.Analysis.Matrix.Spectrum

/-!
# Hermitian variational lower bound: `min eigenvalue ≤ rayleighOnVec` on unit vectors

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

For Hermitian `M` and a unit vector `v` (in the matrix-side sense
`dotProduct (star v) v = 1`), the Rayleigh quotient is bounded below by the
minimum eigenvalue:
`hermitianMinEigenvalue hM ≤ rayleighOnVec M v`.

Proof: by `Matrix.IsHermitian.spectral_theorem`, `M = U * D * Uᴴ` where
`U = eigenvectorUnitary hM` and `D = diagonal eigenvalues`. Apply
`rayleighOnVec_unitary_conj` to reduce to the diagonal case
`rayleighOnVec D (Uᴴ v)`, then apply the diagonal variational bound
(PR #3944) and the unitary unit-norm preservation (PR #3945).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- The Hermitian eigenvectorUnitary `U` is unitary: `U * Uᴴ = 1`. -/
theorem eigenvectorUnitary_mul_conjTranspose_eq_one
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (Matrix.IsHermitian.eigenvectorUnitary hM : Matrix n n ℂ) *
      (Matrix.IsHermitian.eigenvectorUnitary hM : Matrix n n ℂ).conjTranspose = 1 := by
  have h := (Matrix.IsHermitian.eigenvectorUnitary hM).property
  rw [show (Matrix.IsHermitian.eigenvectorUnitary hM :
        Matrix n n ℂ).conjTranspose = star (Matrix.IsHermitian.eigenvectorUnitary hM :
        Matrix n n ℂ) from rfl]
  exact h.2

omit [Nonempty n] in
/-- The Hermitian eigenvectorUnitary `U` is unitary: `Uᴴ * U = 1`. -/
theorem eigenvectorUnitary_conjTranspose_mul_eq_one
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (Matrix.IsHermitian.eigenvectorUnitary hM : Matrix n n ℂ).conjTranspose *
      (Matrix.IsHermitian.eigenvectorUnitary hM : Matrix n n ℂ) = 1 := by
  have h := (Matrix.IsHermitian.eigenvectorUnitary hM).property
  rw [show (Matrix.IsHermitian.eigenvectorUnitary hM :
        Matrix n n ℂ).conjTranspose = star (Matrix.IsHermitian.eigenvectorUnitary hM :
        Matrix n n ℂ) from rfl]
  exact h.1

end LatticeSystem.Quantum
