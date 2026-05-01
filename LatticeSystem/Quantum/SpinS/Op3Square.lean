import LatticeSystem.Quantum.SpinS.Operators

/-!
# `(Ŝ^{(3)})²` for the spin-`S` operator (Tasaki §2.1 P1d''' β-11)

The square of the diagonal operator `Ŝ^{(3)}` is itself diagonal,
with entries the squared eigenvalues `(λ_i)²`:

  `(Ŝ^{(3)})² = diag(λ_i²) = diag((N/2 − i)²)`.

This is a step toward the **Casimir identity**
`(Ŝ^{(1)})² + (Ŝ^{(2)})² + (Ŝ^{(3)})² = (N(N+2)/4) · 1`
(equivalent to `S(S+1) · 1` for `S = N/2`), the next milestone of
the §2.1 track.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- `(Ŝ^{(3)})² = diag((N/2 − i)²)`. -/
theorem spinSOp3_sq_eq_diagonal (N : ℕ) :
    spinSOp3 N * spinSOp3 N =
      Matrix.diagonal (fun i : Fin (N + 1) =>
        ((N : ℂ) / 2 - (i.val : ℂ)) * ((N : ℂ) / 2 - (i.val : ℂ))) := by
  unfold spinSOp3
  rw [Matrix.diagonal_mul_diagonal]

end LatticeSystem.Quantum
