import LatticeSystem.Quantum.SpinS.Operators

/-!
# Spin-`S` eigenstates of `Ŝ^{(3)}` (Tasaki §2.1 P1d''' β-15)

Each unit basis vector `|k⟩ = Pi.single k 1` of `(Fin (N + 1) → ℂ)`
is an eigenvector of `Ŝ^{(3)}` with eigenvalue `λ_k = N/2 − k`:

  `Ŝ^{(3)} · |k⟩ = (N/2 − k) · |k⟩`.

This is the operator-level statement that `{|k⟩}` is the **eigenbasis**
of the diagonal operator `Ŝ^{(3)}`.  Combined with Casimir
`(Ŝ)² = (N(N+2)/4) · 1` (β-14), each `|k⟩` is also a `(Ŝ)²`
eigenvector with the universal eigenvalue, reflecting that the
spin-`S` representation is a single irreducible.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- The unit basis vector `|k⟩` is an eigenvector of `Ŝ^{(3)}` with
eigenvalue `λ_k = N/2 − k`. -/
theorem spinSOp3_mulVec_basis (N : ℕ) (k : Fin (N + 1)) :
    (spinSOp3 N).mulVec (Pi.single k 1) =
      (((N : ℂ) / 2 - (k.val : ℂ))) • (Pi.single k 1 : Fin (N + 1) → ℂ) := by
  unfold spinSOp3
  rw [Matrix.diagonal_mulVec_single]
  rw [mul_one]
  funext i
  simp [Pi.single, Pi.smul_apply, smul_eq_mul, Function.update]

end LatticeSystem.Quantum
