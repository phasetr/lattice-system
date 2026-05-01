import LatticeSystem.Quantum.MarshallLiebMattis.MatrixPowPath

/-!
# One-step extension of matrix-power positivity

This module provides a one-step extension lemma for matrix-power
positivity that is the inductive step in lifting `SwapReachable`
to `(B^k) σ τ > 0`:

  If `0 < (B^m) σ τ` and `0 < B τ ρ`, then `0 < (B^(m+1)) σ ρ`.

Combined with PR α-5j's single-step swap positivity, this allows
inductively building up matrix-power positivity along a chain of
swap steps in the Marshall–Lieb–Mattis Perron–Frobenius
irreducibility argument.

Generic to any non-negative real matrix.
-/

namespace LatticeSystem.Math

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- One-step extension: if `(B^m) σ τ > 0` and `B τ ρ > 0` for a
non-negative matrix `B`, then `(B^(m+1)) σ ρ > 0`.

Proof: `B^(m+1) = B^m · B`; pick the path-`τ` term in the matrix-mul
sum, both factors positive. -/
theorem matrix_pow_succ_pos_of_pow_pos_step
    {B : Matrix n n ℝ} (hB_nn : ∀ i j, 0 ≤ B i j)
    {m : ℕ} {σ τ ρ : n}
    (hpow : 0 < (B ^ m) σ τ) (hstep : 0 < B τ ρ) :
    0 < (B ^ (m + 1)) σ ρ := by
  rw [pow_succ, Matrix.mul_apply]
  apply Finset.sum_pos'
  · intro l _
    exact mul_nonneg (Matrix.pow_apply_nonneg hB_nn _ _ _) (hB_nn _ _)
  · refine ⟨τ, Finset.mem_univ _, mul_pos hpow hstep⟩

end LatticeSystem.Math
