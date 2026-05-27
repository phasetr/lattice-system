import LatticeSystem.Quantum.SpinS.ParityReachable
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Matrix-power positivity from parity-block reachability

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For a non-negative matrix `B` on the configuration space that is strictly positive on every
parity-block move (`ParityStepS`), `ParityReachableS G σ σ'` lifts to a positive power
`0 < (B^k) σ' σ`.  Applied to the shifted dressed Perron–Frobenius matrix (strictly positive on the
moves, case (i)), this turns parity-block reachability into the matrix-power positivity feeding
`Matrix.isIrreducible_iff_exists_pow_pos`.

The proof is the parity-block analogue of `exists_matrixPow_apply_pos_of_raiseLowerReachableS`,
by induction on the `Relation.ReflTransGen` chain.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Matrix-power positivity from parity-block reachability.** For a non-negative `B` strictly
positive on every `ParityStepS`, `ParityReachableS G σ σ'` gives some `k` with `0 < (B^k) σ' σ`. -/
theorem exists_matrixPow_apply_pos_of_parityReachableS
    {G : SimpleGraph V}
    {B : Matrix (V → Fin (N + 1)) (V → Fin (N + 1)) ℝ}
    (hB_nn : ∀ σ τ, 0 ≤ B σ τ)
    (hB_step : ∀ {σ τ : V → Fin (N + 1)}, ParityStepS G σ τ → 0 < B τ σ)
    {σ σ' : V → Fin (N + 1)}
    (hreach : ParityReachableS G σ σ') :
    ∃ k : ℕ, 0 < (B ^ k) σ' σ := by
  induction hreach with
  | refl => refine ⟨0, ?_⟩; simp [Matrix.one_apply_eq]
  | tail _h₁ h₂ ih =>
    obtain ⟨k, hpos⟩ := ih
    refine ⟨k + 1, ?_⟩
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_pos'
    · intro l _
      exact mul_nonneg (hB_nn _ _) (Matrix.pow_apply_nonneg hB_nn _ _ _)
    · exact ⟨_, Finset.mem_univ _, mul_pos (hB_step h₂) hpos⟩

end LatticeSystem.Quantum
