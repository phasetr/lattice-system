import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Matrix-power positivity from a positive path

This module proves a generic algebraic result needed for the
Perron–Frobenius irreducibility step in the Marshall–Lieb–Mattis
formalization:

  For a non-negative matrix `B` and a path
  `p_0, p_1, …, p_{k+1}` of vertices with `B(p_i, p_{i+1}) > 0` for
  every `i ≤ k`, the matrix-power entry
  `(B^(k + 1))(p_0)(p_{k+1}) > 0`.

Proof: induction on `k`. The base `k = 0` is the single-edge case
`(B^1) i j = B i j > 0`. The inductive step expands
`B^(k+2) = B^(k+1) · B` via `pow_succ` and extracts the path-l
term in the matrix-mul sum, where `l = p_{k+1}`.

This is generic to any `n × n` non-negative real matrix and is
used in the MLM track to lift single-step swap positivity (PR α-5j)
to multi-step matrix-power positivity, which is the input shape
required by Perron–Frobenius's
`isIrreducible_iff_exists_pow_pos`.
-/

namespace LatticeSystem.Math

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a non-negative matrix `B` and a path `p` of vertices with
positive `B`-entries on every consecutive pair, the matrix-power
entry between the endpoints is strictly positive. -/
theorem matrix_pow_succ_pos_of_path
    {B : Matrix n n ℝ} (hB_nn : ∀ i j, 0 ≤ B i j) :
    ∀ (k : ℕ) (p : ℕ → n),
      (∀ i ≤ k, 0 < B (p i) (p (i + 1))) →
      0 < (B ^ (k + 1)) (p 0) (p (k + 1))
  | 0, p, hpos => by
    rw [pow_one]
    exact hpos 0 (le_refl 0)
  | k + 1, p, hpos => by
    -- B^(k+2) = B^(k+1) * B  (`pow_succ`).
    rw [pow_succ, Matrix.mul_apply]
    -- Σ_l B^(k+1) (p 0) l * B l (p (k+2)). Take l = p (k+1).
    apply Finset.sum_pos'
    · intro l _
      exact mul_nonneg (Matrix.pow_apply_nonneg hB_nn _ _ _) (hB_nn _ _)
    · refine ⟨p (k + 1), Finset.mem_univ _, mul_pos ?_ ?_⟩
      · -- B^(k+1) (p 0) (p (k+1)) > 0 by IH on k.
        exact matrix_pow_succ_pos_of_path hB_nn k p
          (fun i hi => hpos i (Nat.le_succ_of_le hi))
      · -- B (p (k+1)) (p (k+2)) > 0 by hpos at i = k+1.
        exact hpos (k + 1) (le_refl _)

end LatticeSystem.Math
