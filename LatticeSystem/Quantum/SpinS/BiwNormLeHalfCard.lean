import LatticeSystem.Quantum.SpinS.BiwNormSqLeHalfCardSq

/-!
# `‖biw‖ ≤ |Λ|·N/2` unconditionally

Square-root of PR #3225 (`‖biw‖² ≤ (|Λ|·N/2)²`). Since both sides
are non-negative, taking the square root preserves the inequality:

  `‖biw‖ ≤ |Λ|·N/2`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`‖biw‖ ≤ |Λ|·N/2`** unconditionally. Square-root of PR #3225. -/
theorem bipartiteImbalanceWeight_norm_le_half_card
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ≤ (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  have hsq := bipartiteImbalanceWeight_norm_sq_le_half_card_sq (Λ := Λ) A N
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := norm_nonneg _
  have hhalf_nn : (0 : ℝ) ≤ (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
    have hΛ : (0 : ℝ) ≤ (Fintype.card Λ : ℝ) := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    positivity
  -- ‖biw‖² ≤ (|Λ|·N/2)² and both sides non-negative → ‖biw‖ ≤ |Λ|·N/2.
  exact (sq_le_sq₀ hbiw_nn hhalf_nn).mp hsq

end LatticeSystem.Quantum
