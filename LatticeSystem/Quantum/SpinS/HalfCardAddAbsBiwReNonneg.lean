import LatticeSystem.Quantum.SpinS.AbsBiwReNonneg

/-!
# `0 ≤ |Λ|·N/2 + |biw.re|` unconditionally

Sum of two non-negative reals (|Λ|·N/2 ≥ 0 and |biw.re| ≥ 0).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ |Λ|·N/2 + |biw.re|`** unconditionally. Sum of non-negatives. -/
theorem bipartiteImbalanceWeight_half_card_add_abs_re_nonneg
    (A : Λ → Bool) (N : ℕ) :
    0 ≤ (Fintype.card Λ : ℝ) * (N : ℝ) / 2 +
          |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
  have h1 : (0 : ℝ) ≤ (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
    have hΛ : (0 : ℝ) ≤ (Fintype.card Λ : ℝ) := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    positivity
  have h2 := bipartiteImbalanceWeight_abs_re_nonneg (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
