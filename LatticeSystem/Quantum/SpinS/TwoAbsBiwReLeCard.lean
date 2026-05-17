import LatticeSystem.Quantum.SpinS.AbsBiwReLeHalfCard

/-!
# `2·|biw.re| ≤ |Λ|·N` unconditionally

Doubled form of PR #3293.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`2·|biw.re| ≤ |Λ|·N`** unconditionally. Doubled form of PR #3293. -/
theorem bipartiteImbalanceWeight_two_abs_re_le_card
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    2 * |(bipartiteImbalanceWeight (Λ := Λ) A N).re| ≤
      (Fintype.card Λ : ℝ) * (N : ℝ) := by
  classical
  have h := bipartiteImbalanceWeight_abs_re_le_half_card (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
