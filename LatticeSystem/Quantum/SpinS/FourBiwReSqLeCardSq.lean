import LatticeSystem.Quantum.SpinS.BiwReSqLeHalfCardSq

/-!
# `4·biw.re² ≤ (|Λ|·N)²` unconditionally

Doubled-coefficient form of PR #3319.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`4·biw.re² ≤ (|Λ|·N)²`** unconditionally. Doubled-coefficient form of PR #3319. -/
theorem bipartiteImbalanceWeight_four_re_sq_le_card_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    4 * (bipartiteImbalanceWeight (Λ := Λ) A N).re ^ 2 ≤
      ((Fintype.card Λ : ℝ) * (N : ℝ)) ^ 2 := by
  classical
  have h := bipartiteImbalanceWeight_re_sq_le_half_card_sq (Λ := Λ) A N
  nlinarith

end LatticeSystem.Quantum
