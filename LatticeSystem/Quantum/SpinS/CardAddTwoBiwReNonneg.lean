import LatticeSystem.Quantum.SpinS.HalfCardAddBiwReNonneg

/-!
# `0 ≤ |Λ|·N + 2·biw.re` unconditionally

Mirror of PR #3316. Doubled form of PR #3315.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ |Λ|·N + 2·biw.re`** unconditionally. Mirror of PR #3316. -/
theorem bipartiteImbalanceWeight_card_add_two_re_nonneg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    0 ≤ (Fintype.card Λ : ℝ) * (N : ℝ) +
          2 * (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  classical
  have h := bipartiteImbalanceWeight_half_card_add_re_nonneg (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
