import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `0 ≤ (2·biw.re)²` unconditionally

Doubled form of PR #3322. Direct `sq_nonneg`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ (2·biw.re)²`** unconditionally. -/
theorem bipartiteImbalanceWeight_two_re_sq_nonneg
    (A : Λ → Bool) (N : ℕ) :
    0 ≤ (2 * (bipartiteImbalanceWeight (Λ := Λ) A N).re) ^ 2 := sq_nonneg _

end LatticeSystem.Quantum
