import LatticeSystem.Quantum.SpinS.AbsBiwReNonneg

/-!
# `0 ≤ 2·|biw.re|` unconditionally

Doubled form of PR #3331.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ 2·|biw.re|`** unconditionally. Doubled form of PR #3331. -/
theorem bipartiteImbalanceWeight_two_abs_re_nonneg
    (A : Λ → Bool) (N : ℕ) :
    0 ≤ 2 * |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
  have h := bipartiteImbalanceWeight_abs_re_nonneg (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
