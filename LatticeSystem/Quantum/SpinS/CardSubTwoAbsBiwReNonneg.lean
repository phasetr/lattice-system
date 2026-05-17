import LatticeSystem.Quantum.SpinS.TwoAbsBiwReLeCard

/-!
# `0 ≤ |Λ|·N − 2·|biw.re|` unconditionally

Direct from PR #3325 (`2·|biw.re| ≤ |Λ|·N`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ |Λ|·N − 2·|biw.re|`** unconditionally. Direct from PR #3325. -/
theorem bipartiteImbalanceWeight_card_sub_two_abs_re_nonneg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    0 ≤ (Fintype.card Λ : ℝ) * (N : ℝ) -
          2 * |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
  classical
  have h := bipartiteImbalanceWeight_two_abs_re_le_card (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
