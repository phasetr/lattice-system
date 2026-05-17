import LatticeSystem.Quantum.SpinS.AbsBiwReLeHalfCard

/-!
# `0 ≤ |Λ|·N/2 − |biw.re|` unconditionally

Direct from PR #3293 (`|biw.re| ≤ |Λ|·N/2`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ |Λ|·N/2 − |biw.re|`** unconditionally. Direct from PR #3293. -/
theorem bipartiteImbalanceWeight_half_card_sub_abs_re_nonneg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    0 ≤ (Fintype.card Λ : ℝ) * (N : ℝ) / 2 -
          |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
  classical
  have h := bipartiteImbalanceWeight_abs_re_le_half_card (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
