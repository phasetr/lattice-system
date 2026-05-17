import LatticeSystem.Quantum.SpinS.BiwReLeHalfCard
import LatticeSystem.Quantum.SpinS.NegBiwReLeHalfCard

/-!
# `|biw.re| ≤ |Λ|·N/2` unconditionally

Combines PR #3291 (`biw.re ≤ |Λ|·N/2`) + PR #3292
(`−biw.re ≤ |Λ|·N/2`) via `abs_le`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`|biw.re| ≤ |Λ|·N/2`** unconditionally. -/
theorem bipartiteImbalanceWeight_abs_re_le_half_card
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    |(bipartiteImbalanceWeight (Λ := Λ) A N).re| ≤
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  classical
  have h1 := bipartiteImbalanceWeight_re_le_half_card (Λ := Λ) A N
  have h2 := bipartiteImbalanceWeight_neg_re_le_half_card (Λ := Λ) A N
  exact abs_le.mpr ⟨by linarith, h1⟩

end LatticeSystem.Quantum
