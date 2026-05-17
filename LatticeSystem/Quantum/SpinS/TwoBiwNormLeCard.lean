import LatticeSystem.Quantum.SpinS.BiwNormLeHalfCard

/-!
# `2 · ‖biw‖ ≤ |Λ| · N` unconditionally

Doubled form of PR #3226 (`‖biw‖ ≤ |Λ|·N/2`):

  `2 · ‖biw‖ ≤ |Λ| · N`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`2·‖biw‖ ≤ |Λ|·N`** unconditionally. Doubled form of PR #3226. -/
theorem two_bipartiteImbalanceWeight_norm_le_card_times_n
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    2 * ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ≤ (Fintype.card Λ : ℝ) * (N : ℝ) := by
  have h := bipartiteImbalanceWeight_norm_le_half_card (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
