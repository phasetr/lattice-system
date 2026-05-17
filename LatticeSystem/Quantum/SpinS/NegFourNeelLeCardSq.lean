import LatticeSystem.Quantum.SpinS.NegTwoNeelLeHalfCardSq

/-!
# `−4 · ⟨Φ_Néel⟩.re ≤ (|Λ|·N)²` unconditionally

Doubled form of PR #3281.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`−4·⟨Φ_Néel⟩.re ≤ (|Λ|·N)²`** unconditionally. Doubled form of PR #3281. -/
theorem heisenbergToyHamiltonianS_neg_four_neel_expectation_re_le_card_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    -(4 * (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re) ≤
      ((Fintype.card Λ : ℝ) * (N : ℝ)) ^ 2 := by
  have h := heisenbergToyHamiltonianS_neg_two_neel_expectation_re_le_half_card_sq
    (Λ := Λ) (A := A) (N := N)
  linarith [h, sq_nonneg ((Fintype.card Λ : ℝ) * (N : ℝ))]

end LatticeSystem.Quantum
