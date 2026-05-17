import LatticeSystem.Quantum.SpinS.NegTwoNeelExpectationEqVariationalGap
import LatticeSystem.Quantum.SpinS.VariationalGapLeHalfCardSq

/-!
# `−2 · ⟨Φ_Néel⟩.re ≤ (|Λ|·N/2)²` unconditionally

Mirror of PR #3280 via PR #3201.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`−2·⟨Φ_Néel⟩.re ≤ (|Λ|·N/2)²`** unconditionally. Mirror of PR #3280. -/
theorem heisenbergToyHamiltonianS_neg_two_neel_expectation_re_le_half_card_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    -(2 * (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re) ≤
      ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 := by
  have h_eq := heisenbergToyHamiltonianS_neg_two_neel_expectation_re_eq_variational_gap_re
    (Λ := Λ) (A := A) (N := N)
  have h_bound := heisenbergToyHamiltonianS_variational_gap_re_le_half_card_sq
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum
