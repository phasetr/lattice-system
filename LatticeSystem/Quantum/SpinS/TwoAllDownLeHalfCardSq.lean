import LatticeSystem.Quantum.SpinS.AllUpEqAllDownExpectation
import LatticeSystem.Quantum.SpinS.TwoAllUpLeHalfCardSq

/-!
# `2 · ⟨Φ_↓⟩.re ≤ (|Λ|·N/2)²` unconditionally

Mirror of PR #3280. Combines PR #3199 (`⟨Φ_↑⟩.re = ⟨Φ_↓⟩.re`) +
PR #3280 (`2·⟨Φ_↑⟩.re ≤ (|Λ|·N/2)²`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`2·⟨Φ_↓⟩.re ≤ (|Λ|·N/2)²`** unconditionally. Mirror of PR #3280. -/
theorem heisenbergToyHamiltonianS_two_allAligned_last_expectation_re_le_half_card_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    2 * (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re ≤
      ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 := by
  have h_eq := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_last_expectation_re
    (Λ := Λ) (A := A) (N := N)
  have h_bound := heisenbergToyHamiltonianS_two_allAligned_zero_expectation_re_le_half_card_sq
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum
