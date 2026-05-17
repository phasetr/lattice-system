import LatticeSystem.Quantum.SpinS.AllUpAddAllDownLeHalfCardSq

/-!
# `4·(⟨Φ_↑⟩ + ⟨Φ_↓⟩).re ≤ (|Λ|·N)²` unconditionally

Doubled form of PR #3286.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`4·(⟨Φ_↑⟩+⟨Φ_↓⟩).re ≤ (|Λ|·N)²`** unconditionally. Doubled form of PR #3286. -/
theorem heisenbergToyHamiltonianS_four_allAligned_zero_add_last_expectation_re_le_card_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    4 * (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) +
          dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re ≤
      ((Fintype.card Λ : ℝ) * (N : ℝ)) ^ 2 := by
  have h := heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_le_half_card_sq
    (Λ := Λ) (A := A) (N := N)
  linarith [h, sq_nonneg ((Fintype.card Λ : ℝ) * (N : ℝ))]

end LatticeSystem.Quantum
