import LatticeSystem.Quantum.SpinS.AllUpAddAllDownExpectationEqVariationalGap
import LatticeSystem.Quantum.SpinS.VariationalGapLeHalfCardSq

/-!
# `(⟨Φ_↑⟩ + ⟨Φ_↓⟩).re ≤ (|Λ|·N/2)²` unconditionally

Combines PR #3203 (`(⟨Φ_↑⟩ + ⟨Φ_↓⟩).re = gap.re`) + PR #3278
(`gap.re ≤ (|Λ|·N/2)²`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(⟨Φ_↑⟩ + ⟨Φ_↓⟩).re ≤ (|Λ|·N/2)²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_le_half_card_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) +
          dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re ≤
      ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 := by
  have h_eq := heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_eq_variational_gap_re
    (Λ := Λ) (A := A) (N := N)
  have h_bound := heisenbergToyHamiltonianS_variational_gap_re_le_half_card_sq
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum
