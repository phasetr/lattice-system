import LatticeSystem.Quantum.SpinS.AllUpAddAllDownExpectationEqVariationalGap
import LatticeSystem.Quantum.SpinS.VariationalGapReNonneg

/-!
# `0 ≤ (⟨Φ_↑⟩ + ⟨Φ_↓⟩).re` unconditionally

The saturated-sum expectation is always non-negative. Combines PR #3215
(saturated sum = gap) + PR #3195 (gap ≥ 0).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ (⟨Φ_↑⟩ + ⟨Φ_↓⟩).re`** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_nonneg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    0 ≤ (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) +
          dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re := by
  rw [heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_eq_variational_gap_re]
  exact heisenbergToyHamiltonianS_variational_gap_re_nonneg (Λ := Λ) A N

end LatticeSystem.Quantum
