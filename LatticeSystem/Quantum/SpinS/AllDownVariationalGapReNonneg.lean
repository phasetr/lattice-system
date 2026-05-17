import LatticeSystem.Quantum.SpinS.AllDownSubNeelExpectationEqVariationalGap
import LatticeSystem.Quantum.SpinS.VariationalGapReNonneg

/-!
# `0 ≤ (⟨Φ_↓⟩ − ⟨Φ_Néel⟩).re` unconditionally

Mirror of PR #3195. The all-down vs Néel gap is always non-negative.

Direct corollary of PR #3203 (`all-down gap = all-up gap`) + PR #3195.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ (⟨Φ_↓⟩ − ⟨Φ_Néel⟩).re`** unconditionally. Mirror of PR #3195. -/
theorem heisenbergToyHamiltonianS_all_down_variational_gap_re_nonneg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    0 ≤ (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re := by
  rw [heisenbergToyHamiltonianS_allAligned_last_sub_neel_expectation_re_eq_zero_sub_neel_expectation_re]
  exact heisenbergToyHamiltonianS_variational_gap_re_nonneg (Λ := Λ) A N

end LatticeSystem.Quantum
