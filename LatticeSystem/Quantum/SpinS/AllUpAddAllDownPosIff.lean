import LatticeSystem.Quantum.SpinS.AllUpAddAllDownExpectationEqVariationalGap
import LatticeSystem.Quantum.SpinS.VariationalGapRePosIff

/-!
# iff: `0 < (⟨Φ_↑⟩ + ⟨Φ_↓⟩).re ↔ nondeg`

The saturated-sum expectation is strictly positive exactly when the
orientation pair is non-degenerate:

  `0 < (⟨Φ_↑|Ĥ_toy|Φ_↑⟩ + ⟨Φ_↓|Ĥ_toy|Φ_↓⟩).re
   ↔ 0 < |A| ∧ 0 < |¬A| ∧ 0 < N`.

Direct corollary of PR #3215 (saturated sum = gap) + PR #3193
(gap pos iff nondeg).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`0 < (⟨Φ_↑⟩ + ⟨Φ_↓⟩).re iff nondeg`** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_pos_iff_nondeg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    0 < (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) +
          dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
      0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
      0 < N := by
  rw [heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_eq_variational_gap_re]
  exact heisenbergToyHamiltonianS_variational_gap_re_pos_iff_nondeg (Λ := Λ) A N

end LatticeSystem.Quantum
