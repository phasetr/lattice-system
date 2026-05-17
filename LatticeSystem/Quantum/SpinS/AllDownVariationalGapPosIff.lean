import LatticeSystem.Quantum.SpinS.AllDownSubNeelExpectationEqVariationalGap
import LatticeSystem.Quantum.SpinS.VariationalGapRePosIff

/-!
# iff: `0 < (⟨Φ_↓⟩ − ⟨Φ_Néel⟩).re ↔ nondeg`

Mirror of PR #3193 for the all-down state. The all-down vs Néel gap
is strictly positive exactly when the orientation pair is non-degenerate:

  `0 < (⟨Φ_↓|Ĥ_toy|Φ_↓⟩ − ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩).re
   ↔ 0 < |A| ∧ 0 < |¬A| ∧ 0 < N`.

Direct corollary of PR #3203 (`all-down gap = all-up gap`) + PR #3193
(`all-up gap > 0 iff nondeg`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`0 < (⟨Φ_↓⟩ − ⟨Φ_Néel⟩).re iff nondeg`** unconditionally. Mirror of PR #3193. -/
theorem heisenbergToyHamiltonianS_all_down_variational_gap_re_pos_iff_nondeg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    0 < (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
      0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
      0 < N := by
  rw [heisenbergToyHamiltonianS_allAligned_last_sub_neel_expectation_re_eq_zero_sub_neel_expectation_re]
  exact heisenbergToyHamiltonianS_variational_gap_re_pos_iff_nondeg (Λ := Λ) A N

end LatticeSystem.Quantum
