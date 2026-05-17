import LatticeSystem.Quantum.SpinS.AllUpExpectationRePosIffNondeg
import LatticeSystem.Quantum.SpinS.AllUpEqAllDownExpectation

/-!
# iff: `0 < ⟨Φ_↓⟩.re ↔ nondeg`

Mirror of PR #3245 via PR #3202.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`0 < ⟨Φ_↓⟩.re iff nondeg`** unconditionally. Mirror of PR #3245. -/
theorem heisenbergToyHamiltonianS_allAligned_last_expectation_re_pos_iff_nondeg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    0 < (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧
      0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧
      0 < N := by
  rw [← heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_last_expectation_re]
  exact heisenbergToyHamiltonianS_allAligned_zero_expectation_re_pos_iff_nondeg (Λ := Λ) A N

end LatticeSystem.Quantum
