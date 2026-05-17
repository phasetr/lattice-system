import LatticeSystem.Quantum.SpinS.AllUpExpectationReEqZeroIff
import LatticeSystem.Quantum.SpinS.AllUpEqAllDownExpectation

/-!
# iff: `⟨Φ_↓⟩.re = 0 ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`

Mirror of PR #3243 via PR #3202 (`⟨Φ_↑⟩.re = ⟨Φ_↓⟩.re`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`⟨Φ_↓⟩.re = 0 iff degenerate`** unconditionally. Mirror of PR #3243. -/
theorem heisenbergToyHamiltonianS_allAligned_last_expectation_re_eq_zero_iff
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (allAlignedStateS Λ N (Fin.last N)))).re = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨
      N = 0 := by
  rw [← heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_last_expectation_re]
  exact heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_zero_iff (Λ := Λ) A N

end LatticeSystem.Quantum
