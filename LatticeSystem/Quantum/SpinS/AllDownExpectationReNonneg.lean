import LatticeSystem.Quantum.SpinS.AllUpExpectationReNonneg
import LatticeSystem.Quantum.SpinS.AllUpEqAllDownExpectation

/-!
# `0 ≤ ⟨Φ_↓⟩.re` unconditionally

Mirror of PR #3240 via PR #3202 (`⟨Φ_↑⟩.re = ⟨Φ_↓⟩.re`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ ⟨Φ_↓⟩.re`** unconditionally. Mirror of PR #3240. -/
theorem heisenbergToyHamiltonianS_allAligned_last_expectation_re_nonneg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    0 ≤ (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re := by
  have h1 := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_nonneg
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_last_expectation_re
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum
