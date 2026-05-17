import LatticeSystem.Quantum.SpinS.AllAlignedAddNeelExpectationEqZero
import LatticeSystem.Quantum.SpinS.AllUpEqAllDownExpectation

/-!
# `(⟨Φ_↓⟩ + ⟨Φ_Néel⟩).re = 0` unconditionally

Mirror of PR #3198 for the all-down state:

  `(⟨Φ_↓|Ĥ_toy|Φ_↓⟩ + ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩).re = 0`

unconditionally. Direct corollary of PR #3198 + PR #3202.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **All-down + Néel = 0** unconditionally. Mirror of PR #3198. -/
theorem heisenbergToyHamiltonianS_allAligned_last_add_neel_expectation_re_eq_zero
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (allAlignedStateS Λ N (Fin.last N))) +
        dotProduct (star (neelStateOfS A N))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (neelStateOfS A N))).re = 0 := by
  have h1 := heisenbergToyHamiltonianS_allAligned_zero_add_neel_expectation_re_eq_zero
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_last_expectation_re
    (Λ := Λ) (A := A) (N := N)
  rw [Complex.add_re] at h1 ⊢
  linarith

end LatticeSystem.Quantum
