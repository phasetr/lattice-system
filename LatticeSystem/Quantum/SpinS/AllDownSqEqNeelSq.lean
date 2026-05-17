import LatticeSystem.Quantum.SpinS.AllDownExpectationEqNegNeel

/-!
# `⟨Φ_↓⟩.re² = ⟨Φ_Néel⟩.re²` unconditionally

Mirror of PR #3269 via PR #3207.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`⟨Φ_↓⟩.re² = ⟨Φ_Néel⟩.re²`** unconditionally. Mirror of PR #3269. -/
theorem heisenbergToyHamiltonianS_allAligned_last_expectation_re_sq_eq_neel_expectation_re_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (allAlignedStateS Λ N (Fin.last N)))).re ^ 2 =
      (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ^ 2 := by
  have h := heisenbergToyHamiltonianS_allAligned_last_expectation_re_eq_neg_neel_expectation_re
    (Λ := Λ) (A := A) (N := N)
  rw [h]; ring

end LatticeSystem.Quantum
