import LatticeSystem.Quantum.SpinS.AllAlignedExpectationEqNegNeel

/-!
# `⟨Φ_↑⟩.re² = ⟨Φ_Néel⟩.re²` unconditionally

Squared form of PR #3199 (`⟨Φ_↑⟩.re = −⟨Φ_Néel⟩.re`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`⟨Φ_↑⟩.re² = ⟨Φ_Néel⟩.re²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_zero_expectation_re_sq_eq_neel_expectation_re_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (allAlignedStateS Λ N (0 : Fin (N + 1))))).re ^ 2 =
      (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ^ 2 := by
  have h := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_neg_neel_expectation_re
    (Λ := Λ) (A := A) (N := N)
  rw [h]; ring

end LatticeSystem.Quantum
