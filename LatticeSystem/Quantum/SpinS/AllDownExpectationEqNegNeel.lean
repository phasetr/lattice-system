import LatticeSystem.Quantum.SpinS.AllDownAddNeelExpectationEqZero

/-!
# `⟨Φ_↓⟩.re = −⟨Φ_Néel⟩.re` unconditionally

Mirror of PR #3199. Direct corollary of PR #3206 (`(⟨Φ_↓⟩ + ⟨Φ_Néel⟩).re = 0`):

  `⟨Φ_↓|Ĥ_toy|Φ_↓⟩.re = −⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`⟨Φ_↓⟩.re = −⟨Φ_Néel⟩.re`** unconditionally. Mirror of PR #3199. -/
theorem heisenbergToyHamiltonianS_allAligned_last_expectation_re_eq_neg_neel_expectation_re
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (allAlignedStateS Λ N (Fin.last N)))).re =
      - (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re := by
  have h := heisenbergToyHamiltonianS_allAligned_last_add_neel_expectation_re_eq_zero
    (Λ := Λ) (A := A) (N := N)
  rw [Complex.add_re] at h
  linarith

end LatticeSystem.Quantum
