import LatticeSystem.Quantum.SpinS.AllUpEqAllDownExpectation
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho

/-!
# `(⟨Φ_↓⟩ − ⟨Φ_Néel⟩).re = (⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re` unconditionally

The all-down vs Néel gap equals the all-up vs Néel gap (since the two
saturated states have identical expectations):

  `(⟨Φ_↓|Ĥ_toy|Φ_↓⟩ − ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩).re
   = (⟨Φ_↑|Ĥ_toy|Φ_↑⟩ − ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩).re
   = |A| · |¬A| · N²`

unconditionally. Direct corollary of PR #3202 (`⟨Φ_↑⟩ = ⟨Φ_↓⟩` after .re).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **All-down vs Néel gap equals all-up vs Néel gap** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_last_sub_neel_expectation_re_eq_zero_sub_neel_expectation_re
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re =
      (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re := by
  have h := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_last_expectation_re
    (Λ := Λ) (A := A) (N := N)
  rw [Complex.sub_re, Complex.sub_re]
  linarith

end LatticeSystem.Quantum
