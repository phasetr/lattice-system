import LatticeSystem.Quantum.SpinS.AllUpAddAllDownExpectationEqVariationalGap
import LatticeSystem.Quantum.SpinS.VariationalGapReEqZeroIff

/-!
# iff: `(⟨Φ_↑⟩ + ⟨Φ_↓⟩).re = 0 ↔ degenerate`

The saturated-sum expectation vanishes exactly when the orientation
pair is degenerate:

  `(⟨Φ_↑|Ĥ_toy|Φ_↑⟩ + ⟨Φ_↓|Ĥ_toy|Φ_↓⟩).re = 0
   ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`.

Composes PR #3215 + PR #3194.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(⟨Φ_↑⟩ + ⟨Φ_↓⟩).re = 0 iff degenerate`** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_eq_zero_iff
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) +
          dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨
      N = 0 := by
  rw [heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_eq_variational_gap_re]
  exact heisenbergToyHamiltonianS_variational_gap_re_eq_zero_iff (Λ := Λ) A N

end LatticeSystem.Quantum
