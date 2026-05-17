import LatticeSystem.Quantum.SpinS.TwoAllDownExpectationEqVariationalGap

/-!
# `4 · ⟨Φ_↓⟩.re² = gap²` unconditionally

Mirror of PR #3268. Squared form of PR #3208.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`4·⟨Φ_↓⟩.re² = gap²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_four_allAligned_last_expectation_re_sq_eq_variational_gap_re_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    4 * (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re ^ 2 =
      (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ^ 2 := by
  have h := heisenbergToyHamiltonianS_two_allAligned_last_expectation_re_eq_variational_gap_re
    (Λ := Λ) (A := A) (N := N)
  have hsq : (2 * (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re) ^ 2 =
      ((dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re) ^ 2 := by rw [h]
  linarith [hsq]

end LatticeSystem.Quantum
