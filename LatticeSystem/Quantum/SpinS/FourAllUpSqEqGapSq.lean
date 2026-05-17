import LatticeSystem.Quantum.SpinS.TwoAllUpExpectationEqVariationalGap

/-!
# `4 · ⟨Φ_↑⟩.re² = gap²` unconditionally

Squared form of PR #3200 (`2·⟨Φ_↑⟩.re = gap.re`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`4·⟨Φ_↑⟩.re² = gap²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_four_allAligned_zero_expectation_re_sq_eq_variational_gap_re_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    4 * (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re ^ 2 =
      (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ^ 2 := by
  have h := heisenbergToyHamiltonianS_two_allAligned_zero_expectation_re_eq_variational_gap_re
    (Λ := Λ) (A := A) (N := N)
  have hsq : (2 * (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re) ^ 2 =
      ((dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re) ^ 2 := by rw [h]
  linarith [hsq]

end LatticeSystem.Quantum
