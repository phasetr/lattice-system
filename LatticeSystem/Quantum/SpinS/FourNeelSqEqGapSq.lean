import LatticeSystem.Quantum.SpinS.NegTwoNeelExpectationEqVariationalGap

/-!
# `4 · ⟨Φ_Néel⟩.re² = gap²` unconditionally

Squared form of PR #3201 (`−2·⟨Φ_Néel⟩.re = gap.re`):

  `4 · (⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re)² = (gap.re)²`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`4·⟨Φ_Néel⟩.re² = gap²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_four_neel_expectation_re_sq_eq_variational_gap_re_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    4 * (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ^ 2 =
      (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ^ 2 := by
  have h := heisenbergToyHamiltonianS_neg_two_neel_expectation_re_eq_variational_gap_re
    (Λ := Λ) (A := A) (N := N)
  -- Square both sides.
  have hsq : (-(2 * (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re)) ^ 2 =
      ((dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re) ^ 2 := by rw [h]
  linarith [hsq, sq_nonneg (dotProduct (star (neelStateOfS A N))
    ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
      (neelStateOfS A N))).re]

end LatticeSystem.Quantum
