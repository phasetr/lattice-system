import LatticeSystem.Quantum.SpinS.AllUpAddAllDownExpectationEqVariationalGap
import LatticeSystem.Quantum.SpinS.NegTwoNeelExpectationEqVariationalGap

/-!
# `(⟨Φ_↑⟩ + ⟨Φ_↓⟩).re = −2 · ⟨Φ_Néel⟩.re` unconditionally

Composes PR #3215 (`(⟨Φ_↑⟩ + ⟨Φ_↓⟩).re = gap.re`) with PR #3201
(`−2·⟨Φ_Néel⟩.re = gap.re`):

  `(⟨Φ_↑|Ĥ_toy|Φ_↑⟩ + ⟨Φ_↓|Ĥ_toy|Φ_↓⟩).re = −2 · ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(⟨Φ_↑⟩ + ⟨Φ_↓⟩).re = −2·⟨Φ_Néel⟩.re`** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_eq_neg_two_neel_expectation_re
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) +
          dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re =
      -(2 * (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re) := by
  have h1 := heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_eq_variational_gap_re
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_neg_two_neel_expectation_re_eq_variational_gap_re
    (Λ := Λ) (A := A) (N := N)
  linarith

end LatticeSystem.Quantum
