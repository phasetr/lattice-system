import LatticeSystem.Quantum.SpinS.AllUpEqAllDownExpectation
import LatticeSystem.Quantum.SpinS.TwoAllUpExpectationEqVariationalGap

/-!
# `(⟨Φ_↑⟩ + ⟨Φ_↓⟩).re = (⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re` unconditionally

The sum of the two saturated expectations equals the variational gap.
Combines PR #3202 (`⟨Φ_↑⟩.re = ⟨Φ_↓⟩.re`) with PR #3200
(`2·⟨Φ_↑⟩.re = gap.re`):

  `(⟨Φ_↑|Ĥ_toy|Φ_↑⟩ + ⟨Φ_↓|Ĥ_toy|Φ_↓⟩).re
   = (⟨Φ_↑|Ĥ_toy|Φ_↑⟩ − ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩).re`

unconditionally.

Concretely: each saturated state has `+|A|·|¬A|·N²/2`, so sum =
`+|A|·|¬A|·N² = gap`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(⟨Φ_↑⟩ + ⟨Φ_↓⟩).re = gap.re`** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_eq_variational_gap_re
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) +
          dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re =
      (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re := by
  have h1 := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_last_expectation_re
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_two_allAligned_zero_expectation_re_eq_variational_gap_re
    (Λ := Λ) (A := A) (N := N)
  rw [Complex.add_re]
  linarith

end LatticeSystem.Quantum
