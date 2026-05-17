import LatticeSystem.Quantum.SpinS.AllAlignedAddNeelExpectationEqZero
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho

/-!
# `2 · ⟨Φ_↑⟩.re = (⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re` unconditionally

From PR #3198 (`⟨Φ_↑⟩.re + ⟨Φ_Néel⟩.re = 0`):

  `2 · ⟨Φ_↑|Ĥ_toy|Φ_↑⟩.re = (⟨Φ_↑|Ĥ_toy|Φ_↑⟩ − ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩).re`

unconditionally. The all-up expectation equals half the variational
gap. Concretely:
  `⟨Φ_↑⟩.re = +|A|·|¬A|·N²/2`,
  `gap = |A|·|¬A|·N²`,
  `2·⟨Φ_↑⟩.re = gap`. ✓

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`2·⟨Φ_↑⟩.re = (⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re`** unconditionally. -/
theorem heisenbergToyHamiltonianS_two_allAligned_zero_expectation_re_eq_variational_gap_re
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    2 * (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re =
      (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re := by
  have h := heisenbergToyHamiltonianS_allAligned_zero_add_neel_expectation_re_eq_zero
    (Λ := Λ) (A := A) (N := N)
  rw [Complex.add_re] at h
  rw [Complex.sub_re]
  linarith

end LatticeSystem.Quantum
