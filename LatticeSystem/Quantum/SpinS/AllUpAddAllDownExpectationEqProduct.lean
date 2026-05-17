import LatticeSystem.Quantum.SpinS.AllUpAddAllDownExpectationEqVariationalGap
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho

/-!
# `(⟨Φ_↑⟩ + ⟨Φ_↓⟩).re = |A| · |¬A| · N²` unconditionally

Closed-form for the saturated-state expectation sum. Composes PR #3215
(saturated sum = gap) with the explicit gap formula `|A|·|¬A|·N²`:

  `(⟨Φ_↑|Ĥ_toy|Φ_↑⟩ + ⟨Φ_↓|Ĥ_toy|Φ_↓⟩).re = |A| · |¬A| · N²`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(⟨Φ_↑⟩ + ⟨Φ_↓⟩).re = |A|·|¬A|·N²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_eq_product
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) +
          dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N)))).re =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        ((N : ℝ) * (N : ℝ)) := by
  rw [heisenbergToyHamiltonianS_allAligned_zero_add_last_expectation_re_eq_variational_gap_re,
      heisenbergToyHamiltonianS_variational_gap]
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, mul_zero, zero_mul, add_zero, sub_zero]

end LatticeSystem.Quantum
