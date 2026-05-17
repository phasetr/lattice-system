import LatticeSystem.Quantum.SpinS.AllDownSubNeelExpectationEqVariationalGap
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho

/-!
# `(⟨Φ_↓⟩ − ⟨Φ_Néel⟩).re = |A| · |¬A| · N²` unconditionally

Closed form of the all-down vs Néel gap:

  `(⟨Φ_↓|Ĥ_toy|Φ_↓⟩ − ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩).re = |A| · |¬A| · N²`

unconditionally. Composes PR #3203 (`all-down gap = all-up gap`) with
the existing `heisenbergToyHamiltonianS_variational_gap`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(⟨Φ_↓⟩ − ⟨Φ_Néel⟩).re = |A|·|¬A|·N²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_last_sub_neel_expectation_re_eq_product
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (Fin.last N))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        ((N : ℝ) * (N : ℝ)) := by
  rw [heisenbergToyHamiltonianS_allAligned_last_sub_neel_expectation_re_eq_zero_sub_neel_expectation_re,
      heisenbergToyHamiltonianS_variational_gap]
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, mul_zero, zero_mul, add_zero, sub_zero]

end LatticeSystem.Quantum
