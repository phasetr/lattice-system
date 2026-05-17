import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho

/-!
# `0 ≤ (⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re` unconditionally

The variational spin gap between all-up and Néel state expectations
is always non-negative:

  `0 ≤ (⟨Φ_↑|Ĥ_toy|Φ_↑⟩ − ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩).re`

unconditionally. From the explicit gap formula `|A|·|¬A|·N²`, which is
non-negative as a product of non-negative naturals.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **0 ≤ (⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re** unconditionally. -/
theorem heisenbergToyHamiltonianS_variational_gap_re_nonneg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    0 ≤ (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re := by
  rw [heisenbergToyHamiltonianS_variational_gap]
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, mul_zero, zero_mul, add_zero, sub_zero]
  have hA_nn : (0 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := Nat.cast_nonneg _
  have hNotA_nn : (0 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := Nat.cast_nonneg _
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hA_NotA : (0 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    mul_nonneg hA_nn hNotA_nn
  have hNN : (0 : ℝ) ≤ (N : ℝ) * (N : ℝ) := mul_nonneg hN_nn hN_nn
  exact mul_nonneg hA_NotA hNN

end LatticeSystem.Quantum
