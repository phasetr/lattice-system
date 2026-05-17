import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho

/-!
# `0 ≤ ⟨Φ_↑⟩.re` unconditionally

The all-up state's toy-Hamiltonian expectation is always non-negative.
Directly `+|A|·|¬A|·N²/2 ≥ 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`0 ≤ ⟨Φ_↑⟩.re`** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_zero_expectation_re_nonneg
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    0 ≤ (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1))))).re := by
  rw [allAlignedStateS_zero_heisenbergToyHamiltonianS_expectation]
  simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul,
    add_zero, sub_zero]
  have hA : (0 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) := Nat.cast_nonneg _
  have hNotA : (0 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  positivity

end LatticeSystem.Quantum
