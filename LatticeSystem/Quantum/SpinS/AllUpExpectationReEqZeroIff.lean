import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho

/-!
# iff: `⟨Φ_↑⟩.re = 0 ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`

The all-up state's toy-Hamiltonian expectation `+|A|·|¬A|·N²/2`
vanishes exactly at degenerate configurations.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`⟨Φ_↑⟩.re = 0 iff degenerate`** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_zero_iff
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (allAlignedStateS Λ N (0 : Fin (N + 1))))).re = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨
      N = 0 := by
  rw [allAlignedStateS_zero_heisenbergToyHamiltonianS_expectation]
  simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul,
    add_zero, sub_zero]
  constructor
  · intro heq
    -- |A|·|¬A|·(N·N)/2 = 0 → some factor 0.
    have hprod_zero : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        ((N : ℝ) * (N : ℝ)) = 0 := by linarith
    rcases mul_eq_zero.mp hprod_zero with hANotA | hNN
    · rcases mul_eq_zero.mp hANotA with hA | hNotA
      · left; exact_mod_cast hA
      · right; left; exact_mod_cast hNotA
    · right; right
      have hN_eq : (N : ℝ) = 0 := by
        rcases mul_eq_zero.mp hNN with h | h
        · exact h
        · exact h
      exact_mod_cast hN_eq
  · intro hor
    rcases hor with hA | hNotA | hN
    · have hA_re : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) = 0 := by
        exact_mod_cast hA
      rw [hA_re]; ring
    · have hNotA_re : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 := by
        exact_mod_cast hNotA
      rw [hNotA_re]; ring
    · have hN_re : (N : ℝ) = 0 := by exact_mod_cast hN
      rw [hN_re]; ring

end LatticeSystem.Quantum
