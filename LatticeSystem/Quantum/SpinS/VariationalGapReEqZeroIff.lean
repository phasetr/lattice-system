import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho

/-!
# iff: `(⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re = 0 ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`

Equality companion of PR #3193. The variational spin gap between
all-up and Néel state expectations vanishes exactly when the
orientation pair is degenerate (i.e. some factor is zero):

  `(⟨Φ_↑|Ĥ_toy|Φ_↑⟩ − ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩).re = 0
   ↔ |A| = 0 ∨ |¬A| = 0 ∨ N = 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re = 0 iff some factor is 0`**. Equality companion of PR #3193. -/
theorem heisenbergToyHamiltonianS_variational_gap_re_eq_zero_iff
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨
      N = 0 := by
  rw [heisenbergToyHamiltonianS_variational_gap]
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, mul_zero, zero_mul, add_zero, sub_zero]
  -- Goal: |A|·|¬A|·(N·N) = 0 ↔ one of the factors is 0.
  constructor
  · intro heq
    have hsplit : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) = 0 ∨
        ((N : ℝ) * (N : ℝ)) = 0 := mul_eq_zero.mp heq
    rcases hsplit with hANotA | hNN
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
