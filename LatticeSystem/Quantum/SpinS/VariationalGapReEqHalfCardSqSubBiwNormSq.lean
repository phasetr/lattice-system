import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs

/-!
# `(⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re = (|Λ|·N/2)² − ‖biw‖²` unconditionally

biw-norm² form of the variational spin gap. Combines the existing gap
formula `|A|·|¬A|·N²` with the algebraic identity
`|A|·|¬A| = ((|A|+|¬A|)² − (|A|−|¬A|)²)/4 = (|Λ|² − (|A|−|¬A|)²)/4`:

  `(⟨Φ_↑|Ĥ_toy|Φ_↑⟩ − ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩).re = (|Λ|·N/2)² − ‖biw‖²`

unconditionally. Equivalent factorization: gap = `max(|A|,|¬A|)·N ·
min(|A|,|¬A|)·N = (|Λ|·N/2 + ‖biw‖)(|Λ|·N/2 − ‖biw‖)`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **biw-norm² form: `(⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re = (|Λ|·N/2)² − ‖biw‖²`** unconditionally. -/
theorem heisenbergToyHamiltonianS_variational_gap_re_eq_half_card_sq_sub_biw_norm_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re =
      ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) ^ 2 -
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ^ 2 := by
  rw [heisenbergToyHamiltonianS_variational_gap]
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, mul_zero, zero_mul, add_zero, sub_zero]
  rw [bipartiteImbalanceWeight_norm_eq]
  -- Goal: |A|·|¬A|·(N·N) = (|Λ|·N/2)² − (||A|−|¬A||·(N/2))²
  --      = |Λ|²·N²/4 − (|A|−|¬A|)²·N²/4
  --      = (|Λ|² − (|A|−|¬A|)²)·N²/4
  --      = 4·|A|·|¬A|·N²/4 = |A|·|¬A|·N². ✓
  have hsum : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
      (Fintype.card Λ : ℝ) := by
    classical
    have hN' : (Finset.univ.filter (fun x : Λ => A x = true)).card +
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = Fintype.card Λ := by
      rw [← Finset.card_union_of_disjoint, ← Finset.card_univ]
      · congr 1
        ext x
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        cases A x <;> simp
      · rw [Finset.disjoint_filter]
        intro x _ hx
        simp [hx]
    exact_mod_cast hN'
  -- |x − y|² = (x − y)².
  have habs_sq : (|((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        ((N : ℝ) / 2)) ^ 2 =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) ^ 2 *
        ((N : ℝ) / 2) ^ 2 := by
    rw [mul_pow, sq_abs]
  rw [habs_sq]
  -- Substitute |Λ| via hsum.
  rw [show (Fintype.card Λ : ℝ) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) from hsum.symm]
  ring

end LatticeSystem.Quantum
