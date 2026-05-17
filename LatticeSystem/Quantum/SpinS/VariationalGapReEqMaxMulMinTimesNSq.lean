import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho

/-!
# `(⟨Φ_↑⟩ − ⟨Φ_Néel⟩).re = max(|A|,|¬A|) · min(|A|,|¬A|) · N²` unconditionally

Min/max factored form of the variational spin gap. Combines existing
`|A|·|¬A|·N²` with `|A|·|¬A| = max(|A|,|¬A|) · min(|A|,|¬A|)` (via
`min_mul_max`):

  `(⟨Φ_↑|Ĥ_toy|Φ_↑⟩ − ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩).re
   = max(|A|, |¬A|) · min(|A|, |¬A|) · N²`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Min/max factored form of variational gap**:
  `gap = max(|A|, |¬A|) · min(|A|, |¬A|) · N²` unconditionally. -/
theorem heisenbergToyHamiltonianS_variational_gap_re_eq_max_mul_min_times_n_sq
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re =
      max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        ((N : ℝ) * (N : ℝ)) := by
  rw [heisenbergToyHamiltonianS_variational_gap]
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, mul_zero, zero_mul, add_zero, sub_zero]
  -- |A|·|¬A| = min · max via min_mul_max.
  have hmin_max : min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
      max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    min_mul_max _ _
  -- min*max = |A|·|¬A|; want max*min*N² = |A|·|¬A|·N². Rearrange with mul_comm.
  have hmax_min : max ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
      min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    rw [mul_comm (max _ _) (min _ _)]; exact hmin_max
  linear_combination -((N : ℝ) * (N : ℝ)) * hmax_min

end LatticeSystem.Quantum
