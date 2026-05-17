import LatticeSystem.Quantum.SpinS.VariationalGapReEqHalfCardSqSubBiwNormSq
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho

/-!
# `(|Λ|·N/2 − ‖biw‖)(|Λ|·N/2 + ‖biw‖) = |A|·|¬A|·N²` unconditionally

Difference-of-squares factorization of PR #3196. The variational gap
`|A|·|¬A|·N²` factors as the product of `|Λ|·N/2 ± ‖biw‖`, which equal
`max(|A|, |¬A|)·N` and `min(|A|, |¬A|)·N` respectively.

  `(|Λ|·N/2 − ‖biw‖)(|Λ|·N/2 + ‖biw‖) = |A|·|¬A|·N²`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`(|Λ|·N/2 − ‖biw‖)(|Λ|·N/2 + ‖biw‖) = |A|·|¬A|·N²`** unconditionally. -/
theorem bipartiteImbalanceWeight_half_card_sub_norm_mul_add_norm_eq_product
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 - ‖bipartiteImbalanceWeight (Λ := Λ) A N‖) *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 +
          ‖bipartiteImbalanceWeight (Λ := Λ) A N‖) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
        ((N : ℝ) * (N : ℝ)) := by
  have hgap := heisenbergToyHamiltonianS_variational_gap_re_eq_half_card_sq_sub_biw_norm_sq
    (Λ := Λ) (A := A) (N := N)
  rw [heisenbergToyHamiltonianS_variational_gap] at hgap
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, mul_zero, zero_mul, add_zero, sub_zero] at hgap
  -- gap = (|Λ|·N/2)² − ‖biw‖² = (a − b)(a + b) where a = |Λ|·N/2, b = ‖biw‖.
  linear_combination -hgap

end LatticeSystem.Quantum
